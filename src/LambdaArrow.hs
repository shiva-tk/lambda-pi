module LambdaArrow where

import Control.Monad.Except


--------------------------------------------------
--                                              --
--               Abstract Syntax                --
--                                              --
--------------------------------------------------

-- Terms with an inferable type
data Inferable
  = Ann   Checkable Type       -- A checkable term with a type annotation
  | Bound Int                  -- A bound variable, represented using De Bruijn indices
  | Free  Name                 -- Free variables are named
  | (:@:) Inferable Checkable  -- Infix operator represents application
  deriving (Show, Eq)

-- Terms with a checkable type
data Checkable
  = Inf Inferable              -- Inferable terms
  | Lam Checkable              -- Lambda abstraction
  deriving (Show, Eq)

data Name
  = Global String
  | Local  Int
  | Quote  Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | TFun   Type Type
  deriving (Show, Eq)

data Value
  = VLam     (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp  Neutral Value


--------------------------------------------------
--                                              --
--                  Evaluation                  --
--                                              --
--------------------------------------------------

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp (VLam f)     v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

type Env = [Value]

evalInferable :: Inferable -> Env -> Value
evalInferable (Ann e _)  env = evalCheckable e env
evalInferable (Bound i)  env = env !! i
evalInferable (Free n)   _   = vfree n
evalInferable (e :@: e') env = vapp v v'
  where
    v  = evalInferable e  env
    v' = evalCheckable e' env

evalCheckable :: Checkable -> Env -> Value
evalCheckable (Inf e) env = evalInferable e env
evalCheckable (Lam e) env = VLam (\v -> evalCheckable e (v : env))


--------------------------------------------------
--                                              --
--                    Typing                    --
--                                              --
--------------------------------------------------

data Kind = Star
  deriving (Show)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [(Name, Info)]

type Result a = Either String a

kind :: Context -> Type -> Kind -> Result ()
kind gamma (TFree n) Star = case lookup n gamma of
  Just (HasKind Star) -> return ()
  _                   -> throwError $ "Type identifer " <> show n <> " not found in typing context"
kind gamma (TFun t t') Star = do
  kind gamma t  Star
  kind gamma t' Star

infer :: Context -> Inferable -> Result Type
infer = infer' 0

infer' :: Int -> Context -> Inferable -> Result Type
infer' i gamma (Ann e t) = do
  kind gamma t Star
  check' i gamma e t
  return t
-- Convert relative to absolute, so that we find the correct local variable in the typing environment
infer' i gamma (Bound i') = case lookup (Local (i - i')) gamma of
  Just (HasType t) -> return t
  _                -> throwError "Bound variable not found in typing context"
infer' _ gamma (Free n) = case lookup n gamma of
  Just (HasType t) -> return t
  _                -> throwError $ "Free variable " <> show n <> " not found in typing context"
infer' i gamma (e :@: e') = do
  t  <- infer' i gamma e
  case t of
    TFun t' t'' -> do check' i gamma e' t'
                      return t''
    _            -> throwError "Illegal application"

check' :: Int -> Context -> Checkable -> Type -> Result ()
check' i gamma (Inf e) t = do
  t' <- infer' i gamma e
  if t == t'
    then return ()
    else throwError "Inferred type does not match given type"
check' i gamma (Lam e) (TFun t t') =
  check' i' gamma' e t'
  where i'     = i + 1
        gamma' = (Local (i + 1), HasType t) : gamma
check' _ _ _ _ = throwError "Inferred type does not match given type"
