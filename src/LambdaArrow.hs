module LambdaArrow where

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
  | Fun   Type Type
  deriving (Show, Eq)

data Value
  = VLam     (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp  Neutral Value

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
