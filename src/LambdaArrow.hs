module LambdaArrow where

import           Control.Monad.Except
import           Data.List
import           Text.Parsec
import           Text.Parsec.String   (Parser)


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
  deriving (Eq)

-- Terms with a checkable type
data Checkable
  = Inf Inferable              -- Inferable terms
  | Lam Checkable              -- Lambda abstraction
  deriving (Eq)

data Name
  = Global String
  | Local  Int
  | Quote  Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | TFun   Type Type
  deriving (Eq)

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


--------------------------------------------------
--                                              --
--                  Quotation                   --
--                                              --
--------------------------------------------------

quote :: Value -> Checkable
quote = quote' 0

quote' :: Int -> Value -> Checkable
quote' i (VLam f)     = Lam (quote' (i + 1) (f (vfree (Quote i))))
quote' i (VNeutral n) = Inf (neutralQuote' i n)

neutralQuote' :: Int -> Neutral -> Inferable
neutralQuote' i (NFree n)  = boundFree i n
neutralQuote' i (NApp n v) = neutralQuote' i n :@: quote' i v

boundFree :: Int -> Name -> Inferable
boundFree i (Quote k) = Bound (i - k - 1)
boundFree _ n         = Free n


--------------------------------------------------
--                                              --
--                Pretty Printing               --
--                                              --
--------------------------------------------------

instance Show Type where
  show (TFree (Global a))     = a
  show (TFun t@(TFun _ _) t') = "(" <> show t <> ")" <> " -> " <> show t'
  show (TFun t t')            =  show t  <> " -> " <> show t'
  show _                      = error "Error showing type - expected global type identifier"

showInferable :: [String] -> Inferable -> String
showInferable xs = fst . showInferable' xs []

showCheckable :: [String] -> Checkable -> String
showCheckable xs = fst . showCheckable' xs []

showInferable' :: [String] -> [String] -> Inferable -> (String, [String])
showInferable' xs ys (Ann e t)
  = (s <> " :: " <> show t, xs')
  where (s, xs') = showCheckable' xs ys e
showInferable' xs  ys (Bound i)
  = (ys !! i, xs)
showInferable' xs  _  (Free (Global x))
  = (x, xs)
showInferable' _  _  (Free _)
  = error "Error showing inferable term - expected global identifier"
showInferable' xs ys (e :@: e')
  = ("(" <> s <> ") (" <> s' <> ")", xs'')
  where (s, xs') = showInferable' xs ys e
        (s', xs'')  = showCheckable' xs' ys e'

showCheckable' :: [String] -> [String] -> Checkable -> (String, [String])
showCheckable' xs ys (Inf e) = showInferable' xs ys e
showCheckable' xs ys e       = ("(λ" <> s <> ")", xs')
  where (s, xs') = showCheckable'' xs ys e

showCheckable'' :: [String] -> [String] -> Checkable -> (String, [String])
showCheckable'' xs       ys (Inf e) = (". " <> s, xs')
  where (s, xs') = showInferable' xs  ys e
showCheckable'' (x : xs) ys (Lam e) = (" " <> x <> s, xs')
  where (s, xs') = showCheckable'' xs (x : ys) e
showCheckable'' []       _  (Lam _) = error "Error showing checkable term - not enough binders provided"

instance Show Inferable where
  show = showInferable xs
    where xs = map (\n -> "x" <> show n) ([0..] :: [Int])

instance Show Checkable where
  show = showCheckable xs
    where xs = map (\n -> "x" <> show n) ([0..] :: [Int])


--------------------------------------------------
--                                              --
--                   Parsing                    --
--                                              --
--------------------------------------------------

tok :: Parser a -> Parser a
tok p = p <* spaces

lexeme :: String -> Parser String
lexeme s = tok (string s)

identifier :: Parser String
identifier = tok (many1 letter)

parens :: Parser a -> Parser a
parens p = between (lexeme "(") (lexeme ")") p

-- Parser for a free type (one or more letters)
freeType :: Parser Type
freeType = do
  x <- identifier
  return $ TFree (Global x)

-- Parser for a type expression with brackets
types :: Parser Type
types = funType

-- Parser for atomic types (single variables or parenthesized expressions)
atomicType :: Parser Type
atomicType = freeType <|> parens types

-- Parser for function types (right associative)
funType :: Parser Type
funType = do
  ts <- atomicType `sepBy1` lexeme "->"
  return $ foldr1 TFun ts

lam :: [String] -> Parser (Checkable, [String])
lam xs = do
  _          <- tok $ oneOf "λ\\"
  xs'        <- many1 identifier
  _          <- lexeme "."
  (e, xs'')  <- checkable (reverse xs' ++ xs)
  let n = length xs'
  return (iterate Lam e !! n, xs' <> xs'')

inf :: [String] -> Parser (Checkable, [String])
inf xs = do
  (e, xs') <- inferable xs
  return (Inf e, xs')

checkable :: [String] -> Parser (Checkable, [String])
checkable xs = inf xs <|> lam xs

var :: [String] -> Parser (Inferable, [String])
var xs = do
  x <- identifier
  case x `elemIndex` xs of
    Just i  -> return (Bound i, [])
    Nothing -> return (Free (Global x), [])

ann :: [String] -> Parser (Inferable, [String])
ann xs = do
  (e, xs') <- parens (checkable xs)
  _ <- lexeme "::"
  t <- types
  return (Ann e t, xs')

app :: [String] -> Parser (Inferable, [String])
app xs = do
  (e, xs')   <- parens (inferable xs)
  (e', xs'') <- parens (checkable xs)
  return (e :@: e', xs' ++ xs'')

inferable :: [String] -> Parser (Inferable, [String])
inferable xs = try (ann xs) <|> try (app xs) <|> var xs

contents :: Parser a -> Parser a
contents p = do
  spaces
  r <- p
  eof
  return r

readInferable :: String -> Either ParseError (Inferable, [String])
readInferable = parse (contents (inferable [])) "<stdin>"
