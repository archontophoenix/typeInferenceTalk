module LetPoly (Term(..), Type(..), TypeVar(..)) where

data Term =
    Var String |
    Lam String Term |
    App Term Term |
    Const String Type | -- doesn't do anything but typecheck
    If Term Term Term |
    Let String Term Term
  deriving (Eq)
instance Show Term where
  show (Var v) =
    v
  show (Lam v body) =
    "(\\" ++ v ++ ". " ++ show body ++ ")"
  show (App fun arg) =
    showMaybeParened fun ++ " " ++ showMaybeParened arg
    where showMaybeParened t @ (App _ _) = "(" ++ show t ++ ")"
          showMaybeParened t = show t
  show (Const name _) =
    name
  show (If cond trueBranch falseBranch) =
    "(" ++ show cond ++ " ?? " ++ show trueBranch ++ " !! " ++
      show falseBranch ++ ")"
  show (Let v def body) =
    "(let " ++ v ++ " = " ++ show def ++ " in " ++ show body ++
      ")"

data Type =
    BoolType |
    IntType |
    FunType Type Type |
    LetType Term |      -- let where Term is macro definition
    Unknown TypeVar
  deriving (Eq)
instance Show Type where
  show BoolType =
    "Bool"
  show IntType = 
    "Int"
  show (FunType t1 t2) =
    showMaybeParened t1 ++ " -> " ++ showMaybeParened t2
    where showMaybeParened t @ (FunType _ _) =
            "(" ++ show t ++ ")"
          showMaybeParened t = show t
  show (LetType t) =
    "[macro def: " ++ show t ++ "]"
  show (Unknown tv) =
   show tv

-- Int in TypeVar is a counter to distinguish different
-- occurrences of structurally identical terms:
data TypeVar = TypeVar Int Term deriving (Eq)
instance Show TypeVar where
  show (TypeVar n term) =
    "<#" ++ show n ++ ": " ++ show term ++ ">"