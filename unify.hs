module Unify (
  Term(..),
  atom,
  Constraint(..),
  unify,
  solve,
  elimVars,
  (??)) where

import Data.List

-- terms are parameterized by their variable representation (a):
data Term a =
  V a |
  K String [Term a]
atom name = K name []
instance (Eq a) => Eq (Term a) where
  V a1 == V a2 =
    a1 == a2
  K n1 ts1 == K n2 ts2 =
    n1 == n2 && ts1 == ts2
  _ == _ =
    False
instance (Show a) => Show (Term a) where
  show (V name) =
    "?<" ++ show name ++ ">"
  show (K name []) =
    name
  show (K name args) =
    name ++ "(" ++ concat (intersperse "," (map show args)) ++ ")"

data Constraint a =
  (Term a) `MustEqual` (Term a)
instance (Show a) => Show (Constraint a) where
  show (t1 `MustEqual` t2) = (show t1) ++ " =!= " ++ (show t2)

unify :: (Eq a,Show a) =>
  [Constraint a] -> Either String [Constraint a]
unify [] =
  Right []      -- no constraints means no constraints
unify (t1 `MustEqual` t2 : cs)
    | t1 == t2 =
  unify cs      -- t1 already equals t2 -- that's no constraint
unify (t1 @ (K n1 ts1) `MustEqual` t2 @ (K n2 ts2) : cs)
    | n1 /= n2 =
  Left ("Can't unify unequal constants: " ++
         show t1 ++ " and " ++ show t2)
    | length ts1 /= length ts2 =
  Left ("Can't unify argument lists of different lengths: " ++
          show t1 ++ " and " ++ show t2)
unify ((K _ ts1) `MustEqual` (K _ ts2) : cs) =
  -- equal heads with args of equal length, so recurse:
  unify (correspondingArgConstraints ++ cs)
  where correspondingArgConstraints =
          map (uncurry MustEqual) (zip ts1 ts2)
unify (k @ (K _ _) `MustEqual` v @ (V _) : cs) =
  -- swap to put V on left and handle below:
  unify (v `MustEqual` k : cs)
unify (v @ (V vName) `MustEqual` t : cs) | vName `occursIn` t =
  Left ("Infinite term would result from " ++
         show v ++ " = " ++ show t)
unify (c @ ((V vName) `MustEqual` t) : cs) =
  -- we have the right definition for variable vName; substitute
  -- that definition into remaining constraints, and include it
  -- in the result:
  fmap (\newCs -> c : newCs) (unify (substitute vName t cs))

occursIn :: (Eq a) => a -> (Term a) -> Bool
vName `occursIn` (V name) = name ==
  vName
vName `occursIn` (K _ ts) =
  or (map (\t -> vName `occursIn` t) ts)

substitute :: (Eq a) =>
  a -> (Term a) -> [Constraint a] -> [Constraint a]
substitute vName t cs = map substituteInConstraint cs
  where substituteInConstraint (t1 `MustEqual` t2) =
          (substituteInTerm vName t t1) `MustEqual`
            (substituteInTerm vName t t2)
        substituteInTerm vName t (V name)
            | name == vName =
          t
        substituteInTerm vName t (v @ (V _)) =
          v
        substituteInTerm vName t (K n ts) =
          K n (map (\t' -> substituteInTerm vName t t') ts)

solve :: (Eq a,Show a) => [Constraint a] -> [(a,Term a)]
solve constraints =
  case unify constraints of
    Left errMsg ->
      error (errMsg ++ "\nin constraints:\n" ++ showConstraints)
    Right cs ->
      map toPair cs
  where toPair ((V v) `MustEqual` t2) =
          (v,t2)
        toPair c =
          error ("Solved constraint " ++ show c ++
                  " should have variable on left!\nin:\n" ++
                  showConstraints)
        showConstraints =
          concat (intersperse "\n" (map show constraints))

elimVars :: (Eq a) => [(a,Term a)] -> Term a -> Term a
elimVars solutions (thisVar @ (V v)) =
  case lookup v solutions of
    Just nextTerm -> elimVars solutions nextTerm
    Nothing -> thisVar
elimVars solutions (K name ts) =
  K name (map (elimVars solutions) ts)

(??) :: (Eq a,Show a) => [Constraint a] -> a -> Term a
constraints ?? v = elimVars (solve constraints) (V v)
