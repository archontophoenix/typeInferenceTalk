module InferTests where

import Data.List
import LetPoly
import Infer (check)

test :: Term -> String
test term =
  let (t,typeVars) = check term
  in  "\n\n" ++ show term ++ ":\n" ++ show t ++ "\n\n" ++
        (concat (intersperse "\n" (map showTypeVar typeVars))) ++
        "\n\n"
  where showTypeVar (typeVar,t,elimT) =
          show typeVar ++ " =\n  " ++ show t ++ " =\n  " ++
            show elimT

fortyTwo = Const "42" IntType

inc = Const "inc" (FunType IntType IntType)

plus = Const "+" (FunType IntType (FunType IntType IntType))

knot = Const "not" (FunType BoolType BoolType)

eyeDee = Lam "x" (Var "x")      -- leaves x unconstrained

t1 = App (App plus fortyTwo) fortyTwo

t2 =
  Lam "f" (
    Lam "g" (
      Lam "x" (
        Lam "y" (
          If (App (App (Var "f") (Var "x")) (Var "y"))
            (App (App plus (Var "x")) (Const "1" IntType))
            (App (Var "g")
                 (App (App (Var "f") (Var "x"))
                      (Const "true" BoolType)))))))

t3 =                    -- leaves y unconstrained
  Lam "h" (
    Lam "x" (
      Lam "y" (
        If (App (App (Var "h") (Var "x")) (Var "y"))
           (App (App (Var "h") (Const "3" IntType)) (Var "y"))
           (App (App (Var "h") (Var "x")) (Var "y")))))

t4 =
  Let "id" eyeDee
    (If (App (Var "id") (Const "true" BoolType))
        (Const "1" IntType)
        (App (App (Var "id") (Var "id")) (Const "2" IntType)))

t5 =    -- leaves x unconstrained and f partially constrained
  Lam "x" (Lam "f" (App (Var "f") (Var "x")))

t6 =    -- leaves x unconstrained and f partially constrained
  Lam "x" (Lam "f" (App (Var "f") (App (Var "f") (Var "x"))))

t7 =    -- all types underconstrained
  Lam "x" (
    Lam "y" (
      Lam "z" (
        App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

t8 =
  Let "twice" (
      Lam "f" (Lam "x" (App (Var "f") (App (Var "f") (Var "x")))))
    (If (App (App (Var "twice") knot) (Const "true" BoolType))
        (App (App (Var "twice") inc) (Const "1" IntType))
        fortyTwo)

allTests = [fortyTwo,inc,plus,knot,eyeDee,t1,t2,t3,t4,t5,t6,t7,t8]

main = putStrLn (concat (map test allTests))

-- testing these should fail: ------------------------------------

overconstrained1 =      -- f cannot take both Int and Bool
  Lam "f" (
    Lam "x" (
      If (App (Var "f") (Var "x"))
         (App (Var "f") (Const "3" IntType))
         (App (Var "f") (Const "false" BoolType))))

overconstrained2 =      -- k cannot take both Bool and function
  Lam "c" (
    Let "k" (Lam "x" (Var "c"))
      (If (App (Var "k") (Const "true" BoolType))
          (Const "1" IntType)
          (App (App (Var "k") (Var "k")) (Const "2" IntType))))

overconstrained3 =      -- id as a parameter can't be polymorphic
  App
    (Lam "id"
      (If (App (Var "id") (Const "true" BoolType))
          (Const "1" IntType)
          (App (App (Var "id") (Var "id")) (Const "2" IntType))))
    eyeDee

unusedBadLet = Let "garbage" (App fortyTwo fortyTwo) fortyTwo

