module Infer where

import Unify hiding (Term,Constraint)
import qualified Unify (Term,Constraint)
import LetPoly hiding (Term)
import qualified LetPoly (Term)

type Term = LetPoly.Term
type Unificand = Unify.Term TypeVar
type Constraint = Unify.Constraint TypeVar
type Env = [(String,Type)]

-- discover types of expressions while generating constraints
-- on those types
typeCheck ::  Env -> Term -> Int -> (Type,[Constraint],Int)
typeCheck e (Var v) n =
  case lookup v e of
    Just (LetType def) -> typeCheck e def n
    Just t -> (t,[],n)
    Nothing -> error ("Unknown variable " ++ v)
typeCheck e lam @ (Lam v body) n =
  let varT = Unknown (TypeVar n (Var v))
      (bodyT,bodyConstraints,n') =
        typeCheck ((v,varT) : e) body (n + 1)
  in  (FunType varT bodyT,bodyConstraints,n')
typeCheck e app @ (App fun arg) n =
  let (funT,funConstraints,n') = typeCheck e fun n
      (argT,argConstraints,n'') = typeCheck e arg n'
      subconstraints = funConstraints ++ argConstraints
      resT = Unknown (TypeVar n'' app)
  in  (resT,(constrain funT (FunType argT resT)) : subconstraints,
        n'' + 1)
typeCheck e (Const _ t) n =
  (t,[],n)
typeCheck e (If cond trueBranch falseBranch) n =
  let (condT,condConstraints,n') = typeCheck e cond n
      (trueT,trueConstraints,n'') = typeCheck e trueBranch n'
      (falseT,falseConstraints,n''') = typeCheck e falseBranch n''
      subconstraints =
        condConstraints ++ trueConstraints ++ falseConstraints
  in  (trueT,
        (constrain condT BoolType) : (constrain trueT falseT) :
          subconstraints,
        n''')
typeCheck e (Let name def body) n =
  -- typecheck def separately: if unused, would go unchecked:
  let (_,defConstraints,n') =
        typeCheck e def n
      (bodyT,bodyConstraints,n'') =
        typeCheck ((name,LetType def) : e) body n'
  in  (bodyT,defConstraints ++ bodyConstraints,n'')

constrain :: Type -> Type -> Constraint
constrain t1 t2 = (unificand t1) `MustEqual` (unificand t2)

unificand :: Type -> Unificand
unificand BoolType = atom "bool"
unificand IntType = atom "int"
unificand (FunType t1 t2) = K "fun" [unificand t1,unificand t2]
unificand (Unknown tv) = V tv

uType :: Unificand -> Type
uType (K "bool" []) = BoolType
uType (K "int" []) = IntType
uType (K "fun" [u1,u2]) = FunType (uType u1) (uType u2)
uType (V tv) = Unknown tv
uType x = error ("Invalid unificand " ++ show x)

check :: Term -> (Type,[(TypeVar,Type,Type)])
check term =
  let (t,constraints,_) = typeCheck [] term 1
      solutions = solve constraints
  in  (uType (elimVars solutions (unificand t)),
        map (\(tv,u) -> (tv,uType u,uType (elimVars solutions u)))
          solutions)


  

