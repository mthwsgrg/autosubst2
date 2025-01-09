-- Signature for 

-- the types
ty : Type
tm : Type
nat : Type
pat : Type
clause : Type

-- the functors 
list : Functor
prod : Functor

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
wedge : ty -> ty -> ty
recvar : "list" ("prod" (nat, ty)) -> ty

-- the constructors for patterns
patvar : ty -> pat 
patlist : "prod" (pat, pat) -> pat

-- the constructors for clause
pipe (p:nat) : pat -> (<p, tm> -> tm) -> clause

-- the constructors for tm
app  : tm -> tm -> tm
abs : (tm -> tm) -> tm 
vartm : nat -> tm -> ty -> tm
couple : tm -> tm -> tm
proj1 : tm -> tm
proj2 : tm -> tm
case : tm -> "list" ("prod" (nat, clause)) -> tm
