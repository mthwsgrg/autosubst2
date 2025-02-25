-- Signature for System F

-- the types
ty : Type
tm : Type
nat : Type
pat : Type

-- the functors 
list : Functor
prod : Functor
cod : Functor

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
all : ty -> (ty -> ty) -> ty
recty : "list" ("prod" (nat, ty)) -> ty
listty (p: nat) : "cod (fint p)" (ty) -> ty

-- the constructors for patterns
patvar : ty -> pat 
patlist : "list" ("prod" (nat, pat)) -> pat

-- the constructors for tm
app  : tm -> tm -> tm
tapp : tm -> ty -> tm
abs : ty -> (tm -> tm) -> tm 
tabs : ty -> (ty -> tm) -> tm 
rectm : "list" ("prod" (nat, tm)) -> tm
proj : tm -> nat -> tm 
letpat (p : nat) : pat -> tm -> (<p, tm> -> tm) -> tm
appv (p: nat): tm -> "cod (fint p)" (tm) -> tm
lamv (p: nat) : ((<p,tm>) -> tm) -> tm

