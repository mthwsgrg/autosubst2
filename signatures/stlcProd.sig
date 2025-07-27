-- Signature for stlcPlusProd

-- the types
ty : Type
tm : Type
nat : Type
pat : Type

-- the functors 
prod : Functor

-- the constructors for ty
top : ty
arr : ty -> ty -> ty
wedge : ty -> ty -> ty

-- the constructors for patterns
patvar : ty -> pat 
patlist : "prod" (pat, pat) -> pat



-- the constructors for tm
ttxx : tm
app  : tm -> tm -> tm
abs : (tm -> tm) -> tm 
couple : tm -> tm -> tm
letpat (n : nat) : pat -> tm -> (<n, tm> -> tm) -> tm
