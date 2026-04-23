list: Functor
prod: Functor

-- Signature for System F

-- the types
ty : Type
tm : Type
bool: Type

-- the constructors for ty
arr : ty -> ty -> ty
all : (ty -> ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
lam  : ty -> (tm -> tm) -> tm
tapp : tm -> ty -> tm
tlam : (ty -> tm) -> tm
lam2: (tm -> ty -> tm) -> tm
lam3 : (ty -> tm -> "list" (tm)) -> tm
lam4 : (ty -> ty -> tm) -> tm
con5 : "prod" (tm,tm) -> tm
lam5 (p: nat) : (tm -> <p,tm>  -> tm) -> tm
lam6 (p: nat) : (<p,tm> -> tm -> tm) -> tm
lam7 (p: nat) (q: nat) : (<p,tm> -> <q,tm> -> tm) -> tm
con6 : bool -> tm -> tm