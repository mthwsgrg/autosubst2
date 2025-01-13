tm: Type

cod : Functor

app (p: nat): tm -> "cod (fint p)" (tm) -> tm
lam (p: nat) : ((<p,tm>) -> tm) -> tm
