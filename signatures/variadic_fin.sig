tm: Type

cod : Functor

app (p: nat): tm -> "cod (finat p)" (tm) -> tm
lam (p: nat) : ((<p,tm>) -> tm) -> tm
