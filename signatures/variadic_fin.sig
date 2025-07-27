tm: Type

cod : Functor

app (n: nat): tm -> "cod (finat n)" (tm) -> tm
lam (n: nat) : ((<n,tm>) -> tm) -> tm
