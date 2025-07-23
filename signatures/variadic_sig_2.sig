tm: Type

vec : Functor

app (p: nat): tm -> "vec p" (tm) -> tm
lam (p: nat) : ((<p,tm>) -> tm) -> tm
