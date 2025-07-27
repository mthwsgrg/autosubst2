tm: Type

vec : Functor

app (n: nat): tm -> "vec n" (tm) -> tm
lam (n: nat) : ((<n,tm>) -> tm) -> tm
