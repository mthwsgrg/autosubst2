tm: Type

cod : Functor

appv (n: nat): tm -> "cod (finat n)" (tm) -> tm
app : tm -> tm -> tm
lamv (n: nat) : ((<n,tm>) -> tm) -> tm
lam : (tm -> tm) -> tm
