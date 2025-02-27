tm: Type

cod : Functor

appv (p: nat): tm -> "cod (fint p)" (tm) -> tm
app : tm -> tm -> tm
lamv (p: nat) : ((<p,tm>) -> tm) -> tm
lam : (tm -> tm) -> tm
