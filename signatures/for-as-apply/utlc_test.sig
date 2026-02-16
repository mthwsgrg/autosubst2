tm: Type

app : tm -> tm -> tm
lam1 : (tm -> tm) -> tm
lam2 (p: nat) : (tm -> tm -> <p,tm> -> tm) -> tm