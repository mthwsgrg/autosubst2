tm: Type

app : tm -> tm -> tm
lam1 : (tm -> tm) -> tm
lam2 (p: nat) : (tm -> tm -> <p,tm> -> tm) -> tm
lam3 (p: nat) : (<p,tm> -> tm -> tm -> tm) -> tm
lam4 (p: nat) (q: nat) : (<q,tm> -> tm ->  <p,tm> -> tm) -> tm