tm: Type

cod : Functor

app (p: nat): tm -> "cod (fin (Base p))" (tm) -> tm
lam (p: nat) : ((<p,tm>) -> tm) -> tm
