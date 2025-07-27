tm: Type

list : Functor

app : tm -> "list" (tm) -> tm
lam (n: nat) : ((<n,tm>) -> tm) -> tm
