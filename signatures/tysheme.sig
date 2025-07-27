ty: Type
ts: Type


base : ty
arr : ty -> ty -> ty

fall (n: nat) : ((<n,ty>) -> ty) -> ts
