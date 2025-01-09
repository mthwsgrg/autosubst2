ty: Type
ts: Type


base : ty
arr : ty -> ty -> ty

fall (p: nat) : ((<p,ty>) -> ty) -> ts
