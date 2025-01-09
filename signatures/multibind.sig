tm : Type
ty : Type

lamtm : (tm -> tm) -> tm
lamtwotm : (ty -> tm) -> tm
apptm : tm -> tm -> tm
extm : ty -> tm

lamty : (ty -> ty) -> ty
lamtwos2 : (tm -> ty) -> ty
appty : ty -> ty -> ty
exty : tm -> ty
