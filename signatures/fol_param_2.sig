cod: Functor

Funcs : Type
Preds : Type

term  : Type
form  : Type

Func (f : Funcs) : "cod (fun_ar f)" (term) -> term
Fal : form
Pred (P : Preds) : "cod (pred_ar P)" (term) -> form
Impl : form -> form -> form
Conj : form -> form -> form
Disj : form -> form -> form
All  : (term -> form) -> form
Ex   : (term -> form) -> form
