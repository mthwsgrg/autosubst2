tmy: Type
tmx: Type
tmz: Type
pat: Type

appy : tmy -> tmy -> tmy
lamy : (tmy -> tmy) -> tmy

appx : tmx -> tmx -> tmx
lamx : (tmx -> tmx) -> tmx


appz : tmz -> tmz -> tmz
lamz : (tmz -> tmz) -> tmz

pat :  tmy -> tmx -> tmz -> pat

