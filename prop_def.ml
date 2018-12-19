exception EndSession;;
exception LexError;;
exception EOF;;
type proposition = 
Vrai
  |Faux
  |Var of string 
  | ET of proposition * proposition
  | NEG of proposition 
  | OU of proposition * proposition
  |IMPLIQ of proposition * proposition
;;


let lines = ref 0;;
let words = ref 0;;

