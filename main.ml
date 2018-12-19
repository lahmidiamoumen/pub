(*
	@program quine algorithm
	@auther Moumen_x0x <a.lahmidi@univ-boumerdes.dz>
	@total hours  4H 
	@version 1

*)


open Prop_def;;
 
open List;;
open Prop_lexer;;


let rec cnf ter = match ter with
  |Var x ->  Var x (* sortir*)
  |Vrai ->      Vrai; (* sortir*)
  |Faux  ->     Faux; (* sortir*)
  |NEG NEG (x) -> cnf(x);
  |NEG IMPLIQ (x,y) -> cnf (ET(x,NEG y)) 
  |NEG OU (x,y) -> cnf (ET(x,y)) 
  |NEG ET (x,y) -> cnf (OU(x,y)) 
  |OU(ET(x,y),z) -> cnf (ET(OU(z,x),OU(z,y)));
  |OU(z,ET(x,y)) -> cnf (ET(OU(z,x),OU(z,y)));
  |OU(NEG IMPLIQ (x,y),z) ->cnf(ET(OU(z,x),OU(z,NEG y)));
  |OU(z,NEG IMPLIQ (x,y)) ->cnf(ET(OU(z,x),OU(z,NEG y)));
  |OU(NEG OU(x,y),z) -> cnf(ET(OU(z,NEG x),OU(z,NEG y)));
  |OU(z,NEG OU(x,y)) -> cnf(ET(OU(z,NEG x),OU(z,NEG y)));             
  |OU(x, y) ->   OU(cnf x,cnf y)
  |ET(x,y)      ->  ET(cnf x,cnf y)
  |IMPLIQ(x,y) -> cnf (OU(NEG x,y))
  |NEG x -> NEG (cnf(x)) 
  ;;

let rec choisirLiteral  fp :proposition = match fp with
  |Var x -> Var x (* sortir*)
  |Vrai ->  Vrai (* sortir*)
  |Faux  ->  Faux  (* sortir*)
  |NEG NEG x -> choisirLiteral  (x)
  |NEG IMPLIQ (x,y) -> choisirLiteral  (ET(x,NEG y)) 
  |NEG OU (x,y) -> choisirLiteral  (ET(NEG x,NEG y)) 
  |NEG ET (x,y) -> choisirLiteral  (OU(NEG x,NEG y)) 
  |OU(ET(x,y),c) -> choisirLiteral  (ET(OU(x,c),OU(y,c)))               
  |OU(x,ET(y,c)) -> choisirLiteral  (ET(OU(x,y),OU(x,c)))               
  |OU(Var x,y) -> Var x (* sortir*)
  |OU(x,y) ->   if((choisirLiteral  x = Vrai) || (choisirLiteral  x = Faux)) then choisirLiteral  y else choisirLiteral  x
  |ET(x,y) ->  if((choisirLiteral  x = Vrai) || (choisirLiteral  x = Faux)) then choisirLiteral  y else choisirLiteral  x
  |NEG x  ->  (choisirLiteral  x) 
  |IMPLIQ(x,y) -> failwith "impossible condition"
  ;;


let rec substitution f element boolien = match f with
  | Var x  when Var(x) = element ->  boolien (* sortir*)
  | ET(x,Vrai) -> x (* sortir*)
  | ET(Vrai,x) -> x (* sortir*)
  | ET(x,Faux) -> Faux (* sortir*)
  | ET(Faux,x) -> Faux (* sortir*)
  | OU(_,Vrai) -> Vrai (* sortir*)
  | OU(Vrai,_) -> Vrai (* sortir*)
  | OU(x,Faux) -> x (* sortir*)
  | OU(Faux,x) -> x (* sortir*)
  | ET(x,y)  -> ET((substitution x element boolien),(substitution y element boolien))
  | OU(x,y)  -> OU((substitution x element boolien),(substitution y element boolien))
  | NEG Vrai -> Faux (* sortir*)
  | NEG Faux -> Vrai (* sortir*)
  | NEG x -> NEG (substitution x element boolien)
  | _ -> f
  ;; 


let rec tutologie l = match l with
  | [] -> true
  | Vrai::l -> tutologie l
  | _::x -> false
  ;;

let rec contradiction l = match l with
  | [] -> true
  | Faux::l -> contradiction l
  | _::x -> false
  ;;

let find (l) = match l with
  | l when (tutologie l) -> print_string "Tautologie"
  | l when (contradiction l) -> print_string "Contradiction"
  | _ -> print_string "Satisfaisable"
  ;;

let rec df f = 
  let fp = cnf f in 
    if fp = Vrai then [Vrai]
    else if f = Faux then [Faux]
    else
      begin
        let p = choisirLiteral  fp in
        let ft =(substitution (fp) (p) (Vrai)) in
        let fs =(substitution ( fp) (p) (Faux)) in
        (df ft)@(df fs) 
      end
;;  	

(*----Read from Buffer------*)
let boucle in_channel =
let lexbuffer = Lexing.from_channel in_channel in
let lire_prop_expr () =
  Prop_parser.programme Prop_lexer.token lexbuffer in
   let p = lire_prop_expr () in find (df p) ;;
 


let readLineLoop a = let rec g i d m s= if( i > 0) 
			then
			  g (i-1) (boucle stdin) (flush  stdout)  (print_string "\n>> ")  
			else print_string "\n---------------END"  
		 		in g a (boucle stdin) (flush stdout) (print_string "----------------Quine_Algorithm--------------\n>> ") ;;


	(*-----Loop on stdin n times------*)

	readLineLoop 200 ;;

