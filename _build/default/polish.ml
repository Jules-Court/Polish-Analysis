
(** Projet Polish -- Analyse statique d'un mini-langage impératif *)

(** Note : cet embryon de projet est pour l'instant en un seul fichier
    polish.ml. Il est recommandé d'architecturer ultérieurement votre
    projet en plusieurs fichiers source de tailles raisonnables *)

(*****************************************************************************)
(** Syntaxe abstraite Polish (types imposés, ne pas changer sauf extensions) *)

(** Position : numéro de ligne dans le fichier, débutant à 1 *)
type position = int

(** Nom de variable *)
type name = string

(** Opérateurs arithmétiques : + - * / % *)
type op = Add | Sub | Mul | Div | Mod

(** Expressions arithmétiques *)
type expr =
  | Num of int
  | Var of name
  | Op of op * expr * expr

(** Opérateurs de comparaisons *)
type comp =
| Eq (* = *)
| Ne (* Not equal, <> *)
| Lt (* Less than, < *)
| Le (* Less or equal, <= *)
| Gt (* Greater than, > *)
| Ge (* Greater or equal, >= *)

(** Condition : comparaison entre deux expressions *)
type cond = expr * comp * expr

(** Instructions *)
type instr =
  | Set of name * expr
  | Read of name
  | Print of expr
  | If of cond * block * block
  | While of cond * block
and block = (position * instr) list

(** Signes **)
type sign =
|Neg (*négatif*)
|Zero (*nul*)
|Pos (*positif*)
|Error (*cas particulier si division par zero*)


(** Un programme Polish est un bloc d'instructions *)
type program = block

(**********READ POLISH************)


let condition cond = (*renvoie un boolean de la comparaison numerique entre deux expressions*) (*utilisé pour --simpl*)
	let comparaison c1 com c2 =
		match com with
		|Eq -> if c1 = c2 then true else false
		|Ne -> if c1 = c2 then false else true
		|Lt -> if c1 < c2 then true else false
		|Le -> if c1 <= c2 then true else false
		|Gt -> if c1 > c2 then true else false
		|Ge -> if c1 >= c2 then true else false in
	match cond with (c1,com,c2) -> comparaison c1 com c2

let est_un_entier chaine = (*true si chaine contient un entier*)
	let check_str s = 
	  try (int_of_string s |> string_of_int) = s
	  with Failure _ -> false in
	check_str chaine

let rec est_un_comparateur ligne i = (*verifie si l'un des prochains element sur ligne est un comparateur renvoie son type correspandant et sa position*)
	match ligne with
	|[] -> (Eq,0) (*temporaire*)
	|e::ligne' -> match e with
		|"=" -> (Eq,i)
		|"<>" -> (Ne,i)
		|"<" -> (Lt,i)
		|"<=" -> (Le,i)
		|">" -> (Gt,i)
		|">=" -> (Ge,i)
		|_ -> est_un_comparateur (ligne') (i+1)

let rec profondeur ligne i= (*prend une ligne non parsé et renvoie sa profondeur*)
	try
		if (String.get ligne i = ' '); then
			profondeur (ligne) (i+1)
		else
		(i/2)
	with e-> -1

(***********************************************************************)
let rec sublist b e l = (*renvoie une liste a partir d'une autre liste l allant de l'indice b a e*)
  match l with
   | [] -> []
   | h :: t -> 
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail

let r_file (file:string) : ((int * string) list) =	(*renvoie une liste de couple (numero de ligne),(ligne) contenant le contenu d'un fichier .p passé en paramètre*)
	let ifile = open_in file in 
	(*************version recursive peu concluante, pas pu la faire fonctionner correctement on a donc garder la version iterative*************)
	(*let try_read () =   
		try Some (input_line ifile) with End_of_file -> None in
	let rec aux acc = match try_read () with
		|Some s -> aux (s::acc)
		|None -> close_in ifile; List.rev acc in
	let rec numeroter liste nligne=
		match liste with
		|[] -> []
		|e::l -> (nligne,e)::numeroter l (nligne+1) in
	List.rev (numeroter (aux []) 0) *)
	let ret = ref [(0,"")] in
	let nligne = ref 0 in
	try
		while true do
			nligne := (!nligne + 1);
			ret := (!nligne,(input_line ifile))::!ret
		done; []
	with |End_of_file -> close_in_noerr (ifile); 
	List.rev(!ret);; 

let rec recupere_expr ligne = (*prend une ligne deja parsé (liste de mots sans espaces)*)
	(*lit une ligne et place l'expression qu'elle contient dans un type correspandant*)
	if(List.length ligne > 2) then (*verifie s'il sagit d'une ligne a plus de deux elements*)
		(match ligne with
		|[] -> Var("aucune expression")
		|_::[] -> failwith("recupere_expr") 
		|e::e'::ligne' ->(match e with
			|"+" -> Op(Add,(recupere_expr (e'::ligne')),(recupere_expr (ligne')))
			|"-" -> Op(Sub,(recupere_expr (e'::ligne')),(recupere_expr (ligne')))
			|"*" -> Op(Mul,(recupere_expr (e'::ligne')),(recupere_expr (ligne')))
			|"/" -> Op(Div,(recupere_expr (e'::ligne')),(recupere_expr (ligne')))
			|"%" -> Op(Mod,(recupere_expr (e'::ligne')),(recupere_expr (ligne')))
			|_ -> if(est_un_entier e) then Num(int_of_string e) else Var(e) (*si ne contient pas d'operateur la variable/constante*)
		))
	else (*si la ligne contient moins de deux elements*)
		match ligne with
		|[] -> Var("aucune expression")
		|e::l -> if(est_un_entier e) then Num(int_of_string e) else Var(e)

let recupere_cond ligne = (*recupere un objet cond a partir de la ligne*)
	if (List.length ligne) > 0 then 
		let com = est_un_comparateur ligne 0 in
		 (*recupere les expressions avant et apres le comparateur et le comparateur lui meme et renvoie un triplet les contenant*)
		(recupere_expr ligne,fst com,recupere_expr (sublist ((snd com) + 1) (List.length ligne) ligne)) (*recupere les expressions avant et apres le comparateur et le comparateur lui meme et renvoie un triplet les contenant*)
	else (Var(""),Eq,Var(""))

let rec recupere_affectation ligne =
	(*met les affectations dans un type Set*)
	match ligne with
	|[] -> failwith "pas trouvé"
	|e::l -> if (List.nth l 0) = ":=" then Set(e, recupere_expr (sublist 1 (List.length l) l)) else recupere_affectation l

let rec existe_affectation ligne = 
	(*verifie si une affectation est presente sur ligne*)
	match ligne with
	|[] -> false
	|e::l -> if e = ":=" then true else existe_affectation l

let soc ligne =
	(*split_on_char n'est pas suffisant et ne prend pas les espaces en debut de ligne soc remedie a ça et renvoie une liste de mots sans espaces*)
	let ret = String.split_on_char ' ' ligne in
	let rec socau tab = 
		(match tab with
		|[] -> []
		|e::l -> (match e with
			|"" -> socau l
			(*renvoie une liste sans les espaces au debut de la ligne donc jusqu'au moment ou on croise le premier mot*)
			|_ -> e::(socau l))) in
	socau ret

let existe_else ligne =
	(*verifie si il ya un ELSE sur la ligne sert a recuperer les blocks correspandant pour le type IF avec read_polish*)
	let lpar = soc ligne in
	match lpar with
	|[] -> (-1,"")
	|e::l -> if (e = "ELSE") then (profondeur ligne 0,"ELSE") else (-1,"")

let rec recupere_instr ligne prog prof= (*ligne pas encore parsé, prog issue de r_file, profondeur de la ligne*)
	let rec recupere_block progb profb= (*profondeur parente*)(*sert pour les block de profondeur > 0,les block de if ou hile quoi*)	
		(match progb with (*prog restante pas depuis le debut*)
		|[] -> []
		(*si la profondeur de la ligne courante est exactement superieur de 1 par rapport a la profondeur parente il s'agit donc d'un block 'enfant' et on la recupere pour le parent*)
		|e::l -> if (profondeur (snd e) 0) = (profb + 1) then
			(fst (e),recupere_instr (snd e) (progb) (profb+1))::(recupere_block (l) (profb))else
			(*si la profondeur parente est inferieur ou egale a la profondeur de la ligne on est alors sorti du block qu'on cherchait a recuperer*)
			(*sinon si elle est superieur alors il doit s'agir d'un autre block descendant et appelle la fonction sur le reste du programme*)
			if ((profondeur (snd e) 0) <= profb) then [] else recupere_block l profb) in 
	let rec recupere_else proge profe= 
		(*On cherche une ligne contenant ELSE si elle existe (On l'appelle pour recuperer un type IF) et une fois qu'on la trouvé on applique recupere_block sur le reste du programme*)
		match proge with
		|[] -> []
		|e::l -> if (existe_else (snd e)) = (profe,"ELSE") then recupere_block l profe else recupere_else l profe in
	(*on change la ligne de string a liste de string sans espaces*)
	let l = soc ligne in
	(*On recupere les instructions en appelant les fonctions auxiliaire adequat enoncés plus haut*)
	(match l with
	|[] -> failwith ("recupere_instr")
	|e::l' ->
		(match e with 
		(*Read avec le nom de la variable positionné juste après sur la liste*)
		|"READ" -> Read (List.nth l 1)
		(*recupere_expr sur le reste de la liste apres PRINT*)
		|"PRINT" -> Print (recupere_expr l')
		(*recupere_cond pour la condition, et recupere_block et recupere_else pour les deux block*)
		|"IF" -> If (recupere_cond l',(recupere_block (List.tl prog) prof),(recupere_else (List.tl prog) prof))
		(*comme pour if mais avec un seul block a recuperer*)
		|"WHILE" -> While (recupere_cond l',(recupere_block (List.tl prog) prof))
		|_ -> if existe_affectation l then recupere_affectation l else Set("Fin",Var("Else")) ))
	

let existe_comment ligne = (*regarde si la ligne contient un commentaire pour qu'il soit caché a l'affichage*)
	let lpar = String.split_on_char ' ' ligne in
	match lpar with
	|[] -> false
	|e::l -> match e with
		|"COMMENT" -> true
		|_ -> false

let rec prog_sans_com prog = (*Analyse le programme et retir les ligne avec des commentaire*)
	match prog with
	|[] -> []
	|e::l -> if existe_comment (snd e) then prog_sans_com l else e::prog_sans_com l

let read_polish (filename:string) : program = 
	(*recupere les lignes de string avec le contenu du fichier passé en paramètres*)
	let programme = r_file filename in
	(*retire les commentaire de la liste*)
	let programmesanscom = prog_sans_com programme in
	let rec au prog =
	(*on parcourt le programme*)
		match prog with
		|[] -> []
		(*si la ligne fait partie de la profondeur du block general (0) la recupere sinon continue le parcours, les lignes de profondeur superieur a 0 seront recuperer recursivement dans leur block if et hile correspandant*)
		|e::l -> if (profondeur (snd e) 0) = 0  then ((fst e),(recupere_instr (snd e) prog (profondeur (snd e) 0)))::(au l)
			else au l in
	au programmesanscom 


(*********************PRINT POLISH*********************)

(*on print les opérateurs en évaluant le type op*)
let translate_op operate=match operate with (*lire le constructeur operation*)
		|Add->"+"
		|Sub->"-"
		|Mul->"*"
		|Div->"/"
		|Mod->"%"


(*on print les comparateurs évaluant le type comp*)
let translate_comp comp=match comp with
	|Eq->"="
	|Ne->"<>"
	|Lt->"<"
	|Le->"<="
	|Gt->">"
	|Ge->">="


(*on print les expressions évaluant le type expr*)
let rec translate expr= match expr with (*lire le constructeur expression*)
		|Num(n)->string_of_int n
		|Var(n)->n
		|Op(o,exp1,exp2)->(translate_op o)^" "^(translate exp1)^" "^(translate exp2)


(*on print le type condition en l'évaluant*)
let translate_cond cond = match cond with 
		|exp1,comp,exp2->translate exp1^" "^translate_comp comp^" "^translate exp2

(*fonction qui gère l'indentation du programme*)
let rec indentation i =
	if i>0 then 
		"  "^indentation (i-1)
	else 
		""

	(*fonction appelé dans print_polish pour mieux gérer l'indentation*)
	let rec print_polish_depth (p:program) (cpt: int) : unit=
		match p with
		|[]->print_string ""
		|(_,b)::sublist-> 
			match b with 
			|Read(n) -> print_string ((indentation cpt)^"READ "^n^"\n");print_polish_depth sublist cpt
			|Print(n) -> print_string ((indentation cpt)^"PRINT "^ translate n^"\n");print_polish_depth sublist cpt
			|Set(n,expr) ->
			if(n<>"Fin")then (print_string((indentation cpt)^n^" := "^translate expr^"\n");print_polish_depth sublist cpt)
			else (print_polish_depth sublist cpt)
			|If(cond,block1,block2) -> print_string ((indentation cpt)^"IF "^translate_cond cond^"\n");
			print_polish_depth block1 (cpt+1);
			print_string ((indentation cpt)^"ELSE \n");print_polish_depth block2 (cpt+1);print_polish_depth sublist cpt
			
			|While(cond,block)->print_string ((indentation cpt)^"WHILE "^translate_cond cond^"\n");
			print_polish_depth block (cpt+1);
			print_polish_depth sublist cpt

(*print_polish qui appelle la fonction du dessus avec 0 en indentation pour commencer*)
let print_polish (p:program) : unit = print_polish_depth p 0

	

(*************EVAL POLISH**********************)

(* on évalue le type expression pour les cas Print/Set/Read *) 
let rec eval expr env = match expr with
	| Num(n) -> n
	| Var(n) -> (try List.assoc n env with e->print_string ""; 0)
	| Op(op, expr1, expr2) ->
		match op with
			| Add -> eval expr1 env + eval expr2 env
			| Sub -> eval expr1 env - eval expr2 env
			| Mul -> eval expr1 env * eval expr2 env
			| Div -> eval expr1 env / eval expr2 env
			| Mod -> eval expr1 env mod eval expr2 env


(* on supprime l'ancienne valeur qui se trouve dans l'env pour la supprimé par une nouvelle *)
let maj_env key expr env = let new_env = List.remove_assoc key env in (key,expr)::new_env

(* on évalue le type condition pour les cas If/While *)
let eval_cond cond env = match cond with 
	|expr1,comp,expr2->match comp with 
		|Eq -> (eval expr1 env) = (eval expr2 env)
		|Ne -> (eval expr1 env) <> (eval expr2 env)
		|Lt -> (eval expr1 env) < (eval expr2 env)
		|Le -> (eval expr1 env) <= (eval expr2 env)
		|Gt -> (eval expr1 env) > (eval expr2 env)
		|Ge -> (eval expr1 env) >= (eval expr2 env)


let eval_polish (p:program) : unit =
	let rec environnement prog env = 
		match prog with
			|[]->env
			|(_,b)::sublist->
				match b with 
					|Read(n)-> let read = read_int () in environnement sublist (maj_env n read env)
					|Set(n,expr)-> let eval_expr = eval expr env in environnement sublist (maj_env n eval_expr env) 
					|Print(expr)-> print_string(string_of_int (eval expr env)^"\n"); environnement sublist env
					|If(cond,block1,block2)-> let eval_if = 
						if eval_cond cond env then
								environnement block1 env 
						else
								environnement block2 env in environnement sublist eval_if
						 
					|While(cond,block1)->(*let eval_while=
					if eval_cond cond env then 
						environnement block1 env
					else env in*)
						if eval_cond cond env then
							environnement prog (environnement block1 env) (*eval_while*)
						else
							environnement sublist env  

		in let environnement2 =  environnement p [] in ()



(********************SIMPL POLISH************************) 
let est_un_num expr =
	match expr with
	|Num(n) -> true
	|_ -> false

let rec simpl_expr e =
	let rec simpl_add e1 e2 = (*Pour les additions*)
		match e1 with
		|Num(0) -> e2 (*si le chiffre est egale a 0 donc la valeur sera celle du 2eme composant quel qu'il soit*)
		|Num(n) -> (match e2 with 
					|Num(n2) -> Num(n+n2) (*Si on a 2 nombre on les additionne*)
					|Op(o,c1,c2) -> simpl_add e1 (simpl_expr e2)
					|_ -> Op(Add,e1,e2)) (*si la 2eme composante est une variable on laisse tel quel*)
		|Var(v) -> (match e2 with
					|Num(0) -> e1
					|Op(o,c1,c2) -> simpl_add e1 (simpl_expr e2)
					|_ -> Op(Add,e1,e2) ) (*si 2 variables*) 
		|_ -> Op(Add,e1,e2) in
	let rec simpl_sub e1 e2 = (*Pour les soustractions*)
		match e1 with
		|Num(n) -> (match e2 with
					|Num(n2) -> Num(n-n2)
					|Op(o,c1,c2) -> simpl_sub e1 (simpl_expr e2)
					|_ -> Op(Sub,e1,e2))
		|Var(v) -> (match e2 with
					|Num(0) -> e1
					|Op(o,c1,c2) -> simpl_sub e1 (simpl_expr e2)
					|_ -> Op(Sub,e1,e2))
		|_ -> Op(Sub,e1,e2) in
	let rec simpl_mul e1 e2 = (*Multiplication*)
		match e1 with
		|Num(0) -> Num(0)
		|Num(1) -> e2
		|Num(n) -> (match e2 with
					|Num(n2) -> Num(n*n2)
					|Op(o,c1,c2) -> simpl_mul e1 (simpl_expr e2)
					|_ -> Op(Mul,e1,e2) )
		|Var(v) -> (match e2 with
					|Num(0) -> Num(0)
					|Num(1) -> Var(v)
					|Op(o,c1,c2) -> simpl_mul e1 (simpl_expr e2)
					|_ -> Op(Mul,e1,e2))
		|_ -> Op(Mul,e1,e2) in
	let rec simpl_div e1 e2 = (*Division*)
		match e1 with
		|Num(0) -> Num(0)
		|Num(n) -> (match e2 with
					|Num(n2) -> Num(n/n2)
					|Op(o,c1,c2) -> simpl_div e1 (simpl_expr e2)
					|_ -> Op(Div,e1,e2) )
		|Var(v) -> (match e2 with
					|Num(1) -> Var(v)
					|Op(o,c1,c2) -> simpl_div e1 (simpl_expr e2)
					|_ -> Op(Div,e1,e2) )
		|_ -> Op(Div,e1,e2) in
	let rec simpl_mod e1 e2 = (*Modulo*)
		match e1 with
		|Num(n) -> (match e2 with
					|Num(n2) -> Num(n mod n2)
					|Op(o,c1,c2) -> simpl_mod e1 (simpl_expr e2)
					|_ -> Op(Mod,e1,e2) )
		|Var(v) -> (match e2 with
					|Num(1) -> Num(0)
					|Op(o,c1,c2) -> simpl_mod e1 (simpl_expr e2)
					|_ -> Op(Mod,e1,e2))
		|_ -> Op(Mod,e1,e2) in
	match e with
	(*Simplifie chaque operation selon leur type*)
	|Op(o,e1,e2) -> 
		(match o with
			|Add -> simpl_add e1 e2
			|Sub -> simpl_sub e1 e2
			|Mul -> simpl_mul e1 e2
			|Div -> simpl_div e1 e2
			|Mod -> simpl_mod e1 e2)
	|_ -> e

let simpl_cond cond =
	(*simplifie chaque elements d'une condition*)
	match cond with
	|e1,c,e2 -> (simpl_expr e1,c,simpl_expr e2)

let simpl_polish (p:program) : unit = 
	let rec simpl_polish_PC (prog:program) : program = (*Propagation des constantes*)
		match prog with
		 |[] -> []
		 |(line,b)::sublist ->
		 	match b with
		 	(*On commence par simplifier toute les expressions du programme autant que possible*)
		 	 |Set(n,expr) -> (line, Set(n,(simpl_expr expr)))::simpl_polish_PC sublist
		 	 |Print(expr) -> (line, Print(simpl_expr expr))::simpl_polish_PC sublist
		 	 |If(cond,block1,block2) -> (line, If(simpl_cond cond,(simpl_polish_PC block1),(simpl_polish_PC block2)))::simpl_polish_PC sublist
		 	 |While(cond,block) -> (line, While(cond,(simpl_polish_PC block)))::simpl_polish_PC sublist
		 	 |_ -> (line,b)::simpl_polish_PC sublist in
	let rec simpl_polish_elim (prog:program) : program = (*Elimination du code mort*)
		match prog with
		 |[] -> []
		 |(line,b)::sublist ->
		 	match b with
		 	(*On retire de l'affichage les blocks obsolète en fonction de la simplification de leur condtion*)
		 	 |If(cond,block1,block2) -> 
		 	 	(match cond with
		 	 	|e1,c,e2 -> if (est_un_num e1 && est_un_num e2) then if (condition cond) then (simpl_polish_elim block1)@simpl_polish_elim sublist else (simpl_polish_elim block2)@simpl_polish_elim sublist else (line,b)::simpl_polish_elim sublist)
		 	 |While(cond,block) -> (line, While(cond,(simpl_polish_elim block)))::simpl_polish_elim sublist
		 	 |_ -> (line,b)::simpl_polish_elim sublist in
	(*On utilise print_polish pour afficher la liste resultante des fonctions internes ci-dessus*)
	print_polish (simpl_polish_elim (simpl_polish_PC p))



(****************************VARS POLISH*******************************)
module Names = Set.Make(String) (*Creation du module *)

let maj_set n new_module= Names.add n new_module (*Ajout dans le module*)

let eval_expr_vars e = (*eval expr pour ajouter au module*)
	let rec eval_update expr set_module = match expr with 
		|Num(n)-> set_module
		|Var(n)-> Names.add n set_module 
		|Op(op,e1,e2)-> Names.union (eval_update e1 set_module)  (eval_update e2 set_module)

	in eval_update e Names.empty 

(*
		Trois module, un pour comparaison des variables
		on compare set_module et wrong_list, si la variable est dans wrong_list
		on l'affiche dans les variables a risque. On concatene ensuite wrong_list et 
		set_all pour avoir toutes les variables 
		*)

let vars_polish (p:program) : unit = 
	let rec set_update prog set_module wrong_list set_all = 
		match prog with
			|[]-> (set_module, wrong_list,set_all)
			|(_,b)::sublist->
				match b with
				|Read(n)-> set_update sublist (maj_set n set_module) wrong_list (maj_set n set_all)
				|Set(n,expr)->
				if(n<>"Fin") then
				let eval = (eval_expr_vars expr) in
				 let compare = Names.diff eval set_module in set_update sublist (maj_set n set_module) (Names.union compare wrong_list) (maj_set n set_all)
				else set_update sublist (set_module) wrong_list set_all
				
				|Print(expr)-> 
				let eval = (eval_expr_vars expr) in
					let compare = Names.diff eval  set_module in set_update sublist (set_module) (Names.union compare wrong_list) (set_all)

				|If(cond,block1,block2)->
				let (set_module1,wrong1,set_all1)= set_update block1 (set_module) wrong_list set_all in
				 let (set_module2,wrong2,set_all2) = set_update block2 (set_module) wrong_list set_all
				 	in set_update sublist set_module (Names.union wrong1 wrong2) (Names.union set_all1 set_all2)

				|While(cond,block)->
				let (set_module1,wrong1,set_all1) = set_update block (set_module) wrong_list set_all in set_update sublist set_module wrong1 set_all1
				
				in let (set_module1,wrong1,set_all1) =  set_update p Names.empty Names.empty Names.empty in
				 Names.iter (fun x-> print_string (x^" ")) (Names.union wrong1 set_all1); print_string "\n" ;Names.iter (fun x-> print_string (x^" ")) (wrong1);print_string "\n"


(****************************SIGN POLISH*************************)

let rec is_present env key =
	(*verifie si une variable est deja presente dans l'environnement passé en paramètres*)
	match env with
	|[] -> false
	|e::l -> if ((fst e) = (key)) then true else is_present l key

let add_toenv env elem =
	(*ajoute un element a l'environnement*)
	(elem::env) 

let rec maj_sign_env env key new_val =
	(*met a jour la variable de environnement avec une nouvelle valeur, necessite que la variable existe deja dans l'environnement*)
	match env with
	|[] -> failwith ("maj_sign_env")
	|e::l -> if ((fst e) = key) then (key, new_val)::l else e::(maj_sign_env l key new_val)

let rec get_sign env key =
	(*recupere le sign list d'une variable d'un environnement*)
	match env with
	|[] -> Pos::Zero::Neg::[]
	|e::l -> if (fst e) = key then snd e else get_sign l key

let sign_int n = 
	(*recupere le signe d'une constante*)
	match n with
	|0 -> [Zero]
	|_ -> if (n < 0) then [Neg] else [Pos]



let rec sign_op op e1 e2 env=
	let get_sign_intorval env expr =
		(*recupere le sign list d'une constante ou variable, fonctionne recursivement avec les operations*)
		match expr with
		|Num(n) -> sign_int n
		|Var(v) -> (get_sign env v)
		|Op(o,c1,c2) -> sign_op o c1 c2 env in
	let sign_mul e1 e2 = (*signe d'une operation de multiplication*)
		if (get_sign_intorval env e1 = [Zero]) || (get_sign_intorval env e2 = [Zero]) then [Zero] else
		if (get_sign_intorval env e1 = get_sign_intorval env e2) then [Pos] else
		if ((get_sign_intorval env e1 = [Pos]) && (get_sign_intorval env e2 = [Neg])) || ((get_sign_intorval env e1 = [Neg]) && (get_sign_intorval env e2 = [Pos])) then [Neg] else
		Pos::Neg::[] in
	let sign_div e1 e2 = (*division*)
		if (get_sign_intorval env e2 = [Zero]) then [Error] else
		if (get_sign_intorval env e1 = [Zero]) then [Zero] else
		if (get_sign_intorval env e1 = get_sign_intorval env e2) then [Pos] else
		if ((get_sign_intorval env e1 = [Pos]) && (get_sign_intorval env e2 = [Neg])) || ((get_sign_intorval env e1 = [Neg]) && (get_sign_intorval env e2 = [Pos])) then [Neg] else
		Pos::Neg::[]  in
	let sign_mod e1 e2 = (*modulo*)
		if (get_sign_intorval env e2 = [Zero]) then [Error] else
		if (get_sign_intorval env e1 = [Zero]) then [Zero] else
		[Pos] in
	match op with
	|Add -> if (get_sign_intorval env e1) = (get_sign_intorval env e2) then get_sign_intorval env e1 else Pos::Zero::Neg::[]
	|Sub -> Pos::Zero::Neg::[]
	|Mul -> sign_mul e1 e2
	|Div -> sign_div e1 e2 
	|Mod -> sign_mod e1 e2

let sign_set_expr env name expr=
	(*ajoute les variables ajouté dans une affection dans l'environnement ou met a jour leur valeur sont deja presente avec leur affection*)
	match expr with
	|Op(o,c1,c2) -> if (is_present env name) then maj_sign_env env name (sign_op o c1 c2 env) else add_toenv env (name, sign_op o c1 c2 env)
	|Num(n) -> if (is_present env name) then maj_sign_env env name (sign_int n) else add_toenv env (name,sign_int n)
	|Var(v) -> if (is_present env name) then maj_sign_env env name (get_sign env v) else add_toenv env (name,get_sign env v)

let rec print_sign_line sign_list = 
	(*affichage de la sign list passé en paramètres*)
	match sign_list with
	|[] -> print_string "\n"
	|e::l -> match e with
			|Pos -> print_string "+" ; print_sign_line l
			|Zero -> print_string "0" ; print_sign_line l
			|Neg -> print_string "-" ; print_sign_line l
			|Error -> print_string "!" ; print_sign_line l

let sign_polish prog =
	let rec sign_polish_aux prog env= 
		(*remplissage de l'environnement avec le programme*)
		match prog with 
		|[] -> List.rev env
		|(_,e)::l -> match e with
				(*Pour les affectations*)
				|Set(name,expr) -> let new_envs = (sign_set_expr env name expr) in if (name <> "Fin") then sign_polish_aux l new_envs else sign_polish_aux l env
				|Read(name) -> if (is_present env name) then let new_envm = (maj_sign_env env name (Pos::Zero::Neg::Error::[])) in 
							sign_polish_aux l new_envm else let new_enva = (add_toenv env (name, Pos::Zero::Neg::Error::[])) in
							sign_polish_aux l new_enva
				(*seuls cas traités*)
				|_ -> sign_polish_aux l env in
	let rec print_sign_env env =
		(*affichage de l'environnement*)
		match env with
		|[] -> print_string ""
		|(name,signs)::l -> print_string name ; print_string " " ; print_sign_line signs ; print_sign_env l in
	print_sign_env (sign_polish_aux prog [])




(**************************MAIN**********************)


let usage () =
  print_string "Polish : analyse statique d'un mini-langage\n";
  print_string "usage:
	./run --reprint <file.p> : Afficher le programme du fichier Polish
	./run --eval <file.p> : Evaluer le programme du fichier Polish
	./run --vars <file.p> : Calcul statique des variables risquant d'être accédés avant d'être écrites.
	./run --simp <file.p> : Simplification d’un programme effectuant une propagationdes constantes et l’élimination des blocs “morts”.
	./run --sign <file.p> : analyse statique du signe possible des variables lors du dé-roulement du programme.\n"

let main () =
  match Sys.argv with

  
  | [|_;"--reprint";file|] -> print_polish (read_polish file)
  | [|_;"--eval";file|] -> eval_polish (read_polish file)
  | [|_;"--simpl";file|] -> simpl_polish (read_polish file)
  | [|_;"--vars";file|] -> vars_polish (read_polish file)
  | [|_;"--sign";file|] -> sign_polish (read_polish file)
  | _ -> usage ()

(* lancement de ce main *)
let () = main ()
