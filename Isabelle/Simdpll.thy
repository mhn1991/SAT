theory Simdpll 
imports Main

begin
datatype 'a Option      = None | Some 'a
type_synonym    Literal =  int  
type_synonym  Clause    =  "Literal list" 
type_synonym Formula    = "Clause list"

fun negateLiteral :: "(Literal) ⇒  Literal "
where
"negateLiteral  a =   (-1*a)"

fun findUnit :: "Formula ⇒ (Literal) Option "
where
"findUnit [] = None"
|
"findUnit (c#cs) = (if length c = 1 then Some (hd c) else findUnit cs)"

fun notElem :: "(Literal) ⇒ Clause ⇒ bool" 
where
"notElem _ [] = True" 
|
"notElem p (x#xs) = (if p=x then False else notElem p xs)"

fun elem :: "Clause ⇒ Formula ⇒bool"
where
"elem _ [] = False"
|
"elem p (x#xs) = (if p=x then True else elem p xs)"

(*should work on termination of this function *)
fun resolve ::"Formula ⇒ (Literal) ⇒ (Formula)"
where
"resolve f literal =(let  q = filter (notElem literal) f in map (removeAll (negateLiteral literal)) q)"


(*second section of case has problem*)
function unitPropagate:: "Formula ⇒ Formula "
where
"unitPropagate f = (case (findUnit f) of None ⇒  f  | Some a ⇒ unitPropagate (resolve f a))"
apply auto
done

function dpll:: "Formula ⇒ bool"
where
"dpll f = (if f = [] then True else if (elem [] f) then False else  (let ff = unitPropagate f in(let nextLiteral = hd( hd f) in dpll (resolve f nextLiteral) | dpll (resolve f (negateLiteral nextLiteral)))))"  
apply auto 
done

end
