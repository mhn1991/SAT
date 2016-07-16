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

value "negateLiteral 1" 
value "negateLiteral 0"
value "negateLiteral (-1::int)"


fun findUnit :: "Formula ⇒ (Literal) Option "
where
"findUnit [] = None"
|
"findUnit (c#cs) = (if length c = 1 then Some (hd c) else findUnit cs)"

value "findUnit [[1,2,3],[1],[2]]" 
value "findUnit [[],[1,2],[2]]"

fun notElem :: "(Literal) ⇒ Clause ⇒ bool" 
where
"notElem _ [] = True" 
|
"notElem p (x#xs) = (if p=x then False else notElem p xs)"

value "notElem 1 [1,2,3]"
value "notElem 4 [1,2,3]"
value "notElem 1 [] "

fun elem :: "Clause ⇒ Formula ⇒bool"
where
"elem _ [] = False"
|
"elem p (x#xs) = (if p=x then True else elem p xs)"



(*should work on termination of this function *)
fun resolve ::"Formula ⇒ (Literal) ⇒ (Formula)"
where
"resolve f literal =(let  q = filter (notElem literal) f in map (removeAll (negateLiteral literal)) q)"

value "resolve [[]] 1"
value "resolve [[1,2,3],[-1,2,3],[4]] 1"

fun mm ::"Formula ⇒ nat"
where 
"mm f= (if (findUnit f) = None then 0 else 1 )"

(*second section of case has problem*)
function  unitPropagate:: "Formula ⇒ Formula "
where 
"unitPropagate f = (case (findUnit f) of None ⇒  f  | Some a ⇒ unitPropagate (resolve f a))"
apply auto 
done


value "unitPropagate [[1,2],[1],[1,2]]"

function dpll:: "Formula ⇒ bool"
where
"dpll f = (if f = [] then True else if (elem [] f) then False else  (let ff = unitPropagate f in(let nextLiteral = hd( hd f) in dpll (resolve f nextLiteral) | dpll (resolve f (negateLiteral nextLiteral)))))"
apply auto 
done
termination sorry
value "dpll [[1],[2],[(-1),(-2)]]"
value "dpll [[]]"

end
