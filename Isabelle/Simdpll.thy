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

fun deOption::"(Formula) Option ⇒ Formula"
where
"deOption None = undefined"
|
"deOption (Some f) =  f" 

fun findUnit :: "Formula ⇒ (Literal) Option "
where
"findUnit [] = None"
|
"findUnit (c#cs) = (if length c = 1 then Some (hd c) else findUnit cs)"

value "findUnit [[1,2,3],[1],[2]]" 
value "findUnit [[],[1,2],[2]]"
value "findUnit [[1,2]]"


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
fun resolve ::"Formula ⇒ Literal ⇒ Formula"
where
"resolve f literal =  (let  q = filter (notElem literal) f in map (removeAll (negateLiteral literal)) q)"

value "resolve [[-1]] (-1::int)"
value "resolve [[1,2,3],[-1,2,3],[4]] 1"

lemma 1[simp]: "resolve [] a = []"
apply simp
done

lemma ter: "findUnit f = Some x ⟹ length (filter (notElem x) f) < length f"
proof (induction f)
  case Nil
  then show ?case by simp
next
  case Cons
  fix f a
  assume
    prems: "findUnit (a # f) = Some x" and
    IH: "findUnit f = Some x ⟹ length (filter (notElem x) f) < length f"
  then show "length (filter (notElem x) (a # f)) < length (a # f)"
  proof (cases "notElem x a")
    case
      H1: True
    then show ?thesis
    proof (cases "findUnit f = Some x")
      case True
      with IH show ?thesis by simp
    next
      case False
      then have "Some (hd a) = Some x" "length a = 1"
        using findUnit.simps prems by presburger+
      then have "¬ notElem x a" by (induction a) simp_all
      with H1 show ?thesis by simp
    qed
  next
    case False
    then show ?thesis by (simp add: le_imp_less_Suc)
  qed
qed


(*second section of case has problem*)
function  unitPropagate:: "Formula ⇒ Formula "
where 
"unitPropagate f = (case (findUnit f) of None ⇒  f  | Some a ⇒ unitPropagate (resolve f a))"
by pat_completeness auto

termination 
apply (relation "measure (λx. size x)")
apply (auto)
apply (simp add: ter)
done







value "unitPropagate [[1,2],[1],[1,2]]"
value "unitPropagate [[1,2,3]]"

function dpll:: "Formula ⇒ bool"
where
"dpll f = (if f = [] then True else if (elem [] f) then False else  (let ff = unitPropagate f in(let nextLiteral = hd( hd f) in dpll (resolve f nextLiteral) | dpll (resolve f (negateLiteral nextLiteral)))))"
by pat_completeness auto 
termination sorry

value "dpll [[1],[2],[(-1),(-2)]]"
value "dpll [[]]"

function fib :: "nat ⇒ nat" where
"fib 0 = 0" |
"fib (Suc 0) = 1" |
"fib (Suc(Suc x)) = fib x + fib (Suc x)"

by pat_completeness auto 

termination 
apply (relation "measure (λx. x)") 
apply auto
done


end
