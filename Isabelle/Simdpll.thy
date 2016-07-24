theory Simdpll 
imports Main

begin
 
datatype 'a Option      = None | Some 'a
type_synonym    Literal =  int  
type_synonym  Clause    =  "Literal list" 
type_synonym Formula    = "Clause list"

fun negateLiteral :: "(Literal) \<Rightarrow>  Literal "
where
"negateLiteral  a =   (-1*a)"

value "negateLiteral 1" 
value "negateLiteral 0"
value "negateLiteral (-1::int)"

fun deOption::"(Formula) Option \<Rightarrow> Formula"
where
"deOption None = undefined"
|
"deOption (Some f) =  f" 

fun findUnit :: "Formula \<Rightarrow> (Literal) Option "
where
"findUnit [] = None"
|
"findUnit (c#cs) = (if length c = 1 then Some (hd c) else findUnit cs)"

value "findUnit [[1,2,3],[1],[2]]" 
value "findUnit [[],[1,2],[2]]"
value "findUnit [[1,2]]"


fun notElem :: "(Literal) \<Rightarrow> Clause \<Rightarrow> bool" 
where
"notElem _ [] = True" 
|
"notElem p (x#xs) = (if p=x then False else notElem p xs)"

value "notElem 1 [1,2,3]"
value "notElem 4 [1,2,3]"
value "notElem 1 [] "

fun elem :: "Clause \<Rightarrow> Formula \<Rightarrow>bool"
where
"elem _ [] = False"
|
"elem p (x#xs) = (if p=x then True else elem p xs)"


value "elem [] [[]]"
(*should work on termination of this function *)
fun resolve ::"Formula \<Rightarrow> Literal \<Rightarrow> Formula"
where
"resolve f literal =  (let  q = filter (notElem literal) f in map (removeAll (negateLiteral literal)) q)"

value "resolve [[-1]] (-1::int)"
value "resolve [[1,2,3],[-1,2,3],[4]] 1"

lemma 1[simp]: "resolve [] a = []"
apply simp
done



lemma yes: "findUnit f = Some x \<Longrightarrow> length (filter (notElem x) f) < length f"
proof (induction f)
  case Nil
  then show ?case by simp
next
  case Cons
  fix f a
  assume
    prems: "findUnit (a # f) = Some x" and
    IH: "findUnit f = Some x \<Longrightarrow> length (filter (notElem x) f) < length f"
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
      then show ?thesis by (metis H1 One_nat_def Option.inject findUnit.simps(2) list.sel(1) list.size(3) n_not_Suc_n notElem.elims(2) prems)
qed 
next case False
then show ?thesis by (simp add: filter.simps(2) le_imp_less_Suc length_Cons length_filter_le)
qed
qed


lemma ter: "findUnit f = Some x \<Longrightarrow> length (filter (notElem x) f) < length f"
proof (induction f)
  case Nil
  then show ?case by simp
next
  case Cons
  fix f a
  assume
    prems: "findUnit (a # f) = Some x" and
    IH: "findUnit f = Some x \<Longrightarrow> length (filter (notElem x) f) < length f"
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
      then have "\<not> notElem x a" by (induction a) simp_all
      with H1 show ?thesis by simp
    qed
  next
    case False
    then show ?thesis by (simp add: le_imp_less_Suc)
  qed
qed


(*second section of case has problem*)
function  unitPropagate:: "Formula \<Rightarrow> Formula "
where 
"unitPropagate f = (case (findUnit f) of None \<Rightarrow>  f  | Some a \<Rightarrow> unitPropagate (resolve f a))"
by pat_completeness auto

termination 
apply (relation "measure (\<lambda>x. size x)")
apply (auto)
apply (simp add: yes)
done

value "unitPropagate [[1,2],[1],[1,2]]"
value "unitPropagate [[1,2,3]]"

lemma ter2: "f \<noteq> [] \<Longrightarrow> \<not> elem [] f \<Longrightarrow> length (filter (notElem (hd (hd f))) f) < length f"
proof (induction f)
case Nil
then show ?case by simp
next
  case Cons
  fix f a 
 assume
    prems: "(a#f) \<noteq> []" and
    premss: " \<not> elem [] (a#f)" and
    IM: "f \<noteq> [] \<Longrightarrow> \<not> elem [] f \<Longrightarrow> length (filter (notElem (hd (hd f))) f) < length f"
    then show "length (filter (notElem (hd (hd (a#f)))) (a#f)) < length (a#f)"
    proof (cases "notElem (hd (hd (a#f))) a") 
    case 
    H1: True
    then show ?thesis
    proof (cases "(a#f) \<noteq> []")
    case True
    then show ?thesis  
    proof (cases"\<not> elem [] (a#f)" )
    case True
    then show ?thesis by (metis H1 elem.simps(2) list.sel(1) notElem.elims(2))
      next 
    case False
    then show ?thesis using premss by blast
qed
  next 
    case False
        then show ?thesis by simp
        qed
next 
case False 
then show ?thesis by (simp add: filter.simps(2) le_imp_less_Suc length_Cons length_filter_le)
qed
qed

lemma ter3: "f \<noteq> [] \<Longrightarrow> \<not> elem [] f \<Longrightarrow> length (filter (notElem (- hd (hd f))) f) < length f"
oops


fun slm ::"Formula \<Rightarrow> Formula"
where
"slm f = filter (notElem (-hd (hd f))) f"

value "slm [[-1]]"

function dpll:: "Formula \<Rightarrow> bool"
where
"dpll f = (if f = [] then True else if (elem [] f) then False else (let ff = unitPropagate f in(let nextLiteral = hd( hd f) in dpll (resolve f nextLiteral) \<or> dpll (resolve f (negateLiteral nextLiteral)))))"
by pat_completeness auto 

termination
apply (relation "measure (\<lambda> x. size x)")
apply auto
apply (simp add : ter2)
apply try
done


value "dpll [[1],[2],[(-1),(-2)]]"
value "dpll [[-1]]"
end