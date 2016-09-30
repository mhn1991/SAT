theory Simdpll 
imports Main 

begin
datatype 'a Option      =  None | Some 'a
type_synonym    Literal =  int  
type_synonym  Clause    =  "Literal list" 
type_synonym Formula    =  "Clause list"
type_synonym Model      =  "int list"

fun negateLiteral :: "(Literal) \<Rightarrow>  Literal "
where
"negateLiteral  a =   (-1*a)"


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


fun notElem :: "(Literal) \<Rightarrow> Clause \<Rightarrow> bool" 
where
"notElem _ [] = True" 
|
"notElem p (x#xs) = (if p=x then False else notElem p xs)"


fun elem :: "Clause \<Rightarrow> Formula \<Rightarrow>bool"
where
"elem _ [] = False"
|
"elem p (x#xs) = (if p=x then True else elem p xs)"


(*should work on termination of this function *)
fun resolve ::"Formula \<Rightarrow> Literal \<Rightarrow> Formula"
where
"resolve f literal =  (let  q = filter (notElem literal) f in map (removeAll (negateLiteral literal)) q)"



(*second section of case has problem*)
function  unitPropagate:: "Formula \<Rightarrow> Formula "
where 
"unitPropagate f = (case (findUnit f) of None \<Rightarrow>  f  | Some a \<Rightarrow> unitPropagate (resolve f a))"
by pat_completeness auto


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


termination 
apply (relation "measure (\<lambda>x. size x)")
apply (auto)
apply (simp add: ter)
done


lemma [fundef_cong]:"(\<not>Q' \<Longrightarrow>  P=P') \<Longrightarrow> (Q=Q') \<Longrightarrow> (P \<or> Q)=(P'\<or> Q')"
by blast

function dpll:: "Formula \<Rightarrow> bool"
where
"dpll f = (if f = [] then True else if (elem [] f) then False else (let ff = unitPropagate f in(let nextLiteral = hd( hd f) in  dpll (resolve f (negateLiteral nextLiteral)) \<or>  dpll (resolve f nextLiteral))))"
by pat_completeness auto 


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

lemma elim:"dpll_dom (map (removeAll (- hd (hd (a # f)))) (filter (notElem (hd (hd (a # f)))) (a # f))) \<Longrightarrow> length (filter (notElem (- hd (hd (a # f)))) (a # f)) < length (a # f)"
apply (induction  rule: "dpll.pinduct") 
sorry
lemma ter3: "f \<noteq> [] \<Longrightarrow>
         \<not> elem [] f \<Longrightarrow>
          \<not> dpll (map (removeAll (- hd (hd f))) (filter (notElem (hd (hd f))) f)) \<Longrightarrow>
         dpll_dom (map (removeAll (- hd (hd f))) (filter (notElem (hd (hd f))) f)) \<Longrightarrow>
         length (filter (notElem (- hd (hd f))) f) < length f"
proof(induction f)
case Nil 
then show ?case by simp
next 
case Cons
fix 
f a 
assume 
prems: "(a#f) \<noteq> []" and
premss : "\<not> elem [] (a#f)"and
premsss : "\<not> dpll (map (removeAll (- hd (hd (a#f)))) (filter (notElem (hd (hd (a#f)))) (a#f)))"and
premssss: "dpll_dom (map (removeAll (- hd (hd (a#f)))) (filter (notElem (hd (hd (a#f)))) (a#f)))"and
IM: "f \<noteq> [] \<Longrightarrow>
         \<not> elem [] f \<Longrightarrow>
         \<not> dpll (map (removeAll (- hd (hd f))) (filter (notElem (hd (hd f))) f)) \<Longrightarrow>
         dpll_dom (map (removeAll (- hd (hd f))) (filter (notElem (hd (hd f))) f)) \<Longrightarrow>
         length (filter (notElem (- hd (hd f))) f) < length f"

then show " length (filter (notElem (- hd (hd (a#f)))) (a#f)) < length (a#f)"
proof (cases "notElem (- hd (hd (a#f))) a")
case 
H1: True
then show ?thesis
proof(cases "(a#f) \<noteq> []")
case 
True
then show ?thesis
proof (cases "\<not> elem [] (a#f)")
case True
then show ?thesis 
proof (cases "\<not> dpll (map (removeAll (- hd (hd (a#f)))) (filter (notElem (hd (hd (a#f)))) (a#f)))")
case True
then show ?thesis
proof (cases "dpll_dom (map (removeAll (- hd (hd (a#f)))) (filter (notElem (hd (hd (a#f)))) (a#f)))")
case True
then show ?thesis using elim  by simp
next 
case False
then show ?thesis using premssss by blast
qed
next
case False
then show ?thesis using premsss by linarith 
qed
next 
case False 
then show ?thesis using premss by linarith
qed
next case False
then show ?thesis by simp
qed
next case False
then show ?thesis by (simp add: filter.simps(2) le_imp_less_Suc length_Cons length_filter_le)
qed
qed

termination
apply (relation "(measure (length))")
apply auto
apply (simp add:ter2)
apply (simp add:ter3)
done

value "dpll [[1],[2],[(-1),(-2)]]"
value "dpll [[-1]]"
value "dpll []"


(*============================================================================================*) 
fun validModel::"Model \<Rightarrow> bool"
where
"validModel [] = True"
|
"validModel (m#rest) =(if m > 0 then True \<and> validModel rest else False  \<and> validModel rest)"


fun evalLiteral::"Literal \<Rightarrow> Model \<Rightarrow> bool"
where
"evalLiteral l [] = (if l>0 then False else True)"
|
"evalLiteral l (m#ms) = (if (l > 0 ) \<and> (l = m) then True else if ((l < 0) \<and> ((-1*l) = m)) then False else evalLiteral l ms)"

fun evalClause::"Clause \<Rightarrow> Model \<Rightarrow> bool"
where
"evalClause [] m = False"
|
"evalClause (l#ls) m = ((evalLiteral l m) \<or> evalClause ls m)"

fun eval'::"Formula \<Rightarrow>Model \<Rightarrow>bool"
where
"eval' [] m = True"
|
"eval' (c#cs) m = (((evalClause c m) \<and> (eval' cs m)))"



end



