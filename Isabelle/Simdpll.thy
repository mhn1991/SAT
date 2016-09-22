theory Simdpll 
imports Main

begin
datatype 'a Option      =  None | Some 'a
type_synonym    Literal =  int  
type_synonym  Clause    =  "Literal list" 
type_synonym Formula    =  "Clause list"
type_synonym Model      =  Clause

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


(*the other proof for the lemma which help the simp for unitpropagate termination*)
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
apply (simp add: ter)
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

lemma [fundef_cong]:"(\<not>Q' \<Longrightarrow>  P=P') \<Longrightarrow> (Q=Q') \<Longrightarrow> (P \<or> Q)=(P'\<or> Q')"
by blast

function dpll:: "Formula \<Rightarrow> bool"
where
"dpll f = (if f = [] then True else if (elem [] f) then False else (let ff = unitPropagate f in(let nextLiteral = hd( hd f) in  dpll (resolve f (negateLiteral nextLiteral)) \<or>  dpll (resolve f nextLiteral))))"
by pat_completeness auto 



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
then show ?thesis sorry 
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
apply (relation "measure (\<lambda>f. length f)")
apply auto
apply (simp add:ter2)
apply (simp add:ter3)
done

value "dpll [[1],[2],[(-1),(-2)]]"
value "dpll [[-1]]"
value "dpll []"


lemma step_1:"f = [] \<Longrightarrow> dpll f = True"
apply auto
done 

lemma step_2:"f \<noteq> [] \<Longrightarrow> elem [] f = True \<Longrightarrow> dpll f = False"
apply auto
done

lemma step_3: "\<exists>m. dpll m = True"
using step_1 by blast

lemma step_4: "\<forall>f. f \<noteq> []  \<Longrightarrow>\<exists>m. dpll m = True"
using step_3
apply auto
done 

(*============================================================================================*)
fun evalClause::"Formula \<Rightarrow> Literal \<Rightarrow> Formula"
where
"evalClause f l =  (resolve f l) "

function eval::"Formula \<Rightarrow> Model \<Rightarrow> bool"
where
"eval f [] = (if f = [] then True else False)"
|
"eval f (m#ms)= (if f = [] then True else if elem [] f then False  else  eval (evalClause f m) ms)"
apply auto
by (meson list.exhaust)

termination 

apply (relation "measure (\<lambda>(f,m). length m)")
apply auto
done

value"[[]] = []"


lemma step_5[simp]:"eval [] [] = True"
by simp

lemma step_6[simp]:"f\<noteq>[] \<Longrightarrow> eval f [] = False"
by simp

lemma step_7[simp]:"eval [] m = True"
using eval.elims(3) by fastforce

value "eval [[]] []"

lemma [simp]:"\<forall>f. dpll f = True \<Longrightarrow> \<exists>m. eval f m =True"
using step_2 by fastforce

lemma "\<forall>f. dpll f = True \<Longrightarrow>  \<exists>m. eval f m =True"
using step_2 by fastforce

lemma [simp]:"\<forall>f . \<exists>m. eval f m =True \<Longrightarrow> dpll f = True"
apply (induction f)
apply simp
by (meson elem.simps(2) eval.elims(2) not_Cons_self2)

lemma "(\<forall>f m. eval f m = False \<Longrightarrow>  dpll f = False)"
apply (induction f)
using step_5 apply auto[1]
using step_5 by blast


lemma [simp]:"(\<forall>f. dpll f = False \<Longrightarrow> \<forall>m. eval f m = False)"
apply (induction f)
apply simp
apply metis
using step_3 by blast

end



