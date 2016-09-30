theory lemm 
imports Main Simdpll
begin
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

lemma "m = [] \<Longrightarrow> \<exists>f. validModel m  \<and> eval' f m =True"
using eval'.simps(1) validModel.simps(1) by blast

lemma st_1[simp]: "\<forall>f. dpll f = True \<Longrightarrow>  \<exists>m. validModel m  \<and> eval' f m =True"
apply (induction f)
using eval'.simps(1) validModel.simps(1) apply blast
using step_2 by fastforce

lemma st_2[simp]:"\<forall>f.  \<exists>m. validModel m  \<and>  eval' f m =True \<Longrightarrow> dpll f = True"
using eval'.simps(2) evalClause.simps(1) by blast

lemma st_3: "\<forall>f. dpll f = False \<Longrightarrow>  \<exists>m. validModel m =True  \<and> eval' f m =False"
using st_1 
using step_1 by blast

lemma st_4[simp]:"\<forall>f. \<exists>m. validModel m =True  \<and> eval' f m =False \<Longrightarrow> dpll f = False"
using st_2
using eval'.simps(1) by blast
end