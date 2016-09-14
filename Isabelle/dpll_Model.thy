theory dpll_Model 
imports Main 

begin 
datatype 'a Option      =  None | Some 'a
type_synonym Literal  = "int \<times> int"
type_synonym Clause   = "Literal list"
type_synonym Formula  = "Clause list"

fun negateLiteral::"Literal \<Rightarrow> Literal"
where
"negateLiteral (a,b) = ((-1*a),b)"

value "negateLiteral (1,2)"

fun findUnit::"Formula \<Rightarrow> Literal Option"
where
"findUnit [] = None"
|
"findUnit (c#cs) = (if ((length c = 1) \<and> (snd (hd c) = 0)) then Some (hd c) else findUnit cs )"


fun chooseLiteral::"Formula \<Rightarrow> Literal"
where
"chooseLiteral (c#cs) = (if snd (hd c) = 0 then  (hd c) else  chooseLiteral cs )" 

fun assignT::"Literal \<Rightarrow> Clause \<Rightarrow> Clause"
where
"assignT _ [] = []"
|
"assignT l (c#cs) = (if (fst l = fst c) then [(fst c, 1)] else c#assignT l cs)"

fun notElem::"Literal \<Rightarrow> Literal \<Rightarrow> bool"
where
"notElem a b = (if fst a = fst b then False else True)"

fun resolve::"Formula \<Rightarrow> Literal  \<Rightarrow> Formula"
where
"resolve f l = (let f' = map (assignT l ) f in map (filter (notElem (negateLiteral l ))) f' )"

function unitPropagate::"Formula \<Rightarrow> Formula "
where
"unitPropagate f = (case (findUnit f) of None \<Rightarrow> f | Some a \<Rightarrow> unitPropagate (resolve f a ))"
by pat_completeness auto 


termination sorry

fun checkClause::"Clause \<Rightarrow> bool"
where
"checkClause [] = False"
|
"checkClause (l#ls) = (if snd l = 1 then True \<or> checkClause ls else False \<or> checkClause ls )"

fun checkFormula ::"Formula \<Rightarrow> bool"
where
"checkFormula [] = True"
|
"checkFormula (c#cs) = ((checkClause c) \<and> (checkFormula cs))"

fun noZL::"Clause \<Rightarrow> bool"
where
"noZL [] = True"
|
"noZL (l#ls) = (if snd l = 0 then False else noZL ls)"

fun noZ::"Formula \<Rightarrow> bool"
where
"noZ [] = True"
|
"noZ (c#cs) = (noZL c \<and> noZ cs)"

fun elem :: "Clause \<Rightarrow> Formula \<Rightarrow>bool"
where
"elem _ [] = False"
|
"elem p (x#xs) = (if p=x then True else elem p xs)"


function dpll1:: "Formula  \<Rightarrow> (bool\<times>Formula)"
where
"dpll1 f = (if elem [] f then (False,f) else if noZ f then (checkFormula f, f ) else (let f' = unitPropagate f in (let nextLiteral = chooseLiteral f  in  dpll1 (resolve f nextLiteral))))"
by pat_completeness auto
termination sorry

function dpll2::"Formula  \<Rightarrow> (bool\<times>Formula)"
where
"dpll2 f = (if elem [] f then (False,f) else if noZ f then (checkFormula f, f ) else (let f' = unitPropagate f in (let nextLiteral = chooseLiteral f  in  dpll2 (resolve f nextLiteral))))"
by pat_completeness auto
termination sorry

fun dpll::"Formula \<Rightarrow> (bool\<times>Formula) Option"
where
"dpll f = (if fst (dpll1 f) = True then Some (dpll1 f) else if fst(dpll2 f) = True then Some (dpll2 f) else None)"

fun assign:: "Clause \<Rightarrow> Literal \<Rightarrow> Clause"
where
"assign [] _ = []"
|
"assign (c#cs) l = (if (fst c = fst l) then l#assign cs l else if ((snd c) \<noteq> 0) then c#assign cs l  else (fst c,-1)#assign cs l)"

fun assignClause::"Clause \<Rightarrow> Clause \<Rightarrow> Clause " 
where
"assignClause c [] = c"
|
"assignClause [] c = c"
|
"assignClause c (l'#ls') = assignClause (assign c l') ls'"


fun assignFormula::"Formula \<Rightarrow>Formula \<Rightarrow>Formula"
where
"assignFormula f [] = f"
|
"assignFormula [] f = f"
|
"assignFormula (c#cs) (c'#cs') = assignClause c c'#assignFormula cs cs'"

fun eval::"Formula \<Rightarrow> bool\<times>Formula \<Rightarrow> bool"
where
"eval f (a,f') = (if checkFormula (assignFormula f f') then True else False)"

lemma step_1[simp]:"fst (dpll1 f) = True \<or> fst (dpll2 f) = True \<Longrightarrow>dpll f = Some m \<Longrightarrow>fst m = True"
by (metis Option.inject dpll.simps)

lemma "dpll f = Some m \<Longrightarrow> fst m = True"
by (metis Option.distinct(1) dpll.simps step_1)

lemma step_2[simp]:"checkFormula (assignFormula f (snd f')) = True \<Longrightarrow> eval f f' = True"
by (metis dpll_Model.eval.simps surjective_pairing)

lemma "\<exists>f' f. eval f f' =True"
by (metis assignFormula.simps(1) checkFormula.simps(1) dpll_Model.eval.simps)

lemma final:"\<forall>f. dpll f = Some m \<Longrightarrow> \<exists>f m. eval f m =True"
by (metis assignFormula.simps(1) checkFormula.simps(1) dpll_Model.eval.simps)

end