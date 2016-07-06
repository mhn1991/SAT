theory Simdpll 
imports Main 
begin
datatype 'a Option  = None | Some 'a
type_synonym    Literal =  int  
type_synonym  Clause =  "Literal list" 
type_synonym Formula = "Clause list"

fun negateLiteral :: "Literal  \<Rightarrow>  Literal "
where
"negateLiteral a = (-1*a)"

fun findUnit :: "Formula \<Rightarrow> Literal"
where
"findUnit (c#cs) = (if length c = 1 then  (hd c) else findUnit cs)"
|
"findUnit []     = undefined"

fun notElem :: " Literal \<Rightarrow> Clause \<Rightarrow> bool" 
where
"notElem _ [] = True" 
|
"notElem p (x#xs) = (if p=x then False else notElem p xs)"

fun elem :: "Literal \<Rightarrow> Clause \<Rightarrow> bool"
where 
" elem _ [] = False"
|
"elem p (x#xs) = (if p=x then True else elem p xs)"


fun remove':: "Literal  \<Rightarrow> Formula \<Rightarrow> Formula"
where
"remove' _ [] = []"
|
"remove' l (x#xs) = (if (elem l x) then  (removeAll l x)# xs else (remove' l xs)) "

fun resolve ::"Formula \<Rightarrow> Literal \<Rightarrow> Formula"
where
"resolve f literal =(let q = filter (notElem literal) f in remove' literal q)"


end
