theory Simdpll 
imports Main 
begin
datatype 'a Option  = None | Some 'a
type_synonym    Literal =  int  
type_synonym  Clause =  "Literal list" 
type_synonym Formula = "Clause list"

fun negateLiteral :: "Literal  ⇒  Literal "
where
"negateLiteral a = (-1*a)"

fun findUnit :: "Formula ⇒ Literal"
where
"findUnit (c#cs) = (if length c = 1 then  (hd c) else findUnit cs)"
|
"findUnit []     = undefined"

fun notElem :: " Literal ⇒ Clause ⇒ bool" 
where
"notElem _ [] = True" 
|
"notElem p (x#xs) = (if p=x then False else notElem p xs)"

fun resolve ::"Formula ⇒ Literal ⇒ Formula"
where
"resolve f literal =(let q = filter (notElem literal) f in map (removeAll (negateLiteral literal)) q)"


end
