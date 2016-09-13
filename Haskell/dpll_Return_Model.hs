--data Exbool = Bool | Undef deriving (Show,Eq)
type Literal a = (Int,Int)
type Clause a = [Literal a]
type Formula a = [Clause a]

negateLiteral::Literal a -> Literal a
negateLiteral (a,b) = ((-1*a),b)

findUnit::Formula a -> Maybe (Literal a)
findUnit [] = Nothing
findUnit (c:cs) = if ((snd (head c) == 0) && (length c == 1)) then Just (head c) else findUnit cs


chooseLiteral::Formula a -> Literal a
chooseLiteral (c:cs) = if snd (head c) == 0 then head c else chooseLiteral cs 

assignT::Literal a -> Clause a -> Clause a 
assignT _ [] = []
assignT l (c:cs) = if fst l == fst c then [(fst c, 1)] else c:assignT l cs

remo::Literal a -> Literal a -> Bool
remo a b = if fst a == fst b then False else True

resolve::Formula a -> Literal a -> Formula a
resolve f l = let f' = map (assignT l ) f in map (filter (remo (negateLiteral l))) f' 

unitPropagate::Formula a -> Formula a
unitPropagate f = case findUnit f of
                       Nothing -> f
                       Just a -> unitPropagate (resolve f a)


checkClause :: Clause a -> Bool
checkClause [] = False
checkClause (l:ls) = if snd l == 1 then True || checkClause ls else False || checkClause ls  

checkFormula :: Formula a -> Bool
checkFormula [] = True
checkFormula (c:cs) = checkClause c && checkFormula cs

noZL::Clause a -> Bool
noZL [] = True
noZL (l:ls) = if snd l == 0 then False else noZL ls

noZ::Formula a -> Bool
noZ [] = True
noZ (c:cs) = noZL c && noZ cs

dpll1:: Formula a -> (Bool,Formula a)
dpll1 f =  if [] `elem` f then (False,f) else if noZ f then (checkFormula f, f )else let f' = unitPropagate f in let nextLiteral = chooseLiteral f  in  dpll1 (resolve f nextLiteral)

dpll2::Formula a -> (Bool,Formula a)
dpll2 f =  if [] `elem` f then (False,f) else if noZ f then (checkFormula f, f )else let f' = unitPropagate f in let nextLiteral = chooseLiteral f in dpll2 (resolve f (negateLiteral nextLiteral)) 


dpll::  Formula a -> Bool
dpll f = fst (dpll1 f) || fst (dpll2 f)
