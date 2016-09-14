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


dpll::  Formula a -> Maybe (Bool,Formula a)
dpll f = if fst (dpll1 f) == True then Just (dpll1 f) else if fst (dpll2 f) == True  then Just (dpll2 f) else Nothing


assignFormula::Formula a -> Formula a -> Formula a
assignFormula f [] = f
assignFormula [] f = f
assignFormula (c:cs) (c':cs') = assignClause c c':assignFormula cs cs'

assign::Clause a -> Literal a -> Clause a
assign [] _ = []
assign (c:cs) l = if (fst c == fst l) then l:assign cs l else if snd c /= 0 then c:assign cs l  else (fst c , -1):assign cs l

assignClause :: Clause a -> Clause a -> Clause a
assignClause c [] = c
assignClause [] c = c
assignClause c (l':ls') = assignClause (assign c l') ls' 

eval'::Formula a -> (Bool,Formula a) -> Bool
eval' f (a,f') = if checkFormula (assignFormula f f') then True else False 
