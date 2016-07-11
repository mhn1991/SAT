import Data.List(nub, elem, notElem)

data Literal a = Yes a | Not a
                  deriving (Eq, Show)

type Clause a = [Literal a]

type Formula a = [Clause a]

negateLiteral :: Literal a -> Literal a
negateLiteral (Yes x) = Not x
negateLiteral (Not x) = Yes x


findUnit :: Formula a -> Maybe (Literal a)
findUnit (c:cs) = if length c == 1 then Just (head c) else findUnit cs
findUnit []     = Nothing

resolve :: (Eq a)=>Formula a -> Literal a -> Formula a
resolve f literal = let f' = filter (notlem literal) f in map (removeAll (negateLiteral literal)) f'

removeAll ::(Eq a) =>  Literal a -> Clause a -> Clause a
removeAll y [] = [] 
removeAll y (x : xs) = if x == y then removeAll y xs else x : removeAll y xs

notlem :: (Eq a) =>Literal a -> Clause a -> Bool 
notlem _ [] = True
notlem p (x:xs) = if p==x then False else notlem p xs
  

unitPropagate :: (Eq a) => Formula a -> Formula a
unitPropagate f = case findUnit f of 
                     Nothing -> f 
                     Just a -> unitPropagate $ resolve f a

isPure :: (Eq a) => Formula a -> Literal a -> Bool
isPure f l = (negateLiteral l) `notElem` (concat f)


findPureLiteral :: (Eq a) => Formula a -> Maybe (Literal a)
findPureLiteral f = locatePureLiteral f (nub $ concat f)
                    where locatePureLiteral f (l:ls) = if isPure f l then Just l else locatePureLiteral f ls
                          locatePureLiteral f []     = Nothing

purePropagate :: (Eq a) => Formula a -> Formula a
purePropagate f = case findPureLiteral f of
                    Nothing -> f
		    Just a  -> purePropagate $ resolve f a

-- this function is same as `elem` just to use it in Isabelle
elem' :: (Eq a) =>Clause a -> Formula a -> Bool 
elem' _ [] = Fasle
elem' p (x:xs) = if p==x then True else elem' p xs

-- with pure literal
dpll :: (Eq a) => Formula a -> Bool
dpll f = if [] == f then True                                 
         else if elem' [] f then False                        
              else
                  let f' = purePropagate $ unitPropagate f in  
                  let nextLiteral = head $ head f in          
                  dpll (resolve f nextLiteral) || dpll (resolve f (negateLiteral nextLiteral))

-- without pure literal                  
dpll'::(Eq a) => Formula a -> Bool
dpll' f = if [] == f then True                                 
         else if elem' [] f then False                        
              else
                  let f' = unitPropagate f in  
                  let nextLiteral = head $ head f in          
                  dpll (resolve f nextLiteral) || dpll (resolve f (negateLiteral nextLiteral))
