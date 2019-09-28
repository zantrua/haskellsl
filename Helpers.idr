module LSL.Helpers

%access public export

total Map : Type -> Type -> Type
Map a b = List (a, b)

total andmap : (a -> Bool) -> List a -> Bool
andmap f as = foldr (\a, b => a && b) True (map f as)

total join : List String -> String
join = foldr (++) ""

total joinSep : String -> List String -> String
joinSep sep as = join $ intersperse sep as 

total joinShow : Show a => List a -> String
joinShow as = join $ map show as

total joinSepShow : Show a => String -> List a -> String
joinSepShow sep as = joinSep sep $ map show as

implementation [blank] Show a => Show (Maybe a) where
    show a = maybe "" show a
