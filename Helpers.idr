module LSL.Helpers

import Data.Bits

%default total
%access public export

total Map : Type -> Type -> Type
Map a b = List (a, b)

total andmap : (a -> Bool) -> List a -> Bool
andmap f as = foldr (\a, b => a && b) True (map f as)

total ormap : (a -> Bool) -> List a -> Bool
ormap f as = foldr (\a, b => a || b) False (map f as)

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

total uncurry3 : (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

total uncurry4 : (a -> b -> c -> d -> e) -> (a, b, c, d) -> e
uncurry4 f (a, b, c, d) = f a b c d

Cast Int (Bits 32) where
	cast = intToBits . cast

Cast (Bits 32) Int where
	cast = fromInteger . bitsToInt
	
total complement : Int -> Int
complement a = cast $ Bits.complement $ cast a

total and : Int -> Int -> Int
and a b = cast $ Bits.and (cast a) (cast b)

total or : Int -> Int -> Int
or a b = cast $ Bits.or (cast a) (cast b)

total xor : Int -> Int -> Int
xor a b = cast $ Bits.xor (cast a) (cast b)

total defineBy : %static (a -> a -> Bool) -> a -> b -> List (a, b) -> (Maybe b, List (a, b))
defineBy p a b xs = case findIndex (p a . fst) xs of
	Nothing => (Nothing, (a, b) :: xs)
	Just n => let split = splitAt n xs in
		(map snd $ index' n xs, fst split ++ [(a, b)] ++ drop 1 (snd split))
		
total define : Eq a => a -> b -> List (a, b) -> (Maybe b, List (a, b))
define = defineBy (==)
