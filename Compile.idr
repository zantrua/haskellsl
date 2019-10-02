module LSL.Compile

import Data.Vect as V

import LSL.Helpers
import LSL.Syntax
import LSL.Typecheck

%access public export

interface Unused r where
	usedVars : r -> List Symbol
	removeUnused : r -> r
	
usedMaybe : Unused r => Maybe r -> List Symbol
usedMaybe a = maybe [] usedVars a
	
usedList : Unused r => List r -> List Symbol
usedList as = foldr union [] $ map usedVars as
	
Unused Expr where
	usedVars (LitExpr _) = []
	
	usedVars (VarExpr v) = [v]
	
	usedVars (ParenExpr a) = usedVars a
	
	usedVars (VectorExpr x y z) = (usedVars x `union` usedVars y) `union` usedVars z
	usedVars (RotationExpr x y z s) = ((usedVars x `union` usedVars y) `union` usedVars z) `union` usedVars s
	usedVars (ListExpr as) = usedList as
	
	usedVars (CastExpr t a) = usedVars a
	
	usedVars (NotExpr a) = usedVars a
	usedVars (AndExpr a b) = usedVars a `union` usedVars b
	usedVars (OrExpr a b) = usedVars a `union` usedVars b
	
	usedVars (BNotExpr a) = usedVars a
	usedVars (BAndExpr a b) = usedVars a `union` usedVars b
	usedVars (BOrExpr a b) = usedVars a `union` usedVars b
	usedVars (BXorExpr a b) = usedVars a `union` usedVars b
	
	usedVars (NegExpr a) = usedVars a
	usedVars (AddExpr a b) = usedVars a `union` usedVars b
	usedVars (SubExpr a b) = usedVars a `union` usedVars b
	usedVars (MulExpr a b) = usedVars a `union` usedVars b
	usedVars (DivExpr a b) = usedVars a `union` usedVars b
	usedVars (ModExpr a b) = usedVars a `union` usedVars b
	
	usedVars (SHLExpr a b) = usedVars a `union` usedVars b
	usedVars (SHRExpr a b) = usedVars a `union` usedVars b
	
	usedVars (EqExpr a b) = usedVars a `union` usedVars b
	usedVars (NeExpr a b) = usedVars a `union` usedVars b
	usedVars (LtExpr a b) = usedVars a `union` usedVars b
	usedVars (LteExpr a b) = usedVars a `union` usedVars b
	usedVars (GtExpr a b) = usedVars a `union` usedVars b
	usedVars (GteExpr a b) = usedVars a `union` usedVars b
	
	usedVars (FnExpr f as) = f :: (usedList as)
	
	usedVars (SetExpr v _ a) = v :: (usedVars a)
	usedVars (SetAddExpr v _ a) = v :: (usedVars a)
	usedVars (SetSubExpr v _ a) = v :: (usedVars a)
	usedVars (SetMulExpr v _ a) = v :: (usedVars a)
	usedVars (SetDivExpr v _ a) = v :: (usedVars a)
	usedVars (SetModExpr v _ a) = v :: (usedVars a)
	
	usedVars (PreIncExpr v) = [v]
	usedVars (PostIncExpr v) = [v]
	usedVars (PreDecExpr v) = [v]
	usedVars (PostDecExpr v) = [v]
	
	removeUnused a = a
	
Unused Stmt where
	usedVars (ExprStmt a) = usedVars a
	usedVars (DefStmt t v a) = usedMaybe a
	
	usedVars (ScopeStmt as) = usedList as
	
	usedVars DefaultStmt = []
	usedVars (StateStmt v) = [v]
	
	usedVars (IfStmt c t f) = (usedVars c `union` usedVars t) `union` usedMaybe f
	usedVars (DoWhileStmt body test) = usedVars body `union` usedVars test
	usedVars (ForStmt pre test post body) = ((usedList pre `union` usedMaybe test) `union` usedList post) `union` usedVars body
	usedVars (WhileStmt test a) = usedVars test `union` usedVars a
	
	usedVars (JumpStmt v) = [v]
	usedVars (LabelStmt v) = []
	
	usedVars (ReturnStmt a) = usedMaybe a
	
	removeUnused (ScopeStmt as) = ScopeStmt $ mapMaybe (removeScope $ usedVars $ ScopeStmt as) as where
		removeScope : List Symbol -> Stmt -> Maybe Stmt
		removeScope used (DefStmt t v a) = toMaybe (elem v used) (DefStmt t v a)
		removeScope used (LabelStmt v) = toMaybe (elem v used) (LabelStmt v)
		removeScope used a = Just $ removeUnused a
	removeUnused (IfStmt c t f) = IfStmt c (removeUnused t) (map removeUnused f)
	removeUnused (DoWhileStmt body test) = DoWhileStmt (removeUnused body) test
	removeUnused (ForStmt pre test post body) = ForStmt pre test post (removeUnused body)
	removeUnused (WhileStmt test body) = WhileStmt test (removeUnused body)
	removeUnused a = a
	
Unused Event where
	usedVars e = (usedList $ body e) \\ (toList $ args e)
	removeUnused e = MkEvent (type e) (args e) (unScope $ removeUnused $ ScopeStmt $ body e)
	
Unused State where
	usedVars s = usedList $ body s
	removeUnused s = MkState (name s) (map removeUnused $ body s)
	
Unused Function where
	usedVars f = (usedList $ body f) \\ (map fst $ args f)
	removeUnused f = MkFunction (result f) (name f) (args f) (map removeUnused $ body f)
	
Unused Script where
	usedVars s = (usedList $ funcs s) `union` (usedList $ states s)
	removeUnused s = let used = usedVars s in
		MkScript (filter (\g => elem (fst g) used) $ globals s)
			(filter (\f => elem (name f) used) $ map removeUnused $ funcs s)
			(filter (\s => maybe True (\n => elem n used) $ name s) $ map removeUnused $ states s)

isCompound : Expr -> Bool
isCompound (LitExpr _) = False
isCompound (VarExpr _) = False
isCompound (ParenExpr _) = False
isCompound (VectorExpr _ _ _) = False
isCompound (RotationExpr _ _ _ _) = False
isCompound (ListExpr _) = False
isCompound (FnExpr _ _) = False
isCompound _ = True

interface Parens r where
	addParens : r -> r

-- TODO: This adds too many parens, it should use precedence
maybeParen : Expr -> Expr
maybeParen a = if isCompound a then ParenExpr a else a

Parens Expr where
	addParens (ParenExpr a) = ParenExpr (addParens a)

	addParens (VectorExpr x y z) = VectorExpr (addParens x) (addParens y) (addParens z)
	addParens (RotationExpr x y z s) = RotationExpr (addParens x) (addParens y) (addParens z) (addParens s)
	addParens (ListExpr as) = ListExpr $ map addParens as

	addParens a = map maybeParen a

Parens Stmt where
	addParens (ExprStmt a) = ExprStmt $ addParens a
	addParens (DefStmt t v a) = DefStmt t v $ map addParens a
	
	addParens (ScopeStmt as) = ScopeStmt $ map addParens as
	
	addParens (IfStmt c t f) = IfStmt (addParens c) (addParens t) (map addParens f)
	addParens (DoWhileStmt body test) = DoWhileStmt (addParens body) (addParens test)
	addParens (ForStmt pre test post body) = ForStmt (map addParens pre) (map addParens test) (map addParens post) (addParens body)
	addParens (WhileStmt test body) = WhileStmt (addParens test) (addParens body)

	addParens (ReturnStmt a) = ReturnStmt $ map addParens a
	
	addParens a = a
	
Parens Event where
	addParens e = MkEvent (type e) (args e) (map addParens $ body e)
	
Parens State where
	addParens s = MkState (name s) (map addParens $ body s)
	
Parens Function where
	addParens f = MkFunction (result f) (name f) (args f) (map addParens $ body f)
	
Parens Script where
	addParens s = MkScript (globals s) (map addParens $ funcs s) (map addParens $ states s)

compile : Script -> Maybe String
compile s = do
	let s = removeUnused s
	let s = addParens s
	_ <- scopedInfer [] [] s
	Just $ show s
