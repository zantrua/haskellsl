module LSL.Typecheck

import Data.Vect

import LSL.Helpers
import LSL.Syntax

%access public export

interface Checkable r where
	infer : Map Symbol SymbolType -> r -> Maybe SymbolType
	inferValue : Map Symbol SymbolType -> r -> Maybe LSLType
	
	inferValue ctx v = do
		v <- infer ctx v
		case v of
			ValueType a => Just a
			_ => Nothing
			
private total inferList : Checkable r => Map Symbol SymbolType -> List r -> Maybe ()
inferList ctx as = toMaybe (andmap (isJust . infer ctx) as) ()

Checkable Symbol where
	infer ctx v = lookup v ctx
	
Checkable Literal where
	infer _ (IntLit _) = Just $ ValueType LSLInteger
	infer _ (FloatLit _) = Just $ ValueType LSLFloat
	infer _ (StringLit _) = Just $ ValueType LSLString
	infer _ (KeyLit _) = Just $ ValueType LSLKey
	
public export check : Checkable r => Map Symbol SymbolType -> r -> SymbolType -> Maybe Bool
check ctx a t = do
	a <- infer ctx a
	Just $ a == t
	
public export checkValue : Checkable r => Map Symbol SymbolType -> r -> LSLType -> Maybe Bool
checkValue ctx a t = do
	a <- inferValue ctx a
	Just $ a == t

private total numeric : LSLType -> Bool
numeric LSLInteger = True
numeric LSLFloat = True
numeric _ = False

private total castable : LSLType -> LSLType -> Bool
castable LSLInteger LSLFloat = True
castable LSLFloat LSLInteger = True
castable LSLString _ = True
castable _ LSLString = True
castable _ LSLList = True
castable a a' = a == a'

private total negable : LSLType -> Bool
negable LSLInteger = True
negable LSLFloat = True
negable LSLVector = True
negable LSLRotation = True
negable _ = False

private total inferAdd : LSLType -> LSLType -> Maybe LSLType
inferAdd LSLInteger LSLInteger = Just LSLInteger
inferAdd LSLInteger LSLFloat = Just LSLFloat
inferAdd LSLFloat LSLInteger = Just LSLFloat
inferAdd LSLFloat LSLFloat = Just LSLFloat
inferAdd LSLString LSLString = Just LSLString
inferAdd LSLVector LSLVector = Just LSLVector
inferAdd LSLRotation LSLRotation = Just LSLRotation
inferAdd LSLList _ = Just LSLList
inferAdd _ LSLList = Just LSLList
inferAdd _ _ = Nothing

private total inferSub : LSLType -> LSLType -> Maybe LSLType
inferSub LSLInteger LSLInteger = Just LSLInteger
inferSub LSLInteger LSLFloat = Just LSLFloat
inferSub LSLFloat LSLInteger = Just LSLFloat
inferSub LSLFloat LSLFloat = Just LSLFloat
inferSub LSLVector LSLVector = Just LSLVector
inferSub LSLRotation LSLRotation = Just LSLRotation
inferSub _ _ = Nothing

private total inferMul : LSLType -> LSLType -> Maybe LSLType
inferMul LSLInteger LSLInteger = Just LSLInteger
inferMul LSLInteger LSLFloat = Just LSLFloat
inferMul LSLInteger LSLVector = Just LSLVector
inferMul LSLFloat LSLInteger = Just LSLFloat
inferMul LSLFloat LSLFloat = Just LSLFloat
inferMul LSLFloat LSLVector = Just LSLVector
inferMul LSLVector LSLInteger = Just LSLVector
inferMul LSLVector LSLFloat = Just LSLVector
inferMul LSLVector LSLVector = Just LSLVector
inferMul LSLRotation LSLRotation = Just LSLRotation
inferMul _ _ = Nothing

private total inferDiv : LSLType -> LSLType -> Maybe LSLType
inferDiv LSLInteger LSLInteger = Just LSLInteger
inferDiv LSLInteger LSLFloat = Just LSLFloat
inferDiv LSLFloat LSLInteger = Just LSLFloat
inferDiv LSLFloat LSLFloat = Just LSLFloat
inferDiv LSLVector LSLInteger = Just LSLVector
inferDiv LSLVector LSLFloat = Just LSLVector
inferDiv LSLRotation LSLRotation = Just LSLRotation
inferDiv _ _ = Nothing

private total inferMod : LSLType -> LSLType -> Maybe LSLType
inferMod LSLInteger LSLInteger = Just LSLInteger
inferMod LSLVector LSLVector = Just LSLVector
inferMod _ _ = Nothing

private total inferEq : LSLType -> LSLType -> Maybe LSLType
inferEq LSLInteger LSLFloat = Just LSLInteger
inferEq LSLFloat LSLInteger = Just LSLInteger
inferEq a b = toMaybe (a == b) LSLInteger

private total inferComp : LSLType -> LSLType -> Maybe LSLType
inferComp LSLInteger LSLFloat = Just LSLInteger
inferComp LSLFloat LSLInteger = Just LSLInteger
inferComp _ _ = Nothing

Checkable Expr where
	infer ctx (LitExpr a) = infer ctx a
	
	infer ctx (VarExpr v) = infer ctx v
	
	infer ctx (ParenExpr a) = infer ctx a
	
	infer ctx (VectorExpr x y z) = do
		x <- inferValue ctx x
		y <- inferValue ctx y
		z <- inferValue ctx z
		toMaybe (numeric x && numeric y && numeric z) $ ValueType LSLVector
	infer ctx (RotationExpr x y z s) = do
		x <- inferValue ctx x
		y <- inferValue ctx y
		z <- inferValue ctx z
		s <- inferValue ctx s
		toMaybe (numeric x && numeric y && numeric z && numeric s) $ ValueType LSLRotation
	infer ctx (ListExpr as) = do
		_ <- inferList ctx as
		Just $ ValueType LSLList
	
	infer ctx (CastExpr b a) = do
		a <- inferValue ctx a
		toMaybe (castable a b) (ValueType b)
	
	infer ctx (NotExpr a) = do
		a <- checkValue ctx a LSLInteger
		toMaybe a $ ValueType LSLInteger
	infer ctx (AndExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (OrExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	
	infer ctx (BNotExpr a) = do
		a <- checkValue ctx a LSLInteger
		toMaybe a $ ValueType LSLInteger
	infer ctx (BAndExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (BOrExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (BXorExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
		
	infer ctx (NegExpr a) = do
		a <- inferValue ctx a
		toMaybe (negable a) $ ValueType a
	infer ctx (AddExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferAdd a b
		Just $ ValueType t
	infer ctx (SubExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferSub a b
		Just $ ValueType t
	infer ctx (MulExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferMul a b
		Just $ ValueType t
	infer ctx (DivExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferDiv a b
		Just $ ValueType t
	infer ctx (ModExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferMod a b
		Just $ ValueType t
	
	infer ctx (SHLExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
	infer ctx (SHRExpr a b) = do
		a <- checkValue ctx a LSLInteger
		b <- checkValue ctx b LSLInteger
		toMaybe (a && b) $ ValueType LSLInteger
		
	infer ctx (EqExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferEq a b
		Just $ ValueType t
	infer ctx (NeExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferEq a b
		Just $ ValueType t
	infer ctx (LtExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
	infer ctx (LteExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
	infer ctx (GtExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
	infer ctx (GteExpr a b) = do
		a <- inferValue ctx a
		b <- inferValue ctx b
		t <- inferComp a b
		Just $ ValueType t
		
	infer ctx (FnExpr f as) = do
		f <- infer ctx f
		case f of
			FnType r as' => let checks = zipWith (checkValue ctx) as as' in
				toMaybe (andmap (maybe False id) checks) $ maybe NoneType ValueType r
			_ => Nothing
			
	infer ctx (SetExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		toMaybe (v == a || (v == LSLFloat && a == LSLInteger)) $ ValueType v
	infer ctx (SetAddExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferAdd v a
		Just $ ValueType t
	infer ctx (SetSubExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferSub v a
		Just $ ValueType t
	infer ctx (SetMulExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferMul v a
		Just $ ValueType t
	infer ctx (SetDivExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferDiv v a
		Just $ ValueType t
	infer ctx (SetModExpr v a) = do
		v <- inferValue ctx v
		a <- inferValue ctx a
		t <- inferMod v a
		Just $ ValueType t
		
	infer ctx (PreIncExpr v) = do
		v <- checkValue ctx v LSLInteger
		toMaybe v $ ValueType LSLInteger
	infer ctx (PostIncExpr v) = do
		v <- checkValue ctx v LSLInteger
		toMaybe v $ ValueType LSLInteger
	infer ctx (PreDecExpr v) = do
		v <- checkValue ctx v LSLInteger
		toMaybe v $ ValueType LSLInteger
	infer ctx (PostDecExpr v) = do
		v <- checkValue ctx v LSLInteger
		toMaybe v $ ValueType LSLInteger
		
interface ScopedCheckable r where
	scopedInfer : Map Symbol SymbolType -> Map Symbol SymbolType -> r -> Maybe (SymbolType, Map Symbol SymbolType)
	
private total scopedInferList : ScopedCheckable r => Map Symbol SymbolType -> Map Symbol SymbolType -> List r -> Maybe ()
scopedInferList _ _ [] = Just ()
scopedInferList old new (a :: as) = do
	a <- scopedInfer old new a
	scopedInferList old (snd a) as
	
private total getLabels : List Stmt -> List Symbol
getLabels = mapMaybe getLabel where
	total getLabel : Stmt -> Maybe Symbol
	getLabel (LabelStmt v) = Just v
	getLabel _ = Nothing
	
private total getLabelMap  : List Stmt -> Map Symbol SymbolType
getLabelMap as = let as = getLabels as in
	zip as $ replicate (length as) LabelType
	
ScopedCheckable Stmt where
	scopedInfer old new (ExprStmt a) = do
		a <- infer (new ++ old) a
		Just (a, new)
	scopedInfer old new (DefStmt t v a) = case lookup v new of
		Just _ => Nothing
		Nothing => let result = (NoneType, (v, ValueType t) :: new) in
			case a of
				Nothing => Just result
				Just a => do
					a <- checkValue (new ++ old) a t
					toMaybe a result
					
	scopedInfer old new (ScopeStmt body) = do
		_ <- scopedInferList (new ++ old) (getLabelMap body) body
		Just (NoneType, new)
		
	scopedInfer old new DefaultStmt = Just (NoneType, new)
	scopedInfer old new (StateStmt v) = do
		v <- check (new ++ old) v StateType
		toMaybe v (NoneType, new)
		
	scopedInfer old new (IfStmt test tb fb) = do
		_ <- infer (new ++ old) test
		_ <- scopedInfer (new ++ old) [] tb
		_ <- map (scopedInfer (new ++ old) []) fb
		Just (NoneType, new)
	scopedInfer old new (DoWhileStmt body test) = do
		_ <- infer (new ++ old) test
		_ <- scopedInfer (new ++ old) [] body
		Just (NoneType, new)
	scopedInfer old new (ForStmt pres test posts body) = do
		_ <- infer (new ++ old) $ maybe (LitExpr $ IntLit 1) id test
		_ <- inferList (new ++ old) pres
		_ <- inferList (new ++ old) posts
		_ <- scopedInfer (new ++ old) [] body
		Just (NoneType, new)
	scopedInfer old new (WhileStmt test body) = do
		_ <- infer (new ++ old) test
		_ <- scopedInfer (new ++ old) [] body
		Just (NoneType, new)
	
	scopedInfer old new (JumpStmt v) = do
		v <- check (new ++ old) v LabelType
		toMaybe v (NoneType, new)
	scopedInfer _ new (LabelStmt _) = Just (NoneType, new)
	
	scopedInfer old new (ReturnStmt a) = do
		_ <- maybe (Just NoneType) (infer (new ++ old)) a
		Just (NoneType, new)

ScopedCheckable Event where
	scopedInfer old new e = do
		_ <- scopedInferList (namedArgs (type e) (args e) ++ new ++ old) [] (body e)
		Just (EventType, [])
	
private total checkDupedEvents : List Event -> Bool
checkDupedEvents [] = False
checkDupedEvents (a :: as) = elemBy checkDupe a as || checkDupedEvents as where
	checkDupe : Event -> Event -> Bool
	checkDupe e e' = eventName (type e) == eventName (type e') -- TODO: Add a proper Eq implementation
	
ScopedCheckable State where
	scopedInfer old new s = let evts = body s in do
		_ <- scopedInferList old new evts
		toMaybe (not (checkDupedEvents evts) && length evts > 0) (StateType, [])
	
ScopedCheckable Function where
	scopedInfer old new f = do
		_ <- scopedInferList old new (body f)
		Just (FnType (result f) $ map snd (args f), [])
	
private total checkDupedSymbols : List Symbol -> Bool
checkDupedSymbols [] = False
checkDupedSymbols (a :: as) = elem a as || checkDupedSymbols as

private hasDefaultState : Script -> Bool
hasDefaultState s = ormap (\s => isNothing $ name s) $ states s

ScopedCheckable Script where
	scopedInfer old new s = let globals = map (\(n, t) => (n, ValueType t)) (globals s) in do
		_ <- scopedInferList (globals ++ old) new (funcs s)
		_ <- scopedInferList (globals ++ old) new (states s)
		toMaybe (hasDefaultState s && (not $ checkDupedSymbols (map fst globals ++ map name (funcs s) ++ map stateName (states s)))) (NoneType, [])
