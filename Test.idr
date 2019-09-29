module LSL.Test

import Data.Vect

import LSL.Helpers
import LSL.Syntax
import LSL.Typecheck
import LSL.Compile

tests : List Script
tests = [
	MkScript [] [] [
		MkState Nothing [
			MkEvent EntryEvent [] [
				DefStmt LSLInteger "a" (Just $ LitExpr $ IntLit 5),
				DefStmt LSLInteger "b" (Just $ LitExpr $ IntLit 6),
				IfStmt (EqExpr (VarExpr "a") (VarExpr "b"))
					(ExprStmt $ PostIncExpr "a")
					(Just $ ExprStmt $ PostIncExpr "b")
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent EntryEvent [] [
				DefStmt LSLVector "a" Nothing,
				DefStmt LSLVector "b" Nothing,
				IfStmt (VarExpr "a")
					(ScopeStmt [
						ExprStmt (SetExpr "a" (VectorExpr (LitExpr $ FloatLit 1) (LitExpr $ FloatLit 2) (LitExpr $ FloatLit 3)))
						])
					(Just $ ScopeStmt [
						ExprStmt (SetExpr "a" (VarExpr "b"))
						])
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent EntryEvent [] [
				ForStmt [] Nothing [] $ ScopeStmt [
					DefStmt LSLInteger "a" Nothing
				]
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent EntryEvent [] [
				ExprStmt $ LitExpr $ IntLit 4
			]
		]
	],
	MkScript [] [] [
		MkState Nothing [
			MkEvent EntryEvent [] [
				ExprStmt $ MulExpr (LitExpr $ IntLit 4) $ AddExpr (LitExpr $ IntLit 5) (LitExpr $ IntLit 6)
			]
		]
	]
]
