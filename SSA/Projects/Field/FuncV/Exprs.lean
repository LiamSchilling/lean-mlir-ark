import SSA.Projects.Field.FuncV.Defs

variable {D : Dialect} [DialectSignature D] {Γ : Ctxt (FuncV.Ty D.Ty D.m)} {eff : EffectKind}
variable {funcSig : FuncV.FunctionSignature (FuncV.Ty D.Ty D.m) D.Ty}

namespace FuncV

/-- An expression in the dialect realizing a raised operation. -/
def raiseExpr
    (op' : D.Op)
    (args : HVector Γ.Var (DialectSignature.sig op' |>.map .raise))
    (regArgs : HVector (Region (FuncV D)) (DialectSignature.regSig op' |>.map Ty.raise)) :
    Expr (FuncV D) Γ
      (DialectSignature.effectKind op')
      (DialectSignature.returnTypes op' |>.map .raise) :=
  Expr.mk (.raise op') rfl (le_of_eq rfl) args regArgs

/-- An expression in the dialect realizing a `call` operation. -/
def callExpr
    (f : Γ.Var <| .pi funcSig)
    (fArgs : HVector Γ.Var (funcSig.sig.map .raise)) :
    Expr (FuncV D) Γ
      .impure
      (funcSig.returnTypes.map .raise) :=
  Expr.mk (.call funcSig) rfl (le_of_eq rfl) (f ::ₕ fArgs) []ₕ

/-- An expression in the dialect realizing a `func` operation. -/
def funcExpr
    (ctxtArgs : HVector Γ.Var funcSig.context.toList)
    (body : Region (FuncV D) (funcSig.map .raise).toRegSigElem) :
    Expr (FuncV D) Γ
      .pure
      [.pi funcSig] :=
  Expr.mk (.func funcSig) rfl (le_of_eq rfl) ctxtArgs [body]ₕ

end FuncV
