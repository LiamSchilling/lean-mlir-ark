import LeanMLIR.Basic

variable {Ty Ty' : Type} [DecidableEq Ty] [DecidableEq Ty'] [TyDenote Ty]
variable (m : Type → Type) [Monad m]

namespace FuncV

/-- The type signature of a function in the dialect.
This definition is modeled after `Signature`, with regional arguments omitted.
Also included is the context captured by the function body. -/
structure FunctionSignature (Ty Ty' : Type) where
  mkEffectful ::
  sig : List Ty'
  returnTypes : List Ty'
  effectKind : EffectKind := .pure
  context : Ctxt Ty

instance : DecidableEq (FunctionSignature Ty Ty')
| ⟨a, b, c, d⟩, ⟨e, f, g, h⟩ => decidable_of_iff (a = e ∧ b = f ∧ c = g ∧ d = h) <| by simp

namespace FunctionSignature

/-- A map on input and output types.
Since the context will usually already be of the higher type, there is no need to map it. -/
def map (f : Ty' → Ty) (funcSig : FunctionSignature Ty Ty') : FunctionSignature Ty Ty where
  sig := funcSig.sig.map f
  returnTypes := funcSig.returnTypes.map f
  effectKind := funcSig.effectKind
  context := funcSig.context

/-- The type signature of the region that contains the body of the function.
The context comes from the input to the function and the captured external context,
and the return types come from the output of the function. -/
@[reducible]
def toRegSig (funcSig : FunctionSignature Ty Ty) : RegionSignature Ty :=
  [(funcSig.context ++ .ofList funcSig.sig, funcSig.returnTypes)]

/-- A function type denotes to a Lean function from its inputs types to its output types,
which may be effectful with effects in the monad `m`. -/
@[simp_denote, reducible]
def toType (toType : Ty' → Type) (funcSig : FunctionSignature Ty Ty') : Type :=
  HVector toType funcSig.sig → EffectKind.impure.toMonad m (HVector toType funcSig.returnTypes)
  -- for now, the effect must be assumed to be `.impure`
  -- this is due to the upstream issue that regions must be impure
  -- once that is fixed, the effect should be replaced with `funcSig.effectKind`

end FunctionSignature

end FuncV
