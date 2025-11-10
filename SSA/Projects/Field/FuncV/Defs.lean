import SSA.Projects.Field.FuncV.Data

/-!
# Function Dialect

Defines a wrapper dialect `FuncV` for function abstractions.
`FuncV` is similar to the MLIR dialect `Func`, but they live at different scopes.
`Func` functions exists at the module level and are associated with static symbols.
`FuncV` functions exist at the program level and are associated with SSA values.

The goal of this dialect is to abstract away inlining for dialect lowering.
Higher-level dialects should lower to a `FuncV`-wrapped dialect
when its expressions lower to computations that would fit more cleanly in a function.
Then, the `FuncV`-wrapped dialect lowers by inlining those function calls generically.

Functions in the dialect are not first-class,
in that they may not be passed in and out of functions themselves.
However, the bodies of functions may capture previously-defined SSA values, including functions,
by taking them as regional context.
Functions may be effectful.
Functions may not be recursive, since this would prevent lowering by inlining.
-/

variable {Ty' Op' : Type} [DecidableEq Ty'] [TyDenote Ty'] {m : Type → Type}
variable {D : Dialect} [DialectSignature D]

namespace FuncV

/-- The types in the dialect:
- `raise`: a type in the underlying dialect
- `pi`: the type of a function -/
inductive Ty (Ty' : Type) (m : Type → Type) where
| raise : Ty' → Ty Ty' m
| pi : FunctionSignature (Ty Ty' m) Ty' → Ty Ty' m

def Ty.lower : Ty Ty' m → Option Ty'
| .raise ty' => some ty'
| .pi _ => none

instance : DecidableEq (Ty Ty' m)
| .raise a, .raise b => decidable_of_iff (a = b) <| by simp
| .raise _, .pi _ => isFalse <| by intro; contradiction
| .pi _, .raise _ => isFalse <| by intro; contradiction
| .pi a, .pi b => sorry

/-- A map from types in the dialect to the Lean types of their semantic interpretations.
The semantic interpretations of types from the underlying dialect are preserved.
`pi` denotes to a Lean function from the types of its inputs to the types of its outputs. -/
@[simp_denote, reducible]
instance : TyDenote (Ty Ty' m) where
toType
| .raise ty' => ⟦ty'⟧
| .pi funcSig => funcSig.toType m toType

/-- The operations in the dialect:
- `raise`: an operation in the underlying dialect
- `call`: a call to a value whose type is a function, followed by the arguments to the function,
  outputing memebers of the return types of the function
- `func`: a function definition explicitly passing values from the external context as arguments,
  defining the function body in a region
  whose context is the captured external context followed by the function's arugments

The flow of external context into regional argument context
is balanced between the native operations `call` and `func`.
The regional context may be divided into two segments.
- The first segment is the captured external context during the function definition,
  the values of which will be explicitly passed as arguments to `func` at the time of definition.
  This explicit passing is necessary
  since regions do not automatically capture previous context in MLIR.
  This piece of the regional context is the only piece that may contain function values,
  which is what enables us to reuse previously-defined functions in function definitions.
- The last segment contains the function's arguments,
  which will be passed to `call` and may vary by call.
  The types of these arguments are guarenteed to be raised from the underlying dialect,
  since function values are not first-class. -/
inductive Op (Ty' Op' : Type) (m : Type → Type) where
| raise : Op' → Op Ty' Op' m
| call : FunctionSignature (Ty Ty' m) Ty' → Op Ty' Op' m
| func : FunctionSignature (Ty Ty' m) Ty' → Op Ty' Op' m

def Op.lower : Op Ty' Op' m → Option Op'
| .raise ty' => some ty'
| .call _ => none
| .func _ => none

/-- A map from operations to the types of their outputs. -/
@[reducible]
def Op.sig (sig' : Op' → List Ty') : Op Ty' Op' m → List (Ty Ty' m)
| .raise op' => sig' op' |>.map .raise
| .call funcSig => .pi funcSig :: funcSig.sig.map .raise
| .func funcSig => funcSig.context.toList

/-- A map from operations to the types of their outputs. -/
@[reducible]
def Op.returnTypes (returnTypes' : Op' → List Ty') : Op Ty' Op' m → List (Ty Ty' m)
| .raise op' => returnTypes' op' |>.map .raise
| .call funcSig => funcSig.returnTypes.map .raise
| .func funcSig => [.pi funcSig]

/-- A map from operations to the signatures of their attached regions.
The only native operation with a region is `func`, which takes the body of the function. -/
@[reducible]
def Op.regSig (regSig' : Op' → RegionSignature Ty') : Op Ty' Op' m → RegionSignature (Ty Ty' m)
| .raise op' => regSig' op' |>.map .raise
| .call _ => []
| .func funcSig => funcSig.map .raise |>.toRegSig

/-- A map from operations to the kinds of their effects.
The native operation `call` has the effect kind of the function being called. -/
@[reducible]
def Op.effectKind (effectKind' : Op' → EffectKind) : Op Ty' Op' m → EffectKind
| .raise op' => effectKind' op'
| .call _ => .impure
| .func _ => .pure
  -- for now, the effect must be assumed to be `.impure`
  -- this is due to the upstream issue that regions must be impure
  -- once that is fixed, the effect should be replaced with `funcSig.effectKind`

/-- A map from operations to their full type signatures. -/
@[reducible]
def Op.signature (signature' : Op' → Signature Ty') : Op Ty' Op' m → Signature (Ty Ty' m)
| op => {
  sig := op.sig (Signature.sig <| signature' .),
  returnTypes := op.returnTypes (Signature.returnTypes <| signature' .),
  regSig := op.regSig (Signature.regSig <| signature' .),
  effectKind := op.effectKind (Signature.effectKind <| signature' .) }

end FuncV

/-- The dialect, which wraps the underlying dialect `D`. -/
@[reducible]
def FuncV (D : Dialect) : Dialect where
Ty := FuncV.Ty D.Ty D.m
Op := FuncV.Op D.Ty D.Op D.m
m := D.m

namespace FuncV

/-- The type signatures for the dialect. -/
@[reducible]
instance : DialectSignature (FuncV D) where
signature := Op.signature DialectSignature.signature

end FuncV
