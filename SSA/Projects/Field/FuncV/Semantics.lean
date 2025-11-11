import SSA.Projects.Field.FuncV.Defs

variable {D : Dialect} [TyDenote D.Ty] [DialectSignature D] [DialectDenote D] [Monad D.m]

namespace FuncV

/-- The semantics for the dialect.

`call` is denoted by taking the denotation of its first argument,
which is a Lean function,
and applying to it the donations of the rest of its arguments,
which are the arguments to that function.

`func` is denoted by taking the denotations of the external captured context,
and the denotation of the regional argument, which is a Lean function,
and partially applying to that function the captured context,
yielding a function mapping from the region's argument parameters to its outputs. -/
@[simp_denote]
instance : DialectDenote (FuncV D) where
denote
| .raise op', arg, regArg => do
  let res ← DialectDenote.denote op' (arg.castFromMap Ty.raise rfl) <|
    regArg.fromMap' (RegionSignature.mapElem Ty.raise) fun _ denote val => do
      let res ← denote <| val.castToMap rfl
      return res.castFromMap Ty.raise rfl
  return res.castMap Ty.raise rfl
| .call funcSig, f ::ₕ fArgs, _ => do
  let res ← f <| fArgs.castFromMap Ty.raise rfl
  return res.castMap Ty.raise rfl
| .func funcSig, ctxtArgs, [body]ₕ => [fun fArgs => do
  let res ← body <| .ofHVector <| .append ctxtArgs (fArgs.castMap Ty.raise rfl)
  return res.castFromMap Ty.raise rfl ]ₕ

end FuncV
