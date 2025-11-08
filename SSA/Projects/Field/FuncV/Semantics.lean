import SSA.Projects.Field.FuncV.Basic
import SSA.Projects.Field.Util

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
  let res ← DialectDenote.denote op' (arg.fromMap' Ty.raise fun _ => id) <|
    regArg.fromMap' (RegionSignature.mapElem Ty.raise) fun _ denote val => do
      let res ← denote <| val.toMap (by simp) fun _ => id
      return res.fromMap' Ty.raise fun _ => id
  return res.map' Ty.raise fun _ => id
| .call funcSig, f ::ₕ fArgs, _ => do
  let res ← f <| fArgs.fromMap' Ty.raise fun _ => id
  return res.map' Ty.raise fun _ => id
| .func funcSig, ctxtArgs, [regArg]ₕ => [fun fArgs => do
  let res ← regArg <| .ofHVector <| HVector.append ctxtArgs (fArgs.map' Ty.raise fun _ => id)
  return res.fromMap' Ty.raise fun _ => id ]ₕ

end FuncV
