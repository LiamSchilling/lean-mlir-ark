# Computation-to-Computation Lowerings for a Field Dialect Blueprint

## Lowering Framework

### Lowering

We begin by defining the lowering paradigm we will follow to transform computations in high-level IRs into equivalent computations in low-level IRs (primarily LLVM). A lowering from a source dialect to a target dialect [2] is a computation-to-computation function from the source dialect to the target dialect that preserves semantics. Since the semantics of distinct dialects may be in terms of distinct yet isomorphic types, semantic preservation will always be in terms of some relation between the semantics of the dialects [1].

#### Roadmap

- [x] [1] Define the type of a lowering from the semantics of `D` to the semantics of `D'`.
- [x] [2] Define the type of a computation-to-computation lowering from `D` to `D'` that is correct according to a semantic lowering.

### The inlining pass

When implementing lowerings, it is common that single-line expressions in the source dialect map to multiple-line computations in the target dialect. This inlining transformation may be complicated to manage. In classic MLIR, this is fixed by encapsulating the computation into a function using the `func` dialect, allowing any lowering to be specified by an expression-to-expression map accompanied by some function definitions. However, functions in MLIR exist at the module level, whereas we are concerned with computation-to-computation lowerings rather than module-to-module lowerings.

To address this, we define a modified `func` dialect [1] where functions exist at the computation level as SSA values instead of at the module level. Similarly to `func`, this dialect will allow us to specify any computation-to-computation lowering by an expression-to-expression map [2, 3], abstracting away the inlining pass. This pass will instead be handled by a lowering from our function dialect [4] that dissolves all functions defined in a program by inlining their definitions wherever they are called.

#### Roadmap

- [x] [1] Define the `FuncV[D]` ("**FUNC**tion **V**alues") wrapper around a dialect `D` for defining and calling functions as SSA values.
- [ ] [2] Define the type of an expression-to-expression lowering from `D` to `FuncV[D]` that is allowed a constant preamble of function definitions.
- [ ] [3] Implement the transformation from an expression-to-expression lowering to a program-to-program lowering.
- [ ] [4] Implement a lowering from `FuncV[D]` to `D` using inlining.

An important technical consideration is the flow of context into function bodies. Function bodies are specified by MLIR regions, which do not implicitly capture values from the current context in the computation. So, it is necessary to explicitly pass any values that should be captured, including previously defined functions, from the current context into the function body at the time of definition. To accomodate this, the initial context of the region specifying the function body will be in two parts: the first *n* values will be captured from the external context and passed in at definition time, and the last *m* values will be the arguments to the function passed in at call time.

## Considerations for Dialect Design

### Dialect compositionality

Unlike in classic MLIR, where we may register new dialects and use them in the same computation automatically, in Lean MLIR, we must be very explicit about how to compose dialects since computations are always restricted to one dialect. This challenge has been addressed previously in the `scf` dialect. In Lean MLIR, `scf` is implemented as a "dialect wrapper" that transforms an underlying dialect by attaching structured control flow functionality on top of it.

Our dialects will similarly reuse constructs implemented in underlying dialects by wrapping them. For instance, a field dialect should have a type for integers to support taking integer multiples and integer powers of field elements. Though, implementing such a type with full integer arithmetic within the field dialect would be cumbersome and against the compositionality paradigm of MLIR. Instead, the field dialect will wrap an underlying dialect that is required to provide its own representative integer type. This way, the task of handling integer arithmetic is left up to the underlying dialect, and the field dialect only has to handle its field operations.

Wrapping compositionality is not free of limitations. Notably, wrappers impose a compositional imbalance where the underlying dialect is unaware of the wrapper. For instance, suppose we want a Lean MLIR dialect that attaches to `D` control flow from `Scf` and function abstractions from `FuncV`. In the dialect `Scf[FuncV[D]]`, `FuncV[D]` is unaware of `Scf` so control flow operations cannot be used in function bodies. On the other hand, in the dialect `FuncV[Scf[D]]`, `Scf[D]` is unaware of `FuncV` so function operations cannot be used in control flow bodies. In general, the problem arises when the underlying dialect has generic constructs like type-parameterized operations or regional arguments, since the application of a wrapper introduces new types and operations that these constructs will be unaware of. One workaround is to repeatedly layer wrappers as in `FuncV[Scf[...FuncV[Scf[D]]...]]`, though defining computations in these dialects is cumbersome for obvious resons.

### Capturing poison semantics

When lowering to LLVM, poison semantics are an important consideration. Specifically, any LLVM value is either valid—in which case it has a meaningful value—or poison, with poison propagating through most operations. This means that dialects whose types will lower to or interact with LLVM types must also propagate poison and thus give their types poison semantics. One solution is to give all the types in our dialects poison semantics. This is undesirable because it assumes the use of our dialects alongside LLVM, whereas MLIR dialects should be generically compositional.

To resolve this, we will give all the types in our dialects `m`-semantics for a generic monad `m`. This handles the case where poison is unnecessary (`m := Id`), the case where poison is necessary (`m := PoisonOr`), and in general, any case where values may carry additional contextual information in their semantics.

## Field Dialect

### The dialect

To demonstrate our lowering pipeline, we define a minimal field dialect and implement multiple lowerings to `LLVM` for different fields.

#### Roadmap

- [ ] [1] Define the `Flop(F)[D]` ("**F**ie**L**d **OP**erations") wrapper around an integer dialect `D` for operating on elements of a field `F`.
- [ ] [2] Implement a lowering from `Flop(F)[LLVM]` to `FuncV[LLVM]` for the base fields `F := ZMod p` using the Montgomery integer representation.
- [ ] [3] Implement a lowering from `Flop(F)[LLVM]` to `FuncV[LLVM]` for the binary splitting fields `F := (ZMod 2)[x] / p(x)` using the bitvector of coefficients representation.
