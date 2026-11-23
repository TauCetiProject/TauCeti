/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.RingTheory.Semisimple.Trace.Form
import Mathlib.Algebra.CharP.Algebra
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# The Jacobson radical under extension of scalars

Let `A` be a finite-dimensional algebra over a field `K` of characteristic zero, not necessarily
commutative, and let `L` be a field extension of `K`. This file proves that forming the Jacobson
radical commutes with extending scalars to `L`:

```text
rad(L ⊗[K] A) = L ⊗[K] rad(A).
```

In particular `L ⊗[K] A` is semisimple whenever `A` is.

The proof goes through the regular trace form `(x, y) ↦ tr(L_{xy})`. In characteristic zero the
Jacobson radical of a finite-dimensional algebra is the kernel of this form
(`TauCeti.restrictScalars_jacobson_eq_ker_regularTraceForm`). The regular trace form of `L ⊗[K] A`
is the base change of that of `A` (`Algebra.regularTraceForm_baseChange`), and the kernel of a
bilinear form commutes with extension of scalars (`LinearMap.BilinForm.ker_baseChange`).

Characteristic zero is essential. Over `K = 𝔽_p(t)`, the field `A = K(t^{1/p})` has zero radical,
but `A ⊗[K] A` contains the nonzero nilpotent `t^{1/p} ⊗ 1 - 1 ⊗ t^{1/p}`, whose `p`-th power is
`t ⊗ 1 - 1 ⊗ t = 0`.

This is the scalar-extension step in Jannsen's proof that numerical motives form a semisimple
category: the algebra of homological self-correspondences is extended to the coefficient field of
a Weil cohomology, where traces are available, and the radical must be computed there.

## Main results

* `TauCeti.restrictScalars_jacobson_tensorProduct_eq_baseChange`: **the Jacobson radical of
  `L ⊗[K] A` is the base change of the Jacobson radical of `A`.**
* `TauCeti.isSemisimpleRing_tensorProduct`: the base change of a finite-dimensional semisimple
  algebra in characteristic zero is semisimple.

## References

* U. Jannsen, *Motives, numerical equivalence, and semi-simplicity*, Invent. Math. **107** (1992),
  447–452, proof of Theorem 1.
* N. Bourbaki, *Algebra, Chapter 8*, §12, no. 7, for the behaviour of the radical under extension
  of scalars.
-/

public section

open scoped TensorProduct

open Algebra

namespace TauCeti

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A] [FiniteDimensional K A]
  (L : Type*) [Field L] [Algebra K L]

/-- **The Jacobson radical commutes with extension of scalars in characteristic zero.** For a
finite-dimensional algebra `A` over a field `K` of characteristic zero and a field extension `L` of
`K`, the Jacobson radical of `L ⊗[K] A` is the base change of the Jacobson radical of `A`, as
`L`-subspaces of `L ⊗[K] A`. -/
theorem restrictScalars_jacobson_tensorProduct_eq_baseChange :
    (Ring.jacobson (L ⊗[K] A)).restrictScalars L =
      ((Ring.jacobson A).restrictScalars K).baseChange L := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  rw [restrictScalars_jacobson_eq_ker_regularTraceForm, regularTraceForm_baseChange,
    LinearMap.BilinForm.ker_baseChange, restrictScalars_jacobson_eq_ker_regularTraceForm]

/-- **Semisimplicity is preserved by extension of scalars in characteristic zero.** The base change
of a finite-dimensional semisimple algebra over a field of characteristic zero to a field extension
is semisimple, its regular trace form being the base change of a nondegenerate form. -/
instance isSemisimpleRing_tensorProduct [IsSemisimpleRing A] : IsSemisimpleRing (L ⊗[K] A) :=
  isSemisimpleRing_of_nondegenerate_regularTraceForm (K := L) <| by
    rw [regularTraceForm_baseChange]
    exact nondegenerate_regularTraceForm.baseChange L

end TauCeti
