/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.FreeBaseChange

import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# Scalar extension of the symplectic-basis Arf sum

Let `Q` be a quadratic form on a free module `V` over a commutative ring `k`, and let
`b : Module.Basis (ι ⊕ ι) k V` be a symplectic basis for its polar form, that is, a basis in
which `Q.polarBilin` has the matrix `Matrix.J ι k`. The Arf invariant of `Q` is read off from the
sum `∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. Over `ZMod 2` this sum is the Arf invariant
itself (`QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`). Over a finite field `k` of
characteristic two, the sum depends on the basis, but its absolute trace
`Algebra.trace (ZMod 2) k` does not, and that trace is the Arf invariant.

This file computes the effect on that coordinate of the scalar extension
`QuadraticForm.freeBaseChange` along an `k`-algebra `l`, which needs no inverse of `2`:

* the extended basis `b.baseChange l` is again a symplectic basis for the polar form of
  `Q.freeBaseChange l` (`QuadraticForm.toMatrix_polarBilin_freeBaseChange_eq_J`);
* when `l` is free over `k` and `k` is free over a base ring `F`, the trace to `F`
  of the extended sum is `Module.finrank k l` times the trace to `F` of the original sum
  (`QuadraticForm.trace_sum_mul_freeBaseChange_eq_finrank_smul`).

For finite fields `k ⊆ l` of characteristic two and `F = ZMod 2`, scalar extension therefore
multiplies the absolute-trace Arf coordinate by the degree `[l : k]` modulo two. For example the
plane `x ^ 2 + x * y + y ^ 2` over `ZMod 2` has Arf invariant one, while its extension to the field
with four elements has trace sum zero, since that extension has degree two.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. 183 (1941), 148–167.
-/

public section

open TensorProduct

namespace QuadraticForm

variable {k l V ι : Type*} [CommRing k] [CommRing l] [Algebra k l]
  [AddCommGroup V] [Module k V] [Module.Free k V] [Fintype ι]

/-- **Scalar extension of a symplectic basis.** If `b` is a symplectic basis for the polar form of
`Q`, then its base change `b.baseChange l` is a symplectic basis for the polar form of
`Q.freeBaseChange l`. -/
theorem toMatrix_polarBilin_freeBaseChange_eq_J [DecidableEq ι] {Q : QuadraticForm k V}
    {b : Module.Basis (ι ⊕ ι) k V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι k) :
    LinearMap.BilinForm.toMatrix (b.baseChange l) (Q.freeBaseChange l).polarBilin =
      Matrix.J ι l := by
  rw [polarBilin_freeBaseChange, LinearMap.BilinForm.toMatrix_baseChange, hb, Matrix.map_J]

/-- **Extension-degree law for the trace of the Arf sum.** Let `k` be free over a base ring `F`
and `l` free over `k`. For a quadratic form `Q` on a free `k`-module and a basis
`b` indexed by `ι ⊕ ι`, the trace to `F` of the sum `∑ i, Q' (b' (Sum.inl i)) * Q' (b' (Sum.inr i))`
for `Q' = Q.freeBaseChange l` and `b' = b.baseChange l` is `Module.finrank k l` times the trace to
`F` of the corresponding sum for `Q` and `b`.

When `b` is a symplectic basis for the polar form of `Q`, so is `b.baseChange l` for that of
`Q.freeBaseChange l` (`QuadraticForm.toMatrix_polarBilin_freeBaseChange_eq_J`). For finite fields
of characteristic two and `F = ZMod 2`, both sides are then the absolute-trace Arf coordinates. -/
theorem trace_sum_mul_freeBaseChange_eq_finrank_smul (F : Type*) [CommRing F] [Algebra F k]
    [Algebra F l] [IsScalarTower F k l] [Module.Free F k] [Module.Free k l] (Q : QuadraticForm k V)
    (b : Module.Basis (ι ⊕ ι) k V) :
    Algebra.trace F l (∑ i : ι, Q.freeBaseChange l (b.baseChange l (Sum.inl i)) *
        Q.freeBaseChange l (b.baseChange l (Sum.inr i))) =
      Module.finrank k l • Algebra.trace F k (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))) := by
  simp only [freeBaseChange_basis_baseChange, ← map_mul, ← map_sum]
  exact TauCeti.Algebra.trace_algebraMap_tower _

end QuadraticForm
