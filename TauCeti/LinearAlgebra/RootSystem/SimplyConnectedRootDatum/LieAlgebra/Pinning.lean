/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic

/-!
# Uniform Chevalley pinning for the Demazure construction

The pinned rational Lie algebra of a valid Dynkin type carries Bourbaki-numbered generators
(`TauCeti.DynkinType.lieBasis`): raising generators `e i` and lowering generators `f i` that
are nilpotent matrices, Cartan generators `h i`, satisfying the Cartan-matrix relations
(`TauCeti.DynkinType.lie_lieBasis_h_e`, `TauCeti.DynkinType.lie_lieBasis_h_f`) and exchanged
by the Chevalley involution (`TauCeti.DynkinType.chevalleyInvolution_lieBasis_e`).

This module packages the uniform exponential `exp(u • e i)`, the pinning isomorphism
`𝔾_a → U_i` that is the input to the Chevalley-Demazure group-scheme construction. The
nilpotency makes the exponential a finite sum, hence a polynomial map over any `ℚ`-algebra.

## Main definitions

* `TauCeti.DynkinType.pinnedExp`: the uniform exponential `u ↦ exp(u • e_i)` as a matrix
  over any `ℚ`-algebra, defined as a finite sum using the matrix dimension as bound.

## Main results

* `TauCeti.DynkinType.pinnedExp_zero`: the exponential at zero is the identity matrix.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

Roadmap: ReductiveGroups (Layer 9, uniform pinned Chevalley-Demazure construction).
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ## The uniform exponential -/

/-- The uniform exponential of the `i`-th simple raising generator: `exp(u • e_i)` as a
finite sum over `k < Fintype.card (t.GeckIndex ht)`. Since `e_i` is nilpotent
(`TauCeti.DynkinType.isNilpotent_coe_lieBasis_e`), terms beyond the nilpotency index vanish,
so the matrix-dimension bound is safe. -/
def pinnedExp (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
    (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) •
      (((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k).map
        (algebraMap ℚ R)

/-- The exponential at `u = 0` is the identity matrix: only the `k = 0` term survives. -/
theorem pinnedExp_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExp ht R i 0 = 1 := by
  unfold pinnedExp
  have h0mem : (0 : ℕ) ∈ Finset.range (Fintype.card (t.GeckIndex ht)) := by
    simp only [Finset.mem_range]
    have hpos : 0 < t.numRoots := t.numRoots_pos ht
    have hcard : Fintype.card (t.GeckIndex ht)
        = Fintype.card (t.rationalBase ht).support + t.numRoots := by
      simp [GeckIndex, Fintype.card_sum]
    omega
  rw [Finset.sum_eq_single_of_mem _ h0mem]
  · simp
  · intro k _ hk
    rw [zero_pow hk]
    simp

end

end TauCeti.DynkinType
