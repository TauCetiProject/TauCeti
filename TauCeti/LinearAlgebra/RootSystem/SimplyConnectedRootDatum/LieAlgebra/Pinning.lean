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
* `TauCeti.DynkinType.pinnedExpNeg`: the uniform lowering exponential `u ↦ exp(u • f_i)`.
* `TauCeti.DynkinType.pinnedExpNeg_zero`: its value at zero.
* `TauCeti.DynkinType.pinnedExp_comm_of_matrix_comm`: commuting generators give commuting
  exponentials, the group-level form of a vanishing Lie bracket.

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

/-- The uniform lowering exponential `u ↦ exp(u • f_i)`, defined as the same finite sum with
the lowering generator. -/
def pinnedExpNeg (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
    (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) •
      (((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k).map
        (algebraMap ℚ R)

/-- The lowering exponential at `u = 0` is the identity matrix. -/
theorem pinnedExpNeg_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExpNeg ht R i 0 = 1 := by
  unfold pinnedExpNeg
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

/-! ## Commutator relations -/

/-- If the simple raising generators commute as matrices, their uniform exponentials commute.
This is the group-level reflection of a vanishing Lie bracket: when `⁅e_i, e_j⁆ = 0`, the
corresponding root subgroups commute. -/
theorem pinnedExp_comm_of_matrix_comm (R : Type*) [CommRing R] [Algebra ℚ R]
    (i j : Fin t.rank) (u v : R)
    (hcomm : ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)) :
    t.pinnedExp ht R i u * t.pinnedExp ht R j v =
      t.pinnedExp ht R j v * t.pinnedExp ht R i u := by
  unfold pinnedExp
  -- Expand both products as double sums
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  -- Swap summation order on the left to match the right
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  -- Term-wise: (c_k • A^k) * (d_l • B^l) = (d_l • B^l) * (c_k • A^k)
  -- Scalars commute (commutative ring), matrices commute by hypothesis
  let Ei : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ := (t.lieBasis ht).e i
  let Ej : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ := (t.lieBasis ht).e j
  have hmat : ((Ei ^ k).map (algebraMap ℚ R)) * ((Ej ^ l).map (algebraMap ℚ R)) =
      ((Ej ^ l).map (algebraMap ℚ R)) * ((Ei ^ k).map (algebraMap ℚ R)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have hcomm' : Commute Ei Ej := hcomm
    exact (hcomm'.pow_pow k l).eq
  -- Distribute scalars: (c • A) * (d • B) = (c * d) • (A * B)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Use matrix commutativity to align the matrix factors
  rw [hmat]
  -- Now both sides have (B^l * A^k); scalars commute
  rw [mul_comm (u ^ k * _) (v ^ l * _)]

end

end TauCeti.DynkinType
