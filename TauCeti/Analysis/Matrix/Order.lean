/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Order.Compact
public import TauCeti.LinearAlgebra.Matrix.OfReal
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Compact order intervals for the Loewner order

For the Loewner order on square matrices over `ℝ` or `ℂ` (`open scoped MatrixOrder`), every closed
interval `Set.Icc a b` is compact. If the interval is nonempty, then `b - a` is positive
semidefinite and every `x` in it has `0 ≤ x - a ≤ b - a`, so the spectrum of `x - a` lies in
`[0, r]` for any upper bound `r` of the spectrum of `b - a`; the `ℓ²` operator norm of `x - a`,
which is its spectral radius, is then at most `r`. The interval is closed because the Loewner
order is.

This is the compactness behind fixed-point arguments on sets of matrices such as
`{S | α • 1 ≤ S ≤ β • 1}`, which are also convex.

## Main statements

* `Matrix.instCompactIccSpace`: the Loewner order on `Matrix n n 𝕜` has compact closed intervals.
* `Matrix.PosDef.of_le`: a matrix Loewner-dominating a positive definite matrix is positive
  definite.
* `Matrix.IsHermitian.le_smul_one_of_l2_opNorm_le`,
  `Matrix.IsHermitian.neg_smul_one_le_of_l2_opNorm_le`,
  `Matrix.PosSemidef.le_l2_opNorm_smul_one`,
  `Matrix.PosSemidef.l2_opNorm_le_of_le_smul_one`: Loewner bounds from and for the `ℓ²` operator
  norm.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜]

open scoped ContinuousFunctionalCalculus in
/-- Closed intervals of the Loewner order on square matrices are compact. -/
instance instCompactIccSpace [Finite n] : CompactIccSpace (Matrix n n 𝕜) where
  isCompact_Icc {a b} := by
    classical
    have := Fintype.ofFinite n
    rcases (Set.Icc a b).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
    · simp [h]
    have hba : 0 ≤ b - a := sub_nonneg.2 (hx₀.1.trans hx₀.2)
    obtain ⟨r, hr⟩ := (isCompact_iff_compactSpace.mpr inferInstance :
      IsCompact (spectrum ℝ (b - a))).bddAbove
    have hbar : b - a ≤ algebraMap ℝ _ r :=
      le_algebraMap_of_spectrum_le (fun x hx ↦ hr hx) hba.isSelfAdjoint
    -- Measure the interval with the `ℓ²` operator norm, whose topology is the entrywise one.
    open scoped Matrix.Norms.L2Operator in
    let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
    refine Metric.isCompact_of_isClosed_isBounded isClosed_Icc
      ((Metric.isBounded_closedBall (x := a) (r := max r 0)).subset fun x hx ↦ ?_)
    have hy : 0 ≤ x - a := sub_nonneg.2 hx.1
    have hyr : x - a ≤ algebraMap ℝ _ r := (sub_le_sub_right hx.2 a).trans hbar
    rw [Metric.mem_closedBall, dist_eq_norm, ← cfc_id' ℝ (x - a) hy.isSelfAdjoint]
    refine norm_cfc_le (le_max_right _ _) fun t ht ↦ ?_
    have h₁ := (StarOrderedRing.nonneg_iff_spectrum_nonneg _ hy.isSelfAdjoint).1 hy t ht
    have h₂ := (le_algebraMap_iff_spectrum_le (ha := hy.isSelfAdjoint)).1 hyr t ht
    rw [Real.norm_eq_abs, abs_of_nonneg h₁]
    exact h₂.trans (le_max_left _ _)

/-- If `A` is positive definite and `A ≤ B` in the Loewner order, then `B` is positive definite. -/
theorem PosDef.of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (hle : A ≤ B) : B.PosDef := by
  simpa only [add_sub_cancel] using hA.add_posSemidef (le_iff.1 hle)

section L2OpNorm

open scoped Matrix.Norms.L2Operator

/-- A Hermitian matrix with `‖A‖ ≤ L` satisfies `A ≤ L • 1` in the Loewner order. -/
theorem IsHermitian.le_smul_one_of_l2_opNorm_le [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {L : ℝ} (hL : ‖A‖ ≤ L) : A ≤ L • (1 : Matrix n n 𝕜) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  refine le_algebraMap_of_spectrum_le (fun x hx ↦ ?_) hA.isSelfAdjoint
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  exact (le_abs_self _).trans <| le_trans
    (by simpa [hA.l2_opNorm_eq_norm_eigenvalues] using norm_le_pi_norm hA.eigenvalues i) hL

/-- A Hermitian matrix with `‖A‖ ≤ L` satisfies `-(L • 1) ≤ A` in the Loewner order. -/
theorem IsHermitian.neg_smul_one_le_of_l2_opNorm_le [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {L : ℝ} (hL : ‖A‖ ≤ L) : -(L • (1 : Matrix n n 𝕜)) ≤ A :=
  neg_le.1 (hA.neg.le_smul_one_of_l2_opNorm_le (by simpa using hL))

/-- A positive semidefinite matrix is bounded above by `‖A‖ • 1` in the Loewner order. -/
theorem PosSemidef.le_l2_opNorm_smul_one [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : A ≤ ‖A‖ • (1 : Matrix n n 𝕜) :=
  hA.1.le_smul_one_of_l2_opNorm_le le_rfl

/-- A positive semidefinite matrix bounded above by `L • 1` (`0 ≤ L`) has `ℓ²` operator norm at
most `L`. -/
theorem PosSemidef.l2_opNorm_le_of_le_smul_one [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {L : ℝ} (hL : 0 ≤ L) (hU : A ≤ L • (1 : Matrix n n 𝕜)) : ‖A‖ ≤ L := by
  rw [hA.1.l2_opNorm_eq_norm_eigenvalues]
  refine (pi_norm_le_iff_of_nonneg hL).2 fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact (le_algebraMap_iff_spectrum_le (ha := hA.1.isSelfAdjoint)).1
    (by simpa [Algebra.algebraMap_eq_smul_one] using hU) _ (hA.1.eigenvalues_mem_spectrum_real i)

end L2OpNorm

end Matrix

namespace TauCeti

/-- The entrywise complex embedding `TauCeti.mapToComplexStarAlgHom` preserves and reflects the
Loewner order. -/
@[simp]
theorem mapToComplexStarAlgHom_le_iff {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} :
    mapToComplexStarAlgHom A ≤ mapToComplexStarAlgHom B ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← map_sub, posSemidef_mapToComplexStarAlgHom_iff]

end TauCeti
