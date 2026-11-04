/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Sqrt

/-!
# Positive-definite solutions of the Bures–Wasserstein fixed-point equation

Let `C j` be finitely many positive semidefinite matrices and `w j ≥ 0` weights. The fixed-point
equation of Bures–Wasserstein barycenters asks for a positive-definite matrix `S` with

`S = ∑ j, w j • √(√S * C j * √S)`,

where `√` is the continuous-functional-calculus square root `CFC.sqrt`. For weights summing to
`1` and covariance matrices `C j`, its positive-definite solutions are the covariances of the
quadratic Wasserstein barycenters of the centred Gaussian laws of covariances `C j`, and the
equation is equivalent to the standard positive matrices `geometricMean S⁻¹ʳ (C j)` averaging to
the identity (`Matrix.PosDef.sum_smul_geometricMean_ringInverse_eq_one_iff`).

This file proves that a positive-definite solution exists as soon as one matrix `C j₀` with a
positive weight is positive definite (`Matrix.exists_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt`).
The weights need not sum to `1`, and the other matrices may be singular.

The solution is a fixed point of the *Bures map* `F S = ∑ j, w j • √(√S * C j * √S)` on an
order interval `α • 1 ≤ S ≤ β • 1`, which is compact (`Matrix.instCompactIccSpace`) and convex,
so Brouwer's fixed-point theorem applies once `F` maps the interval into itself. If
`C j ≤ c j • 1`, then `√S * C j * √S ≤ c j • S ≤ (c j * β) • 1`, so
`F S ≤ (∑ j, w j * √(c j)) * √β • 1`, which is at most `β • 1` for `β` large. If
`κ • 1 ≤ C j₀` with `κ > 0`, then `√S * C j₀ * √S ≥ κ • S ≥ (κ * α) • 1`, so
`F S ≥ w j₀ * √(κ * α) • 1`, which is `α • 1` for `α = w j₀ ^ 2 * κ`. The square roots of these
scalar bounds are `CFC.sqrt_le_algebraMap` and `CFC.algebraMap_le_sqrt`, and the solution is
positive definite because `α > 0`.

## Main statements

* `Matrix.exists_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt`: the fixed-point equation has a
  positive-definite solution when some positively weighted `C j₀` is positive definite.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904–924, Theorem 6.1, for the existence of a positive-definite solution by Brouwer's
  fixed-point theorem on an order interval.
* P. C. Álvarez-Esteban, E. del Barrio, J. A. Cuesta-Albertos and C. Matrán, *A fixed-point
  approach to barycenters in Wasserstein space*, J. Math. Anal. Appl. 441 (2016), 744–762, for
  the fixed-point equation of Gaussian barycenters.
-/

public section

open scoped NNReal MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] {J : Type*} [Fintype J]
  {w : J → ℝ≥0} {C : J → Matrix n n 𝕜} {S : Matrix n n 𝕜}

open scoped Classical in
/-- **The upper bound.** If `C j ≤ c j • 1` and `0 ≤ S ≤ β • 1`, then the Bures map at `S` is at
most `(∑ j, w j * √(c j)) * √β`. -/
private theorem sum_smul_sqrt_le {c : J → ℝ} (hc : ∀ j, 0 ≤ c j)
    (hCc : ∀ j, C j ≤ algebraMap ℝ _ (c j)) {β : ℝ} (hS : 0 ≤ S) (hSβ : S ≤ algebraMap ℝ _ β) :
    ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) ≤
      algebraMap ℝ _ ((∑ j, (w j : ℝ) * √(c j)) * √β) := by
  have key (j : J) :
      CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) ≤ algebraMap ℝ _ (√(c j) * √β) := by
    rw [← Real.sqrt_mul (hc j)]
    refine CFC.sqrt_le_algebraMap ?_
    -- Conjugating `C j ≤ c j` by `√S` gives `√S * C j * √S ≤ c j • S`.
    have h := star_left_conjugate_le_conjugate (hCc j) (CFC.sqrt S)
    rw [(CFC.sqrt_nonneg S).isSelfAdjoint.star_eq, ← Algebra.commutes,
      mul_assoc (algebraMap ℝ _ (c j)), CFC.sqrt_mul_sqrt_self S hS, ← Algebra.smul_def] at h
    rw [map_mul, ← Algebra.smul_def]
    exact h.trans (smul_le_smul_of_nonneg_left hSβ (hc j))
  calc ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)
      ≤ ∑ j, (w j : ℝ) • algebraMap ℝ (Matrix n n 𝕜) (√(c j) * √β) :=
        Finset.sum_le_sum fun j _ ↦ smul_le_smul_of_nonneg_left (key j) (w j).coe_nonneg
    _ = _ := by simp [Finset.sum_mul, Algebra.smul_def, mul_assoc]

open scoped Classical in
/-- **The lower bound.** If `κ • 1 ≤ C j₀` with `κ ≥ 0` and `α • 1 ≤ S`, then the Bures map at
`S` is at least `w j₀ * √(κ * α)`. -/
private theorem algebraMap_le_sum_smul_sqrt (j₀ : J) {κ α : ℝ} (hκ : 0 ≤ κ)
    (hCκ : algebraMap ℝ _ κ ≤ C j₀) (hS : 0 ≤ S) (hSα : algebraMap ℝ _ α ≤ S) :
    algebraMap ℝ _ ((w j₀ : ℝ) * √(κ * α)) ≤
      ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) := by
  have hj₀ : algebraMap ℝ (Matrix n n 𝕜) √(κ * α) ≤
      CFC.sqrt (CFC.sqrt S * C j₀ * CFC.sqrt S) := by
    refine CFC.algebraMap_le_sqrt ?_
    -- Conjugating `κ ≤ C j₀` by `√S` gives `κ • S ≤ √S * C j₀ * √S`.
    have h := star_left_conjugate_le_conjugate hCκ (CFC.sqrt S)
    rw [(CFC.sqrt_nonneg S).isSelfAdjoint.star_eq, ← Algebra.commutes,
      mul_assoc (algebraMap ℝ _ κ), CFC.sqrt_mul_sqrt_self S hS, ← Algebra.smul_def] at h
    rw [map_mul, ← Algebra.smul_def]
    exact (smul_le_smul_of_nonneg_left hSα hκ).trans h
  calc algebraMap ℝ (Matrix n n 𝕜) ((w j₀ : ℝ) * √(κ * α))
      = (w j₀ : ℝ) • algebraMap ℝ (Matrix n n 𝕜) √(κ * α) := by
        rw [map_mul, Algebra.smul_def]
    _ ≤ (w j₀ : ℝ) • CFC.sqrt (CFC.sqrt S * C j₀ * CFC.sqrt S) :=
        smul_le_smul_of_nonneg_left hj₀ (w j₀).coe_nonneg
    _ ≤ _ := Finset.single_le_sum
        (f := fun j ↦ (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S))
        (fun j _ ↦ smul_nonneg (w j).coe_nonneg (CFC.sqrt_nonneg _)) (Finset.mem_univ j₀)

open scoped Classical in
/-- The Bures map is continuous on the cone of positive semidefinite matrices. -/
private theorem continuousOn_sum_smul_sqrt (hC : ∀ j, (C j).PosSemidef) :
    ContinuousOn (fun S ↦ ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S))
      {S | 0 ≤ S} := by
  have hsqrt : ContinuousOn (CFC.sqrt : Matrix n n 𝕜 → Matrix n n 𝕜) {S | 0 ≤ S} := by
    -- Mathlib's continuity of the square root is stated for the `ℓ²` operator norm, whose
    -- topology is the entrywise one.
    open scoped Matrix.Norms.L2Operator in
    let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
    exact CFC.continuousOn_sqrt
  refine continuousOn_finsetSum _ fun j _ ↦ (continuous_const_smul _).comp_continuousOn ?_
  exact hsqrt.comp ((hsqrt.mul continuousOn_const).mul hsqrt) fun S _ ↦
    conjugate_nonneg_of_nonneg (hC j).nonneg (CFC.sqrt_nonneg S)

open scoped Classical ContinuousFunctionalCalculus in
/-- **Existence of a positive-definite solution of the Bures–Wasserstein fixed-point equation.**
Let `C j` be positive semidefinite matrices and `w j ≥ 0` weights. If some `C j₀` with `w j₀ ≠ 0`
is positive definite, then there is a positive-definite matrix `S` with
`S = ∑ j, w j • √(√S * C j * √S)`. -/
theorem exists_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt (w : J → ℝ≥0)
    (hC : ∀ j, (C j).PosSemidef) {j₀ : J} (hj₀ : w j₀ ≠ 0) (hCj₀ : (C j₀).PosDef) :
    ∃ S : Matrix n n 𝕜, S.PosDef ∧
      S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, PosDef.one, Subsingleton.elim _ _⟩
  -- A scalar lower bound `κ > 0` for `C j₀`, and scalar upper bounds `c j ≥ 0` for the `C j`.
  obtain ⟨κ, hκ, hCκ⟩ := (CFC.exists_pos_algebraMap_le_iff (C j₀)
    hCj₀.isHermitian.isSelfAdjoint).2 fun x hx ↦ hCj₀.isStrictlyPositive.spectrum_pos hx
  have hup (j : J) : ∃ c, 0 ≤ c ∧ C j ≤ algebraMap ℝ _ c := by
    obtain ⟨c, hc⟩ := (isCompact_iff_compactSpace.mpr inferInstance :
      IsCompact (spectrum ℝ (C j))).bddAbove
    exact ⟨max c 0, le_max_right _ _, le_algebraMap_of_spectrum_le
      (fun x hx ↦ (hc hx).trans (le_max_left _ _)) (hC j).isHermitian.isSelfAdjoint⟩
  choose c hc hCc using hup
  -- The order interval `[α, β]` that the Bures map sends into itself.
  set α : ℝ := (w j₀ : ℝ) ^ 2 * κ with hαdef
  set σ : ℝ := ∑ j, (w j : ℝ) * √(c j)
  set β : ℝ := max (σ ^ 2) α
  have hα : 0 < α := by positivity
  have hαβ : α ≤ β := le_max_right _ _
  have hσ : σ ≤ √β := Real.le_sqrt_of_sq_le (le_max_left _ _)
  have hmono {a b : ℝ} (h : a ≤ b) : algebraMap ℝ (Matrix n n 𝕜) a ≤ algebraMap ℝ _ b := by
    rw [← sub_nonneg, ← map_sub]
    exact algebraMap_nonneg _ (sub_nonneg.2 h)
  set K := Set.Icc (algebraMap ℝ (Matrix n n 𝕜) α) (algebraMap ℝ _ β)
  have hK0 {S : Matrix n n 𝕜} (hS : S ∈ K) : 0 ≤ S :=
    (algebraMap_nonneg _ hα.le).trans hS.1
  have hmaps : Set.MapsTo
      (fun S ↦ ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)) K K := by
    refine fun S hS ↦ ⟨le_trans (hmono (le_of_eq ?_))
      (algebraMap_le_sum_smul_sqrt j₀ hκ.le hCκ (hK0 hS) hS.1),
      (sum_smul_sqrt_le hc hCc (hK0 hS) hS.2).trans (hmono ?_)⟩
    · rw [show κ * α = ((w j₀ : ℝ) * κ) ^ 2 by ring, Real.sqrt_sq (by positivity), hαdef]
      ring
    · calc σ * √β ≤ √β * √β := by gcongr
        _ = β := Real.mul_self_sqrt (hα.le.trans hαβ)
  -- Brouwer's fixed-point theorem on the compact convex interval `K`, measured with the `ℓ²`
  -- operator norm.
  obtain ⟨S, hSK, hSF⟩ : ∃ S ∈ K, Function.IsFixedPt
      (fun S ↦ ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)) S := by
    open scoped Matrix.Norms.L2Operator in
    let := Matrix.l2OpNormedAlgebraReal (n := n) (𝕜 := 𝕜)
    exact TauCeti.brouwerFixedPoint_compactConvex_continuousOn isCompact_Icc (convex_Icc _ _)
      ⟨_, Set.left_mem_Icc.2 (hmono hαβ)⟩ ((continuousOn_sum_smul_sqrt hC).mono fun S ↦ hK0)
      hmaps
  refine ⟨S, isStrictlyPositive_iff_posDef.1 ?_, hSF.symm⟩
  have hSa := (hK0 hSK).isSelfAdjoint
  exact (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos S hSa).2 fun x hx ↦
    hα.trans_le ((algebraMap_le_iff_le_spectrum (ha := hSa)).1 hSK.1 x hx)

end Matrix
