/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Topology.Semicontinuity.Michael
import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone

/-!
# The Bartle–Graves continuous selection theorem

A surjective continuous linear map `q : E →L[ℝ] F` between Banach spaces need not admit a
continuous *linear* right inverse — for instance, the quotient map `ℓ^∞ → ℓ^∞ / c₀` has none
because `c₀` is uncomplemented in `ℓ^∞`. The Banach open mapping theorem
(`ContinuousLinearMap.exists_nonlinearRightInverse_of_surjective`) produces a norm-bounded right
inverse `s : q.NonlinearRightInverse`, without guaranteeing continuity.

This file proves the **Bartle–Graves theorem**: every surjective continuous linear map between
real (or `RCLike`) Banach spaces admits a *continuous*, positively `ℝ`-homogeneous
`ContinuousLinearMap.NonlinearRightInverse`, with linear norm bound arbitrarily close to the
open-mapping constant. Via Michael's selection theorem
(`LowerHemicontinuous.exists_continuous_selection`), one restricts the bounded-fibre correspondence
`y ↦ q ⁻¹' {y} ∩ closedBall 0 R` (`R > C`) to the unit sphere `Metric.sphere (0 : F) 1`, proves
lower hemicontinuity by shrinking any fibre point slightly toward a `C`-bounded preimage and
correcting the residual error on nearby fibres, selects a continuous section `σ` on the unit
sphere, and extends radially via `TauCeti.sphereCone` (`s(y) = ‖y‖ • σ(‖y‖⁻¹ • y)`, `s(0) = 0`).

## Main results

* `ContinuousLinearMap.lowerHemicontinuous_sphere_preimage_inter_closedBall`: for `R > C` above a
  linear preimage bound `C > 0` of `q : E →L[ℝ] F`, the truncated fibre correspondence
  `y ↦ q ⁻¹' {y} ∩ closedBall 0 R` on `Metric.sphere (0 : F) 1` is lower hemicontinuous.
* `ContinuousLinearMap.exists_continuous_positivelyHomogeneous_nonlinearRightInverse_of_bound`: from
  a linear preimage bound `C > 0` and any `R > C` (requiring completeness only of the domain `E`),
  constructs a continuous, positively homogeneous `s : q.NonlinearRightInverse` with
  `(s.nnNorm : ℝ) = R`.
* `ContinuousLinearMap.exists_continuous_positivelyHomogeneous_nonlinearRightInverse_of_surjective`:
  the Bartle–Graves theorem for surjective `q : E →L[𝕜] F` between `[RCLike 𝕜]` Banach spaces
  (covering `ℝ` and `ℂ`), producing a continuous positively `ℝ`-homogeneous
  `q.NonlinearRightInverse`.

## References

* Robert G. Bartle and Lawrence M. Graves, *Mappings between function spaces*, Trans. Amer. Math.
  Soc. **72** (1952), 400–413, Theorem 4.
* Ernest Michael, *Continuous selections. I*, Ann. of Math. (2) **63** (1956), 361–382,
  Proposition 7.2.
* Yoav Benyamini and Joram Lindenstrauss, *Geometric Nonlinear Functional Analysis*, Vol. 1,
  Amer. Math. Soc. Colloquium Publications **48**, 2000, Proposition 1.19.
-/

public section

open Function Metric Set Topology
open scoped NNReal

namespace ContinuousLinearMap

section RealBanach

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `q : E →L[ℝ] F` admits preimages of norm at most `C * ‖y‖` (`C > 0`) and `R > C`, then on
the unit sphere of `F` the correspondence `y ↦ q ⁻¹' {y} ∩ closedBall 0 R` is lower
hemicontinuous. -/
theorem lowerHemicontinuous_sphere_preimage_inter_closedBall (q : E →L[ℝ] F) {C R : ℝ}
    (hC : 0 < C) (hCR : C < R) (hpre : ∀ y : F, ∃ x : E, q x = y ∧ ‖x‖ ≤ C * ‖y‖) :
    LowerHemicontinuous
      (fun y : sphere (0 : F) 1 ↦ q ⁻¹' {(y : F)} ∩ closedBall (0 : E) R) := by
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
  intro U hU
  rw [Metric.isOpen_iff]
  rintro y₀ ⟨x₀, ⟨hqx₀, hx₀R⟩, hx₀U⟩
  obtain ⟨ε, hε, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀U
  obtain ⟨x₁, hqx₁, hx₁C⟩ := hpre y₀
  rw [norm_eq_of_mem_sphere y₀, mul_one] at hx₁C
  let t : ℝ := min (1 / 2) ((ε / 4) / (‖x₁ - x₀‖ + 1))
  have ht_pos : 0 < t := lt_min (by positivity) (by positivity)
  have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ((min_le_left _ _).trans (by norm_num))
  let x₂ : E := (1 - t) • x₀ + t • x₁
  have hqx₂ : q x₂ = y₀ := by
    simp only [x₂, map_add, map_smul, mem_singleton_iff.mp hqx₀, hqx₁,
      ← add_smul, sub_add_cancel, one_smul]
  have hx₂_dist : ‖x₂ - x₀‖ < ε / 2 := by
    have hsub : x₂ - x₀ = t • (x₁ - x₀) := by simp only [x₂, sub_smul, one_smul, smul_sub]; abel
    have hlt : (ε / 4) / (‖x₁ - x₀‖ + 1) * ‖x₁ - x₀‖ < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (x₁ - x₀)]
    rw [hsub, norm_smul, Real.norm_of_nonneg ht_pos.le]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans_lt hlt
  have hx₂_norm : ‖x₂‖ < R := by
    have hx₀_norm : ‖x₀‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hx₀R
    calc ‖x₂‖ ≤ ‖(1 - t) • x₀‖ + ‖t • x₁‖ := norm_add_le _ _
      _ = (1 - t) * ‖x₀‖ + t * ‖x₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht_nonneg, Real.norm_of_nonneg ht_pos.le]
      _ ≤ (1 - t) * R + t * C := by gcongr
      _ = R - t * (R - C) := by ring
      _ < R := sub_lt_self R (mul_pos ht_pos (sub_pos.mpr hCR))
  let δ : ℝ := min (ε / 2) (R - ‖x₂‖)
  have hδ : 0 < δ := lt_min (half_pos hε) (sub_pos.mpr hx₂_norm)
  refine ⟨δ / C, div_pos hδ hC, fun y hy ↦ ?_⟩
  obtain ⟨z, hqz, hz_norm⟩ := hpre ((y : F) - y₀)
  have hz_lt : ‖z‖ < δ := hz_norm.trans_lt
    ((lt_div_iff₀' hC).mp (by simpa [Subtype.dist_eq, dist_eq_norm] using hy))
  refine ⟨x₂ + z, ⟨by simp [hqx₂, hqz], ?_⟩, hballU ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    linarith [norm_add_le x₂ z, min_le_right (ε / 2) (R - ‖x₂‖)]
  · have hsub : x₂ + z - x₀ = (x₂ - x₀) + z := by abel
    rw [mem_ball, dist_eq_norm, hsub]
    linarith [norm_add_le (x₂ - x₀) z, min_le_left (ε / 2) (R - ‖x₂‖)]

/-- **Bartle–Graves theorem with explicit norm bound.** If `E` is a real Banach space and
`q : E →L[ℝ] F` admits preimages of norm at most `C * ‖y‖` (`C > 0`), then for every `R > C` there
exists a continuous, positively homogeneous `s : q.NonlinearRightInverse` with `(s.nnNorm : ℝ) = R`.
Completeness of `F` is not needed once the linear preimage bound `C` is given. -/
theorem exists_continuous_positivelyHomogeneous_nonlinearRightInverse_of_bound [CompleteSpace E]
    (q : E →L[ℝ] F) {C R : ℝ} (hC : 0 < C) (hCR : C < R)
    (hpre : ∀ y : F, ∃ x : E, q x = y ∧ ‖x‖ ≤ C * ‖y‖) :
    ∃ s : q.NonlinearRightInverse,
      (s.nnNorm : ℝ) = R ∧ Continuous s ∧ ∀ ⦃c : ℝ⦄, 0 ≤ c → ∀ y, s (c • y) = c • s y := by
  have hR : 0 < R := hC.trans hCR
  let Φ : sphere (0 : F) 1 → Set E := fun y ↦ q ⁻¹' {(y : F)} ∩ closedBall (0 : E) R
  have hΦ_ne : ∀ y : sphere (0 : F) 1, (Φ y).Nonempty := fun y ↦ by
    obtain ⟨x, hqx, hxC⟩ := hpre y
    rw [norm_eq_of_mem_sphere y, mul_one] at hxC
    exact ⟨x, hqx, by simpa [mem_closedBall, dist_zero_right] using hxC.trans hCR.le⟩
  obtain ⟨σ, hσ_cont, hσ_mem⟩ :=
    (q.lowerHemicontinuous_sphere_preimage_inter_closedBall hC hCR hpre).exists_continuous_selection
      hΦ_ne
      (fun y ↦ ((convex_singleton (y : F)).linear_preimage q.toLinearMap).inter
        (convex_closedBall 0 R))
      (fun _ ↦ (isClosed_singleton.preimage q.continuous).inter isClosed_closedBall)
  have hσ_bound : ∀ u : sphere (0 : F) 1, ‖σ u‖ ≤ R := fun u ↦ by
    simpa [mem_closedBall, dist_zero_right] using (hσ_mem u).2
  refine ⟨{
    toFun := TauCeti.sphereCone σ
    nnNorm := ⟨R, hR.le⟩
    bound' := TauCeti.norm_sphereCone_le hσ_bound
    right_inv' := fun y ↦ by
      rcases TauCeti.eq_zero_or_exists_eq_smul_coe_sphere y with rfl | ⟨r, hr, u, rfl⟩
      · simp
      · rw [TauCeti.sphereCone_smul_coe hr.le, map_smul, (hσ_mem u).1] },
    rfl, TauCeti.continuous_sphereCone hσ_cont hσ_bound,
    fun {_} hc y ↦ TauCeti.sphereCone_smul hc y⟩

end RealBanach

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **The Bartle–Graves continuous selection theorem (`RCLike` Banach spaces).** Every surjective
continuous `𝕜`-linear map `q : E →L[𝕜] F` between Banach spaces over `𝕜` (`ℝ` or `ℂ`) admits a
continuous, positively `ℝ`-homogeneous `NonlinearRightInverse` with positive norm bound. -/
theorem exists_continuous_positivelyHomogeneous_nonlinearRightInverse_of_surjective
    (q : E →L[𝕜] F) (hq : Surjective q) :
    ∃ s : q.NonlinearRightInverse,
      0 < s.nnNorm ∧ Continuous s ∧
        ∀ ⦃c : ℝ⦄, 0 ≤ c → ∀ y, s (algebraMap ℝ 𝕜 c • y) = algebraMap ℝ 𝕜 c • s y := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have _ : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let _ : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  have _ : IsScalarTower ℝ 𝕜 F := IsScalarTower.restrictScalars ℝ 𝕜 F
  obtain ⟨C, hC, hpre⟩ := (q.restrictScalars ℝ).exists_preimage_norm_le hq
  obtain ⟨s, hsR, hs_cont, hs_hom⟩ :=
    (q.restrictScalars ℝ).exists_continuous_positivelyHomogeneous_nonlinearRightInverse_of_bound
      hC (lt_add_one C) hpre
  exact ⟨{ toFun := s, nnNorm := s.nnNorm, bound' := s.bound, right_inv' := s.right_inv },
    NNReal.coe_pos.mp (hsR.symm ▸ by linarith), hs_cont,
    fun {_} hc y ↦ by simpa only [algebraMap_smul] using hs_hom hc y⟩

end RCLike

end ContinuousLinearMap
