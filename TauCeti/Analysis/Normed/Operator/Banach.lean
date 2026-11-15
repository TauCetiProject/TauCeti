/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Exact preimages from approximate preimages

Banach's open mapping theorem is proved in two steps. Baire's theorem first shows that every
point of the target is approximately the image of a point of controlled norm; a geometric
series then upgrades these approximate preimages to exact ones, using completeness of the
domain. Mathlib only states the composite theorem
`ContinuousLinearMap.exists_preimage_norm_le`, whose hypothesis is surjectivity.

This file isolates the second step, so that other sources of approximate preimages can be fed
into it. The main application is the case where the closure of the image of every ball contains a
ball, as happens when the adjoint is bounded below; this is how surjectivity is recovered in the
closed-range theorem. The scalar actions need no compatibility with the norms; only additivity
and continuity of the map enter the argument.

The file also records the form of the open mapping theorem used to invert operators pointwise:
a bijective continuous linear map between Banach spaces is invertible.

## Main declarations

* `ContinuousLinearMap.exists_preimage_norm_le_of_approx`: approximate preimages of norm at most
  `C * ‖y‖` with relative error `r < 1` give exact preimages of norm at most `C / (1 - r) * ‖y‖`.
* `ContinuousLinearMap.exists_preimage_norm_le_of_mem_closure`: if every `y` lies in the closure of
  the image of the closed ball of radius `C * ‖y‖`, then for every `C' > C`, every `y` has a
  preimage of norm at most `C' * ‖y‖`.
* `ContinuousLinearMap.isInvertible_iff_bijective`: by the open mapping theorem, a continuous
  linear map between Banach spaces is invertible exactly when it is bijective.
* `ContinuousLinearMap.spectrum_restrictScalars`: realification preserves the spectrum of an
  operator on a Banach space.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Lemma 4.13.

The series argument follows the second half of the proof of Mathlib's
`ContinuousLinearMap.exists_preimage_norm_le`.
-/

public section

open Function Metric Set Filter Finset Topology

namespace ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [Semiring 𝕜] [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [Module 𝕜' F]

/-- **Approximate preimages give exact preimages.** Let `r < 1`. If every `y` is within
`r * ‖y‖` of the image of a point of norm at most `C * ‖y‖`, then every `y` is the image of a point
of norm at most `C / (1 - r) * ‖y‖`. -/
theorem exists_preimage_norm_le_of_approx (f : E →SL[σ] F) {r C : ℝ} (hr : r < 1)
    (hC : ∀ y, ∃ x, dist (f x) y ≤ r * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ C / (1 - r) * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  -- The approximate preimage of `y` shows that both constants are nonnegative.
  obtain ⟨x₀, hx₀y, hx₀⟩ := hC y
  have hr0 : 0 ≤ r := nonneg_of_mul_nonneg_left (dist_nonneg.trans hx₀y) (norm_pos_iff.2 hy)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hx₀) (norm_pos_iff.2 hy)
  /- Let `g y` be the approximate preimage of `y`, and `h y = y - f (g y)` the part of `y` that
  is not yet hit. Iterating, `u n = g (h^[n] y)` is a summable series whose sum is a preimage
  of `y`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ r * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ r ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ r ^ n * (C * ‖y‖) := fun n ↦
    calc
      ‖u n‖ ≤ C * ‖h^[n] y‖ := (hg _).2
      _ ≤ C * (r ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = r ^ n * (C * ‖y‖) := by ring
  have hgeom := (summable_geometric_of_lt_one hr0 hr).mul_right (C * ‖y‖)
  have sNu : Summable fun n ↦ ‖u n‖ := .of_nonneg_of_le (fun n ↦ norm_nonneg _) ule hgeom
  let x := tsum u
  have x_ineq : ‖x‖ ≤ C / (1 - r) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, r ^ n * (C * ‖y‖) := sNu.tsum_le_tsum ule hgeom
      _ = (∑' n, r ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = C / (1 - r) * ‖y‖ := by rw [tsum_geometric_of_lt_one hr0 hr]; ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [sum_range_succ, map_add, IH, iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n ↦ f (∑ i ∈ range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp sNu.of_norm.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n ↦ h^[n] y) atTop (𝓝 0) :=
    squeeze_zero_norm hnle <| by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const ‖y‖
  exact ⟨x, by simpa using tendsto_nhds_unique L₁ (tendsto_const_nhds.sub L₂), x_ineq⟩

/-- **Banach's lemma.** If every `y` lies in the closure of the image of the closed ball of radius
`C * ‖y‖`, then for every `C' > C`, every `y` has a preimage of norm at most `C' * ‖y‖`. In
particular, the map is surjective. -/
theorem exists_preimage_norm_le_of_mem_closure (f : E →SL[σ] F) {C : ℝ}
    (hC : ∀ y, y ∈ closure (f '' closedBall 0 (C * ‖y‖))) {C' : ℝ} (hC' : C < C') (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ C' * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  -- The closure around `y` is nonempty, so `C` is nonnegative.
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left
    (nonempty_closedBall.1 (closure_nonempty_iff.1 ⟨y, hC y⟩).of_image) (norm_pos_iff.2 hy)
  /- For `C < C₁ < C'`, approximate preimages of norm at most `C₁ * ‖z‖` can be found with
  relative error `r = 1 - C₁ / C'`, and then `C₁ / (1 - r) = C'`. -/
  obtain ⟨C₁, hCC₁, hC₁C'⟩ := exists_between hC'
  have hC₁ : 0 < C₁ := hC0.trans_lt hCC₁
  have hr : 0 < 1 - C₁ / C' := sub_pos.2 <| (div_lt_one (hC₁.trans hC₁C')).2 hC₁C'
  have happrox (z : F) : ∃ x, dist (f x) z ≤ (1 - C₁ / C') * ‖z‖ ∧ ‖x‖ ≤ C₁ * ‖z‖ := by
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨0, by simp, by simp⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hxz⟩ :=
      Metric.mem_closure_iff.mp (hC z) ((1 - C₁ / C') * ‖z‖) (mul_pos hr (norm_pos_iff.2 hz))
    refine ⟨x, by rw [dist_comm]; exact hxz.le, ?_⟩
    calc ‖x‖ ≤ C * ‖z‖ := by simpa using hx
      _ ≤ C₁ * ‖z‖ := by gcongr
  obtain ⟨x, hxy, hx⟩ :=
    f.exists_preimage_norm_le_of_approx (sub_lt_self 1 (div_pos hC₁ (hC₁.trans hC₁C'))) happrox y
  rw [sub_sub_cancel, div_div_cancel₀ hC₁.ne'] at hx
  exact ⟨x, hxy, hx⟩

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- By the open mapping theorem, a continuous linear map between Banach spaces is invertible, that
is, a continuous linear equivalence, exactly when it is bijective. -/
theorem isInvertible_iff_bijective {f : E →L[𝕜] F} : f.IsInvertible ↔ Bijective f :=
  ⟨IsInvertible.bijective, fun h ↦ ⟨.ofBijective f (LinearMap.ker_eq_bot.2 h.1)
    (LinearMap.range_eq_top.2 h.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩⟩

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Realification preserves the spectrum** of a bounded operator on a Banach space over a normed
`ℝ`-algebra `𝕜`, for any real algebra structure on the operators compatible with the `𝕜`-action:
by Banach's inverse mapping theorem an operator is invertible exactly when it is bijective, and the
realification has the same underlying function. -/
theorem spectrum_restrictScalars (T : E →L[𝕜] E) :
    spectrum ℝ (T.restrictScalars ℝ) = spectrum ℝ T := by
  have h (r : ℝ) : ⇑(algebraMap ℝ (E →L[ℝ] E) r - T.restrictScalars ℝ) =
      ⇑(algebraMap ℝ (E →L[𝕜] E) r - T) := by
    ext x
    simp [IsScalarTower.algebraMap_apply ℝ 𝕜 (E →L[𝕜] E), Algebra.algebraMap_eq_smul_one]
  ext r
  simp only [spectrum.mem_iff, isUnit_iff_bijective, h]

end ContinuousLinearMap
