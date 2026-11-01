/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Basic
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# Spatial Hölder estimates for the Hessian of the Duhamel potential

For bounded measurable forcing whose spatial slices are uniformly `α`-Hölder, `0 < α < 1`,
the spatial Hessian of the Duhamel heat potential is `α`-Hölder with a constant independent of
time. This is the spatial top-order estimate in the parabolic Schauder estimate. It does not
assert Hölder regularity in time or the inhomogeneous heat equation.

Cancellation of the differentiated heat kernel gives bounds of orders `r^(α/2-1)` and
`r^((α-3)/2)` for the second and third derivatives of a heat convolution. For two spatial points
at distance `d`, integrate the second-derivative bound over `0 < r < d²`, and the mean-value
bound from the third derivative over `r > d²`. Both contributions have size `O(d^α)`.
The proof uses the weighted kernel moments and differentiation under the integral already
provided by the heat-kernel API.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Real
open scoped Convolution NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {α : ℝ≥0}

/-- The cancellation bounds for the two derivatives used in the spatial Hessian estimate. -/
private theorem exists_hessian_bounds :
    ∃ C₂ > 0, ∃ C₃ > 0, ∀ {r : ℝ} {g : E → F} {M : ℝ} {H : ℝ≥0}, 0 < r →
      AEStronglyMeasurable g → (∀ᵐ y, ‖g y‖ ≤ M) → HolderWith H α g →
      (∀ x, ‖iteratedFDeriv ℝ 2 (heatKernel r ⋆ g) x‖ ≤
        C₂ * H * r ^ ((α : ℝ) / 2 - 1)) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (heatKernel r ⋆ g) x -
          iteratedFDeriv ℝ 2 (heatKernel r ⋆ g) y‖ ≤
        C₃ * H * ‖x - y‖ * r ^ (((α : ℝ) - 3) / 2)) := by
  obtain ⟨C₂, hC₂, hb₂⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) 2 α.coe_nonneg
  obtain ⟨C₃, hC₃, hb₃⟩ :=
    exists_integral_norm_iteratedFDeriv_heatKernel_mul_rpow_le (E := E) 3 α.coe_nonneg
  refine ⟨C₂, hC₂, C₃, hC₃, fun {r g M H} hr hg hM hH => ⟨?_, ?_⟩⟩
  · intro x
    have h := (norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith hr hg hM hH
      two_ne_zero x).trans (mul_le_mul_of_nonneg_left (hb₂ r hr) H.coe_nonneg)
    have hexp : ((α : ℝ) - 2) / 2 = α / 2 - 1 := by ring
    simpa only [Nat.cast_ofNat, hexp, mul_assoc, mul_comm, mul_left_comm] using h
  · intro x y
    have hderiv (z : E) :
        ‖fderiv ℝ (iteratedFDeriv ℝ 2 (heatKernel r ⋆ g)) z‖ ≤
          C₃ * H * r ^ (((α : ℝ) - 3) / 2) := by
      rw [norm_fderiv_iteratedFDeriv]
      have h := (norm_iteratedFDeriv_heatKernel_convolution_le_of_holderWith hr hg hM hH
        (by norm_num : 3 ≠ 0) z).trans (mul_le_mul_of_nonneg_left (hb₃ r hr) H.coe_nonneg)
      simpa only [Nat.reduceAdd, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using h
    have hdiff := (contDiff_heatKernel_convolution hr hg hM).differentiable_iteratedFDeriv
      (by exact_mod_cast (WithTop.coe_lt_top 2 : (2 : ℕ∞) < ⊤))
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hdiff z) (fun z _ => hderiv z) (mem_univ y) (mem_univ x)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The integrability and formula for the Hessian, using elapsed time `r = t - s`. -/
private theorem hessian_integral {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hM : ∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M)
    (hH : ∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s))
    (hα : 0 < α) (ht : 0 < t) (x : E) :
    IntervalIntegrable (fun r => iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) x)
      volume 0 t ∧
    iteratedFDeriv ℝ 2 (heatDuhamelPotential f t) x =
      ∫ r in 0..t, iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) x := by
  have hi := intervalIntegrable_iteratedFDeriv_heatKernel_convolution_of_holderWith
    hf hM hH hα ht (le_refl 2) x
  have he := congrFun
    (iteratedFDeriv_heatDuhamelPotential_of_holderWith hf hM hH hα ht (le_refl 2)) x
  constructor
  · simpa using (hi.comp_sub_left t).symm
  · rw [he]
    simpa using (intervalIntegral.integral_comp_sub_left
      (a := 0) (b := t) (fun r => iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) x) t)

/-- **Spatial Schauder estimate for the Duhamel potential.** If `0 < α < 1`, there is a positive
constant `C`, depending only on the dimension and `α`, such that the Hessian is `α`-Hölder
with constant `C H` whenever the spatial forcing slices are `α`-Hölder with constant `H`.
Neither the upper time `t` nor the essential bound `M` enters this estimate. -/
theorem exists_holderWith_iteratedFDeriv_two_heatDuhamelPotential
    (hα : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {f : ℝ → E → F} {M t : ℝ} {H : ℝ≥0},
      StronglyMeasurable (Function.uncurry f) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), ∀ᵐ y, ‖f s y‖ ≤ M) →
      (∀ᵐ s ∂volume.restrict (Ioo 0 t), HolderWith H α (f s)) → 0 < t →
      HolderWith (C * H) α (iteratedFDeriv ℝ 2 (heatDuhamelPotential f t)) := by
  obtain ⟨C₂, hC₂, C₃, hC₃, hb⟩ := exists_hessian_bounds (E := E) (F := F) (α := α)
  have ha : (0 : ℝ) < α := hα
  have ha₁ : (α : ℝ) < 1 := hα₁
  let C : ℝ := 4 * C₂ / α + 2 * C₃ / (1 - α)
  have hC : 0 < C := by dsimp [C]; positivity
  let K : ℝ≥0 := ⟨C, hC.le⟩
  have hK : (K : ℝ) = C := rfl
  refine ⟨K, hC, fun {f M t H} hf hM hH ht => ?_⟩
  apply holderOnWith_univ.mp
  apply HolderOnWith.of_dist_le
  intro x _ y _
  simp only [dist_eq_norm, NNReal.coe_mul, hK]
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    positivity
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨hix, hex⟩ := hessian_integral hf hM hH hα ht x
  obtain ⟨hiy, hey⟩ := hessian_integral hf hM hH hα ht y
  -- Reverse the time variable, retaining the almost-everywhere hypotheses on the forcing.
  have hrev : ∀ᵐ r ∂volume.restrict (Ioo 0 t),
      (∀ᵐ z, ‖f (t - r) z‖ ≤ M) ∧ HolderWith H α (f (t - r)) := by
    have h := hM.and hH
    rw [ae_restrict_iff' measurableSet_Ioo] at h ⊢
    filter_upwards [(volume.measurePreserving_sub_left t).quasiMeasurePreserving.ae h]
      with r hr hrI
    exact hr ⟨by linarith [hrI.2], by linarith [hrI.1]⟩
  have hnear : ∀ᵐ r ∂volume.restrict (Ioo 0 t),
      ‖iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) x -
          iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) y‖ ≤
        (2 * C₂ * H) * r ^ ((α : ℝ) / 2 - 1) := by
    filter_upwards [hrev, ae_restrict_mem measurableSet_Ioo] with r hr hrI
    have hg : AEStronglyMeasurable (f (t - r)) volume :=
      (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    obtain ⟨hs, -⟩ := hb hrI.1 hg hr.1 hr.2
    exact (norm_sub_le _ _).trans (by linarith [hs x, hs y])
  have hfar : ∀ᵐ r ∂volume.restrict (Ioo 0 t),
      ‖iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) x -
          iteratedFDeriv ℝ 2 (heatKernel r ⋆ f (t - r)) y‖ ≤
        (C₃ * H * ‖x - y‖) * r ^ (-((1 - (α : ℝ)) / 2) - 1) := by
    filter_upwards [hrev, ae_restrict_mem measurableSet_Ioo] with r hr hrI
    have hg : AEStronglyMeasurable (f (t - r)) volume :=
      (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    have hs := (hb hrI.1 hg hr.1 hr.2).2 x y
    have hexp : -((1 - (α : ℝ)) / 2) - 1 = ((α : ℝ) - 3) / 2 := by ring
    simpa only [hexp] using hs
  -- The integrable power at zero and the mean-value power at infinity meet at distance squared.
  rw [hex, hey, ← intervalIntegral.integral_sub hix hiy]
  have hi := norm_intervalIntegral_le_of_rpow_bounds (by linarith : 0 < (α : ℝ) / 2)
    (by linarith : 0 < (1 - (α : ℝ)) / 2)
    (by positivity : 0 ≤ 2 * C₂ * (H : ℝ))
    (by positivity : 0 ≤ C₃ * (H : ℝ) * ‖x - y‖)
    (sq_pos_of_pos hd) ht.le (hix.sub hiy) hnear hfar
  -- At this scale both integrals are a constant times the same spatial Hölder power.
  refine hi.trans_eq ?_
  rw [← Real.rpow_natCast ‖x - y‖ 2, ← Real.rpow_mul hd.le, ← Real.rpow_mul hd.le]
  norm_num only [Nat.cast_ofNat]
  have hpow : ‖x - y‖ * ‖x - y‖ ^ (-(1 - (α : ℝ))) = ‖x - y‖ ^ (α : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one ‖x - y‖]
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have he₁ : (2 : ℝ) * ((α : ℝ) / 2) = α := by ring
  have he₂ : (2 : ℝ) * (-((1 - (α : ℝ)) / 2)) = -(1 - (α : ℝ)) := by ring
  rw [he₁, he₂]
  calc
    _ = (4 * C₂ / α) * H * ‖x - y‖ ^ (α : ℝ) +
        (2 * C₃ / (1 - α)) * H * (‖x - y‖ * ‖x - y‖ ^ (-(1 - (α : ℝ)))) := by
          field_simp
          ring
    _ = C * H * ‖x - y‖ ^ (α : ℝ) := by rw [hpow]; dsimp [C]; ring

end TauCeti
