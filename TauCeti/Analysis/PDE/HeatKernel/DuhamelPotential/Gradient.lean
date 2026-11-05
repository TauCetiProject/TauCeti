/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.DuhamelPotential.Holder
import TauCeti.Analysis.Holder.Interpolation

/-!
# Regularity of the gradient of the Duhamel potential in space and time

Let `w(t, x) = ∫₀ᵗ (K_{t-s} ⋆ f(s, ·))(x) ds` be the Duhamel heat potential of a jointly
measurable forcing `f` whose slices `f(r, ·)`, `0 ≤ r ≤ T`, are bounded by `M` and `α`-Hölder with
constant `H`, where `α > 0`. This file controls the gradient `D w` on the closed slab
`[0, T] × E`, including the initial time, where every slice `w(t, ·)` is `C²`
(`TauCeti.contDiff_heatDuhamelPotential_of_forall_holderWith`):

* `D w(t, ·)` is Lipschitz with constant `C H T^(α/2)`
  (`TauCeti.exists_lipschitzWith_fderiv_heatDuhamelPotential`);
* for `α < 2`, at each point `x` the gradient `t ↦ D w(t, ·)(x)` is `α/2`-Hölder on `[0, T]`,
  with constant `2 K + C H` (`TauCeti.exists_holderOnWith_fderiv_heatDuhamelPotential`), where
  `K = T H (1 + M_α) + M max(1, T)` is the constant of the parabolic Hölder estimate of `w`
  (`TauCeti.holderWith_heatDuhamelPotential`) and `M_α` is the heat-kernel moment;
* consequently, for `α < 2`, the gradient `(t, x) ↦ D w(t, ·)(x)` is jointly continuous on
  `[0, T] × E` (`TauCeti.continuousOn_fderiv_heatDuhamelPotential`).

The constants `C` depend only on `α` and the dimension. The joint continuity is what the
order-two parabolic Hölder space requires of its bounded continuous gradient field.

## The argument

The Lipschitz bound is the Hessian bound `‖D² w(t, x)‖ ≤ C H t^(α/2)`
(`TauCeti.exists_norm_iteratedFDeriv_two_heatDuhamelPotential_le`). For the temporal estimate,
fix `t, s ∈ [0, T]` and put `g = w(t, ·) - w(s, ·)`. The parabolic Hölder estimate of `w` bounds
`‖g‖_∞ ≤ K |t - s|^(α/2)`, since points with the same spatial coordinate are at parabolic
distance `√|t - s|`. The temporal Hölder estimate of the Hessian
(`TauCeti.exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential`) bounds
`‖D² g‖_∞ ≤ C H |t - s|^(α/2)`, so `D g` is Lipschitz with that constant. The Landau-type
inequality `‖D g(x)‖ ≤ 2 ‖g‖_∞ + Lip(D g)` (`HolderWith.norm_le_of_hasFDerivAt` at scale one)
then gives the estimate. A field that is Lipschitz in space uniformly in time and continuous in
time at each point is jointly continuous (`continuousOn_prod_of_continuousOn_lipschitzOnWith'`).

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1, Section 3.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti

open MeasureTheory Set Real ParabolicSpaceTime
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℝ → E → F} {T M H α : ℝ≥0}

/-- **Temporal Hölder continuity of the gradient of the Duhamel potential.** For `0 < α < 2`
there is a constant `C`, depending only on `α` and the dimension, with the following property.
If `f` is jointly measurable and its slices `f(r, ·)`, `0 ≤ r ≤ T`, are bounded by `M` and
`α`-Hölder with constant `H`, then at every point `x` the gradient `t ↦ D w(t, ·)(x)` of the
Duhamel potential is `α/2`-Hölder on `[0, T]`, with constant `2 K + C H`, where
`K = T H (1 + M_α) + M max(1, T)` is the constant of `TauCeti.holderWith_heatDuhamelPotential`. -/
theorem exists_holderOnWith_fderiv_heatDuhamelPotential (hα : 0 < α) (hα₂ : α < 2) :
    ∃ C : ℝ≥0, ∀ {f : ℝ → E → F} {T M H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖f r y‖ ≤ M) →
      (∀ r ∈ Icc (0 : ℝ) T, HolderWith H α (f r)) → ∀ x,
        HolderOnWith (2 * (T * H * (1 + heatKernelMoment E α) + M * max 1 T) + C * H) (α / 2)
          (fun t => fderiv ℝ (heatDuhamelPotential f t) x) (Icc 0 T) := by
  obtain ⟨C, hC⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_heatDuhamelPotential (E := E) (F := F) hα hα₂
  refine ⟨C, fun {f T M H} hf hM hH x => ?_⟩
  set K : ℝ≥0 := T * H * (1 + heatKernelMoment E α) + M * max 1 T
  have hval := holderWith_heatDuhamelPotential hf hM hH hα hα₂.le
  have hhess := hC hf
    (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr =>
      ae_of_all _ (hM r (Ioo_subset_Icc_self hr)))
    (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => hH r (Ioo_subset_Icc_self hr))
  refine HolderOnWith.of_dist_le fun t ht s hs => ?_
  set u := heatDuhamelPotential f t
  set v := heatDuhamelPotential f s
  have hu : ContDiff ℝ 2 u := contDiff_heatDuhamelPotential_of_forall_holderWith hf hM hH hα ht
  have hv : ContDiff ℝ 2 v := contDiff_heatDuhamelPotential_of_forall_holderWith hf hM hH hα hs
  have hg : ContDiff ℝ 2 (u - v) := hu.sub hv
  set d : ℝ≥0 := nndist t s ^ ((α / 2 : ℝ≥0) : ℝ)
  have hd : (d : ℝ) = dist t s ^ ((α / 2 : ℝ≥0) : ℝ) := by
    simp only [d, NNReal.coe_rpow, coe_nndist]
  -- Points with the same spatial coordinate are at parabolic distance `√|t - s|`.
  have hgM : ∀ y, ‖(u - v) y‖ ≤ K * d := by
    intro y
    have h := hval.dist_le (slabMk y ⟨t, ht⟩) (slabMk y ⟨s, hs⟩)
    rw [Subtype.dist_eq, ParabolicSpaceTime.dist_eq] at h
    simp only [space_slabMk, time_slabMk, dist_self, zero_add] at h
    rw [Pi.sub_apply, ← dist_eq_norm]
    refine h.trans_eq ?_
    rw [hd, Real.dist_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _), NNReal.coe_div,
      NNReal.coe_ofNat]
    congr 2
    ring
  -- The Hessian of `u - v` is bounded by the temporal Hölder estimate of the Hessian.
  have hlip : LipschitzWith (C * H * d) (fderiv ℝ (u - v)) := by
    refine lipschitzWith_of_nnnorm_fderiv_le
      ((hg.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) fun y => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
      iteratedFDeriv_sub_apply hu.contDiffAt hv.contDiffAt, ← dist_eq_norm]
    simpa only [NNReal.coe_mul, hd] using (hhess y).dist_le ht hs
  have hD := (holderWith_one.2 hlip).norm_le_of_hasFDerivAt
    (fun y => ((hg.differentiable two_ne_zero) y).hasFDerivAt) hgM one_pos x
  rw [fderiv_sub (hu.differentiable two_ne_zero x) (hv.differentiable two_ne_zero x)] at hD
  rw [dist_eq_norm]
  refine hD.trans_eq ?_
  simp only [NNReal.coe_one, Real.rpow_one, div_one, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_ofNat, hd]
  ring

/-- **The gradient of the Duhamel potential is Lipschitz in space.** For `α > 0` there is a
constant `C`, depending only on `α` and the dimension, with the following property. If `f` is
jointly measurable and its slices `f(r, ·)`, `0 ≤ r ≤ T`, are bounded by `M` and `α`-Hölder with
constant `H`, then for every `0 ≤ t ≤ T` the gradient `D w(t, ·)` of the Duhamel potential is
Lipschitz with constant `C H T^(α/2)`. -/
theorem exists_lipschitzWith_fderiv_heatDuhamelPotential (hα : 0 < α) :
    ∃ C : ℝ≥0, ∀ {f : ℝ → E → F} {T M H : ℝ≥0}, StronglyMeasurable (Function.uncurry f) →
      (∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖f r y‖ ≤ M) →
      (∀ r ∈ Icc (0 : ℝ) T, HolderWith H α (f r)) → ∀ t ∈ Icc (0 : ℝ) T,
        LipschitzWith (C * H * T ^ ((α : ℝ) / 2)) (fderiv ℝ (heatDuhamelPotential f t)) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_two_heatDuhamelPotential_le (E := E) (F := F) hα
  refine ⟨C.toNNReal, fun {f T M H} hf hM hH t ht => ?_⟩
  have hcd := contDiff_heatDuhamelPotential_of_forall_holderWith hf hM hH hα ht
  refine lipschitzWith_of_nnnorm_fderiv_le
    ((hcd.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero) fun y => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0, heatDuhamelPotential_zero, Pi.zero_def, iteratedFDeriv_const_of_ne two_ne_zero,
      Pi.zero_apply, norm_zero]
    positivity
  refine (hC hf
    (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr =>
      ae_of_all _ (hM r ⟨hr.1.le, hr.2.le.trans ht.2⟩))
    (ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => hH r ⟨hr.1.le, hr.2.le.trans ht.2⟩)
    hpos y).trans ?_
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal']
  gcongr
  · exact le_max_left _ _
  · exact ht.2

/-- **Joint continuity of the gradient of the Duhamel potential.** If `f` is jointly measurable
and its slices `f(r, ·)`, `0 ≤ r ≤ T`, are uniformly bounded and uniformly `α`-Hölder, with
`0 < α < 2`, then `(t, x) ↦ D w(t, ·)(x)` is continuous on `[0, T] × E`. -/
theorem continuousOn_fderiv_heatDuhamelPotential (hf : StronglyMeasurable (Function.uncurry f))
    (hM : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖f r y‖ ≤ M) (hH : ∀ r ∈ Icc (0 : ℝ) T, HolderWith H α (f r))
    (hα : 0 < α) (hα₂ : α < 2) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (heatDuhamelPotential f p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
  obtain ⟨A, hA⟩ := exists_lipschitzWith_fderiv_heatDuhamelPotential (E := E) (F := F) hα
  obtain ⟨B, hB⟩ := exists_holderOnWith_fderiv_heatDuhamelPotential (E := E) (F := F) hα hα₂
  -- The gradient is Lipschitz in space with a constant independent of time, and continuous in
  -- time at each point.
  exact continuousOn_prod_of_continuousOn_lipschitzOnWith'
    (fun p : ℝ × E => fderiv ℝ (heatDuhamelPotential f p.1) p.2) (A * H * T ^ ((α : ℝ) / 2))
    (fun t ht => (hA hf hM hH t ht).lipschitzOnWith)
    (fun x _ => (hB hf hM hH x).continuousOn (div_pos hα two_pos))

end TauCeti
