/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compact-parameter integration

This file uses Mathlib's continuity theorem for parameterized interval integrals and proves that
integration over the compact unit interval preserves differentiation and continuous
differentiability in a normed-space parameter. Continuous differentiability is preserved at every
finite or infinite order and with independent domain and codomain universes.

These results supply the analytic regularity used by smooth Hadamard factorization, a prerequisite
for the point-derivation/tangent-space equivalence in the Lie groups roadmap.

The file also differentiates a parametrized interval integral `x ↦ ∫ t in a..b, G (x, t)` in a
real parameter `x` at a point `x₀`, assuming only that `G` is `C¹` on an open set containing the
compact segment `{x₀} × [a, b]`: the derivative is the integral of the partial derivative of `G`
in `x`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Interval

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
private theorem exists_eventually_norm_le_on_Icc
    {X : Type*} [TopologicalSpace X]
    (h : X → ℝ → F) (hh : Continuous h.uncurry) (x₀ : X) :
    ∃ C : ℝ, ∀ᶠ x in nhds x₀, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖h x t‖ ≤ C := by
  have hfiber : Continuous (fun t : ℝ ↦ ‖h x₀ t‖) :=
    hh.norm.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image
    hfiber.continuousOn
  refine ⟨C + 1, ?_⟩
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  have hlt : ‖h x₀ t‖ < C + 1 :=
    lt_of_le_of_lt (hC (Set.mem_image_of_mem (fun t : ℝ ↦ ‖h x₀ t‖) ht))
      (lt_add_of_pos_right C zero_lt_one)
  have hn : {z : X × ℝ | ‖h.uncurry z‖ < C + 1} ∈ nhds (x₀, t) :=
    (isOpen_lt hh.norm continuous_const).mem_nhds hlt
  filter_upwards [hn] with z hz
  exact hz.le

/-- Differentiation under an integral over the compact unit interval for a continuously
differentiable parameterized function. -/
theorem hasFDerivAt_integral_Icc_of_contDiff
     (h : E → ℝ → F) (hh : ContDiff ℝ 1 h.uncurry) (x₀ : E) :
    HasFDerivAt (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t)
      (∫ t in Set.Icc (0 : ℝ) 1,
        (fderiv ℝ h.uncurry (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  let h' : E → ℝ → E →L[ℝ] F := fun x t ↦
    (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hh' : Continuous h'.uncurry := by
    have hd : Continuous (fderiv ℝ h.uncurry) :=
      (hh.fderiv_right (m := 0) (by norm_num)).continuous
    fun_prop
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_on_Icc h' hh' x₀
  let s : Set E := {x | ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖h' x t‖ ≤ C}
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (F := h) (F' := h')
    (bound := fun _ ↦ C) (s := s)
  · exact hC
  · exact Filter.Eventually.of_forall fun x ↦
      (hh.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hh.continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  · exact (hh'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro x hx
    exact hx t ht
  · exact continuous_const.integrableOn_Icc
  · filter_upwards with t
    intro x _hx
    have hd := hh.differentiable_one.differentiableAt.hasFDerivAt.comp x
        (hasFDerivAt_id x |>.prodMk (hasFDerivAt_const t x))
    -- Expose the derivative of the fixed-`t` slice; `inl` is definitionally `id.prod 0`.
    change HasFDerivAt (fun y ↦ h y t)
      ((fderiv ℝ h.uncurry (x, t)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x at hd
    simpa only [h', ContinuousLinearMap.inl] using hd

private theorem contDiff_integral_Icc_of_contDiff_nat
    {V : Type u} {W : Type max u v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  induction n generalizing W with
  | zero =>
      have hc : Continuous (fun x ↦ ∫ t in (0 : ℝ)..1, h x t) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          hh.continuous 0 1
      apply contDiff_zero.2
      simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
        using hc
  | succ n ih =>
      let h' : V → ℝ → V →L[ℝ] W := fun x t ↦
        (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ V ℝ)
      have hh' : ContDiff ℝ n h'.uncurry := by
        have hd : ContDiff ℝ n (fderiv ℝ h.uncurry) :=
          hh.fderiv_right (m := n) (by norm_num)
        fun_prop
      have hsmooth : ContDiff ℝ ((n : ℕ∞ω) + 1)
          (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
        rw [contDiff_succ_iff_hasFDerivAt]
        exact ⟨fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h' x t, ih h' hh',
          hasFDerivAt_integral_Icc_of_contDiff h (hh.of_le (by norm_num))⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hsmooth

/-- Integration over the compact unit interval preserves continuous differentiability of any
possibly infinite order in a parameter. -/
theorem contDiff_integral_Icc_of_contDiff
    {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ∞) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  let eW : Type max u v := ULift.{u} W
  let isoW : eW ≃L[ℝ] W := ContinuousLinearEquiv.ulift
  let eh : V → ℝ → eW := fun x t ↦ isoW.symm (h x t)
  have heh : ContDiff ℝ n eh.uncurry := by
    apply isoW.symm.contDiff.comp hh
  have he : ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, eh x t) := by
    rw [contDiff_iff_forall_nat_le]
    intro m hm
    exact contDiff_integral_Icc_of_contDiff_nat m eh (heh.of_le (by exact_mod_cast hm))
  convert isoW.contDiff.comp he using 1
  funext x
  simpa only [Function.comp_apply, eh, ContinuousLinearEquiv.apply_symm_apply] using
    (isoW.integral_comp_comm (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (fun t ↦ eh x t))

namespace TauCeti

/-- **Differentiation under a parametrized interval integral.** If `G` is `C¹` on an open set
containing the segment `{x₀} × [a, b]`, then the partial derivative of `G` in the first variable
is interval integrable along that segment, and `x ↦ ∫ t in a..b, G (x, t)` is differentiable at
`x₀` with derivative the integral of this partial derivative. -/
theorem hasDerivAt_intervalIntegral_of_contDiffOn {G : ℝ × ℝ → F}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {x₀ a b : ℝ}
    (hsub : {x₀} ×ˢ Set.uIcc a b ⊆ U) :
    IntervalIntegrable (fun t ↦ fderiv ℝ G (x₀, t) (1, 0)) volume a b ∧
      HasDerivAt (fun x ↦ ∫ t in a..b, G (x, t))
        (∫ t in a..b, fderiv ℝ G (x₀, t) (1, 0)) x₀ := by
  obtain ⟨u, v, huo, hvo, hu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hU hsub
  have hx₀u : x₀ ∈ u := hu (Set.mem_singleton x₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (huo.mem_nhds hx₀u)
  have hK : Metric.closedBall x₀ (ε / 2) ×ˢ Set.uIcc a b ⊆ U := fun z hz ↦
    huv ⟨hball (Metric.closedBall_subset_ball (half_lt_self hε) hz.1), hv hz.2⟩
  -- the partial derivative in the first variable, continuous on `U`
  set G' : ℝ × ℝ → F := fun z ↦ fderiv ℝ G z (1, 0)
  have hG'cont : ContinuousOn G' U :=
    (hG.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ (ε / 2)).prod isCompact_uIcc)
    |>.exists_bound_of_continuousOn (hG'cont.mono hK)
  have hslice : ∀ {x : ℝ}, x ∈ u → ∀ {W : ℝ × ℝ → F}, ContinuousOn W U →
      ContinuousOn (fun t ↦ W (x, t)) (Set.uIcc a b) := by
    intro x hx W hW
    exact hW.comp
      (continuous_const.prodMk continuous_id : Continuous fun t : ℝ ↦ (x, t)).continuousOn
      fun t ht ↦ huv ⟨hx, hv ht⟩
  have hdiff : ∀ t ∈ Ι a b, ∀ x ∈ Metric.closedBall x₀ (ε / 2),
      HasDerivAt (fun x ↦ G (x, t)) (G' (x, t)) x := by
    intro t ht x hx
    have hz : (x, t) ∈ U := hK ⟨hx, Set.uIoc_subset_uIcc ht⟩
    have hGz : HasFDerivAt G (fderiv ℝ G (x, t)) (x, t) :=
      ((hG.differentiableOn one_ne_zero (x, t) hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    exact hGz.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x t ↦ G (x, t)) (F' := fun x t ↦ G' (x, t))
    (bound := fun _ ↦ C) (Metric.closedBall_mem_nhds x₀ (half_pos hε)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_)
  · filter_upwards [huo.mem_nhds hx₀u] with x hx
    exact ((hslice hx hG.continuousOn).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact (hslice hx₀u hG.continuousOn).intervalIntegrable
  · exact ((hslice hx₀u hG'cont).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht x hx ↦
      hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t ht x hx ↦ hdiff t ht x hx

end TauCeti
