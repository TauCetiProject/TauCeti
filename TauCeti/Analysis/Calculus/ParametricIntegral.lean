/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Compactness.Normed

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

Finally, for a compact parameter space `α` mapped continuously into a normed space `P` by `ι`, an
integrable weight `g` on `α`, and `F` that is `C^n` on an open set `W ⊆ E × P`, the integral
`x ↦ ∫ y, g y • F (x, ι y) ∂μ` is `C^n` on every open set `U` with `U × ι(α) ⊆ W`
(`TauCeti.contDiffOn_integral_smul_of_contDiffOn`), with derivative the integral of the partial
derivatives of `F` in `x` (`TauCeti.hasFDerivAt_integral_smul_of_contDiffOn`).  The weight need
not be continuous; this is the regularity of kernel integrals such as the Poisson integral of
integrable boundary data on a sphere.

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

/-! ### Integration against a weight over a compact parameter space -/

section CompactParameter

open Filter Set
open scoped Topology

variable {E : Type u} {P α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace α] [CompactSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} {ι : α → P} {g : α → ℝ} {W : Set (E × P)}

/-- **Partial derivatives in the first variable.** If `F` is `C^(m+1)` on an open set
`W ⊆ E × P`, then the derivative of `x ↦ F (x, p.2)` at `p.1` is `C^m` in `p` on `W`. -/
theorem _root_.ContDiffOn.fderiv_partial_of_isOpen {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} {m : WithTop ℕ∞} (hF : ContDiffOn ℝ (m + 1) F W)
    (hW : IsOpen W) :
    ContDiffOn ℝ m (fun p : E × P ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1) W := by
  intro p hp
  have hFp : ContDiffAt ℝ (m + 1) (fun q : (E × P) × E ↦ F (q.2, q.1.2)) (p, p.1) :=
    (hF.contDiffAt (hW.mem_nhds hp)).comp (p, p.1) (by fun_prop)
  exact (ContDiffAt.fderiv (f := fun (q : E × P) (x : E) ↦ F (x, q.2)) hFp contDiffAt_fst
    le_rfl).contDiffWithinAt

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
/-- An integrable weight on a compact space times a function continuous along `{x} × ι(α)` is
integrable. -/
theorem integrable_smul_of_continuousOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : E × P → H} (hg : Integrable g μ) (hι : Continuous ι) (hF : ContinuousOn F W) {x : E}
    (hx : ∀ y, (x, ι y) ∈ W) :
    Integrable (fun y ↦ g y • F (x, ι y)) μ := by
  have hφ : Continuous fun y ↦ F (x, ι y) := hF.comp_continuous (continuous_const.prodMk hι) hx
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact hg.smul_bdd C hφ.aestronglyMeasurable (ae_of_all _ fun y ↦ hC y (mem_univ y))

omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
/-- Integration against an integrable weight over a compact parameter space is continuous in a
parameter `x` of the integrand, at any `x₀` with `{x₀} × ι(α)` inside the open set where the
integrand is continuous. -/
theorem continuousAt_integral_smul_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι) (hW : IsOpen W)
    (hF : ContinuousOn F W) {x₀ : E} (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    ContinuousAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) x₀ := by
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_compact_family hι hW hF hx₀
  refine continuousAt_of_dominated (bound := fun y ↦ ‖g y‖ * C) ?_ ?_ (hg.norm.mul_const C)
    (ae_of_all _ fun y ↦ ?_)
  · filter_upwards [hC] with x hx
    exact (integrable_smul_of_continuousOn hg hι hF fun y ↦ (hx y).1).aestronglyMeasurable
  · filter_upwards [hC] with x hx
    exact ae_of_all _ fun y ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hx y).2 (norm_nonneg _)
  · exact ((hF.continuousAt (hW.mem_nhds (hx₀ y))).comp (f := fun x : E ↦ (x, ι y))
      (by fun_prop)).const_smul (g y)

/-- **Differentiation under the integral sign over a compact parameter space.** If `F` is `C¹`
on an open set `W ⊆ E × P` containing `{x₀} × ι(α)`, then integrating `F (x, ι y)` against an
integrable weight `g` is differentiable at `x₀`, with derivative the integral of the partial
derivative of `F` in `x`. -/
theorem hasFDerivAt_integral_smul_of_contDiffOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι) (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) {x₀ : E} (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    HasFDerivAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ)
      (∫ y, g y • fderiv ℝ (fun x ↦ F (x, ι y)) x₀ ∂μ) x₀ := by
  set D : E × P → E →L[ℝ] G := fun p ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1
  have hD : ContinuousOn D W :=
    (ContDiffOn.fderiv_partial_of_isOpen (m := 0) (by simpa using hF) hW).continuousOn
  have hdiff : ∀ p ∈ W, HasFDerivAt (fun x ↦ F (x, p.2)) (D p) p.1 := fun p hp ↦
    (((hF.contDiffAt (hW.mem_nhds hp)).differentiableAt one_ne_zero).comp p.1
      (differentiableAt_id.prodMk (differentiableAt_const p.2))).hasFDerivAt
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_compact_family hι hW hD hx₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x y ↦ g y • D (x, ι y))
    (bound := fun y ↦ ‖g y‖ * C) hC ?_
    (integrable_smul_of_continuousOn hg hι hF.continuousOn hx₀)
    (integrable_smul_of_continuousOn hg hι hD hx₀).aestronglyMeasurable ?_
    (hg.norm.mul_const C) ?_
  · filter_upwards [hC] with x hx
    exact (integrable_smul_of_continuousOn hg hι hF.continuousOn
      fun y ↦ (hx y).1).aestronglyMeasurable
  · refine ae_of_all _ fun y x hx ↦ ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hx y).2 (norm_nonneg _)
  · exact ae_of_all _ fun y x hx ↦ (hdiff (x, ι y) (hx y).1).const_smul (g y)

private theorem contDiffOn_integral_smul_nat {G : Type max u v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (m : ℕ) {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι)
    (hW : IsOpen W) (hF : ContDiffOn ℝ m F W) {U : Set E} (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ m (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) U := by
  induction m generalizing G with
  | zero =>
      exact contDiffOn_zero.2 fun x hx ↦
        (continuousAt_integral_smul_of_continuousOn hg hι hW hF.continuousOn
          (hUW x hx)).continuousWithinAt
  | succ m ih =>
      have hF' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) F W := by exact_mod_cast hF
      have hderiv := fun x hx ↦ hasFDerivAt_integral_smul_of_contDiffOn hg hι hW
        (hF'.of_le le_add_self) (hUW x hx)
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt,
        fun h ↦ absurd h (by simp), ?_⟩
      exact (ih (hF'.fderiv_partial_of_isOpen hW)).congr fun x hx ↦ (hderiv x hx).fderiv

/-- **Smoothness of integrals over a compact parameter space.** If `F` is `C^n` on an open set
`W ⊆ E × P` and `{x} × ι(α) ⊆ W` for every `x` in an open set `U`, then integrating `F (x, ι y)`
against an integrable weight `g` is `C^n` in `x` on `U`. -/
theorem contDiffOn_integral_smul_of_contDiffOn {G : Type v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : ℕ∞} {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hW : IsOpen W) (hF : ContDiffOn ℝ n F W) {U : Set E} (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) U := by
  let eG : Type max u v := ULift.{u} G
  let isoG : eG ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  have he : ContDiffOn ℝ n (fun x ↦ ∫ y, g y • isoG.symm (F (x, ι y)) ∂μ) U := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m hm
    exact contDiffOn_integral_smul_nat m hg hι hW
      (isoG.symm.contDiff.comp_contDiffOn (hF.of_le (by exact_mod_cast hm))) hU hUW
  refine (isoG.contDiff.comp_contDiffOn he).congr fun x _ ↦ ?_
  have hsmul : ∀ y, g y • isoG.symm (F (x, ι y)) = isoG.symm (g y • F (x, ι y)) :=
    fun y ↦ (map_smul _ _ _).symm
  simp only [Function.comp_apply, hsmul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.apply_symm_apply]

end CompactParameter

end TauCeti
