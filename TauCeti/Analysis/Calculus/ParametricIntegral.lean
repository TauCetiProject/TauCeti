/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Compactness.Normed

/-!
# Compact-parameter integration

This file uses Mathlib's continuity theorem for parameterized interval integrals and proves that
integration over the compact unit interval preserves differentiation and continuous
differentiability in a normed-space parameter. Continuous differentiability is preserved at every
finite or infinite order and with independent domain and codomain universes.

These results supply the analytic regularity used by smooth Hadamard factorization and the
identification of point derivations with tangent vectors.

The file also differentiates a parametrized interval integral `x ↦ ∫ t in a..b, G (x, t)` in a
real parameter `x` at a point `x₀`, assuming only that `G` is `C¹` on an open set containing the
compact segment `{x₀} × [a, b]`: the derivative is the integral of the partial derivative of `G`
in `x`.

For a compact parameter space `α` mapped continuously into a topological space `P` by `ι`, an
integrable weight `g` on `α` preserves integrability and continuity of the integrand in a
topological parameter space `E`. No countability assumption on these spaces is needed.

When `E` and `P` are normed spaces and `F` is `C^n` on an open set `W ⊆ E × P`, the integral
`x ↦ ∫ y, g y • F (x, ι y) ∂μ` is `C^n` on every open set `U` with `U × ι(α) ⊆ W`
(`TauCeti.contDiffOn_integral_smul_of_contDiffOn`), with derivative the integral of the partial
derivatives of `F` in `x` (`TauCeti.hasFDerivAt_integral_smul_of_contDiffOn`).  The weight need
not be continuous; this is the regularity of kernel integrals such as the Poisson integral of
integrable boundary data on a sphere.

The parameter may also range over a convex set `s` with unique derivatives that need not be open:
if `F` is `C^n` on a set `W ⊇ s × ι(α)` with unique derivatives, the integral is `C^n` on `s`
(`Convex.contDiffOn_integral_smul_of_contDiffOn`), with derivative within `s` the integral of the
partial derivatives within `s` (`Convex.hasFDerivWithinAt_integral_smul_of_contDiffOn`). This
is the regularity of the Poincaré homotopy operator on a closed half-ball.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Interval

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

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
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_eventually_norm_le
    (F := h'.uncurry) (x₀ := x₀) isOpen_univ (fun _ _ ↦ hh'.continuousAt)
    (fun _ _ ↦ Set.mem_univ _)
  simp only [Set.mem_univ, true_and] at hC
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
    exact hh.differentiable_one.differentiableAt.hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left x t)

private theorem contDiff_integral_Icc_of_contDiff_nat
    {V : Type u} {W : Type max u v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
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
    [NormedAddCommGroup W] [NormedSpace ℝ W]
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
  obtain ⟨u, v, huo, _, hu, hv, huv⟩ :=
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

variable {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} {g : α → ℝ}

section Topological

variable {E P : Type*} [TopologicalSpace E] [TopologicalSpace P] {ι : α → P} {W : Set (E × P)}

/-- An integrable weight on a compact space times a function continuous along `{x} × ι(α)` is
integrable. -/
theorem integrable_smul_of_continuousOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : E × P → H} (hg : Integrable g μ) (hι : Continuous ι) (hF : ContinuousOn F W) {x : E}
    (hx : ∀ y, (x, ι y) ∈ W) :
    Integrable (fun y ↦ g y • F (x, ι y)) μ := by
  have hφ : Continuous fun y ↦ F (x, ι y) := hF.comp_continuous (continuous_const.prodMk hι) hx
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  have hm := hφ.stronglyMeasurable_of_support_subset_isCompact isCompact_univ (subset_univ _)
  exact hg.smul_bdd C hm.aestronglyMeasurable (ae_of_all _ fun y ↦ hC y (mem_univ y))

/-- Integration against an integrable weight over a compact parameter space is continuous in a
parameter `x` of the integrand, at any `x₀` with `{x₀} × ι(α)` inside the open set where the
integrand is continuous. -/
theorem continuousAt_integral_smul_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι) (hW : IsOpen W)
    (hF : ContinuousOn F W) {x₀ : E} (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    ContinuousAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) x₀ := by
  have hmem : {x₀} ×ˢ range ι ⊆ W := by
    rintro ⟨x, p⟩ ⟨hx, y, rfl⟩
    rcases mem_singleton_iff.mp hx with rfl
    exact hx₀ y
  obtain ⟨u, v, hu, _, hxu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_range hι) hW hmem
  have hc : ContinuousOn (fun p : E × α ↦ F (p.1, ι p.2)) (u ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
      fun p hp ↦ huv ⟨hp.1, hv (mem_range_self p.2)⟩
  have hi := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    (ContinuousLinearMap.lsmul ℝ ℝ) isCompact_univ (f := fun x y ↦ F (x, ι y)) hc
    (fun _ _ _ h ↦ absurd (mem_univ _) h) hg.integrableOn
  exact hi.continuousAt (hu.mem_nhds (hxu (mem_singleton x₀)))

end Topological

variable {E : Type u} {P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : α → P} {W : Set (E × P)}

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
  have hmem : ∀ y ∈ Set.range ι, (x₀, y) ∈ W := Set.forall_mem_range.mpr hx₀
  obtain ⟨C, hC⟩ := (isCompact_range hι).exists_eventually_norm_le hW
    (fun y hy ↦ hD.continuousAt (hW.mem_nhds (hmem y hy))) hmem
  simp only [Set.forall_mem_range] at hC
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

/-! ### Parameters in a convex set

The parameter `x` now ranges over a convex set `s`, which need not be open, and the integrand is
only assumed to be `C^n` on a set `W ⊇ s × ι(α)` with unique derivatives. Derivatives are taken
within `s`. This is the setting of a closed half-ball, the image of a boundary chart. -/

section Convex

variable {s : Set E}

/-- **Differentiation under the integral sign within a convex set.** If `F` is `C¹` on a set
`W ⊆ E × P` with unique derivatives, `s` is convex, and `s × ι(α) ⊆ W`, then integrating
`F (x, ι y)` against an integrable weight `g` is differentiable within `s` at every point `x₀` of
`s` at which `s` has unique derivatives, with derivative the integral of the partial derivatives
of `F` in `x` within `s`. -/
theorem _root_.Convex.hasFDerivWithinAt_integral_smul_of_contDiffOn {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hs : Convex ℝ s) (hW : UniqueDiffOn ℝ W) (hF : ContDiffOn ℝ 1 F W)
    (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) {x₀ : E} (hx₀ : x₀ ∈ s)
    (hsu : UniqueDiffWithinAt ℝ s x₀) :
    HasFDerivWithinAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ)
      (∫ y, g y • fderivWithin ℝ (fun x ↦ F (x, ι y)) s x₀ ∂μ) s x₀ := by
  -- the partial derivative in `x`, continuous on `W`
  set D : E × P → E →L[ℝ] G := fun p ↦ (fderivWithin ℝ F W p).comp (.inl ℝ E P)
  have hD : ContinuousOn D W :=
    (ContinuousLinearMap.precomp G (.inl ℝ E P)).continuous.comp_continuousOn
      (hF.continuousOn_fderivWithin hW le_rfl)
  have hderiv (x : E) (hx : x ∈ s) (y : α) :
      HasFDerivWithinAt (fun x ↦ F (x, ι y)) (D (x, ι y)) s x :=
    (hF.differentiableOn one_ne_zero _ (hsW x hx y)).hasFDerivWithinAt.comp x
      (hasFDerivAt_prodMk_left x (ι y)).hasFDerivWithinAt fun x' hx' ↦ hsW x' hx' y
  -- the partial derivative is uniformly close to its value at `x₀` for `x` near `x₀` in `s`
  have hunif (ε : ℝ) (hε : 0 < ε) :
      ∃ v ∈ 𝓝[s] x₀, ∀ x ∈ v, ∀ y ∈ univ, dist (D (x, ι y)) (D (x₀, ι y)) < ε :=
    isCompact_univ.mem_uniformity_of_prod (f := fun x y ↦ D (x, ι y))
      (hD.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
        fun p hp ↦ hsW _ hp.1 _) hx₀ (Metric.dist_mem_uniformity hε)
  have hD₀ : (∫ y, g y • fderivWithin ℝ (fun x ↦ F (x, ι y)) s x₀ ∂μ) =
      ∫ y, g y • D (x₀, ι y) ∂μ :=
    integral_congr_ae (ae_of_all _ fun y ↦ by
      dsimp only
      rw [(hderiv x₀ hx₀ y).fderivWithin hsu])
  rw [hD₀, hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set ε := c / ((∫ y, ‖g y‖ ∂μ) + 1)
  have hgn : 0 ≤ ∫ y, ‖g y‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  have hε : 0 < ε := div_pos hc (by linarith)
  obtain ⟨v, hv, hvD⟩ := hunif ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hv
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hδ)]
    with x hx hxδ
  -- the mean value inequality on the convex set `s ∩ ball x₀ δ`, for each parameter `y`
  have hsδ : Convex ℝ (s ∩ Metric.ball x₀ δ) := hs.inter (convex_ball x₀ δ)
  have hvD' (z : E) (hz : z ∈ s ∩ Metric.ball x₀ δ) (y : α) :
      ‖D (z, ι y) - D (x₀, ι y)‖ < ε := by
    simpa only [dist_eq_norm] using hvD z (hball ⟨hz.2, hz.1⟩) y (mem_univ y)
  have hpt (y : α) : ‖F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)‖ ≤ ε * ‖x - x₀‖ :=
    hsδ.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun z ↦ F (z, ι y))
      (f' := fun z ↦ D (z, ι y))
      (fun z (hz : z ∈ s ∩ Metric.ball x₀ δ) ↦ (hderiv z hz.1 y).mono inter_subset_left)
      (fun z hz ↦ (hvD' z hz y).le)
      ⟨hx₀, Metric.mem_ball_self hδ⟩ ⟨hx, hxδ⟩
  have hDx : ContinuousOn (fun p ↦ D p (x - x₀)) W :=
    (ContinuousLinearMap.apply ℝ G (x - x₀)).continuous.comp_continuousOn hD
  calc ‖(∫ y, g y • F (x, ι y) ∂μ) - (∫ y, g y • F (x₀, ι y) ∂μ) -
        (∫ y, g y • D (x₀, ι y) ∂μ) (x - x₀)‖
      = ‖∫ y, g y • (F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)) ∂μ‖ := by
        have hFx := integrable_smul_of_continuousOn hg hι hF.continuousOn (hsW x hx)
        have hFx₀ := integrable_smul_of_continuousOn hg hι hF.continuousOn (hsW x₀ hx₀)
        rw [ContinuousLinearMap.integral_apply
          (integrable_smul_of_continuousOn hg hι hD (hsW x₀ hx₀))]
        simp only [smul_apply, smul_sub]
        rw [integral_sub (by exact hFx.sub hFx₀ :
            Integrable (fun y ↦ g y • F (x, ι y) - g y • F (x₀, ι y)) μ)
          (integrable_smul_of_continuousOn hg hι hDx (hsW x₀ hx₀)), integral_sub hFx hFx₀]
    _ ≤ ∫ y, ‖g y‖ * (ε * ‖x - x₀‖) ∂μ := by
        refine norm_integral_le_of_norm_le ((hg.norm.mul_const _)) (ae_of_all _ fun y ↦ ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hpt y) (norm_nonneg _)
    _ = (∫ y, ‖g y‖ ∂μ) * ε * ‖x - x₀‖ := by rw [integral_mul_const, mul_assoc]
    _ ≤ c * ‖x - x₀‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

private theorem _root_.Convex.contDiffOn_integral_smul_nat {G : Type max u v}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (m : ℕ) {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hW : UniqueDiffOn ℝ W)
    (hF : ContDiffOn ℝ m F W) (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ m (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) s := by
  induction m generalizing G with
  | zero =>
      have hc : ContinuousOn (fun p : E × α ↦ F (p.1, ι p.2)) (s ×ˢ univ) :=
        hF.continuousOn.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
          fun p hp ↦ hsW _ hp.1 _
      refine contDiffOn_zero.2 <|
        (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
          (ContinuousLinearMap.lsmul ℝ ℝ) isCompact_univ (f := fun x y ↦ F (x, ι y)) hc
          (fun _ _ _ h ↦ absurd (mem_univ _) h) hg.integrableOn).congr fun x _ ↦ by simp
  | succ m ih =>
      have hF' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) F W := by exact_mod_cast hF
      have hderiv := fun x hx ↦ hs.hasFDerivWithinAt_integral_smul_of_contDiffOn hg hι hW
        (hF'.of_le le_add_self) hsW hx (hsu x hx)
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderivWithin hsu]
      refine ⟨fun x hx ↦ (hderiv x hx).differentiableWithinAt, fun h ↦ absurd h (by simp), ?_⟩
      refine (ih (F := fun p ↦ (fderivWithin ℝ F W p).comp (.inl ℝ E P))
        (((ContinuousLinearMap.precomp G (.inl ℝ E P)).contDiff.comp_contDiffOn
          (hF'.fderivWithin hW le_rfl)).congr fun _ _ ↦ by simp)).congr fun x hx ↦ ?_
      rw [(hderiv x hx).fderivWithin (hsu x hx)]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      have hpart : HasFDerivWithinAt (fun x ↦ F (x, ι y))
          ((fderivWithin ℝ F W (x, ι y)).comp (.inl ℝ E P)) s x :=
        ((hF'.of_le le_add_self).differentiableOn one_ne_zero _
          (hsW x hx y)).hasFDerivWithinAt.comp x
            (hasFDerivAt_prodMk_left x (ι y)).hasFDerivWithinAt fun x' hx' ↦ hsW x' hx' y
      dsimp only
      rw [hpart.fderivWithin (hsu x hx)]

/-- **Smoothness of integrals over a compact parameter space, within a convex set.** If `F` is
`C^n` on a set `W ⊆ E × P` with unique derivatives, `s` is convex with unique derivatives, and
`s × ι(α) ⊆ W`, then integrating `F (x, ι y)` against an integrable weight `g` is `C^n` in `x`
on `s`. -/
theorem _root_.Convex.contDiffOn_integral_smul_of_contDiffOn {G : Type v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : ℕ∞} {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι)
    (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hW : UniqueDiffOn ℝ W) (hF : ContDiffOn ℝ n F W)
    (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) s := by
  let eG : Type max u v := ULift.{u} G
  let isoG : eG ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  have he : ContDiffOn ℝ n (fun x ↦ ∫ y, g y • isoG.symm (F (x, ι y)) ∂μ) s := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m hm
    exact hs.contDiffOn_integral_smul_nat m hg hι hsu hW
      (isoG.symm.contDiff.comp_contDiffOn (hF.of_le (by exact_mod_cast hm))) hsW
  refine (isoG.contDiff.comp_contDiffOn he).congr fun x _ ↦ ?_
  have hsmul : ∀ y, g y • isoG.symm (F (x, ι y)) = isoG.symm (g y • F (x, ι y)) :=
    fun y ↦ (map_smul _ _ _).symm
  simp only [Function.comp_apply, hsmul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.apply_symm_apply]

end Convex

end CompactParameter

end TauCeti
