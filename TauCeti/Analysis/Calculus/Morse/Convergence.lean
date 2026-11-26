/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Topology.OmegaLimit
-- Private: the gradient of `-f`, the mean value inequality, Heine--Cantor and monotone
-- convergence are used only inside proofs; no declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Topology.Order.Monotone.Convergence

/-!
# Convergence of a negative gradient trajectory

A negative gradient trajectory `γ` of `f`, followed forward in time and never leaving a compact
set `K`, **converges** to a critical point of `f` provided that `f` has only finitely many critical
points in `K`:

`∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atTop (𝓝 p)`.

This is the statement that makes the moduli spaces of the Morse complex — the trajectories running
from one critical point to another — well defined objects at all. It builds on the dynamical
facts of `TauCeti/Analysis/Calculus/Morse/GradientFlow.lean`.

Some hypothesis beyond compactness is needed to pin the limit down. For a merely smooth `f` a
negative gradient trajectory can spiral forever towards a circle of critical points, its ω-limit
set being the whole circle and the trajectory having no limit at all; for an analytic `f` this is
ruled out by Łojasiewicz's gradient inequality, and here it is ruled out by the Morse condition.
The theorem below therefore assumes that `f` has only **finitely many critical points** in `K`,
which is exactly what a Morse function on a compact set provides, by
`TauCeti.HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero`.

## The argument

The three steps are the classical ones (Audin--Damian, Chapter 2).

*The energy converges.* Along the trajectory `f` is antitone
(`IsIntegralCurveOn.antitoneOn_comp_neg_gradient`) and is bounded below on `K`, so
`f ∘ γ` has a limit.

*The gradient dies.* The trajectory is Lipschitz, with the bound on `‖∇ f‖` over `K` as its
constant, and `∇ f` is uniformly continuous on `K`; so if `‖∇ f (γ t)‖ ≥ ε` at some time `t`, the
same holds with `ε / 2` throughout a time interval `[t, t + δ]` whose length `δ` does not depend on
`t`. The energy identity, in the form `IsIntegralCurveOn.mul_sq_le_sub_of_le_norm_gradient`, then
makes `f` drop by at least `δ (ε / 2) ^ 2` across that interval — impossible infinitely often,
since the energy converges. Hence `∇ f (γ t) → 0`.

*The ω-limit set is a point.* Every cluster point of `γ` along `atTop` is therefore a critical
point in `K`, so the ω-limit set is finite; and it is preconnected, by
`TauCeti.isPreconnected_setOf_mapClusterPt_atTop`. A finite preconnected set is a single point,
and a map into a compact set with a unique cluster point converges to it
(`TauCeti.exists_tendsto_atTop_of_setOf_mapClusterPt_subset`).

## Main results

* `IsIntegralCurveOn.exists_tendsto_comp_atTop`: the energy `f ∘ γ` converges.
* `IsIntegralCurveOn.tendsto_gradient_atTop`: the gradient along the trajectory tends
  to `0`.
* `IsIntegralCurveOn.gradient_eq_zero_of_mapClusterPt`: every point of the ω-limit set is
  a critical point.
* `IsIntegralCurveOn.gradient_eq_zero_of_tendsto`: a convergent trajectory along which `f` is
  bounded below ends at a critical point, wherever the gradient is continuous at the limit.
* `IsIntegralCurveOn.exists_tendsto_atTop`: **a confined negative gradient trajectory
  converges to a critical point**, when the critical points in the confining compact set are
  finite in number.
* `IsIntegralCurveOn.exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn`: the Morse
  form of the same statement, where the finiteness comes from nondegeneracy.
* `IsIntegralCurveOn.exists_tendsto_atBot`: the corresponding backward-time statement.
* `IsIntegralCurveOn.exists_tendsto_atBot_of_hasNondegenerateCriticalPointsOn`: its Morse
  form, where finiteness follows from nondegeneracy.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 2.
* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, for the gradient inequality that
  replaces the finiteness hypothesis used here when `f` is analytic.
-/

public section

open Filter Function InnerProductSpace Metric Set TauCeti
open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {K : Set E} {x : E}

namespace IsIntegralCurveOn

/-! ### The trajectory is Lipschitz -/

/-- **A negative gradient trajectory confined to a compact set is Lipschitz**, with any bound for
the gradient on that set as its constant: the velocity is the negative gradient and therefore has
the same norm as the gradient. -/
theorem norm_sub_le_of_norm_gradient_le {C : ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hmaps : MapsTo γ (Ici 0) K)
    (hC : ∀ y ∈ K, ‖∇ f y‖ ≤ C) {s t : ℝ} (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ)) :
    ‖γ t - γ s‖ ≤ C * ‖t - s‖ :=
  (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr ↦ hγ r hr)
    (fun r hr ↦ by simpa using hC _ (hmaps hr)) hs ht

/-! ### The energy converges -/

/-- **The value of `f` along a confined negative gradient trajectory converges.** It is antitone
along the trajectory and bounded below on the compact set the trajectory never leaves. -/
theorem exists_tendsto_comp_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y) :
    ∃ c, Tendsto (fun t ↦ f (γ t)) atTop (𝓝 c) := by
  have hanti : AntitoneOn (f ∘ γ) (Ici 0) :=
    antitoneOn_comp_neg_gradient hγ (convex_Ici 0) fun t ht ↦ hdiff _ (hmaps ht)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    fun y hy ↦ (hdiff y hy).continuousAt.continuousWithinAt
  refine ⟨_, tendsto_atTop_ciInf_of_antitoneOn_Ici hanti ⟨-M, ?_⟩⟩
  rintro _ ⟨t, ht, rfl⟩
  have h := hM _ (hmaps ht)
  rw [Real.norm_eq_abs] at h
  linarith [neg_abs_le (f (γ t))]

/-! ### The gradient dies along the trajectory -/

/-- **The gradient stays above `ε / 2` for a short time.** If `‖∇ f (γ t)‖` is at least `ε` at a
time `t ≥ 0`, and `δ` is short enough that the trajectory cannot move by `η` in that time, then the
modulus `hUC` keeps the gradient above `ε / 2` throughout `[t, t + δ]`. -/
private theorem le_norm_gradient_of_mem_Icc {C δ ε η : ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hmaps : MapsTo γ (Ici 0) K)
    (hC : ∀ y ∈ K, ‖∇ f y‖ ≤ C)
    (hUC : ∀ y ∈ K, ∀ z ∈ K, dist y z < η → dist (∇ f y) (∇ f z) < ε / 2)
    (hCδ : C * δ < η) {t : ℝ} (ht : 0 ≤ t) (hbig : ε ≤ ‖∇ f (γ t)‖) :
    ∀ s ∈ Icc t (t + δ), ε / 2 ≤ ‖∇ f (γ s)‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hmaps (mem_Ici.mpr le_rfl)))
  intro s hs
  have hs0 : s ∈ Ici (0 : ℝ) := mem_Ici.mpr (ht.trans hs.1)
  have hnorm : ‖s - t‖ ≤ δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
    linarith [hs.2]
  have hdist : dist (γ s) (γ t) < η := by
    rw [dist_eq_norm]
    calc ‖γ s - γ t‖ ≤ C * ‖s - t‖ :=
          norm_sub_le_of_norm_gradient_le hγ hmaps hC (mem_Ici.mpr ht) hs0
      _ ≤ C * δ := by nlinarith
      _ < η := hCδ
  have h := hUC _ (hmaps hs0) _ (hmaps (mem_Ici.mpr ht)) hdist
  rw [dist_eq_norm] at h
  have h' : ‖∇ f (γ t)‖ - ‖∇ f (γ s)‖ ≤ ‖∇ f (γ s) - ∇ f (γ t)‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  linarith

/-- **The gradient tends to zero along a confined negative gradient trajectory.**

The trajectory is Lipschitz and `∇ f` is uniformly continuous on the compact set it stays in, so a
time at which `‖∇ f (γ t)‖` is at least `ε` is the start of a time interval of a fixed length `δ`
on which it is at least `ε / 2`. Across such an interval the energy identity makes `f` drop by at
least `δ (ε / 2) ^ 2`; but the drops of `f` across intervals of fixed length tend to `0`, because
`f` converges along the trajectory. So the times at which `‖∇ f (γ t)‖ ≥ ε` are bounded. -/
theorem tendsto_gradient_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) :
    Tendsto (fun t ↦ ∇ f (γ t)) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_tendsto_comp_atTop hγ hK hmaps hdiff
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgrad
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hmaps (mem_Ici.mpr le_rfl)))
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨η, hη, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hgrad) (ε / 2) (by positivity)
  set δ : ℝ := η / (C + 1) with hδdef
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hCδ : C * δ < η := by
    rw [hδdef, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < δ * (ε / 2) ^ 2 := by positivity
  -- The drops of the energy across intervals of length `δ` tend to `0`.
  have hdrop : Tendsto (fun t ↦ f (γ t) - f (γ (t + δ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t ↦ f (γ (t + δ))) atTop (𝓝 c) :=
      hc.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    simpa using hc.sub h2
  obtain ⟨t, hbig, ht0, hlt⟩ :=
    (hcon.and_eventually ((eventually_ge_atTop (0 : ℝ)).and
      (hdrop.eventually (gt_mem_nhds hpos)))).exists
  -- Across `[t, t + δ]` the gradient stays above `ε / 2`, so `f` drops by `δ * (ε / 2) ^ 2`.
  have hIcc : Icc t (t + δ) ⊆ Ici 0 := fun s hs ↦ mem_Ici.mpr (ht0.trans hs.1)
  have hdrop_le := hγ.mul_sq_le_sub_of_le_norm_gradient (le_add_of_nonneg_right hδ.le) hIcc
    (fun s hs ↦ hdiff _ (hmaps (hIcc hs))) (half_pos hε).le
    (le_norm_gradient_of_mem_Icc hγ hmaps hC hUC hCδ ht0 (not_lt.mp hbig))
  rw [add_sub_cancel_left] at hdrop_le
  exact absurd hdrop_le (not_le.mpr hlt)

/-! ### The ω-limit set -/

/-- **Every cluster point of a confined negative gradient trajectory is a critical point.** The
gradient tends to `0` along the trajectory, so the trajectory eventually lies in the closed set
where `‖∇ f‖ ≤ ε`, and hence so does every one of its cluster points. -/
theorem gradient_eq_zero_of_mapClusterPt
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) (hx : MapClusterPt x atTop γ) :
    ∇ f x = 0 := by
  have hzero := tendsto_gradient_atTop hγ hK hmaps hdiff hgrad
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (norm_nonneg _))
  have hcl : IsClosed (K ∩ (∇ f) ⁻¹' closedBall 0 ε) :=
    hgrad.preimage_isClosed_of_isClosed hK.isClosed isClosed_closedBall
  have hmem : K ∩ (∇ f) ⁻¹' closedBall 0 ε ∈ map γ atTop := by
    rw [mem_map]
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      NormedAddGroup.tendsto_nhds_zero.mp hzero ε hε] with t ht hlt
    exact ⟨hmaps (mem_Ici.mpr ht), mem_closedBall_zero_iff.mpr hlt.le⟩
  have hmemx := hcl.mem_of_mapClusterPt hx hmem
  rw [Set.mem_inter_iff, Set.mem_preimage, mem_closedBall_zero_iff] at hmemx
  linarith [hmemx.2]

/-! ### Convergence -/

/-- **A convergent negative gradient trajectory ends at a critical point.** If a forward
negative gradient trajectory converges to `p`, the gradient is continuous at `p`, and `f` stays
bounded below along the trajectory, then `p` is a critical point of `f`: otherwise the speed
would stay above `‖∇ f p‖ / 2` for all large times, and `f` would drop without bound. No
compactness or finiteness of the critical locus is needed once the limit is known to exist. -/
theorem gradient_eq_zero_of_tendsto {t₀ b : ℝ} {p : E}
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici t₀))
    (hf : ∀ t ∈ Ici t₀, DifferentiableAt ℝ f (γ t)) (hb : ∀ t ∈ Ici t₀, b ≤ f (γ t))
    (hp : Tendsto γ atTop (𝓝 p)) (hgrad : ContinuousAt (∇ f) p) :
    ∇ f p = 0 := by
  by_contra hne
  set δ := ‖∇ f p‖ / 2
  have hδpos : 0 < δ := half_pos (norm_pos_iff.mpr hne)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((eventually_ge_atTop t₀).and
    (((hgrad.tendsto.comp hp).norm).eventually (lt_mem_nhds (half_lt_self
      (norm_pos_iff.mpr hne)))))
  have hT₀t₀ : t₀ ≤ T₀ := (hT₀ T₀ le_rfl).1
  set T := T₀ + (f (γ T₀) - b) / δ ^ 2 + 1 with hT
  have hTT₀ : T₀ ≤ T := by
    have : 0 ≤ (f (γ T₀) - b) / δ ^ 2 :=
      div_nonneg (sub_nonneg.mpr (hb T₀ hT₀t₀)) (sq_nonneg _)
    linarith
  have hdrop := mul_sq_le_sub_of_le_norm_gradient hTT₀ hγ
    (fun t ht ↦ mem_Ici.mpr (hT₀t₀.trans ht.1)) (fun t ht ↦ hf t (hT₀t₀.trans ht.1)) hδpos.le
    (fun t ht ↦ (hT₀ t ht.1).2.le)
  have hlow := hb T (hT₀t₀.trans hTT₀)
  have hkey : (T - T₀) * δ ^ 2 = f (γ T₀) - b + δ ^ 2 := by
    rw [hT]
    field_simp
    ring
  nlinarith [sq_pos_of_pos hδpos]


/-- **A negative gradient trajectory that never leaves a compact set converges to a critical point
of `f` in it**, provided `f` has only finitely many critical points there.

Some such hypothesis is needed: a negative gradient trajectory can spiral forever towards a circle
of critical points and then have no limit, its ω-limit set being the whole circle. The finiteness
holds for a Morse function, which is
`IsIntegralCurveOn.exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn` below.

Nothing is claimed about the *rate* of convergence, nor about the backward limit: the reversed
curve `fun t ↦ γ (-t)` is a negative gradient trajectory of `-f`, so the backward limit is this
same theorem applied to `-f`, whose hypotheses have to be checked separately. -/
theorem exists_tendsto_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) (hfin : {y ∈ K | ∇ f y = 0}.Finite) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atTop (𝓝 p) := by
  -- The ω-limit set consists of critical points in `K`, of which there are finitely many.
  have hsub : {y | MapClusterPt y atTop γ} ⊆ {y ∈ K | ∇ f y = 0} := fun y hy ↦
    ⟨hK.isClosed.mem_of_mapClusterPt hy
        (mem_map.mpr (mem_of_superset (Ici_mem_atTop 0) hmaps)),
      gradient_eq_zero_of_mapClusterPt hγ hK hmaps hdiff hgrad hy⟩
  obtain ⟨p, hp, h⟩ :=
    exists_tendsto_atTop_of_setOf_mapClusterPt_subset hK hγ.continuousOn hmaps hfin hsub
  exact ⟨p, hp.1, hp.2, h⟩

/-- **The Morse form of the convergence theorem.** A negative gradient trajectory confined to a
compact set on which `fderiv ℝ f` is continuous and every critical point of `f` is nondegenerate
converges to a critical point of `f` in that set.

Nondegeneracy enters through the finiteness of the critical locus, which is
`TauCeti.HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero`, and through the
differentiability of `f` on `K`
(`TauCeti.HasNondegenerateCriticalPointsOn.differentiableAt`); the continuity of the gradient is
read off the continuity of `fderiv ℝ f` on `K`, the
gradient being the differential transported by the Riesz isometry. -/
theorem exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K)
    (hfderiv : ContinuousOn (fderiv ℝ f) K) (hM : HasNondegenerateCriticalPointsOn f K) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atTop (𝓝 p) := by
  refine exists_tendsto_atTop hγ hK hmaps (fun _ hy ↦ hM.differentiableAt hy) ?_ ?_
  · rw [gradient_eq_toDual_symm_comp_fderiv]
    exact (toDual ℝ E).symm.continuous.comp_continuousOn hfderiv
  · exact (hM.finite_setOfPred_fderiv_eq_zero hK hfderiv).subset
      fun y hy ↦ ⟨hy.1, gradient_eq_zero_iff.mp hy.2⟩

/-- **A negative gradient trajectory confined to a compact set converges backwards to a critical
point**, provided the critical locus in that set is finite.  Under these compactness, regularity,
and finiteness hypotheses, this is the backward-time counterpart of `exists_tendsto_atTop` and
gives a critical endpoint as `t` tends to `-∞`.
-/
theorem exists_tendsto_atBot
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Iic 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) (hfin : {y ∈ K | ∇ f y = 0}.Finite) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atBot (𝓝 p) := by
  have hgrad_neg : ∀ y : E, ∇ (-f) y = -∇ f y := fun y ↦ gradient_neg
  have hγ_rev' : IsIntegralCurveOn (fun t ↦ γ (-t)) (fun _ x ↦ -∇ (-f) x) (Ici 0) := by
    simpa using hγ.comp_neg_neg_gradient
  have hmaps_rev : MapsTo (fun t ↦ γ (-t)) (Ici 0) K :=
    fun t ht ↦ hmaps (neg_nonpos.mpr (mem_Ici.mp ht))
  have hdiff_neg : ∀ y ∈ K, DifferentiableAt ℝ (-f) y := by
    intro y hy
    simpa only [Pi.neg_apply] using (hdiff y hy).neg
  have hgrad_neg_fun : ∇ (-f) = -∇ f := funext hgrad_neg
  have hgrad_neg_cont : ContinuousOn (∇ (-f)) K := by
    rw [hgrad_neg_fun]
    exact hgrad.neg
  have hfin_neg : {y ∈ K | ∇ (-f) y = 0}.Finite := by
    simpa only [hgrad_neg, neg_eq_zero] using hfin
  obtain ⟨p, hpK, hp, hp_lim⟩ := exists_tendsto_atTop hγ_rev' hK hmaps_rev hdiff_neg
    hgrad_neg_cont hfin_neg
  refine ⟨p, hpK, ?_, ?_⟩
  · simpa only [hgrad_neg, neg_eq_zero] using hp
  · simpa only [Function.comp_def, neg_neg] using hp_lim.comp tendsto_neg_atBot_atTop

/-- **The Morse form of backward convergence.** A negative gradient trajectory confined to a
compact set on which `fderiv ℝ f` is continuous and every critical point is nondegenerate converges
backwards to a critical point in that set.

As in `exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn`, nondegeneracy is used to obtain
finiteness of the critical locus and differentiability of `f` on `K`. -/
theorem exists_tendsto_atBot_of_hasNondegenerateCriticalPointsOn
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Iic 0) K)
    (hfderiv : ContinuousOn (fderiv ℝ f) K) (hM : HasNondegenerateCriticalPointsOn f K) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atBot (𝓝 p) := by
  refine exists_tendsto_atBot hγ hK hmaps (fun _ hy ↦ hM.differentiableAt hy) ?_ ?_
  · rw [gradient_eq_toDual_symm_comp_fderiv]
    exact (toDual ℝ E).symm.continuous.comp_continuousOn hfderiv
  · exact (hM.finite_setOfPred_fderiv_eq_zero hK hfderiv).subset
      fun y hy ↦ ⟨hy.1, gradient_eq_zero_iff.mp hy.2⟩

end IsIntegralCurveOn
