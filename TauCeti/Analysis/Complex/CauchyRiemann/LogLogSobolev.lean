/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.LogLogExample
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.Local.Morrey

/-!
# The `log log` example in Sobolev terms

Elliptic bootstrapping for pseudoholomorphic curves turns a `W^{1,p}_loc` solution of the weak
Cauchy-Riemann equation for a `C¹` structure into a `W^{2,p}_loc` one, but only for finite
`p > 2`. The function `f(z) = z² log log (1 / ‖z‖)` (`TauCeti.logLogExample`) shows that the
endpoint `p = ∞` fails. This file states the example in the local Sobolev classes `MemWkpLoc`
and for the weak equation `IsWeakCauchyRiemannOn`, in which the bootstrapping theorem is phrased.

## Main results

* `TauCeti.not_memWkpLoc_two_top_of_not_isBoundedUnder`: a `C¹` map into a finite-dimensional
  space whose classical second derivative is unbounded near a point `z₀` of an open set `Ω` is
  not `W^{2,∞}_loc` on `Ω`.
* `TauCeti.memWkpLoc_one_logLogExample`, `TauCeti.memWkpLoc_one_graph_logLogExample`: `f` and
  its graph `z ↦ (z, f z)` are `W^{1,p}_loc` on the unit disc for every `p`, including `p = ∞`.
* `TauCeti.isWeakCauchyRiemannOn_graph_logLogExample`: the graph is a weak solution, for every
  exponent, of the homogeneous equation for the `C¹` graph structure
  `TauCeti.conjWirtingerGraphStructure f`.
* `TauCeti.not_memWkpLoc_two_top_logLogExample`,
  `TauCeti.not_memWkpLoc_two_top_graph_logLogExample`: neither `f` nor its graph is
  `W^{2,∞}_loc` on any neighbourhood of the origin.

## Implementation notes

The general criterion compares the weak derivative of `u` with the classical one: both are weak
derivatives on `Ω`, so they agree almost everywhere, and `fderiv u` lies in `W^{1,∞}_loc`. Its
precise representative is Lipschitz on a closed ball around `z₀` by the Morrey embedding, and
equals `fderiv u` on the open ball by continuity, so the classical derivative of `fderiv u` is
bounded there.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.4
  (elliptic bootstrapping).
-/

public section

open Complex Filter Metric Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

section General

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Ω : Opens ℂ} {u : ℂ → F} {z₀ : ℂ}

/-- **Unbounded second derivatives rule out `W^{2,∞}_loc`.** A map that is `C¹` on an open set
`Ω` and whose classical second derivative is unbounded near a point `z₀ ∈ Ω` is not in
`W^{2,∞}_loc` on `Ω`. -/
theorem not_memWkpLoc_two_top_of_not_isBoundedUnder (hu : ContDiffOn ℝ 1 u Ω) (hz₀ : z₀ ∈ Ω)
    (hunb : ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] z₀) fun z ↦ ‖fderiv ℝ (fderiv ℝ u) z‖) :
    ¬ MemWkpLoc ∞ Ω 2 u := by
  intro h
  have hloc : LocallyIntegrableOn (fderiv ℝ u) Ω volume :=
    (hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).locallyIntegrableOn
      Ω.isOpen.measurableSet
  obtain ⟨D, hD, hDk⟩ := h.exists_weakFDeriv_of_isOpen
  have hdu : MemWkpLoc ∞ Ω 1 (fderiv ℝ u) := hDk.congr_ae (hD.ae_eq_fderiv hloc
    fun z hz ↦ (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz))
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  have hK : closedBall z₀ (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrΩ
  obtain ⟨C, hC⟩ := hdu.exists_lipschitzOnWith_preciseRepresentative_of_isCompact
    (isCompact_closedBall z₀ (r / 2)) hK
  have heq : EqOn (preciseRepresentative volume (fderiv ℝ u)) (fderiv ℝ u) (ball z₀ (r / 2)) :=
    eqOn_preciseRepresentative_of_continuousOn isOpen_ball
      (hloc.mono_set (ball_subset_closedBall.trans hK)) EventuallyEq.rfl
      ((hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).mono
        (ball_subset_closedBall.trans hK))
  have hlip : LipschitzOnWith C (fderiv ℝ u) (ball z₀ (r / 2)) := fun x hx y hy ↦ by
    rw [← heq hx, ← heq hy]
    exact hC (ball_subset_closedBall hx) (ball_subset_closedBall hy)
  refine hunb (isBoundedUnder_of_eventually_le (a := (C : ℝ)) ?_)
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z₀ (half_pos hr))] with z hz
  exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hz) hlip

end General

section Example

/-- The graph `z ↦ (z, f z)` of the example is `C¹` on the unit disc. -/
private theorem contDiffOn_graph_logLogExample :
    ContDiffOn ℝ 1 (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) (ball 0 1) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.contDiff.comp_contDiffOn
    (contDiffOn_id.prodMk contDiffOn_logLogExample)

/-- **The example is `W^{1,p}_loc` on the unit disc** for every exponent, including `p = ∞`. -/
theorem memWkpLoc_one_logLogExample (p : ℝ≥0∞) :
    MemWkpLoc p (ball 0 1) 1 logLogExample :=
  ContDiffOn.memWkpLoc (Ω := ⟨ball 0 1, isOpen_ball⟩) (by exact_mod_cast contDiffOn_logLogExample)
    subset_rfl

/-- **The graph of the example is `W^{1,p}_loc` on the unit disc** for every exponent, including
`p = ∞`. -/
theorem memWkpLoc_one_graph_logLogExample (p : ℝ≥0∞) :
    MemWkpLoc p (ball 0 1) 1 (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) :=
  ContDiffOn.memWkpLoc (Ω := ⟨ball 0 1, isOpen_ball⟩)
    (by exact_mod_cast contDiffOn_graph_logLogExample) subset_rfl

/-- **The graph of the example is a weak pseudoholomorphic curve.** For every exponent, including
`p = ∞`, the graph `z ↦ (z, f z)` solves the weak homogeneous Cauchy-Riemann equation on the unit
disc for the graph structure `J_f`, which is `C¹` there
(`TauCeti.contDiffOn_conjWirtingerGraphStructure_logLogExample`). -/
theorem isWeakCauchyRiemannOn_graph_logLogExample (p : ℝ≥0∞) :
    IsWeakCauchyRiemannOn p (ball 0 1) (fun _ ↦ conjWirtingerGraphStructure logLogExample)
      (fun _ _ ↦ 0) (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) :=
  isWeakCauchyRiemannOn_of_contDiffOn (Ω := ⟨ball 0 1, isOpen_ball⟩)
    contDiffOn_graph_logLogExample fun z hz ↦ by
      rw [fderiv_graph_I_eq_conjWirtingerGraphStructure
        ((contDiffOn_logLogExample.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt
          one_ne_zero), conjWirtingerGraphStructure_apply_apply, add_neg_cancel]

/-- **The example is not `W^{2,∞}_loc` on any neighbourhood of the origin.** -/
theorem not_memWkpLoc_two_top_logLogExample {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ¬ MemWkpLoc ∞ U 2 logLogExample := fun h ↦
  not_memWkpLoc_two_top_of_not_isBoundedUnder
    (Ω := ⟨interior U ∩ ball 0 1, isOpen_interior.inter isOpen_ball⟩)
    (contDiffOn_logLogExample.mono inter_subset_right)
    ⟨mem_interior_iff_mem_nhds.2 hU, mem_ball_self one_pos⟩
    not_isBoundedUnder_norm_fderiv_fderiv_logLogExample
    (h.mono (inter_subset_left.trans interior_subset))

/-- **The graph of the example is not `W^{2,∞}_loc` on any neighbourhood of the origin.**
Together with `TauCeti.isWeakCauchyRiemannOn_graph_logLogExample`, it is a `W^{1,∞}_loc` weak
solution for a `C¹` structure that is not `W^{2,∞}_loc`, so elliptic bootstrapping fails at
`p = ∞`. -/
theorem not_memWkpLoc_two_top_graph_logLogExample {U : Set ℂ} (hU : U ∈ 𝓝 0) :
    ¬ MemWkpLoc ∞ U 2 (fun z ↦ WithLp.toLp 2 (z, logLogExample z)) := fun h ↦
  not_memWkpLoc_two_top_logLogExample hU
    (h.clm_comp ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ : WithLp 2 (ℂ × ℂ) →L[ℝ] ℂ × ℂ)))

end Example

end TauCeti
