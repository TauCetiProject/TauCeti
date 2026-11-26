/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator.Holomorphic.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.Analysis.Complex.WeaklyHolomorphic
import TauCeti.Analysis.ODE.Propagator.ParameterContinuity

/-!
# Holomorphy of the propagator uniformly in time

Let `E` be a complex Banach space, `U ⊆ ℂ` open, and `P : ℂ → ℝ → E →L[ℂ] E` a family of
coefficients satisfying the hypotheses of `TauCeti.differentiableOn_propagator`: `P z` is
integrable on `[a, b]` for `z ∈ U`, `z ↦ P z r` is holomorphic on `U` for almost every
`r ∈ [a, b]`, and on every compact `K ⊆ U` the coefficients are dominated by one integrable
function. Then for `s ∈ [a, b]` and every compact `J ⊆ [a, b]`, the map
`z ↦ N_{P z}(·, s)` is holomorphic on `U` as a map into the Banach space `C(J, E →L[ℂ] E)` of
continuous functions on `J` with the supremum norm
(`TauCeti.differentiableOn_continuousMap_propagator`).

The proof combines two results. Each evaluation `z ↦ N_{P z}(t, s)` is holomorphic
(`TauCeti.differentiableOn_propagator`), and the evaluations at the points of `J` are continuous
linear maps on `C(J, E →L[ℂ] E)` whose kernels meet only in `0`. The map is continuous into
`C(J, E →L[ℂ] E)` because `(t, z) ↦ N_{P z}(t, s)` is jointly continuous
(`TauCeti.continuousOn_propagator_parameter`) and `J` is compact. A continuous function whose
composites with such a family are holomorphic is holomorphic
(`TauCeti.differentiableOn_of_continuousOn_of_forall_comp`).

## Main results

* `TauCeti.differentiableOn_continuousMap_propagator`: a map `F : ℂ → C(J, E →L[ℂ] E)` that is
  `t ↦ N_{P z}(t, s)` for every `z ∈ U` is holomorphic on `U`.
* `TauCeti.exists_differentiableOn_continuousMap_propagator`: such a map exists.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {P : ℂ → ℝ → E →L[ℂ] E} {U : Set ℂ} {a b s : ℝ} {J : Set ℝ}

/-- **Holomorphy of the propagator uniformly in time.** Under the hypotheses of
`TauCeti.differentiableOn_propagator`, let `s ∈ [a, b]` and let `J ⊆ [a, b]` be compact. A map
`F : ℂ → C(J, E →L[ℂ] E)` with `F z t = N_{P z}(t, s)` for `z ∈ U` and `t ∈ J` is holomorphic on
`U` for the supremum norm on `C(J, E →L[ℂ] E)`. -/
theorem differentiableOn_continuousMap_propagator [CompactSpace J] (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (hJ : J ⊆ Icc a b) {F : ℂ → C(J, E →L[ℂ] E)}
    (hF : ∀ z ∈ U, ∀ t : J, F z t = propagator (P z) t s) :
    DifferentiableOn ℂ F U := by
  refine differentiableOn_of_continuousOn_of_forall_comp (f := F)
    (fun t : J ↦ (ContinuousMap.evalCLM ℂ t : C(J, E →L[ℂ] E) →L[ℂ] E →L[ℂ] E))
    (fun x hx ↦ by ext1 t; simpa using hx t) ?_
    (fun t ↦ (differentiableOn_propagator hU hP hPd hm hs (hJ t.property)).congr fun z hz ↦
      hF z hz t) hU
  -- Continuity: `(z, t) ↦ N_{P z}(t, s)` is jointly continuous and `J` is compact.
  have hjoint := continuousOn_propagator_parameter (P := fun r z ↦ P z r) (U := U) (a := a)
    (b := b) (fun z hz ↦ (hP z hz).aestronglyMeasurable)
    (hPd.mono fun r h hr ↦ (h hr).continuousOn) fun K hKU hK ↦ by
      obtain ⟨m, hmi, hPm⟩ := hm K hKU hK
      exact ⟨m, hmi, fun z hz ↦ hPm.mono fun r h hr ↦ h hr z hz⟩
  refine ContinuousMap.continuousOn_of_continuousOn_uncurry _ ?_
  have hmaps : MapsTo (fun p : ℂ × J ↦ (((p.2 : ℝ), s), p.1)) (U ×ˢ univ)
      ((Icc a b ×ˢ Icc a b) ×ˢ U) := fun p hp ↦ ⟨⟨hJ p.2.property, hs⟩, hp.1⟩
  exact (hjoint.comp (by fun_prop) hmaps).congr fun p hp ↦ hF p.1 hp.1 p.2

/-- Under the hypotheses of `TauCeti.differentiableOn_continuousMap_propagator`, there is a map
`F : ℂ → C(J, E →L[ℂ] E)`, holomorphic on `U`, with `F z t = N_{P z}(t, s)` for `z ∈ U` and
`t ∈ J`. -/
theorem exists_differentiableOn_continuousMap_propagator [CompactSpace J] (hU : IsOpen U)
    (hP : ∀ z ∈ U, IntegrableOn (P z) (Icc a b))
    (hPd : ∀ᵐ r, r ∈ Icc a b → DifferentiableOn ℂ (P · r) U)
    (hm : ∀ K ⊆ U, IsCompact K → ∃ m : ℝ → ℝ, IntegrableOn m (Icc a b) ∧
      ∀ᵐ r, r ∈ Icc a b → ∀ z ∈ K, ‖P z r‖ ≤ m r)
    (hs : s ∈ Icc a b) (hJ : J ⊆ Icc a b) :
    ∃ F : ℂ → C(J, E →L[ℂ] E), (∀ z ∈ U, ∀ t : J, F z t = propagator (P z) t s) ∧
      DifferentiableOn ℂ F U := by
  classical
  let F : ℂ → C(J, E →L[ℂ] E) := fun z ↦ if hz : z ∈ U then
    ⟨fun t ↦ propagator (P z) t s,
      ((continuousOn_propagator_left (hP z hz) hs).mono hJ).domRestrict⟩
    else 0
  have hF : ∀ z ∈ U, ∀ t : J, F z t = propagator (P z) t s := fun z hz t ↦ by
    simp only [F, dite_eq_left hz]
    exact congrFun (ContinuousMap.coe_mk _ _) t
  exact ⟨F, hF, differentiableOn_continuousMap_propagator hU hP hPd hm hs hJ hF⟩

end TauCeti
