/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.ODE.Gronwall.TwoSided

/-!
# ODE uniqueness on relative neighborhoods

Two solutions of a locally Lipschitz vector field with a common value agree near that time
within an order-connected parameter set. Derivatives are taken within the parameter set,
so the initial time may be a closed endpoint. No completeness of the phase space is needed.
A C¹ vector field supplies the local Lipschitz hypothesis; equality then extends throughout
any preconnected real parameter set.

## Main results

* `TauCeti.ODE_solution_unique_of_eventually_nhdsWithin`: local uniqueness with a uniform
  state-space Lipschitz constant on a neighborhood of the common phase.
* `ContDiffAt.ode_eventuallyEq_nhdsWithin`: C¹ local uniqueness.
* `IsPreconnected.ode_eqOn`: locally Lipschitz uniqueness on a preconnected parameter set.
* `IsPreconnected.ode_eqOn_of_contDiffAt`: the C¹ specialization.

## References

* `Mathlib.Analysis.ODE.ExistUnique` for local Lipschitz uniqueness.
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemmas 6.8 and 6.10:
  closed-endpoint ODE uniqueness is an analytic input to reduced-geodesic and variation
  uniqueness there.
* Public formalizations: [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : ℝ × E → E} {I : Set ℝ} {f g : ℝ → E} {t0 : ℝ}

/-- Local uniqueness within an order-connected parameter set, with derivatives within that
set. The Lipschitz bound is uniform in time but only compares states in each time slice. -/
theorem TauCeti.ODE_solution_unique_of_eventually_nhdsWithin {K : ℝ≥0} {s : Set (ℝ × E)}
    (hs : s ∈ 𝓝 (t0, f t0))
    (hv : ∀ t, LipschitzOnWith K (fun x ↦ V (t, x)) {x | (t, x) ∈ s})
    (hI : Set.OrdConnected I) (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt g (V (t, g t)) I t) :
    f =ᶠ[𝓝[I] t0] g := by
  have hfc := (hf.self_of_nhdsWithin ht0).continuousWithinAt
  have hgc := (hg.self_of_nhdsWithin ht0).continuousWithinAt
  have hfQ : ∀ᶠ t in 𝓝[I] t0, (t, f t) ∈ s :=
    (continuousWithinAt_id.prodMk hfc).preimage_mem_nhdsWithin hs
  have hgQ : ∀ᶠ t in 𝓝[I] t0, (t, g t) ∈ s := by
    apply (continuousWithinAt_id.prodMk hgc).preimage_mem_nhdsWithin
    simpa only [heq, Function.id_def] using hs
  obtain ⟨ε, hε, hdata⟩ := Metric.mem_nhdsWithin_iff.mp (hf.and (hg.and (hfQ.and hgQ)))
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds t0 hε),
    self_mem_nhdsWithin] with t ht htI
  have hsub : Set.uIcc t0 t ⊆ Metric.ball t0 ε ∩ I :=
    ((convex_ball t0 ε).ordConnected.inter hI).uIcc_subset
      ⟨Metric.mem_ball_self hε, ht0⟩ ⟨ht, htI⟩
  have hd := fun r (hr : r ∈ Set.uIcc t0 t) ↦ hdata (hsub hr)
  have hderiv : ∀ r ∈ Set.uIcc t0 t,
      HasDerivWithinAt (fun u ↦ f u - g u) (V (r, f r) - V (r, g r)) (Set.uIcc t0 t) r :=
    fun r hr ↦ ((hd r hr).1.sub (hd r hr).2.1).mono fun _ hx ↦ (hsub hx).2
  have hbound : ∀ r ∈ Set.uIcc t0 t,
      ‖V (r, f r) - V (r, g r)‖ ≤ K * ‖f r - g r‖ + 0 := by
    intro r hr
    simpa only [dist_eq_norm, add_zero] using
      (hv r).dist_le_mul _ (hd r hr).2.2.1 _ (hd r hr).2.2.2
  have hnorm := TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le
    Set.left_mem_uIcc hderiv (δ := 0) (by simp only [heq, sub_self, norm_zero, le_refl])
    hbound t Set.right_mem_uIcc
  simpa only [gronwallBound_ε0_δ0, norm_le_zero_iff, sub_eq_zero] using hnorm

/-- Solutions of a C¹ vector field with the same value have the same relative germ,
including at a closed endpoint of the parameter set. Only smoothness at the common phase
is required. -/
theorem ContDiffAt.ode_eventuallyEq_nhdsWithin
    (hV : ContDiffAt ℝ 1 V (t0, f t0)) (hI : Set.OrdConnected I)
    (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt g (V (t, g t)) I t) :
    f =ᶠ[𝓝[I] t0] g := by
  obtain ⟨K, s, hs, hL⟩ := hV.exists_lipschitzOnWith
  have hLip : ∀ t, LipschitzOnWith K (fun x ↦ V (t, x)) {x | (t, x) ∈ s} := by
    intro t x hx y hy
    simpa only [Prod.edist_eq, edist_self, zero_max] using hL hx hy
  exact TauCeti.ODE_solution_unique_of_eventually_nhdsWithin hs hLip hI ht0 heq hf hg

/-- Two solutions agree throughout a preconnected parameter set if they agree once and
the field has a uniform state-space Lipschitz bound near each phase of the first solution.
The neighborhood and Lipschitz constant may depend on the phase. -/
theorem IsPreconnected.ode_eqOn (hI : IsPreconnected I)
    (hV : ∀ t ∈ I, ∃ (K : ℝ≥0) (s : Set (ℝ × E)), s ∈ 𝓝 (t, f t) ∧
      ∀ r, LipschitzOnWith K (fun x ↦ V (r, x)) {x | (r, x) ∈ s})
    (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ t ∈ I, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ t ∈ I, HasDerivWithinAt g (V (t, g t)) I t) : Set.EqOn f g I := by
  have hfc : ContinuousOn f I := fun t ht ↦ (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g I := fun t ht ↦ (hg t ht).continuousWithinAt
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
  let A : Set I := {t | f t = g t}
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨K, s, hs, hLip⟩ := hV t t.property
    have hlocal := TauCeti.ODE_solution_unique_of_eventually_nhdsWithin hs hLip hI.ordConnected
      t.property ht (eventually_nhdsWithin_of_forall hf) (eventually_nhdsWithin_of_forall hg)
    exact (eventually_nhds_subtype_iff I t (fun r ↦ f r = g r)).mpr hlocal
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t0, ht0⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ A := by rw [hAll]; trivial
  exact hm

/-- Two solutions of a vector field that is C¹ along the first solution agree on a
preconnected parameter set if they have one common value, even at a closed endpoint. -/
theorem IsPreconnected.ode_eqOn_of_contDiffAt (hI : IsPreconnected I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ 1 V (t, f t))
    (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ t ∈ I, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ t ∈ I, HasDerivWithinAt g (V (t, g t)) I t) : Set.EqOn f g I := by
  apply hI.ode_eqOn (fun t ht ↦ ?_) ht0 heq hf hg
  obtain ⟨K, s, hs, hL⟩ := (hV t ht).exists_lipschitzOnWith
  refine ⟨K, s, hs, fun r x hx y hy ↦ ?_⟩
  simpa only [Prod.edist_eq, edist_self, zero_max] using hL hx hy
