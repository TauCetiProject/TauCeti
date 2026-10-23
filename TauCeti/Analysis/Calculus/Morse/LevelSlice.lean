/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Stable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Level slices of connecting gradient trajectories

A negative-gradient trajectory joining distinct limiting points crosses every intermediate
value of the defining function exactly once. Thus an intermediate level provides a
canonical time origin for each parametrized connecting trajectory, a useful slice when forming
Morse trajectory spaces modulo time translation.

The argument needs differentiability along the orbit and continuity of the defining function
at the limiting endpoints. It does not require global regularity of the gradient: a hypothetical
plateau would force a stationary interval, and hence a periodic orbit, which is impossible for a
nonconstant negative-gradient trajectory.

The level-slice construction follows the trajectory-space viewpoint of Audin--Damian,
*Morse Theory and Floer Homology*, Chapter 2.
-/

public section

open Filter Function InnerProductSpace Set Topology
open scoped Gradient

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q x : E}

/-- On a nonconstant negative-gradient orbit, the defining function strictly decreases with time. -/
theorem IsNegativeGradient.orbit_strictAnti_of_nonconstant
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hnonconst : ∃ t, φ t x ≠ x) :
    StrictAnti (fun t : ℝ ↦ f (φ t x)) := by
  have hanti := hφ.orbit_antitone x hf
  apply hanti.strictAnti_of_injective
  intro a b hab
  by_contra hne
  wlog hablt : a < b generalizing a b
  · exact this hab.symm (Ne.symm hne)
      (lt_of_le_of_ne (le_of_not_gt hablt) (Ne.symm hne))
  have hval : ∀ t ∈ Ioo a b, f (φ t x) = f (φ a x) := by
    intro t ht
    apply le_antisymm (hanti ht.1.le)
    rw [hab]
    exact hanti ht.2.le
  have hgrad : ∀ t ∈ Ioo a b, ∇ f (φ t x) = 0 := by
    intro t ht
    apply TauCeti.IsIntegralCurve.gradient_eq_zero_of_eventually_const_value
      (hφ.isIntegralCurve x) (hf t)
    exact Filter.Eventually.mono (isOpen_Ioo.mem_nhds ht) fun u hu ↦ hval u hu
  have hderiv : ∀ t ∈ Ioo a b, deriv (fun u ↦ φ u x) t = 0 := by
    intro t ht
    simpa only [hgrad t ht, neg_zero] using (hφ.isIntegralCurve x t).deriv
  have hcurve : ∀ u v, u ∈ Ioo a b → v ∈ Ioo a b → φ u x = φ v x := by
    intro u v hu hv
    apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun t _ ↦ (hφ.isIntegralCurve x t).differentiableAt.differentiableWithinAt)
      hderiv hu hv
  let u : ℝ := (2 * a + b) / 3
  let v : ℝ := (a + 2 * b) / 3
  have hu : u ∈ Ioo a b := by dsimp [u]; constructor <;> linarith
  have hv : v ∈ Ioo a b := by dsimp [v]; constructor <;> linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hperiod : Periodic (fun t ↦ φ t x) (v - u) := by
    intro t
    have hfix : φ (v - u) x = x := by
      have heq := hcurve u v hu hv
      have heq' := congrArg (φ (-u)) heq
      simpa only [← φ.map_add, neg_add_cancel, φ.map_zero_apply,
        sub_eq_add_neg, add_comm v (-u)] using heq'.symm
    simp only [φ.map_add, hfix]
  have hconst := TauCeti.IsIntegralCurve.eq_of_periodic_neg_gradient
    (hφ.isIntegralCurve x) hf (sub_pos.mpr huv) hperiod
  obtain ⟨t, ht⟩ := hnonconst
  exact ht (by simpa only [φ.map_zero_apply] using hconst t 0)

/-- On a connecting orbit with distinct endpoints, the defining function strictly decreases
with time. In particular no two times on that orbit have the same value. -/
theorem IsNegativeGradient.orbit_strictAnti_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hpq : p ≠ q) (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    StrictAnti (fun t : ℝ ↦ f (φ t x)) := by
  apply hφ.orbit_strictAnti_of_nonconstant hf
  by_contra hnonconst
  have horbit : ∀ t, φ t x = x := by
    intro t
    by_contra ht
    exact hnonconst ⟨t, ht⟩
  have hxp : x = p := tendsto_nhds_unique tendsto_const_nhds (by
    simpa only [horbit] using (mem_unstableSet.mp hx.1))
  have hxq : x = q := tendsto_nhds_unique tendsto_const_nhds (by
    simpa only [horbit] using (mem_stableSet.mp hx.2))
  exact hpq (hxp.symm.trans hxq)

/-- A connecting negative-gradient trajectory crosses each value strictly between its limiting
endpoint values at exactly one time. The unique time gives a canonical representative of its
time-translation orbit on that level. -/
theorem IsNegativeGradient.existsUnique_time_value_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q)
    {c : ℝ} (hc : f q < c ∧ c < f p) :
    ∃! t : ℝ, f (φ t x) = c := by
  have hcont : Continuous (fun t : ℝ ↦ f (φ t x)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp' (f := fun u : ℝ ↦ φ u x) (hf t).continuousAt
      ((φ.continuous continuous_id continuous_const :
        Continuous (fun u : ℝ ↦ φ u x)).continuousAt)
  have hbot : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_unstableSet.mp hx.1)
  have htop : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f q)) :=
    hfq.tendsto.comp (mem_stableSet.mp hx.2)
  obtain ⟨t, ht⟩ := intermediate_value_univ₂_eventually₂ continuous_const hcont
    (hbot.eventually (eventually_gt_nhds hc.2) |>.mono fun _ h ↦ h.le)
    (htop.eventually (eventually_lt_nhds hc.1) |>.mono fun _ h ↦ h.le)
  have hpq : p ≠ q := by
    intro hpq
    simp only [hpq] at hc
    exact (lt_asymm hc.1 hc.2)
  exact ⟨t, ht.symm, fun u hu ↦
    (hφ.orbit_strictAnti_of_mem_unstableSet_inter_stableSet hf hpq hx).injective
      (hu.trans ht)⟩

end Flow
