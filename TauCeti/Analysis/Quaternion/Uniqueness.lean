/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Quaternion.Regularity

/-!
# Uniqueness principles for Fueter regular functions

Because left and right Fueter regular functions on an open set `s ⊆ ℍ` are real analytic on `s`
(`TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`), the real-analytic
identity principle yields uniqueness on every preconnected open set `s`:

* two left (or right) Fueter regular functions on `s` that agree on a neighbourhood of a point
  `q₀ ∈ s`, or on any nonempty open subset `u ⊆ s`, agree throughout `s`;
* equivalently, two left (or right) Fueter regular functions on `s` whose iterated real Fréchet
  derivatives `iteratedFDeriv ℝ n · q₀` agree for every `n : ℕ` at one point `q₀ ∈ s` agree
  throughout `s`.

In contrast with holomorphic functions of one complex variable, agreement on a set with
accumulation points does **not** suffice in quaternionic analysis: the nonconstant function
`q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ)` (`t + i x`) is both left and right Fueter regular on all of `ℍ`
and vanishes on the real two-plane `{q : ℍ | q.re = 0 ∧ q.imI = 0}`, every point of which is an
accumulation point of that plane, yet takes the value `1` at `1`.

## Main declarations

* `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_eventuallyEq`: uniqueness on preconnected open
  sets from local agreement near a point.
* `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_isOpen`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_isOpen`: uniqueness on preconnected open sets from
  agreement on a nonempty open subset.
* `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq`: uniqueness on
  preconnected open sets from equality of all iterated real Fréchet derivatives at a point.
* `TauCeti.exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt_ne_zero`: an accumulating
  zero set does not force a left or right Fueter regular function to vanish.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, remark after Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter Metric Quaternion Set Topology

namespace TauCeti

variable {f g : ℍ → ℍ} {s u : Set ℍ} {q₀ : ℍ}

/-! ### Uniqueness from local agreement or open subsets -/

/-- A left Fueter regular function on a preconnected open set `s` that vanishes on a neighbourhood
of a point `q₀ ∈ s` vanishes on `s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (h0 : f =ᶠ[𝓝 q₀] 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hq₀ h0

/-- A right Fueter regular function on a preconnected open set `s` that vanishes on a neighbourhood
of a point `q₀ ∈ s` vanishes on `s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (h0 : f =ᶠ[𝓝 q₀] 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hq₀ h0

/-- Two left Fueter regular functions on a preconnected open set `s` that agree on a neighbourhood
of a point `q₀ ∈ s` agree on `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc hq₀ hfg

/-- Two right Fueter regular functions on a preconnected open set `s` that agree on a neighbourhood
of a point `q₀ ∈ s` agree on `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_eventuallyEq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc hq₀ hfg

/-- A left Fueter regular function on a preconnected open set `s` that vanishes on a nonempty open
subset `u ⊆ s` vanishes throughout `s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_isOpen
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hu : IsOpen u) (hne : u.Nonempty) (hus : u ⊆ s) (h0 : EqOn f 0 u) : EqOn f 0 s := by
  obtain ⟨q₀, hq₀⟩ := hne
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hc (hus hq₀)
    (eventually_of_mem (hu.mem_nhds hq₀) fun x hx ↦ h0 hx)

/-- A right Fueter regular function on a preconnected open set `s` that vanishes on a nonempty open
subset `u ⊆ s` vanishes throughout `s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_isOpen
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hu : IsOpen u) (hne : u.Nonempty) (hus : u ⊆ s) (h0 : EqOn f 0 u) : EqOn f 0 s := by
  obtain ⟨q₀, hq₀⟩ := hne
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hc (hus hq₀)
    (eventually_of_mem (hu.mem_nhds hq₀) fun x hx ↦ h0 hx)

/-- **Uniqueness principle for left Fueter regular functions.** Two left Fueter regular functions
on a preconnected open set `s` that agree on a nonempty open subset `u ⊆ s` agree on `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_isOpen
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hu : IsOpen u) (hne : u.Nonempty) (hus : u ⊆ s) (hfg : EqOn f g u) : EqOn f g s := by
  obtain ⟨q₀, hq₀⟩ := hne
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hs hc (hus hq₀)
    (eventually_of_mem (hu.mem_nhds hq₀) fun x hx ↦ hfg hx)

/-- **Uniqueness principle for right Fueter regular functions.** Two right Fueter regular functions
on a preconnected open set `s` that agree on a nonempty open subset `u ⊆ s` agree on `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_isOpen
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hu : IsOpen u) (hne : u.Nonempty) (hus : u ⊆ s) (hfg : EqOn f g u) : EqOn f g s := by
  obtain ⟨q₀, hq₀⟩ := hne
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hs hc (hus hq₀)
    (eventually_of_mem (hu.mem_nhds hq₀) fun x hx ↦ hfg hx)

/-! ### Uniqueness from iterated derivatives at a point -/

/-- A left Fueter regular function on a preconnected open set `s` all of whose iterated real
Fréchet derivatives vanish at one point `q₀ ∈ s` vanishes throughout `s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (h0 : ∀ n, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ h0

/-- A right Fueter regular function on a preconnected open set `s` all of whose iterated real
Fréchet derivatives vanish at one point `q₀ ∈ s` vanishes throughout `s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (h0 : ∀ n, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ h0

/-- Two left Fueter regular functions on a preconnected open set `s` whose iterated real Fréchet
derivatives all agree at one point `q₀ ∈ s` agree throughout `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : ∀ n, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ hfg

/-- Two right Fueter regular functions on a preconnected open set `s` whose iterated real Fréchet
derivatives all agree at one point `q₀ ∈ s` agree throughout `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : ∀ n, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ hfg

/-! ### Accumulating zero sets do not force vanishing -/

/-- Every point of the real two-plane `{q : ℍ | q.re = 0 ∧ q.imI = 0}` is an accumulation point of
that plane. -/
theorem accPt_setOf_re_eq_zero_and_imI_eq_zero {q : ℍ} (hq : q.re = 0 ∧ q.imI = 0) :
    AccPt q (𝓟 {x : ℍ | x.re = 0 ∧ x.imI = 0}) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  let u : ℍ := ⟨0, 0, 1, 0⟩
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, inner_self, normSq_def']
    simp [u]
  refine ⟨q + (ε / 2) • u, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_self_add_left, norm_smul, hu_norm, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  · simp [u, hq.1, hq.2]
  · intro heq
    have hj := congrArg QuaternionAlgebra.imJ heq
    simp [u] at hj
    linarith

/-- In quaternionic analysis, an accumulating zero set does not force a regular function to vanish:
`q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ)` (`t + i x`) is both left and right Fueter regular on `univ`, and
vanishes on the real two-plane `{q : ℍ | q.re = 0 ∧ q.imI = 0}` where every point is an
accumulation point, yet takes the value `1 ≠ 0` at `1`. -/
theorem exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt_ne_zero :
    ∃ (f : ℍ → ℍ) (Z : Set ℍ),
      LeftFueterOn f univ ∧ RightFueterOn f univ ∧
      Z.Nonempty ∧ (∀ q ∈ Z, AccPt q (𝓟 Z)) ∧ EqOn f 0 Z ∧ f 1 ≠ 0 := by
  refine ⟨fun q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ), {q : ℍ | q.re = 0 ∧ q.imI = 0},
    leftFueterOn_iff.2 fun _ _ ↦ leftFueterAt_coeComplex_comp differentiableAt_id,
    rightFueterOn_iff.2 fun _ _ ↦ rightFueterAt_coeComplex_comp differentiableAt_id,
    ⟨0, by simp⟩, fun _ hq ↦ accPt_setOf_re_eq_zero_and_imI_eq_zero hq,
    fun q hq ↦ ?_, ?_⟩
  · ext <;> simp [hq.1, hq.2]
  · intro h1
    simpa using congrArg QuaternionAlgebra.re h1

end TauCeti
