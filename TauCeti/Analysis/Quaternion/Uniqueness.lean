/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Quaternion.Analytic

/-!
# Uniqueness principle for Fueter regular functions

Because every left or right Fueter regular function on an open set `s ⊆ ℍ` is real analytic on `s`
(`TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`), the real-analytic
identity principle (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) applies to both left and
right Fueter regular functions on preconnected open sets. On a preconnected open set `s ⊆ ℍ`, two
left (or right) Fueter regular functions `f, g : ℍ → ℍ` agree on all of `s` as soon as any of the
following equivalent local conditions holds:

* `f =ᶠ[𝓝 q₀] g` at some point `q₀ ∈ s`;
* `f` and `g` agree on an open set `U` whose intersection `s ∩ U` is nonempty;
* all iterated real Fréchet derivatives `iteratedFDeriv ℝ n f q₀` and `iteratedFDeriv ℝ n g q₀`
  agree at some point `q₀ ∈ s`.

Unlike holomorphic functions of one complex variable
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure`), vanishing on a set every point of which
is an accumulation point of that set does not suffice in four real dimensions: the slice-holomorphic
map `q ↦ t + i x` is both left and right Fueter regular on all of `ℍ` and vanishes identically on
the `j`–`k` plane `{q | q.re = 0 ∧ q.imI = 0}` (every point of which is an accumulation point of
that plane), yet takes value `1` at `1`
(`TauCeti.exists_leftFueterOn_and_rightFueterOn_eqOn_zero_accPt_ne_zero`).

## Main declarations

* `TauCeti.LeftFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero`,
  `TauCeti.RightFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero`,
  `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_eventuallyEq`: uniqueness on preconnected open
  sets from germ agreement at one point.
* `TauCeti.LeftFueterOn.eqOn_zero_of_preconnected_of_isOpen`,
  `TauCeti.RightFueterOn.eqOn_zero_of_preconnected_of_isOpen`,
  `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_isOpen`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_isOpen`: uniqueness on preconnected open sets from
  agreement on an open set meeting `s`.
* `TauCeti.LeftFueterOn.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.RightFueterOn.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq`: uniqueness on
  preconnected open sets from agreement of all iterated real Fréchet derivatives at one point.
* `TauCeti.exists_leftFueterOn_and_rightFueterOn_eqOn_zero_accPt_ne_zero`: a nonzero function both
  left and right Fueter regular on `ℍ` whose zero set contains a nonempty plane of accumulation
  points.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, remark after Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Quaternion Filter Metric Set Topology

namespace TauCeti

section IdentityPrinciple

variable {f g : ℍ → ℍ} {s U : Set ℍ} {q₀ : ℍ}

/-- If a left Fueter regular function on a preconnected open set `s` vanishes on a neighbourhood of
a point `q₀ ∈ s`, then it vanishes on all of `s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s) (hq₀ : q₀ ∈ s)
    (hf₀ : f =ᶠ[𝓝 q₀] 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hq₀ hf₀

/-- If a right Fueter regular function on a preconnected open set `s` vanishes on a neighbourhood
of a point `q₀ ∈ s`, then it vanishes on all of `s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s) (hq₀ : q₀ ∈ s)
    (hf₀ : f =ᶠ[𝓝 q₀] 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hq₀ hf₀

/-- **Uniqueness principle for left Fueter regular functions (germ form).** Two left Fueter regular
functions on a preconnected open set `s` that agree on a neighbourhood of a point `q₀ ∈ s` agree on
all of `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc hq₀ hfg

/-- **Uniqueness principle for right Fueter regular functions (germ form).** Two right Fueter
regular functions on a preconnected open set `s` that agree on a neighbourhood of a point `q₀ ∈ s`
agree on all of `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_eventuallyEq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc hq₀ hfg

/-- If a left Fueter regular function on a preconnected open set `s` vanishes on an open set `U`
meeting `s`, then it vanishes on all of `s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_isOpen
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s) (hU : IsOpen U)
    (hne : (s ∩ U).Nonempty) (hfU : EqOn f 0 U) : EqOn f 0 s :=
  let ⟨_, hqs, hqU⟩ := hne
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hc hqs
    (hfU.eventuallyEq_of_mem (hU.mem_nhds hqU))

/-- If a right Fueter regular function on a preconnected open set `s` vanishes on an open set `U`
meeting `s`, then it vanishes on all of `s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_isOpen
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s) (hU : IsOpen U)
    (hne : (s ∩ U).Nonempty) (hfU : EqOn f 0 U) : EqOn f 0 s :=
  let ⟨_, hqs, hqU⟩ := hne
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hc hqs
    (hfU.eventuallyEq_of_mem (hU.mem_nhds hqU))

/-- **Uniqueness principle for left Fueter regular functions.** Two left Fueter regular functions
on a preconnected open set `s` that agree on an open set `U` meeting `s` agree on all of `s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_isOpen
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hU : IsOpen U) (hne : (s ∩ U).Nonempty) (hfg : EqOn f g U) : EqOn f g s :=
  let ⟨_, hqs, hqU⟩ := hne
  hf.eqOn_of_preconnected_of_eventuallyEq hg hs hc hqs (hfg.eventuallyEq_of_mem (hU.mem_nhds hqU))

/-- **Uniqueness principle for right Fueter regular functions.** Two right Fueter regular functions
on a preconnected open set `s` that agree on an open set `U` meeting `s` agree on all of `s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_isOpen
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hU : IsOpen U) (hne : (s ∩ U).Nonempty) (hfg : EqOn f g U) : EqOn f g s :=
  let ⟨_, hqs, hqU⟩ := hne
  hf.eqOn_of_preconnected_of_eventuallyEq hg hs hc hqs (hfg.eventuallyEq_of_mem (hU.mem_nhds hqU))

/-- A left Fueter regular function on a preconnected open set `s` vanishes on `s` once all of its
iterated real Fréchet derivatives vanish at a single point `q₀ ∈ s`. -/
theorem LeftFueterOn.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s) (hq₀ : q₀ ∈ s)
    (h : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ h

/-- A right Fueter regular function on a preconnected open set `s` vanishes on `s` once all of its
iterated real Fréchet derivatives vanish at a single point `q₀ ∈ s`. -/
theorem RightFueterOn.eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s) (hq₀ : q₀ ∈ s)
    (h : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ h

/-- Two left Fueter regular functions on a preconnected open set `s` agree on `s` once all of their
iterated real Fréchet derivatives agree at a single point `q₀ ∈ s`. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (h : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ h

/-- Two right Fueter regular functions on a preconnected open set `s` agree on `s` once all of
their iterated real Fréchet derivatives agree at a single point `q₀ ∈ s`. -/
theorem RightFueterOn.eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hq₀ : q₀ ∈ s) (h : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ h

end IdentityPrinciple

private theorem accPt_setOf_re_eq_zero_and_imI_eq_zero {q : ℍ} (hq : q.re = 0 ∧ q.imI = 0) :
    AccPt q (𝓟 {x : ℍ | x.re = 0 ∧ x.imI = 0}) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨q + (ε / 2) • ⟨0, 0, 1, 0⟩, ⟨hball ?_, ?_⟩, ?_⟩
  · have hnorm : ‖(⟨0, 0, 1, 0⟩ : ℍ)‖ = 1 := by
      rw [norm_eq_sqrt_real_inner, inner_self, normSq_def']
      norm_num
    rw [mem_ball, dist_self_add_left, norm_smul, hnorm, Real.norm_of_nonneg (by positivity)]
    linarith
  · simp [hq.1, hq.2]
  · intro heq
    have himJ := congrArg QuaternionAlgebra.imJ heq
    simp only [QuaternionAlgebra.imJ_add, QuaternionAlgebra.imJ_smul, smul_eq_mul, mul_one] at himJ
    linarith

/-- Unlike in one complex variable (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure`),
vanishing on a set of accumulation points does not force a Fueter regular function to vanish:
`q ↦ t + i x` is both left and right Fueter regular on all of `ℍ` and vanishes identically on the
`j`–`k` plane `{q | q.re = 0 ∧ q.imI = 0}`, every point of which is an accumulation point of that
plane, yet takes value `1 ≠ 0` at `1`. -/
theorem exists_leftFueterOn_and_rightFueterOn_eqOn_zero_accPt_ne_zero :
    ∃ (f : ℍ → ℍ) (Z : Set ℍ),
      LeftFueterOn f univ ∧ RightFueterOn f univ ∧ Z.Nonempty ∧
        (∀ q ∈ Z, AccPt q (𝓟 Z)) ∧ EqOn f 0 Z ∧ f 1 ≠ 0 := by
  refine ⟨fun q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ), {q | q.re = 0 ∧ q.imI = 0},
    leftFueterOn_coeComplex_comp isOpen_univ differentiableOn_id,
    rightFueterOn_coeComplex_comp isOpen_univ differentiableOn_id,
    ⟨0, by simp⟩, fun _ hq ↦ accPt_setOf_re_eq_zero_and_imI_eq_zero hq, ?_, ?_⟩
  · rintro q ⟨hre, him⟩
    have h0 : (⟨q.re, q.imI⟩ : ℂ) = 0 := by apply Complex.ext <;> simp [hre, him]
    simp [h0]
  · intro h1
    simpa using congrArg QuaternionAlgebra.re h1

end TauCeti
