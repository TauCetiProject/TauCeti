/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Identity
public import Mathlib.Analysis.Complex.Basic

/-!
# Canonical meromorphic continuation from a half-plane

`meromorphicContinuation σ f` selects the meromorphic normal form agreeing with `f` on
`σ < re s`, or zero if none exists. Normal form removes the freedom to change values at
isolated points: removable singularities take their limiting values and poles take zero.
This makes continued Dirichlet series canonical without asserting value identities between
arbitrary representatives at poles.

The comparison API first identifies punctured germs everywhere, then reads values where the
representatives are analytic. Multiplying by a function that is analytic without zeros on the
initial half-plane commutes with continuation (`TauCeti.meromorphicContinuation_smul`), whether
or not a continuation exists; this compares Dirichlet series differing by finitely many Euler
factors. The construction uses Mathlib's `toMeromorphicNFOn` and its
local normal-form identity principle. The results allow values in a complex normed space.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → E} {σ : ℝ}

/-- Agreement on a right half-plane determines every punctured meromorphic germ. No
normal-form or continuity assumption on the representatives is needed. -/
theorem eventuallyEq_of_meromorphic_of_eqOn_halfPlane
    (hf : Meromorphic f) (hg : Meromorphic g)
    (hfg : EqOn f g {s | σ < s.re}) (z : ℂ) : f =ᶠ[𝓝[≠] z] g := by
  have hx : σ < ((σ + 1 : ℝ) : ℂ).re := by simp
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : f =ᶠ[𝓝 (((σ + 1 : ℝ) : ℂ))] g := by
    filter_upwards [hopen.mem_nhds hx] with s hs using hfg hs
  exact hf.meromorphicOn.eventuallyEq_of_isPreconnected hg.meromorphicOn
    isPreconnected_univ (mem_univ _) (mem_univ z) (heq.filter_mono nhdsWithin_le_nhds)

/-- Half-plane agreement gives value agreement wherever both meromorphic representatives
are analytic. In particular, this statement makes no assertion at a pole. -/
theorem eq_of_meromorphic_of_eqOn_halfPlane
    (hf : Meromorphic f) (hg : Meromorphic g)
    (hfg : EqOn f g {s | σ < s.re}) {z : ℂ}
    (hfz : AnalyticAt ℂ f z) (hgz : AnalyticAt ℂ g z) : f z = g z := by
  exact (hfz.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hgz.continuousAt |>.mp
    (eventuallyEq_of_meromorphic_of_eqOn_halfPlane hf hg hfg z)).eq_of_nhds

/-- Meromorphic normal forms agreeing on a right half-plane are equal, including their
canonical zero values at poles. -/
theorem eq_of_meromorphicNFOn_of_eqOn_halfPlane
    (hf : MeromorphicNFOn f univ) (hg : MeromorphicNFOn g univ)
    (hfg : EqOn f g {s | σ < s.re}) : f = g := by
  exact funext fun z ↦ hf.eqOn_of_isPreconnected hg isPreconnected_univ (mem_univ 0)
    (eventuallyEq_of_meromorphic_of_eqOn_halfPlane
      (meromorphicOn_univ.mp hf.meromorphicOn)
      (meromorphicOn_univ.mp hg.meromorphicOn) hfg 0) (mem_univ z)

/-- The unique whole-plane meromorphic normal form agreeing with `f` on `σ < re s`,
or zero when no such continuation exists. Existence must be proved separately before
using its agreement with the original function. -/
noncomputable def meromorphicContinuation (σ : ℝ) (f : ℂ → E) : ℂ → E := by
  classical
  exact if h : ∃ g : ℂ → E, MeromorphicNFOn g univ ∧ EqOn g f {s | σ < s.re}
    then h.choose else 0

/-- The canonical continuation has normal form even in the failure case. -/
theorem meromorphicNFOn_meromorphicContinuation (σ : ℝ) (f : ℂ → E) :
    MeromorphicNFOn (meromorphicContinuation σ f) univ := by
  classical
  unfold meromorphicContinuation
  split_ifs with h
  · exact h.choose_spec.1
  · exact analyticOnNhd_const.meromorphicNFOn

/-- When a continuation exists, the canonical continuation agrees with the initial
function on its defining half-plane. -/
theorem meromorphicContinuation_eqOn
    (h : ∃ g : ℂ → E, MeromorphicNFOn g univ ∧ EqOn g f {s | σ < s.re}) :
    EqOn (meromorphicContinuation σ f) f {s | σ < s.re} := by
  classical
  simpa only [meromorphicContinuation, dite_eq_left h] using h.choose_spec.2

/-- A given normal-form continuation identifies the canonical choice. -/
theorem meromorphicContinuation_eq (hg : MeromorphicNFOn g univ)
    (hgf : EqOn g f {s | σ < s.re}) : meromorphicContinuation σ f = g := by
  exact eq_of_meromorphicNFOn_of_eqOn_halfPlane
    (meromorphicNFOn_meromorphicContinuation σ f) hg
    ((meromorphicContinuation_eqOn ⟨g, hg, hgf⟩).trans hgf.symm)

/-- The zero function is its own canonical continuation. -/
@[simp]
theorem meromorphicContinuation_zero (σ : ℝ) :
    meromorphicContinuation σ (0 : ℂ → E) = 0 :=
  meromorphicContinuation_eq analyticOnNhd_const.meromorphicNFOn (fun _ _ ↦ rfl)

/-- If no normal-form continuation exists, the canonical continuation is zero. -/
theorem meromorphicContinuation_of_not_exists
    (h : ¬ ∃ g : ℂ → E, MeromorphicNFOn g univ ∧ EqOn g f {s | σ < s.re}) :
    meromorphicContinuation σ f = 0 := by
  classical
  simp only [meromorphicContinuation, dite_eq_right h]

/-- A meromorphic continuation analytic on the initial half-plane gives the canonical
continuation after conversion to normal form. This is how non-normalized analytic
presentations identify the canonical function. -/
theorem meromorphicContinuation_eq_toMeromorphicNFOn (hg : Meromorphic g)
    (hga : AnalyticOnNhd ℂ g {s | σ < s.re}) (hgf : EqOn g f {s | σ < s.re}) :
    meromorphicContinuation σ f = toMeromorphicNFOn g univ := by
  apply meromorphicContinuation_eq (meromorphicNFOn_toMeromorphicNFOn g univ)
  intro s hs
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hg.meromorphicOn (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr (hga s hs).meromorphicNFAt]
  exact hgf hs

/-- The canonical continuation has the same punctured germs as any meromorphic
continuation analytic on the initial half-plane. -/
theorem meromorphicContinuation_eventuallyEq (hg : Meromorphic g)
    (hga : AnalyticOnNhd ℂ g {s | σ < s.re}) (hgf : EqOn g f {s | σ < s.re}) (z : ℂ) :
    meromorphicContinuation σ f =ᶠ[𝓝[≠] z] g := by
  rw [meromorphicContinuation_eq_toMeromorphicNFOn hg hga hgf]
  exact hg.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)

/-- The canonical continuation recovers the value of any meromorphic continuation
at its analytic points, not only in the initial half-plane. -/
theorem meromorphicContinuation_apply (hg : Meromorphic g)
    (hga : AnalyticOnNhd ℂ g {s | σ < s.re}) (hgf : EqOn g f {s | σ < s.re})
    {z : ℂ} (hgz : AnalyticAt ℂ g z) : meromorphicContinuation σ f z = g z := by
  rw [meromorphicContinuation_eq_toMeromorphicNFOn hg hga hgf,
    toMeromorphicNFOn_eq_toMeromorphicNFAt hg.meromorphicOn (mem_univ z),
    toMeromorphicNFAt_eq_self.mpr hgz.meromorphicNFAt]

/-- Restricting the initial half-plane does not change an existing continuation. -/
theorem meromorphicContinuation_eq_of_le {τ : ℝ} (hστ : σ ≤ τ)
    (h : ∃ g : ℂ → E, MeromorphicNFOn g univ ∧ EqOn g f {s | σ < s.re}) :
    meromorphicContinuation τ f = meromorphicContinuation σ f := by
  apply meromorphicContinuation_eq (meromorphicNFOn_meromorphicContinuation σ f)
  intro s hs
  exact meromorphicContinuation_eqOn h (lt_of_le_of_lt hστ hs)

/-- The canonical continuation only reads `f` on the initial half-plane. -/
theorem meromorphicContinuation_congr (hfg : EqOn f g {s | σ < s.re}) :
    meromorphicContinuation σ f = meromorphicContinuation σ g := by
  by_cases h : ∃ g' : ℂ → E, MeromorphicNFOn g' univ ∧ EqOn g' g {s | σ < s.re}
  · exact meromorphicContinuation_eq (meromorphicNFOn_meromorphicContinuation σ g)
      ((meromorphicContinuation_eqOn h).trans hfg.symm)
  · rw [meromorphicContinuation_of_not_exists h, meromorphicContinuation_of_not_exists]
    exact fun ⟨h', hh', hh'f⟩ ↦ h ⟨h', hh', hh'f.trans hfg⟩

/-- If `f` is analytic on the initial half-plane, so is its canonical continuation. -/
theorem analyticOnNhd_meromorphicContinuation (hf : AnalyticOnNhd ℂ f {s | σ < s.re}) :
    AnalyticOnNhd ℂ (meromorphicContinuation σ f) {s | σ < s.re} := by
  by_cases h : ∃ g : ℂ → E, MeromorphicNFOn g univ ∧ EqOn g f {s | σ < s.re}
  · have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    refine fun s hs ↦ (hf s hs).congr ?_
    filter_upwards [hopen.mem_nhds hs] with z hz using (meromorphicContinuation_eqOn h hz).symm
  · rw [meromorphicContinuation_of_not_exists h]
    exact analyticOnNhd_const

/-- **Continuation commutes with multiplication by a function without zeros.** Let `f` be
analytic on `σ < re s`, and let `c` be meromorphic on the plane, analytic and nonvanishing on
that half-plane. Then `c • f` has a continuation exactly when `f` has one, and the canonical
continuation of `c • f` is the normal form of `c` times that of `f`. When no continuation
exists both sides are zero. -/
theorem meromorphicContinuation_smul {c : ℂ → ℂ} (hc : Meromorphic c)
    (hca : AnalyticOnNhd ℂ c {s | σ < s.re}) (hc0 : ∀ s : ℂ, σ < s.re → c s ≠ 0)
    (hf : AnalyticOnNhd ℂ f {s | σ < s.re}) :
    meromorphicContinuation σ (c • f) =
      toMeromorphicNFOn (c • meromorphicContinuation σ f) univ := by
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  by_cases h : ∃ g : ℂ → E, MeromorphicNFOn g univ ∧ EqOn g f {s | σ < s.re}
  · refine meromorphicContinuation_eq_toMeromorphicNFOn
      (hc.smul (meromorphicOn_univ.mp (meromorphicNFOn_meromorphicContinuation σ f).meromorphicOn))
      (fun s hs ↦ (hca s hs).smul (analyticOnNhd_meromorphicContinuation hf s hs))
      fun s hs ↦ ?_
    rw [Pi.smul_apply', Pi.smul_apply', meromorphicContinuation_eqOn h hs]
  -- Without a continuation of `f`, a continuation `g` of `c • f` would give one of `f`,
  -- namely the normal form of `c⁻¹ • g`, which agrees with `f` on the half-plane.
  rw [meromorphicContinuation_of_not_exists h, smul_zero,
    toMeromorphicNFOn_eq_self.mpr (analyticOnNhd_const.meromorphicNFOn (f := (0 : ℂ → E))),
    meromorphicContinuation_of_not_exists]
  rintro ⟨g, hg, hgf⟩
  have hq : EqOn (c⁻¹ • g) f {s | σ < s.re} := fun s hs ↦ by
    simp [hgf hs, smul_smul, inv_mul_cancel₀ (hc0 s hs)]
  have hqa : AnalyticOnNhd ℂ (c⁻¹ • g) {s | σ < s.re} := fun s hs ↦ (hf s hs).congr (by
    filter_upwards [hopen.mem_nhds hs] with z hz using (hq hz).symm)
  have hqm : Meromorphic (c⁻¹ • g) := hc.inv.smul (meromorphicOn_univ.mp hg.meromorphicOn)
  exact h ⟨meromorphicContinuation σ f, meromorphicNFOn_meromorphicContinuation σ f,
    fun s hs ↦ (meromorphicContinuation_apply hqm hqa hq (hqa s hs)).trans (hq hs)⟩

/-- **Continuation commutes with multiplication by a function without zeros, as germs.** Under
the hypotheses of `meromorphicContinuation_smul`, the canonical continuation of `c • f` has the
punctured germ of `c` times the canonical continuation of `f` at every point. -/
theorem meromorphicContinuation_smul_eventuallyEq {c : ℂ → ℂ} (hc : Meromorphic c)
    (hca : AnalyticOnNhd ℂ c {s | σ < s.re}) (hc0 : ∀ s : ℂ, σ < s.re → c s ≠ 0)
    (hf : AnalyticOnNhd ℂ f {s | σ < s.re}) (z : ℂ) :
    meromorphicContinuation σ (c • f) =ᶠ[𝓝[≠] z] c • meromorphicContinuation σ f := by
  rw [meromorphicContinuation_smul hc hca hc0 hf]
  exact (hc.smul (meromorphicOn_univ.mp (meromorphicNFOn_meromorphicContinuation σ f
    ).meromorphicOn)).meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)

/-- **Continuation commutes with multiplication by a function without zeros, on the initial
half-plane.** Under the hypotheses of `meromorphicContinuation_smul`, the canonical continuation
of `c • f` is `c` times the canonical continuation of `f` at every point of `σ < re s`. -/
theorem meromorphicContinuation_smul_apply {c : ℂ → ℂ} (hc : Meromorphic c)
    (hca : AnalyticOnNhd ℂ c {s | σ < s.re}) (hc0 : ∀ s : ℂ, σ < s.re → c s ≠ 0)
    (hf : AnalyticOnNhd ℂ f {s | σ < s.re}) {s : ℂ} (hs : σ < s.re) :
    meromorphicContinuation σ (c • f) s = c s • meromorphicContinuation σ f s := by
  rw [meromorphicContinuation_smul hc hca hc0 hf, toMeromorphicNFOn_eq_toMeromorphicNFAt
      (hc.smul (meromorphicOn_univ.mp (meromorphicNFOn_meromorphicContinuation σ f
        ).meromorphicOn)).meromorphicOn (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr ((hca s hs).smul
      (analyticOnNhd_meromorphicContinuation hf s hs)).meromorphicNFAt, Pi.smul_apply']

end TauCeti
