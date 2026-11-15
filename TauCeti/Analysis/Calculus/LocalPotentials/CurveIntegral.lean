/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LocalPotentials.PathIntegral
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Agreement of `localPotentialIntegral` with `curveIntegral` along `C¹` paths

When the coefficient space `F` is complete and `γ : Path a b` has a `C¹` extension to `[0, 1]`,
both `localPotentialIntegral φ γ` (defined by summing potential differences over a subdivision into
local potential balls) and Mathlib's Bochner curve integral `∫ᶜ x in γ, φ x` are available.

We prove:

* `TauCeti.HasLocalPotentials.curveIntegrable`: integrability of a covector field with local
  potentials along any `C¹` path in its domain, without finite-dimensionality or completeness
  hypotheses.
* `TauCeti.curveIntegral_eq_sub_of_hasFDerivAt`: the fundamental theorem of calculus for
  `curveIntegral` along a `C¹` path in any set carrying an ambient primitive of a continuous
  covector field.
* `TauCeti.HasLocalPotentials.localPotentialIntegral_eq_curveIntegral`: for any `C¹` path in the
  domain of `hφ : HasLocalPotentials s φ`, `localPotentialIntegral φ γ = ∫ᶜ x in γ, φ x`.
-/

public section

open Set Metric MeasureTheory unitInterval
open scoped Topology Interval

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {φ : E → E →L[ℝ] F}

private theorem continuousOn_curveIntegralFun {a b : E} {γ : Path a b}
    (hφ : ContinuousOn φ s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγ_mem : ∀ t, γ t ∈ s) :
    ContinuousOn (curveIntegralFun φ γ) I := by
  simp only [funext (curveIntegralFun_def φ γ)]
  refine ContinuousOn.clm_apply ?_ (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl)
  exact hφ.comp γ.continuous_extend.continuousOn fun t ht ↦
    (γ.extend_extends' ⟨t, ht⟩).symm ▸ hγ_mem ⟨t, ht⟩

/-- A covector field with local potentials on `s` is curve-integrable along every `C¹` path in
`s`. -/
theorem HasLocalPotentials.curveIntegrable (hφ : HasLocalPotentials s φ) {a b : E} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγ_mem : ∀ t, γ t ∈ s) :
    CurveIntegrable φ γ :=
  hφ.continuousOn.curveIntegrable_of_contDiffOn hγ hγ_mem

section CompleteSpace

variable [CompleteSpace F]

/-- Subinterval fundamental theorem of calculus for `curveIntegralFun` along a `C¹` path on any
subinterval `[u, v] ⊆ I` whose image lies in a set `u_set` carrying a primitive `g` of `φ`. -/
private theorem integral_curveIntegralFun_eq_sub {u_set : Set E} {g : E → F}
    {a b : E} {γ : Path a b} {u v : I} (huv : u ≤ v)
    (hφ_cont : ContinuousOn φ u_set) (hγ : ContDiffOn ℝ 1 γ.extend I)
    (hγ_sub : ∀ t ∈ Icc u v, γ t ∈ u_set) (hg : ∀ x ∈ u_set, HasFDerivAt g (φ x) x) :
    (∫ t in (u : ℝ)..(v : ℝ), curveIntegralFun φ γ t) = g (γ v) - g (γ u) := by
  have hIcc_sub : Icc (u : ℝ) (v : ℝ) ⊆ I := fun t ht ↦
    ⟨(unitInterval.nonneg u).trans ht.1, ht.2.trans (unitInterval.le_one v)⟩
  have hmaps : MapsTo γ.extend (Icc (u : ℝ) (v : ℝ)) u_set := fun t ht ↦
    (γ.extend_extends' ⟨t, hIcc_sub ht⟩).symm ▸ hγ_sub ⟨t, hIcc_sub ht⟩ ⟨ht.1, ht.2⟩
  have hg_u : ContinuousOn g u_set := fun z hz ↦ (hg z hz).continuousAt.continuousWithinAt
  have hg_cont : ContinuousOn (g ∘ γ.extend) (Icc (u : ℝ) (v : ℝ)) :=
    hg_u.comp γ.continuous_extend.continuousOn hmaps
  have hfun_cont : ContinuousOn (curveIntegralFun φ γ) (Icc (u : ℝ) (v : ℝ)) := by
    have hωγ : ContinuousOn (fun t ↦ φ (γ.extend t)) (Icc (u : ℝ) (v : ℝ)) :=
      hφ_cont.comp γ.continuous_extend.continuousOn hmaps
    have hdγ : ContinuousOn (derivWithin γ.extend I) (Icc (u : ℝ) (v : ℝ)) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).mono hIcc_sub
    simp only [funext (curveIntegralFun_def φ γ)]
    exact hωγ.clm_apply hdγ
  have hderiv (t : ℝ) (ht : t ∈ Ioo (u : ℝ) (v : ℝ)) :
      HasDerivAt (g ∘ γ.extend) (curveIntegralFun φ γ t) t := by
    have ht0 : 0 < t := (unitInterval.nonneg u).trans_lt ht.1
    have ht1 : t < 1 := ht.2.trans_le (unitInterval.le_one v)
    have ht_nhds : I ∈ 𝓝 t := Icc_mem_nhds ht0 ht1
    have hγ_diff : DifferentiableAt ℝ γ.extend t :=
      (hγ.differentiableOn one_ne_zero t ⟨ht0.le, ht1.le⟩).differentiableAt ht_nhds
    have hcomp := (hg (γ.extend t) (hmaps ⟨ht.1.le, ht.2.le⟩)).comp_hasDerivAt t hγ_diff.hasDerivAt
    rwa [curveIntegralFun_def, derivWithin_of_mem_nhds ht_nhds]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hg_cont hderiv
    (hfun_cont.intervalIntegrable_of_Icc huv)]
  simp only [Function.comp_apply, γ.extend_extends']

/-- Fundamental theorem of calculus for `curveIntegral`: if `φ` is continuous on `s` and admits an
ambient primitive `g` on `s`, then along any `C¹` path `γ : Path a b` in `s`,
`∫ᶜ x in γ, φ x = g b - g a`. -/
theorem curveIntegral_eq_sub_of_hasFDerivAt {g : E → F} {a b : E} {γ : Path a b}
    (hφ : ContinuousOn φ s) (hγ : ContDiffOn ℝ 1 γ.extend I)
    (hγ_mem : ∀ t, γ t ∈ s) (hg : ∀ x ∈ s, HasFDerivAt g (φ x) x) :
    ∫ᶜ x in γ, φ x = g b - g a := by
  rw [curveIntegral_def]
  have heq := integral_curveIntegralFun_eq_sub (u := 0) (v := 1) zero_le_one hφ hγ
    (fun t _ ↦ hγ_mem t) hg
  simpa using heq

/-- Along any `C¹` path in `s`, `localPotentialIntegral φ γ` agrees with Mathlib's Bochner curve
integral `∫ᶜ x in γ, φ x` when `F` is complete. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_curveIntegral
    (hφ : HasLocalPotentials s φ) {a b : E} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγ_mem : ∀ t, γ t ∈ s) :
    localPotentialIntegral φ γ = ∫ᶜ x in γ, φ x := by
  obtain ⟨n, t, c, r, g, ht_mono, ht0, htn, -, hrs, hmaps, -, hg⟩ :=
    hφ.exists_monotone_ball_subdivision γ hγ_mem
  rw [localPotentialIntegral_eq_sum_sub ht_mono ht0 htn (fun _ ↦ isOpen_ball) hmaps hg,
    curveIntegral_def]
  have hcont_all : ContinuousOn (curveIntegralFun φ γ) I :=
    continuousOn_curveIntegralFun hφ.continuousOn hγ hγ_mem
  have hint (k : ℕ) (_ : k < n) :
      IntervalIntegrable (curveIntegralFun φ γ) volume (t k : ℝ) (t (k + 1) : ℝ) := by
    have hle : (t k : ℝ) ≤ (t (k + 1) : ℝ) := ht_mono (Nat.le_succ k)
    refine (hcont_all.mono ?_).intervalIntegrable_of_Icc hle
    exact fun u hu ↦ ⟨(unitInterval.nonneg _).trans hu.1, hu.2.trans (unitInterval.le_one _)⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ht0' : (t 0 : ℝ) = 0 := congrArg Subtype.val ht0
  have htn' : (t n : ℝ) = 1 := congrArg Subtype.val htn
  rw [ht0', htn'] at hsum
  rw [← hsum,
    ← Fin.sum_univ_eq_sum_range (fun k ↦ ∫ x in (t k : ℝ)..(t (k + 1) : ℝ), curveIntegralFun φ γ x)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact (integral_curveIntegralFun_eq_sub (u := t k) (v := t (k + 1))
    (ht_mono (Nat.le_succ k)) (hφ.continuousOn.mono (hrs k)) hγ
    (hmaps k) (hg k)).symm

end CompleteSpace

end TauCeti
