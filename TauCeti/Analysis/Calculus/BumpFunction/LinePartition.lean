/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Smooth partitions of unity on the line with two end pieces

A smooth partition of unity on `ℝ` that splits a function into pieces near finitely many times
and two pieces near `-∞` and `+∞` is how estimates for operators along the line are localized:
the pieces near finite times see a local estimate, the end pieces see the behaviour at `±∞`.

Given a neighbourhood `S s` of every time `s` and `1 ≤ T₀`, this file builds a finite smooth
partition of unity `∑ᵢ ψᵢ = 1` on `ℝ` by functions with bounded values and derivatives, whose
derivatives vanish off `(-(T₀ + 1), T₀ + 1)`, made of one function vanishing on `[-T₀, ∞)`, one
vanishing on `(-∞, T₀]`, and functions `ψ (inr s)` vanishing off `S s ∩ (-(T₀ + 1), T₀ + 1)`
(`TauCeti.exists_contDiff_finset_sum_eq_one_of_mem_nhds`). The two end pieces split the remainder
`1 - ∑ᵢ χᵢ` of a finite partition of unity near `[-T₀, T₀]` by `Real.smoothTransition`
(`TauCeti.exists_contDiff_add_add_finset_sum_eq_one`).
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

/-- **The two end pieces of a partition of unity on the line.** Let `∑ᵢ χᵢ` be a finite sum of
nonnegative smooth functions, supported in `(-T, T)`, at most one everywhere and equal to one on
`[-T₀, T₀]`, where `1 ≤ T₀ < T`. Then `1 - ∑ᵢ χᵢ` splits as `ρbot + ρtop` into smooth functions
with values in `[0, 1]`, locally constant off `(-T, T)`, with `ρbot` vanishing on `[-T₀, ∞)` and
`ρtop` on `(-∞, T₀]`. -/
theorem exists_contDiff_add_add_finset_sum_eq_one {κ : Type*} (t : Finset κ) (χ : κ → ℝ → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hχ0 : ∀ i x, 0 ≤ χ i x) (hχle : ∀ x, ∑ i ∈ t, χ i x ≤ 1)
    {T₀ T : ℝ} (hT₀ : 1 ≤ T₀) (hT₀T : T₀ < T) (hχK : ∀ x ∈ Icc (-T₀) T₀, ∑ i ∈ t, χ i x = 1)
    (hχT : ∀ i, tsupport (χ i) ⊆ Ioo (-T) T) :
    ∃ ρbot ρtop : ℝ → ℝ, ContDiff ℝ ∞ ρbot ∧ ContDiff ℝ ∞ ρtop ∧
      (∀ x, ρbot x + ρtop x + ∑ i ∈ t, χ i x = 1) ∧ (∀ x, |ρbot x| ≤ 1) ∧ (∀ x, |ρtop x| ≤ 1) ∧
      (∀ x ∉ Ioo (-T) T, deriv ρbot x = 0) ∧ (∀ x ∉ Ioo (-T) T, deriv ρtop x = 0) ∧
      (∀ x, -T₀ ≤ x → ρbot x = 0) ∧ (∀ x, x ≤ T₀ → ρtop x = 0) := by
  set θ := Real.smoothTransition
  set χm : ℝ → ℝ := fun x ↦ ∑ i ∈ t, χ i x
  have hχm : ContDiff ℝ ∞ χm := ContDiff.sum fun i _ ↦ hχ i
  have hχm0 (x : ℝ) : 0 ≤ 1 - χm x := sub_nonneg.2 (hχle x)
  have hχm1 (x : ℝ) : 1 - χm x ≤ 1 := sub_le_self _ (Finset.sum_nonneg fun i _ ↦ hχ0 i x)
  -- Off `(-T, T)`, `θ` is locally constant and `∑ᵢ χᵢ` vanishes nearby.
  have hloc (x : ℝ) (hx : x ∉ Ioo (-T) T) :
      ∃ a : ℝ, θ =ᶠ[𝓝 x] (fun _ ↦ a) ∧ χm =ᶠ[𝓝 x] 0 := by
    have hχx : χm =ᶠ[𝓝 x] 0 := (Filter.eventually_all_finset t).2
        (fun i _ ↦ notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hχT i h)) |>.mono
      fun y hy ↦ Finset.sum_eq_zero hy
    rcases not_and_or.1 hx with hx | hx
    · refine ⟨0, (eventually_lt_nhds (show x < 0 by linarith [not_lt.1 hx])).mono fun y hy ↦
        Real.smoothTransition.zero_of_nonpos hy.le, hχx⟩
    · refine ⟨1, (eventually_gt_nhds (show 1 < x by linarith [not_lt.1 hx])).mono fun y hy ↦
        Real.smoothTransition.one_of_one_le hy.le, hχx⟩
  refine ⟨fun x ↦ (1 - θ x) * (1 - χm x), fun x ↦ θ x * (1 - χm x),
    (contDiff_const.sub Real.smoothTransition.contDiff).mul (contDiff_const.sub hχm),
    Real.smoothTransition.contDiff.mul (contDiff_const.sub hχm), fun x ↦ by ring,
    fun x ↦ ?_, fun x ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [abs_of_nonneg (mul_nonneg (sub_nonneg.2 (Real.smoothTransition.le_one x)) (hχm0 x))]
    nlinarith [Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x, hχm0 x, hχm1 x]
  · rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg x) (hχm0 x))]
    nlinarith [Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x, hχm0 x, hχm1 x]
  · obtain ⟨a, hθ, hχx⟩ := hloc x hx
    have h : (fun y ↦ (1 - θ y) * (1 - χm y)) =ᶠ[𝓝 x] fun _ ↦ (1 - a) * 1 := by
      filter_upwards [hθ, hχx] with y h₁ h₂
      simp only [h₁, h₂, Pi.zero_apply, sub_zero]
    rw [h.deriv_eq]
    exact deriv_const _ _
  · obtain ⟨a, hθ, hχx⟩ := hloc x hx
    have h : (fun y ↦ θ y * (1 - χm y)) =ᶠ[𝓝 x] fun _ ↦ a * 1 := by
      filter_upwards [hθ, hχx] with y h₁ h₂
      simp only [h₁, h₂, Pi.zero_apply, sub_zero]
    rw [h.deriv_eq]
    exact deriv_const _ _
  · rcases le_or_gt 1 x with h | h
    · simp [θ, Real.smoothTransition.one_of_one_le h]
    · simp [χm, hχK x ⟨hx, by linarith⟩]
  · rcases le_or_gt x 0 with h | h
    · simp [θ, Real.smoothTransition.zero_of_nonpos h]
    · simp [χm, hχK x ⟨by linarith, hx⟩]

/-- **A partition of unity on the line adapted to local data.** Given a neighbourhood `S s` of
every time `s` and `1 ≤ T₀`, there is a finite smooth partition of unity `∑ᵢ ψᵢ = 1` on `ℝ`, by
functions with bounded values and derivatives, whose derivatives vanish off
`(-(T₀ + 1), T₀ + 1)`, made of one function vanishing on `[-T₀, ∞)`, one vanishing on
`(-∞, T₀]`, and functions `ψ (inr s)` vanishing off `S s ∩ (-(T₀ + 1), T₀ + 1)`. -/
theorem exists_contDiff_finset_sum_eq_one_of_mem_nhds (S : ℝ → Set ℝ) (hS : ∀ s, S s ∈ 𝓝 s)
    {T₀ : ℝ} (hT₀ : 1 ≤ T₀) :
    ∃ (t : Finset (Bool ⊕ ℝ)) (ψ : Bool ⊕ ℝ → ℝ → ℝ), (∀ i, ContDiff ℝ ∞ (ψ i)) ∧
      (∀ i, ∃ C, ∀ x, ‖ψ i x‖ ≤ C) ∧ (∀ i, ∃ C, ∀ x, ‖deriv (ψ i) x‖ ≤ C) ∧
      (∀ x, ∑ i ∈ t, ψ i x = 1) ∧ (∀ i, ∀ s ∉ Ioo (-(T₀ + 1)) (T₀ + 1), deriv (ψ i) s = 0) ∧
      (∀ s, -T₀ ≤ s → ψ (.inl false) s = 0) ∧ (∀ s, s ≤ T₀ → ψ (.inl true) s = 0) ∧
      ∀ i s, s ∉ S i ∩ Ioo (-(T₀ + 1)) (T₀ + 1) → ψ (.inr i) s = 0 := by
  obtain ⟨t, χ, hχ, hχ0, hχle, hχK⟩ :=
    (isCompact_Icc (a := -T₀) (b := T₀)).exists_contDiff_tsupport_subset_finset_sum_eq_one
      (U := fun s₀ ↦ interior (S s₀) ∩ Ioo (-(T₀ + 1)) (T₀ + 1))
      (fun _ ↦ isOpen_interior.inter isOpen_Ioo) fun x hx ↦ mem_iUnion.2
        ⟨x, mem_interior_iff_mem_nhds.2 (hS x), by linarith [hx.1], by linarith [hx.2]⟩
  have hχT (i : ℝ) : tsupport (χ i) ⊆ Ioo (-(T₀ + 1)) (T₀ + 1) :=
    (hχ i).2.2.trans inter_subset_right
  obtain ⟨ρb, ρt, hρb, hρt, hsum, hρb1, hρt1, hρb', hρt', hρb0, hρt0⟩ :=
    exists_contDiff_add_add_finset_sum_eq_one t χ (fun i ↦ (hχ i).1) hχ0 hχle hT₀
      (by linarith) hχK hχT
  -- The pieces, indexed by `Bool ⊕ ℝ`: the two ends and the pieces near `[-T₀, T₀]`.
  let ψ : Bool ⊕ ℝ → ℝ → ℝ := Sum.elim (fun b ↦ bif b then ρt else ρb) χ
  have hψ : ∀ i, ContDiff ℝ ∞ (ψ i) := by
    rintro ((_ | _) | i)
    exacts [hρb, hρt, (hχ i).1]
  have hd : ∀ i, ∀ s ∉ Ioo (-(T₀ + 1)) (T₀ + 1), deriv (ψ i) s = 0 := by
    rintro ((_ | _) | i) s hs
    exacts [hρb' s hs, hρt' s hs, deriv_of_notMem_tsupport fun h ↦ hs (hχT i h)]
  have h₀ : ∀ i, ∃ C, ∀ x, ‖ψ i x‖ ≤ C := by
    rintro ((_ | _) | i)
    · exact ⟨1, fun x ↦ (Real.norm_eq_abs _).trans_le (hρb1 x)⟩
    · exact ⟨1, fun x ↦ (Real.norm_eq_abs _).trans_le (hρt1 x)⟩
    · exact (hχ i).1.continuous.bounded_above_of_compact_support (hχ i).2.1
  -- The derivatives are continuous and vanish off a compact interval, hence are bounded.
  have h₁ (i : Bool ⊕ ℝ) : ∃ C, ∀ x, ‖deriv (ψ i) x‖ ≤ C :=
    ((hψ i).continuous_deriv (by simp)).bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := -(T₀ + 1)) (b := T₀ + 1)) fun s hs ↦
        hd i s fun h ↦ hs (Ioo_subset_Icc_self h))
  refine ⟨Finset.univ.disjSum t, ψ, hψ, h₀, h₁, fun x ↦ ?_, hd, hρb0, hρt0,
    fun i s hs ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hs ⟨interior_subset ((hχ i).2.2 h).1,
      hχT i h⟩⟩
  simp only [Finset.sum_disjSum, Fintype.sum_bool, ψ, Sum.elim_inl, Sum.elim_inr, Bool.cond_true,
    Bool.cond_false]
  linarith [hsum x]

end TauCeti
