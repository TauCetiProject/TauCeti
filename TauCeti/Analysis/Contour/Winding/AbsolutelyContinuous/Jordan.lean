/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.UnboundedComponent
public import TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Topology.MetricSpace.Arclength.SimpleClosed
import Mathlib.Analysis.Normed.Affine.AddTorsor
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Reparam
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.TangentJump
import TauCeti.Analysis.Contour.Winding.Number.Circle
import TauCeti.Analysis.Contour.Winding.Number.Reverse
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Circle
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.NonzeroDeriv
import TauCeti.MeasureTheory.Function.MetricDerivative.ConstantSpeed
import TauCeti.Topology.JordanCurve.Path

/-!
# The Jordan index theorem and orientation sign for absolutely continuous and rectifiable curves

For a simple closed absolutely continuous curve `γ` on `[a, b]` (`a < b`, `γ a = γ b`,
`InjOn γ (Ico a b)`), the trace `C = γ '' uIcc a b` is a planar Jordan curve. Its complement splits
into two connected components: the bounded inside `Ω = filledHull C \ C` and the unbounded outside
`(filledHull C)ᶜ` (where `windingNumber γ a b` vanishes for any closed AC curve by
`AbsolutelyContinuousOnInterval.windingNumber_eq_zero_of_notMem_filledHull`).

This file defines the canonical orientation sign `TauCeti.Contour.jordanSign γ a b : ℤ` and proves
the **Jordan index theorem**:

1. `jordanSign γ a b ∈ {1, -1}` (`AbsolutelyContinuousOnInterval.jordanSign_eq_one_or_neg_one`), and
2. `windingNumber γ a b z = jordanSign γ a b` for every `z ∈ filledHull C \ C`
   (`AbsolutelyContinuousOnInterval.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff`).

At every interior parameter `t₀ ∈ (a, b)` where `γ` is differentiable with nonzero velocity `v ≠ 0`,
`jordanSign γ a b` identifies the geometric normal orientation: the rotated vector
`(jordanSign γ a b : ℝ) • (I * v)` points strictly into `Ω`, while its negation
`-(jordanSign γ a b : ℝ) • (I * v)` points strictly into `(filledHull C)ᶜ`
(`AbsolutelyContinuousOnInterval.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt`).

We also record the reversal and monotone/antitone reparametrization laws of `jordanSign`, evaluate
`jordanSign (circleMap c R) 0 (2 * π) = 1` for every `R ≠ 0`, and specialize the Jordan index
theorem and continuous reparametrization laws to the arclength parametrization
`naturalParameterization γ (Icc a b) a` of any rectifiable simple closed curve.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.
* R. B. Burckel, *An Introduction to Classical Complex Analysis*, Vol. 1, Chapter IV & Chapter IX.
-/

public section

open Bornology Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.Contour

/-! ### Definition and elementary properties of `jordanSign` -/

open scoped Classical in
/-- The **orientation sign** of a planar curve `γ` on `[a, b]`: equal to `1` (resp. `-1`) when the
bounded inside `filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)` is nonempty and `windingNumber γ a b`
is constantly `1` (resp. `-1`) there, and `0` otherwise.

For a simple closed absolutely continuous curve with `a < b`, the Jordan index theorem proves that
`jordanSign γ a b` is always `1` or `-1` and equals the winding number throughout the inside. -/
noncomputable def jordanSign (γ : ℝ → ℂ) (a b : ℝ) : ℤ :=
  if (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty ∧
      ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = 1 then 1
  else if (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty ∧
      ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = -1 then -1
  else 0

open scoped Classical in
/-- Defining formula for `TauCeti.Contour.jordanSign`. -/
theorem jordanSign_def (γ : ℝ → ℂ) (a b : ℝ) :
    jordanSign γ a b =
      if (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty ∧
          ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = 1 then 1
      else if (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty ∧
          ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = -1 then -1
      else 0 :=
  (rfl)

/-- `jordanSign γ a b = 1` if and only if the bounded inside is nonempty and `windingNumber γ a b`
is constantly `1` on it. -/
@[simp]
theorem jordanSign_eq_one_iff {γ : ℝ → ℂ} {a b : ℝ} :
    jordanSign γ a b = 1 ↔
      (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty ∧
        ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = 1 := by
  classical
  rw [jordanSign_def]
  split_ifs with h₁ h₂
  · exact iff_of_true rfl h₁
  · exact iff_of_false (by decide) h₁
  · exact iff_of_false (by decide) h₁

/-- `jordanSign γ a b = -1` if and only if the bounded inside is nonempty and `windingNumber γ a b`
is constantly `-1` on it. -/
@[simp]
theorem jordanSign_eq_neg_one_iff {γ : ℝ → ℂ} {a b : ℝ} :
    jordanSign γ a b = -1 ↔
      (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty ∧
        ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = -1 := by
  classical
  rw [jordanSign_def]
  split_ifs with h₁ h₂
  · refine iff_of_false (by decide) fun ⟨⟨z, hz⟩, hneg⟩ ↦ ?_
    have heq : (1 : ℂ) = -1 := (h₁.2 z hz).symm.trans (hneg z hz)
    norm_num at heq
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by decide) h₂

/-- If the bounded inside is nonempty and `windingNumber γ a b` is `1` throughout it, then
`jordanSign γ a b = 1`. -/
theorem jordanSign_of_windingNumber_eq_one {γ : ℝ → ℂ} {a b : ℝ}
    (hne : (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty)
    (h : ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = 1) :
    jordanSign γ a b = 1 :=
  jordanSign_eq_one_iff.mpr ⟨hne, h⟩

/-- If the bounded inside is nonempty and `windingNumber γ a b` is `-1` throughout it, then
`jordanSign γ a b = -1`. -/
theorem jordanSign_of_windingNumber_eq_neg_one {γ : ℝ → ℂ} {a b : ℝ}
    (hne : (filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)).Nonempty)
    (h : ∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = -1) :
    jordanSign γ a b = -1 :=
  jordanSign_eq_neg_one_iff.mpr ⟨hne, h⟩

/-- Every value of `jordanSign` belongs to `{1, -1, 0}`. -/
theorem jordanSign_eq_one_or_neg_one_or_zero (γ : ℝ → ℂ) (a b : ℝ) :
    jordanSign γ a b = 1 ∨ jordanSign γ a b = -1 ∨ jordanSign γ a b = 0 := by
  classical
  rw [jordanSign_def]
  split_ifs <;> simp

/-- The absolute value of `jordanSign` never exceeds `1`. -/
theorem abs_jordanSign_le_one (γ : ℝ → ℂ) (a b : ℝ) : |jordanSign γ a b| ≤ 1 := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ a b with h | h | h <;> simp [h]

private theorem jordanSign_eq_of_image_eq_and_windingNumber_eq
    {γ₁ γ₂ : ℝ → ℂ} {a₁ b₁ a₂ b₂ : ℝ}
    (himg : γ₁ '' uIcc a₁ b₁ = γ₂ '' uIcc a₂ b₂)
    (hw : ∀ z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂),
      windingNumber γ₁ a₁ b₁ z = windingNumber γ₂ a₂ b₂ z) :
    jordanSign γ₁ a₁ b₁ = jordanSign γ₂ a₂ b₂ := by
  classical
  simp only [jordanSign_def, himg]
  have h1 : (∀ z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂),
      windingNumber γ₁ a₁ b₁ z = 1) ↔
      ∀ z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂),
        windingNumber γ₂ a₂ b₂ z = 1 :=
    forall₂_congr fun z hz ↦ by rw [hw z hz]
  have h2 : (∀ z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂),
      windingNumber γ₁ a₁ b₁ z = -1) ↔
      ∀ z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂),
        windingNumber γ₂ a₂ b₂ z = -1 :=
    forall₂_congr fun z hz ↦ by rw [hw z hz]
  simp only [h1, h2]

private theorem jordanSign_eq_neg_of_image_eq_and_windingNumber_neg
    {γ₁ γ₂ : ℝ → ℂ} {a₁ b₁ a₂ b₂ : ℝ}
    (himg : γ₁ '' uIcc a₁ b₁ = γ₂ '' uIcc a₂ b₂)
    (hw : ∀ z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂),
      windingNumber γ₁ a₁ b₁ z = -windingNumber γ₂ a₂ b₂ z) :
    jordanSign γ₁ a₁ b₁ = -jordanSign γ₂ a₂ b₂ := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ₂ a₂ b₂ with h₂ | h₂ | h₂
  · rw [h₂]
    obtain ⟨hne, hall⟩ := jordanSign_eq_one_iff.mp h₂
    exact jordanSign_eq_neg_one_iff.mpr ⟨himg ▸ hne, fun z hz ↦ by
      have hz' : z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂) := himg ▸ hz
      rw [hw z hz', hall z hz']⟩
  · rw [h₂, neg_neg]
    obtain ⟨hne, hall⟩ := jordanSign_eq_neg_one_iff.mp h₂
    exact jordanSign_eq_one_iff.mpr ⟨himg ▸ hne, fun z hz ↦ by
      have hz' : z ∈ filledHull (γ₂ '' uIcc a₂ b₂) \ (γ₂ '' uIcc a₂ b₂) := himg ▸ hz
      rw [hw z hz', hall z hz', neg_neg]⟩
  · rw [h₂, neg_zero]
    rcases jordanSign_eq_one_or_neg_one_or_zero γ₁ a₁ b₁ with h₁ | h₁ | h₁
    · exfalso
      obtain ⟨hne, hall⟩ := jordanSign_eq_one_iff.mp h₁
      have h₂' : jordanSign γ₂ a₂ b₂ = -1 := jordanSign_eq_neg_one_iff.mpr
        ⟨himg ▸ hne, fun z hz ↦ neg_eq_iff_eq_neg.mp ((hw z hz).symm.trans (hall z (himg ▸ hz)))⟩
      omega
    · exfalso
      obtain ⟨hne, hall⟩ := jordanSign_eq_neg_one_iff.mp h₁
      have h₂' : jordanSign γ₂ a₂ b₂ = 1 := jordanSign_eq_one_iff.mpr
        ⟨himg ▸ hne, fun z hz ↦ neg_inj.mp ((hw z hz).symm.trans (hall z (himg ▸ hz)))⟩
      omega
    · exact h₁

/-- `jordanSign` depends only on the values of the curve on `uIcc a b`. -/
theorem jordanSign_congr {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} (h : EqOn γ₁ γ₂ (uIcc a b)) :
    jordanSign γ₁ a b = jordanSign γ₂ a b :=
  jordanSign_eq_of_image_eq_and_windingNumber_eq (image_congr h) fun _ _ ↦
    windingNumber_congr_curve (h.mono uIoo_subset_uIcc_self)

private theorem jordanSign_eq_zero_of_windingNumber_eq_zero {γ : ℝ → ℂ} {a b : ℝ}
    (hw : ∀ z, windingNumber γ a b z = 0) : jordanSign γ a b = 0 := by
  rcases jordanSign_eq_one_or_neg_one_or_zero γ a b with h | h | h
  · obtain ⟨⟨z, hz⟩, hall⟩ := jordanSign_eq_one_iff.mp h; simpa [hw z] using hall z hz
  · obtain ⟨⟨z, hz⟩, hall⟩ := jordanSign_eq_neg_one_iff.mp h; simpa [hw z] using hall z hz
  · exact h

/-- On a degenerate interval `[a, a]`, `jordanSign` vanishes. -/
@[simp]
theorem jordanSign_same (γ : ℝ → ℂ) (a : ℝ) : jordanSign γ a a = 0 :=
  jordanSign_eq_zero_of_windingNumber_eq_zero (windingNumber_same γ a)

/-- A constant curve has `jordanSign` equal to `0`. -/
@[simp]
theorem jordanSign_const (c : ℂ) (a b : ℝ) : jordanSign (fun _ ↦ c) a b = 0 :=
  jordanSign_eq_zero_of_windingNumber_eq_zero (windingNumber_const c a b)

private theorem isJordanCurve_uIcc {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) : TauCeti.IsJordanCurve (γ '' uIcc a b) := by
  rw [uIcc_of_le hab.le]
  exact TauCeti.isJordanCurve_image_Icc hab (uIcc_of_le hab.le ▸ hγ.continuousOn) hclosed hinj

/-- Pointwise form of the dichotomy: if two points `p`, `q` off the trace of a simple closed AC
curve have winding numbers differing by `1`, then the winding number is `1` on all of
`filledHull C \ C` with `p` inside and `q` outside, or the reverse with winding number `-1`. -/
private theorem winding_dichotomy_of_points
    {γ : ℝ → ℂ} {a b : ℝ} {p q : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (hp : p ∉ γ '' uIcc a b) (hq : q ∉ γ '' uIcc a b)
    (hdiff : windingNumber γ a b p = windingNumber γ a b q + 1) :
    ((∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = 1) ∧
      p ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) ∧ q ∉ filledHull (γ '' uIcc a b)) ∨
    ((∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = -1) ∧
      q ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) ∧ p ∉ filledHull (γ '' uIcc a b)) := by
  set C := γ '' uIcc a b
  have hC : TauCeti.IsJordanCurve C := isJordanCurve_uIcc hab hγ hclosed hinj
  have hzero_out : ∀ {w : ℂ}, w ∉ filledHull C → windingNumber γ a b w = 0 :=
    hγ.windingNumber_eq_zero_of_notMem_filledHull hclosed
  by_cases hposF : p ∈ filledHull C
  · by_cases hnegF : q ∈ filledHull C
    · exfalso
      have heq := hγ.windingNumber_eq_of_mem_connectedComponentIn hclosed
        (hC.mem_connectedComponentIn_of_mem_filledHull_sdiff ⟨hnegF, hq⟩ ⟨hposF, hp⟩)
      have h10 : (1 : ℂ) = 0 := by
        rw [← add_sub_cancel_left (windingNumber γ a b q) 1,
          ← hdiff, heq, sub_self]
      exact one_ne_zero h10
    · left
      have hw1 : windingNumber γ a b p = 1 := by
        rw [hdiff, hzero_out hnegF, zero_add]
      refine ⟨fun z hz ↦ ?_, ⟨hposF, hp⟩, hnegF⟩
      rw [hγ.windingNumber_eq_of_mem_connectedComponentIn hclosed
        (hC.mem_connectedComponentIn_of_mem_filledHull_sdiff ⟨hposF, hp⟩ hz), hw1]
  · by_cases hnegF : q ∈ filledHull C
    · right
      have hwn1 : windingNumber γ a b q = -1 := by
        rw [hzero_out hposF] at hdiff
        exact eq_neg_of_add_eq_zero_left hdiff.symm
      refine ⟨fun z hz ↦ ?_, ⟨hnegF, hq⟩, hposF⟩
      rw [hγ.windingNumber_eq_of_mem_connectedComponentIn hclosed
        (hC.mem_connectedComponentIn_of_mem_filledHull_sdiff ⟨hnegF, hq⟩ hz), hwn1]
    · exfalso
      rw [hzero_out hposF, hzero_out hnegF, zero_add] at hdiff
      exact zero_ne_one hdiff

/-- Core dichotomy at any regular interior point of a simple closed AC curve: either the left
normal ray enters `filledHull C \ C` with winding number `1` on all of `filledHull C \ C` and the
right normal ray enters `(filledHull C)ᶜ`, or the reverse holds with winding number `-1`. -/
private theorem simple_closed_normal_dichotomy
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0) :
    ((∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = 1) ∧
      ∀ᶠ h : ℝ in 𝓝[>] 0,
        γ t₀ + h • (I * v) ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) ∧
          γ t₀ - h • (I * v) ∉ filledHull (γ '' uIcc a b))
    ∨
    ((∀ z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b), windingNumber γ a b z = -1) ∧
      ∀ᶠ h : ℝ in 𝓝[>] 0,
        γ t₀ - h • (I * v) ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) ∧
          γ t₀ + h • (I * v) ∉ filledHull (γ '' uIcc a b)) := by
  set C := γ '' uIcc a b
  have hC : TauCeti.IsJordanCurve C := isJordanCurve_uIcc hab hγ hclosed hinj
  have hjump := hγ.eventually_windingNumber_add_I_mul_eq_add_one hab hclosed hinj ht₀ hd hv
  have hpointwise := fun {h : ℝ} (hh : γ t₀ + h • (I * v) ∉ γ '' uIcc a b ∧
      γ t₀ - h • (I * v) ∉ γ '' uIcc a b ∧
      windingNumber γ a b (γ t₀ + h • (I * v)) =
        windingNumber γ a b (γ t₀ - h • (I * v)) + 1) ↦
    winding_dichotomy_of_points hab hγ hclosed hinj hh.1 hh.2.1 hh.2.2
  obtain ⟨z₀, hz₀⟩ := hC.nonempty_filledHull_sdiff
  obtain ⟨h₀, hh₀⟩ := hjump.exists
  rcases hpointwise hh₀ with ⟨hall1, -, -⟩ | ⟨halln1, -, -⟩
  · refine Or.inl ⟨hall1, hjump.mono fun h hh ↦ ?_⟩
    rcases hpointwise hh with ⟨-, hmem⟩ | ⟨halln1, -⟩
    · exact hmem
    · exfalso
      have heq : (1 : ℂ) = -1 := (hall1 z₀ hz₀).symm.trans (halln1 z₀ hz₀)
      norm_num at heq
  · refine Or.inr ⟨halln1, hjump.mono fun h hh ↦ ?_⟩
    rcases hpointwise hh with ⟨hall1, -⟩ | ⟨-, hmem⟩
    · exfalso
      have heq : (1 : ℂ) = -1 := (hall1 z₀ hz₀).symm.trans (halln1 z₀ hz₀)
      norm_num at heq
    · exact hmem

end TauCeti.Contour

open TauCeti TauCeti.Contour

/-! ### Reparametrization laws and Jordan index theorem for AC curves -/

namespace AbsolutelyContinuousOnInterval

/-- **Reversing the interval orientation negates `jordanSign`.** -/
theorem jordanSign_symm {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    jordanSign γ b a = -jordanSign γ a b :=
  jordanSign_eq_neg_of_image_eq_and_windingNumber_neg (by rw [uIcc_comm]) fun z hz ↦
    windingNumber_symm (cauchyPVExistsAt_of_avoidance hγ.continuousOn
      (fun t ht heq ↦ hz.2 ⟨t, ht, heq⟩) (hγ.intervalIntegrable_inv_sub_mul_deriv hz.2))

/-- **An increasing absolutely continuous reparametrization onto `[c, d]` preserves
`jordanSign`.** -/
theorem jordanSign_comp_of_monotoneOn
    {γ : ℝ → ℂ} {θ : ℝ → ℝ} {a b c d : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) (ha : θ a = c) (hb : θ b = d) :
    jordanSign (γ ∘ θ) a b = jordanSign γ c d := by
  have hcd : c ≤ d := ha ▸ hb ▸ hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hθc : ContinuousOn θ (Icc a b) := uIcc_of_le hab ▸ hθ.continuousOn
  have himg : (γ ∘ θ) '' uIcc a b = γ '' uIcc c d := by
    rw [image_comp, uIcc_of_le hab, uIcc_of_le hcd, hθc.image_Icc_of_monotoneOn hab hmono, ha, hb]
  exact jordanSign_eq_of_image_eq_and_windingNumber_eq himg fun z hz ↦
    hγ.windingNumber_comp_of_monotoneOn hθ hab hmono ha hb hz.2

/-- **A decreasing absolutely continuous reparametrization onto `[c, d]` negates
`jordanSign`.** -/
theorem jordanSign_comp_of_antitoneOn
    {γ : ℝ → ℂ} {θ : ℝ → ℝ} {a b c d : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hanti : AntitoneOn θ (Icc a b)) (ha : θ a = d) (hb : θ b = c) :
    jordanSign (γ ∘ θ) a b = -jordanSign γ c d := by
  have hcd : c ≤ d := ha ▸ hb ▸ hanti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hθc : ContinuousOn θ (Icc a b) := uIcc_of_le hab ▸ hθ.continuousOn
  have himg : (γ ∘ θ) '' uIcc a b = γ '' uIcc c d := by
    rw [image_comp, uIcc_of_le hab, uIcc_of_le hcd, hθc.image_Icc_of_antitoneOn hab hanti, ha, hb]
  exact jordanSign_eq_neg_of_image_eq_and_windingNumber_neg himg fun z hz ↦
    hγ.windingNumber_comp_of_antitoneOn hθ hab hanti ha hb hz.2

/-- **Affine normalization to `[0, 1]` preserves `jordanSign`**, carrying the orientation of the
original ordered pair `(a, b)`. -/
@[simp]
theorem jordanSign_comp_lineMap
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    jordanSign (γ ∘ AffineMap.lineMap a b) 0 1 = jordanSign γ a b := by
  have hseg : AffineMap.lineMap a b '' Icc (0 : ℝ) 1 = uIcc a b := by
    rw [← segment_eq_image_lineMap, segment_eq_uIcc]
  have himg : (γ ∘ AffineMap.lineMap a b) '' uIcc (0 : ℝ) 1 = γ '' uIcc a b := by
    rw [image_comp, uIcc_of_le (zero_le_one' ℝ), hseg]
  exact jordanSign_eq_of_image_eq_and_windingNumber_eq himg fun z hz ↦
    hγ.windingNumber_comp_lineMap hz.2

/-- **Parameter reflection `t ↦ γ (a + b - t)` on `[a, b]` negates `jordanSign`.** -/
theorem jordanSign_comp_sub
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    jordanSign (fun t ↦ γ (a + b - t)) a b = -jordanSign γ a b := by
  have hθ : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ a + b - t) a b := by
    have heq : (fun t : ℝ ↦ a + b - t) = AffineMap.lineMap (a + b) (a + b - 1) := by
      ext t; simp [AffineMap.lineMap_apply]; ring
    rw [heq]
    exact (lipschitzWith_lineMap _ _).lipschitzOnWith.absolutelyContinuousOnInterval
  rcases le_total a b with hab | hba
  · exact hγ.jordanSign_comp_of_antitoneOn hθ hab
      (fun _ _ _ _ hst ↦ sub_le_sub_left hst _) (by ring) (by ring)
  · have hcomp : AbsolutelyContinuousOnInterval (fun t ↦ γ (a + b - t)) b a :=
      hγ.symm.comp_antitoneOn hθ.symm
        (fun _ _ _ _ hst ↦ sub_le_sub_left hst _)
        (fun t ht ↦ by
          rw [uIcc_of_le hba] at ht ⊢
          exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hanti := hγ.symm.jordanSign_comp_of_antitoneOn hθ.symm hba
      (fun _ _ _ _ hst ↦ sub_le_sub_left hst _) (by ring) (by ring)
    dsimp only [Function.comp_def] at hanti
    rw [hcomp.jordanSign_symm, hanti, hγ.symm.jordanSign_symm, neg_neg]

/-- **Jordan index theorem (orientation sign dichotomy):** for a simple closed absolutely
continuous curve on `[a, b]` (`a < b`), `jordanSign γ a b` is either `1` or `-1`, and equals the
winding number at every point of `filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem jordanSign_eq_one_or_neg_one
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    jordanSign γ a b = 1 ∨ jordanSign γ a b = -1 := by
  have hnonconst : ∃ s ∈ Icc a b, ∃ t ∈ Icc a b, γ s ≠ γ t :=
    ⟨a, ⟨le_rfl, hab.le⟩, (a + b) / 2, ⟨by linarith, by linarith⟩,
      fun heq ↦ (by linarith : a ≠ (a + b) / 2)
        (hinj ⟨le_rfl, hab⟩ ⟨by linarith, by linarith⟩ heq)⟩
  obtain ⟨t₀, ht₀, v, hv, hd⟩ := hγ.exists_mem_Ioo_hasDerivAt_ne_zero hnonconst
  have hC := isJordanCurve_uIcc hab hγ hclosed hinj
  rcases simple_closed_normal_dichotomy hab hγ hclosed hinj ht₀ hd hv with
    ⟨hall1, -⟩ | ⟨halln1, -⟩
  · exact Or.inl (jordanSign_of_windingNumber_eq_one hC.nonempty_filledHull_sdiff hall1)
  · exact Or.inr (jordanSign_of_windingNumber_eq_neg_one hC.nonempty_filledHull_sdiff halln1)

/-- The orientation sign of a simple closed absolutely continuous curve (`a < b`) has unit absolute
value. -/
@[simp]
theorem abs_jordanSign_eq_one
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    |jordanSign γ a b| = 1 := by
  rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> simp [h]

/-- The orientation sign of a simple closed absolutely continuous curve (`a < b`) is nonzero. -/
theorem jordanSign_ne_zero
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    jordanSign γ a b ≠ 0 := by
  rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h <;> omega

/-- **The Jordan index theorem for simple closed absolutely continuous curves:** on the bounded
inside `filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`, `windingNumber γ a b` is constantly equal to
`jordanSign γ a b ∈ {1, -1}`. -/
theorem windingNumber_eq_jordanSign_of_mem_filledHull_sdiff
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (hz : z ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)) :
    windingNumber γ a b z = jordanSign γ a b := by
  rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h | h
  · rw [h, Int.cast_one]
    exact (jordanSign_eq_one_iff.mp h).2 z hz
  · rw [h, Int.cast_neg, Int.cast_one]
    exact (jordanSign_eq_neg_one_iff.mp h).2 z hz

/-- **Geometric normal identification of `jordanSign`:** at any interior parameter `t₀ ∈ (a, b)`
where a simple closed absolutely continuous curve has nonzero derivative `v ≠ 0`, the vector
`(jordanSign γ a b : ℝ) • (I * v)` points into the bounded inside
`filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`, while `-(jordanSign γ a b : ℝ) • (I * v)` points
into the unbounded outside `(filledHull (γ '' uIcc a b))ᶜ`. -/
theorem eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      γ t₀ + h • ((jordanSign γ a b : ℝ) • (I * v)) ∈
        filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) ∧
      γ t₀ - h • ((jordanSign γ a b : ℝ) • (I * v)) ∉ filledHull (γ '' uIcc a b) := by
  have hC := isJordanCurve_uIcc hab hγ hclosed hinj
  rcases simple_closed_normal_dichotomy hab hγ hclosed hinj ht₀ hd hv with
    ⟨hall1, hev⟩ | ⟨halln1, hev⟩
  · rw [jordanSign_of_windingNumber_eq_one hC.nonempty_filledHull_sdiff hall1]
    simpa using hev
  · rw [jordanSign_of_windingNumber_eq_neg_one hC.nonempty_filledHull_sdiff halln1]
    simpa [smul_neg, sub_eq_add_neg] using hev

/-- At any regular interior point `t₀ ∈ (a, b)` (`HasDerivAt γ v t₀`, `v ≠ 0`), a simple closed AC
curve is positively oriented (`jordanSign γ a b = 1`) if and only if the leftward normal `I * v`
points into the bounded inside `filledHull (γ '' uIcc a b) \ (γ '' uIcc a b)`. -/
theorem jordanSign_eq_one_iff_eventually_mem_filledHull_sdiff
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0) :
    jordanSign γ a b = 1 ↔
      ∀ᶠ h : ℝ in 𝓝[>] 0,
        γ t₀ + h • (I * v) ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) := by
  have hev :=
    hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt
      hab hclosed hinj ht₀ hd hv
  constructor
  · intro h1
    rw [h1] at hev
    exact hev.mono fun _ hh ↦ by simpa using hh.1
  · intro hin
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h1 | hn1
    · exact h1
    · exfalso
      rw [hn1] at hev
      obtain ⟨h, hmem, hnot⟩ := (hin.and hev).exists
      have hnot' : γ t₀ + h • (I * v) ∉ filledHull (γ '' uIcc a b) := by
        simpa [smul_neg, sub_eq_add_neg] using hnot.2
      exact hnot' hmem.1

/-- Counterpart of `jordanSign_eq_one_iff_eventually_mem_filledHull_sdiff` for negative orientation
(`jordanSign γ a b = -1`): `-(I * v)` points into the bounded inside. -/
theorem jordanSign_eq_neg_one_iff_eventually_mem_filledHull_sdiff
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0) :
    jordanSign γ a b = -1 ↔
      ∀ᶠ h : ℝ in 𝓝[>] 0,
        γ t₀ - h • (I * v) ∈ filledHull (γ '' uIcc a b) \ (γ '' uIcc a b) := by
  have hev :=
    hγ.eventually_mem_filledHull_sdiff_and_notMem_of_hasDerivAt
      hab hclosed hinj ht₀ hd hv
  constructor
  · intro hn1
    rw [hn1] at hev
    exact hev.mono fun _ hh ↦ by simpa [smul_neg, sub_eq_add_neg] using hh.1
  · intro hin
    rcases hγ.jordanSign_eq_one_or_neg_one hab hclosed hinj with h1 | hn1
    · exfalso
      rw [h1] at hev
      obtain ⟨h, hmem, hnot⟩ := (hin.and hev).exists
      exact (by simpa using hnot.2 : γ t₀ - h • (I * v) ∉ filledHull (γ '' uIcc a b)) hmem.1
    · exact hn1

/-- **Arclength invariance of `jordanSign` for absolutely continuous curves:** for `a ≤ b`,
passing to `naturalParameterization γ (Icc a b) a` on `[0, (eVariationOn γ (Icc a b)).toReal]`
preserves `jordanSign`. -/
theorem jordanSign_naturalParameterization
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a ≤ b) :
    jordanSign (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal = jordanSign γ a b := by
  have hBV : BoundedVariationOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.boundedVariationOn
  have hcont : ContinuousOn γ (Icc a b) := uIcc_of_le hab ▸ hγ.continuousOn
  have himg : naturalParameterization γ (Icc a b) a ''
      uIcc 0 (eVariationOn γ (Icc a b)).toReal = γ '' uIcc a b := by
    rw [uIcc_of_le ENNReal.toReal_nonneg, uIcc_of_le hab,
      hBV.image_naturalParameterization_Icc hcont hab]
  exact jordanSign_eq_of_image_eq_and_windingNumber_eq himg fun z hz ↦
    hγ.windingNumber_naturalParameterization hab (uIcc_of_le hab ▸ hz.2)

end AbsolutelyContinuousOnInterval

/-! ### Concrete evaluation on circles -/

namespace TauCeti.Contour

/-- **The standard circle `circleMap c R` (`R ≠ 0`) on `[0, 2π]` has orientation sign `1`.** -/
@[simp]
theorem jordanSign_circleMap (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    jordanSign (circleMap c R) 0 (2 * Real.pi) = 1 := by
  have hab : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hac : AbsolutelyContinuousOnInterval (circleMap c R) 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_circleMap c R 0 (2 * Real.pi)
  have hclosed : circleMap c R 0 = circleMap c R (2 * Real.pi) := by
    simpa using ((periodic_circleMap c R) 0).symm
  have hinj : InjOn (circleMap c R) (Ico 0 (2 * Real.pi)) :=
    injOn_circleMap_of_abs_sub_le' hR (by linarith)
  have hc_not_trace : c ∉ circleMap c R '' uIcc 0 (2 * Real.pi) := by
    rintro ⟨θ, -, hθ⟩
    exact circleMap_ne_center hR hθ
  have hc_wind : windingNumber (circleMap c R) 0 (2 * Real.pi) c = 1 :=
    windingNumber_circleMap_center_eq_one hR
  have hc_hull : c ∈ filledHull (circleMap c R '' uIcc 0 (2 * Real.pi)) := by
    by_contra hnot
    have h0 := hac.windingNumber_eq_zero_of_notMem_filledHull hclosed hnot
    rw [hc_wind] at h0
    exact one_ne_zero h0
  have heq := hac.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff hab hclosed hinj
    ⟨hc_hull, hc_not_trace⟩
  rw [hc_wind, ← Int.cast_one] at heq
  exact Int.cast_inj.mp heq.symm

/-- **The reversed circle `circleMap c R` (`R ≠ 0`) on `[2π, 0]` has orientation sign `-1`.** -/
@[simp]
theorem jordanSign_circleMap_symm (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    jordanSign (circleMap c R) (2 * Real.pi) 0 = -1 := by
  rw [(absolutelyContinuousOnInterval_circleMap c R 0 (2 * Real.pi)).jordanSign_symm,
    jordanSign_circleMap c hR]

end TauCeti.Contour

/-! ### Arclength specialization and continuous reparametrization laws for rectifiable curves -/

namespace BoundedVariationOn

/-- **Jordan index theorem for rectifiable simple closed curves (orientation sign dichotomy):**
the arclength parametrization `naturalParameterization γ (Icc a b) a` on
`[0, (eVariationOn γ (Icc a b)).toReal]` of a continuous simple closed curve of bounded variation
(`a < b`) has orientation sign `1` or `-1`. -/
theorem jordanSign_naturalParameterization_eq_one_or_neg_one
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    jordanSign (naturalParameterization γ (Icc a b) a) 0 (eVariationOn γ (Icc a b)).toReal = 1 ∨
      jordanSign (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal = -1 :=
  (hγ.absolutelyContinuousOnInterval_naturalParameterization hcont
      hab.le).jordanSign_eq_one_or_neg_one
    (hγ.toReal_eVariationOn_pos_of_injOn_Ioo hab (hinj.mono Ioo_subset_Ico_self))
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab.le hclosed)
    (hγ.injOn_naturalParameterization_Ico hcont hinj hab.le)

/-- **The Jordan index theorem for the arclength parametrization of a rectifiable simple closed
curve:** on `filledHull (γ '' Icc a b) \ (γ '' Icc a b)`, the winding number of
`naturalParameterization γ (Icc a b) a` equals its orientation sign `σ ∈ {1, -1}`. -/
theorem windingNumber_naturalParameterization_eq_jordanSign
    {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ} (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (hz : z ∈ filledHull (γ '' Icc a b) \ (γ '' Icc a b)) :
    windingNumber (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal z =
      jordanSign (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal := by
  have hz' : z ∈ filledHull (naturalParameterization γ (Icc a b) a ''
      uIcc 0 (eVariationOn γ (Icc a b)).toReal) \
      (naturalParameterization γ (Icc a b) a '' uIcc 0 (eVariationOn γ (Icc a b)).toReal) := by
    rwa [uIcc_of_le ENNReal.toReal_nonneg, hγ.image_naturalParameterization_Icc hcont hab.le]
  exact (hγ.absolutelyContinuousOnInterval_naturalParameterization hcont
      hab.le).windingNumber_eq_jordanSign_of_mem_filledHull_sdiff
    (hγ.toReal_eVariationOn_pos_of_injOn_Ioo hab (hinj.mono Ioo_subset_Ico_self))
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab.le hclosed)
    (hγ.injOn_naturalParameterization_Ico hcont hinj hab.le) hz'

/-- **Increasing continuous reparametrizations preserve the arclength orientation sign of a
rectifiable curve.** The reparametrization `φ` need not be absolutely continuous. -/
theorem jordanSign_naturalParameterization_comp_of_monotoneOn
    {γ : ℝ → ℂ} {φ : ℝ → ℝ} {a b c d : ℝ} (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hφm : MonotoneOn φ (Icc c d)) (hφc : φ c = a) (hφd : φ d = b) :
    jordanSign (naturalParameterization (γ ∘ φ) (Icc c d) c) 0
        (eVariationOn (γ ∘ φ) (Icc c d)).toReal =
      jordanSign (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal := by
  have hL : eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ hφm,
      hφ.image_Icc_of_monotoneOn hcd hφm, hφc, hφd]
  rw [hL]
  exact jordanSign_congr (uIcc_of_le ENNReal.toReal_nonneg ▸
    hγ.eqOn_naturalParameterization_comp_of_monotoneOn hcont hcd hφ hφm hφc hφd)

/-- **Decreasing continuous reparametrizations negate the arclength orientation sign of a
rectifiable curve.** The reparametrization `φ` need not be absolutely continuous. -/
theorem jordanSign_naturalParameterization_comp_of_antitoneOn
    {γ : ℝ → ℂ} {φ : ℝ → ℝ} {a b c d : ℝ} (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hcd : c ≤ d) (hφ : ContinuousOn φ (Icc c d))
    (hφm : AntitoneOn φ (Icc c d)) (hφc : φ c = b) (hφd : φ d = a) :
    jordanSign (naturalParameterization (γ ∘ φ) (Icc c d) c) 0
        (eVariationOn (γ ∘ φ) (Icc c d)).toReal =
      -jordanSign (naturalParameterization γ (Icc a b) a) 0
        (eVariationOn γ (Icc a b)).toReal := by
  have hab : a ≤ b := hφc ▸ hφd ▸ hφm (left_mem_Icc.mpr hcd) (right_mem_Icc.mpr hcd) hcd
  have hL : eVariationOn (γ ∘ φ) (Icc c d) = eVariationOn γ (Icc a b) := by
    rw [eVariationOn.comp_eq_of_antitoneOn _ _ hφm,
      hφ.image_Icc_of_antitoneOn hcd hφm, hφc, hφd]
  have hη : AbsolutelyContinuousOnInterval (naturalParameterization γ (Icc a b) a) 0
      (eVariationOn γ (Icc a b)).toReal :=
    hγ.absolutelyContinuousOnInterval_naturalParameterization hcont hab
  rw [hL, jordanSign_congr (uIcc_of_le ENNReal.toReal_nonneg ▸
    hγ.eqOn_naturalParameterization_comp_of_antitoneOn hcont hcd hφ hφm hφc hφd)]
  simpa only [zero_add] using hη.jordanSign_comp_sub

end BoundedVariationOn
