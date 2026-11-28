/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Quantization cutoffs

The quantization `Op(a, χ)` of a symbol on the Lie algebra `𝔤` of a Lie group integrates the
representation against the density `χ a^∨`, carried to the group by the exponential map, where
`a^∨` is the inverse Fourier transform of `a` and `χ` is a cutoff near `0`. The cutoff restricts the
integral to a neighbourhood `U` of `0` on which the exponential map is well behaved.

This file defines the admissible cutoffs: a **quantization cutoff in `U`** is a smooth, compactly
supported, even function `χ : E → ℝ` with values in `[0, 1]`, supported in `U` and equal to `1`
near `0`. Evenness is what makes the quantization of a real symbol self-adjoint.

## Main definitions

* `TauCeti.IsQuantizationCutoff U χ`: `χ` is a quantization cutoff in `U`.

## Main statements

* `TauCeti.IsQuantizationCutoff.mem_nhds`: only a neighbourhood of `0` carries a cutoff.
* `ContDiffBump.isQuantizationCutoff`, `TauCeti.exists_isQuantizationCutoff`: a smooth bump centred
  at `0` is a cutoff, so every neighbourhood of `0` in a finite-dimensional space carries one.
* `TauCeti.IsQuantizationCutoff.mono`: a cutoff in `U` is a cutoff in every `U' ⊇ U`.
* `TauCeti.IsQuantizationCutoff.mul`, `TauCeti.convex_setOf_isQuantizationCutoff`: products and
  convex combinations of cutoffs are cutoffs.
* `TauCeti.isQuantizationCutoff_iff_of_subsingleton`: on the zero space the only cutoff is the
  constant `1`, and only when `0 ∈ U`.
* `TauCeti.not_isQuantizationCutoff_one`: on a nonzero space the constant `1` is not a cutoff.

## References

* P. D. Nelson, A. Venkatesh, *The orbit method and analysis of automorphic forms*, Acta Math.
  226 (2021), §2.2.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U U' : Set E} {χ χ₁ χ₂ : E → ℝ}

/-- A **quantization cutoff in `U`**: a smooth, compactly supported, even function with values in
`[0, 1]`, whose topological support lies in `U` and which equals `1` near `0`. These are the
cutoffs against which a symbol on a Lie algebra is quantized (Nelson–Venkatesh, §2.2). -/
structure IsQuantizationCutoff (U : Set E) (χ : E → ℝ) : Prop where
  /-- A cutoff is smooth. -/
  contDiff : ContDiff ℝ ∞ χ
  /-- A cutoff has compact support. -/
  hasCompactSupport : HasCompactSupport χ
  /-- A cutoff in `U` is supported in `U`. -/
  tsupport_subset : tsupport χ ⊆ U
  /-- A cutoff is even. -/
  even : χ.Even
  /-- A cutoff takes values in `[0, 1]`. -/
  mem_Icc : ∀ x, χ x ∈ Icc (0 : ℝ) 1
  /-- A cutoff equals `1` near `0`. -/
  eventuallyEq_one : χ =ᶠ[𝓝 0] 1

namespace IsQuantizationCutoff

/-- A cutoff is continuous. -/
theorem continuous (h : IsQuantizationCutoff U χ) : Continuous χ :=
  h.contDiff.continuous

/-- A cutoff is nonnegative. -/
theorem nonneg (h : IsQuantizationCutoff U χ) (x : E) : 0 ≤ χ x :=
  (h.mem_Icc x).1

/-- A cutoff is at most `1`. -/
theorem le_one (h : IsQuantizationCutoff U χ) (x : E) : χ x ≤ 1 :=
  (h.mem_Icc x).2

/-- A cutoff has absolute value at most `1`. -/
theorem abs_le_one (h : IsQuantizationCutoff U χ) (x : E) : |χ x| ≤ 1 := by
  rw [abs_of_nonneg (h.nonneg x)]
  exact h.le_one x

/-- A cutoff takes the value `1` at `0`. -/
theorem apply_zero (h : IsQuantizationCutoff U χ) : χ 0 = 1 :=
  h.eventuallyEq_one.eq_of_nhds

/-- A set carrying a cutoff is a neighbourhood of `0`: the cutoff is `1`, hence nonzero, near `0`,
and its support lies in the set. -/
theorem mem_nhds (h : IsQuantizationCutoff U χ) : U ∈ 𝓝 (0 : E) := by
  refine mem_of_superset h.eventuallyEq_one fun x (hx : χ x = 1) ↦ h.tsupport_subset ?_
  exact subset_tsupport χ (by simp [hx])

/-- A set carrying a cutoff contains `0`. -/
theorem zero_mem (h : IsQuantizationCutoff U χ) : (0 : E) ∈ U :=
  mem_of_mem_nhds h.mem_nhds

/-- A cutoff in `U` is a cutoff in every larger set. -/
theorem mono (h : IsQuantizationCutoff U χ) (hU : U ⊆ U') : IsQuantizationCutoff U' χ where
  __ := h
  tsupport_subset := h.tsupport_subset.trans hU

/-- The product of a cutoff in `U` and a cutoff in `U'` is a cutoff in `U ∩ U'`. -/
theorem mul (h₁ : IsQuantizationCutoff U χ₁) (h₂ : IsQuantizationCutoff U' χ₂) :
    IsQuantizationCutoff (U ∩ U') (χ₁ * χ₂) where
  contDiff := h₁.contDiff.mul h₂.contDiff
  hasCompactSupport := h₁.hasCompactSupport.mul_right
  tsupport_subset := subset_inter ((tsupport_mul_subset_left).trans h₁.tsupport_subset)
    ((tsupport_mul_subset_right).trans h₂.tsupport_subset)
  even := h₁.even.mul_even h₂.even
  mem_Icc x := ⟨mul_nonneg (h₁.nonneg x) (h₂.nonneg x),
    by rw [Pi.mul_apply]; nlinarith [h₁.nonneg x, h₁.le_one x, h₂.nonneg x, h₂.le_one x]⟩
  eventuallyEq_one := by
    filter_upwards [h₁.eventuallyEq_one, h₂.eventuallyEq_one] with x hx₁ hx₂
    simp [hx₁, hx₂]

end IsQuantizationCutoff

/-- **Convex combinations of cutoffs are cutoffs**: the cutoffs in `U` form a convex set of
functions. -/
theorem convex_setOf_isQuantizationCutoff (U : Set E) :
    Convex ℝ {χ : E → ℝ | IsQuantizationCutoff U χ} := by
  intro χ₁ h₁ χ₂ h₂ a b ha hb hab
  refine
    { contDiff := (h₁.contDiff.const_smul a).add (h₂.contDiff.const_smul b)
      hasCompactSupport := (h₁.hasCompactSupport.smul_left).add h₂.hasCompactSupport.smul_left
      tsupport_subset := (tsupport_add _ _).trans <| union_subset
        ((closure_mono (Function.support_const_smul_subset a χ₁)).trans h₁.tsupport_subset)
        ((closure_mono (Function.support_const_smul_subset b χ₂)).trans h₂.tsupport_subset)
      even := (h₁.even.const_smul a).add (h₂.even.const_smul b)
      mem_Icc := fun x ↦ ?_
      eventuallyEq_one := ?_ }
  · have h₁x := h₁.mem_Icc x
    have h₂x := h₂.mem_Icc x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_Icc] at h₁x h₂x ⊢
    constructor <;> nlinarith
  · filter_upwards [h₁.eventuallyEq_one, h₂.eventuallyEq_one] with x hx₁ hx₂
    simp [hx₁, hx₂, hab]

/-- A smooth bump function centred at `0` whose closed outer ball lies in `U` is a cutoff in
`U`. -/
theorem _root_.ContDiffBump.isQuantizationCutoff [FiniteDimensional ℝ E] [HasContDiffBump E]
    (f : ContDiffBump (0 : E)) (hf : Metric.closedBall (0 : E) f.rOut ⊆ U) :
    IsQuantizationCutoff U f where
  contDiff := f.contDiff
  hasCompactSupport := f.hasCompactSupport
  tsupport_subset := f.tsupport_eq ▸ hf
  even := f.neg
  mem_Icc _ := ⟨f.nonneg, f.le_one⟩
  eventuallyEq_one := f.eventuallyEq_one

/-- **Existence of cutoffs**: every neighbourhood of `0` in a finite-dimensional space carries a
quantization cutoff, a smooth bump centred at `0`. -/
theorem exists_isQuantizationCutoff [FiniteDimensional ℝ E] [HasContDiffBump E]
    (hU : U ∈ 𝓝 (0 : E)) : ∃ χ : E → ℝ, IsQuantizationCutoff U χ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  let f : ContDiffBump (0 : E) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  exact ⟨f, f.isQuantizationCutoff <| (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU⟩

/-- On the zero space a function is a cutoff in `U` exactly when `0 ∈ U` and the function is the
constant `1`. -/
theorem isQuantizationCutoff_iff_of_subsingleton [Subsingleton E] :
    IsQuantizationCutoff U χ ↔ (0 : E) ∈ U ∧ χ = 1 := by
  refine ⟨fun h ↦ ⟨h.zero_mem, funext fun x ↦ by
    rw [Subsingleton.elim x 0, h.apply_zero, Pi.one_apply]⟩, ?_⟩
  rintro ⟨hU, rfl⟩
  exact
    { contDiff := contDiff_const
      hasCompactSupport := HasCompactSupport.of_compactSpace _
      tsupport_subset := fun x _ ↦ Subsingleton.elim x 0 ▸ hU
      even := Function.Even.const 1
      mem_Icc := fun _ ↦ ⟨zero_le_one, le_rfl⟩
      eventuallyEq_one := EventuallyEq.rfl }

/-- On a nonzero space the constant function `1` is not a cutoff in any set, since its support is
not compact. -/
theorem not_isQuantizationCutoff_one [Nontrivial E] : ¬IsQuantizationCutoff U (1 : E → ℝ) := by
  intro h
  have h₁ := h.hasCompactSupport.isCompact
  rw [tsupport, Function.support_one, closure_univ] at h₁
  exact noncompact_univ E h₁

end TauCeti
