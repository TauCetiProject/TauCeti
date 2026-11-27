/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Basic
public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Endpoint boundary data for interval Sobolev functions

For `1 ≤ p < ∞`, the kernel of the endpoint trace on `W^{1,p}(a,b)` is precisely
`W^{1,p}_0(a,b)`. Thus two classes have the same endpoint data exactly when their difference
belongs to the zero-boundary space. The forward inclusion holds also at `p = ∞`; the converse
is deliberately restricted to finite exponents, since the full-norm closure of test functions
at infinity imposes more than vanishing endpoint values.

The bounded linear map `W1p.intervalLiftL` lifts any pair of endpoint values by affine
interpolation, for every `1 ≤ p ≤ ∞`. Subtracting this lift reduces prescribed endpoint data
to the zero-boundary condition at finite exponents. The restriction to `(a,b)` of a test function
on `ℝ` has the test function itself as continuous representative on `[a,b]`
(`W1p.intervalRepresentativeL_restrictL_ofTestFunctionₗ`), so its endpoint data are its values at
`a` and `b` (`W1p.intervalTraceL_restrictL_ofTestFunctionₗ`).

A class with zero endpoint values is bounded by half the `L¹` norm of its weak gradient,
`|u(t)| ≤ (1/2) ∫_a^b |u'|` (`W1p.abs_intervalRepresentativeL_le_of_intervalTraceL_eq_zero`),
which is the one-dimensional embedding of `W^{1,1}_0(a,b)` into the bounded functions.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorems 8.2 and 8.12.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions

namespace TauCeti.W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : IsFiniteMeasure (volume.restrict
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) := ⟨by simp⟩

/-- A class in the closure of the test functions has zero endpoint trace, even at `p = ∞`. -/
theorem intervalTraceL_eq_zero_of_mem_w1p0Submodule (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p}
    (hu : u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    intervalTraceL hab u = 0 := by
  have hint : IntegrableOn (gradient u) (Ioo a b) :=
    (Lp.memLp _).integrable (by exact Fact.out)
  let w : C(Icc a b, ℝ) := ⟨fun t ↦ ∫ s in a..t.val, gradient u s,
    (TauCeti.intervalIntegral.continuousOn_primitive_interval_of_integrableOn_Ioo hint
      (left_mem_Icc.2 hab.le)).domRestrict⟩
  have hw : intervalRepresentativeL hab u = w := by
    apply (intervalRepresentativeL_eq_iff hab u w).2
    filter_upwards [value_ae_eq_intervalIntegral_gradient_of_mem_w1p0Submodule hu,
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)]
    exact ht
  rw [intervalTraceL_apply, hw]
  exact Prod.ext intervalIntegral.integral_same
    (intervalIntegral_gradient_eq_zero_of_mem_w1p0Submodule hab.le hu)

/-- For finite exponents, zero endpoint values characterize the closure of test functions. -/
-- Rewrite before simplification of the open-set coercion in the Sobolev carrier.
@[simp↓]
theorem mem_w1p0Submodule_iff_intervalTraceL_eq_zero (hp : p ≠ ⊤) (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    u ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p ↔ intervalTraceL hab u = 0 := by
  refine ⟨intervalTraceL_eq_zero_of_mem_w1p0Submodule hab, fun h ↦ ?_⟩
  rw [intervalTraceL_apply] at h
  have ha : intervalRepresentativeL hab u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 :=
    congrArg Prod.fst h
  have hb : intervalRepresentativeL hab u ⟨b, right_mem_Icc.2 hab.le⟩ = 0 :=
    congrArg Prod.snd h
  apply (mem_w1p0Submodule_Ioo_iff hp hab u).2
  constructor
  · filter_upwards [value_ae_eq_intervalRepresentativeL hab u,
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    have hftc := integral_gradient_eq_intervalRepresentativeL_sub hab u
      ⟨a, left_mem_Icc.2 hab.le⟩ ⟨t, Ioo_subset_Icc_self hmem⟩
    rw [ha, sub_zero] at hftc
    rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)] at ht
    exact ht.trans hftc.symm
  · simpa only [ha, hb, sub_self] using integral_gradient_eq_intervalRepresentativeL_sub hab u
      ⟨a, left_mem_Icc.2 hab.le⟩ ⟨b, right_mem_Icc.2 hab.le⟩

/-- The endpoint trace kernel is the zero-boundary Sobolev space for `1 ≤ p < ∞`. -/
@[simp↓]
theorem ker_intervalTraceL (hp : p ≠ ⊤) (hab : a < b) :
    (intervalTraceL (p := p) hab).ker =
      (w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p).toSubmodule := by
  ext u
  exact (mem_w1p0Submodule_iff_intervalTraceL_eq_zero hp hab u).symm

/-- Equality of endpoint data is the quotient boundary condition modulo `W^{1,p}_0`. -/
theorem intervalTraceL_eq_iff_sub_mem_w1p0Submodule (hp : p ≠ ⊤) (hab : a < b)
    (u v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    intervalTraceL hab u = intervalTraceL hab v ↔
      u - v ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p := by
  rw [mem_w1p0Submodule_iff_intervalTraceL_eq_zero hp hab, map_sub, sub_eq_zero]

private theorem exists_intervalCoord :
    ∃ v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      value v =ᵐ[volume.restrict (Ioo a b)] (ContinuousLinearMap.id ℝ ℝ) ∧
      gradient v =ᵐ[volume.restrict (Ioo a b)]
        fun _ ↦ (InnerProductSpace.toDual ℝ ℝ).symm (ContinuousLinearMap.id ℝ ℝ) :=
  exists_value_gradient_ae_eq_continuousLinearMap
    (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (p := p)
    (by simpa using Metric.isBounded_Ioo a b) (ContinuousLinearMap.id ℝ ℝ)

/-- The Sobolev class of the coordinate function `t ↦ t` on a bounded interval. -/
def intervalCoord : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p :=
  (exists_intervalCoord (a := a) (b := b) (p := p)).choose

/-- The value component of the coordinate class equals the coordinate almost everywhere. -/
theorem value_intervalCoord :
    value (intervalCoord (a := a) (b := b) (p := p)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ t :=
  (exists_intervalCoord (a := a) (b := b) (p := p)).choose_spec.1

/-- The weak gradient of the coordinate class is one almost everywhere. -/
theorem gradient_intervalCoord :
    gradient (intervalCoord (a := a) (b := b) (p := p)) =ᵐ[volume.restrict (Ioo a b)]
      fun _ ↦ 1 := by
  have hg := (exists_intervalCoord (a := a) (b := b) (p := p)).choose_spec.2
  have hdual : (InnerProductSpace.toDual ℝ ℝ).symm (ContinuousLinearMap.id ℝ ℝ) = 1 := by
    simpa using (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := (1 : ℝ))
      (y := ContinuousLinearMap.id ℝ ℝ))
  exact hg.trans (Filter.Eventually.of_forall fun _ ↦ hdual)

/-- The continuous representative of the coordinate class is the coordinate function. -/
@[simp↓]
theorem intervalRepresentativeL_intervalCoord (hab : a < b) (t : Icc a b) :
    intervalRepresentativeL hab (intervalCoord (p := p)) t = t.val := by
  have heq : intervalRepresentativeL hab (intervalCoord (p := p)) =
      ⟨Subtype.val, continuous_subtypeVal⟩ := by
    apply (intervalRepresentativeL_eq_iff hab _ _).2
    filter_upwards [value_intervalCoord (p := p), ae_restrict_mem measurableSet_Ioo]
      with x hx hmem
    simpa only [ContinuousMap.coe_mk,
      projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)] using hx
  exact congrArg (fun f : C(Icc a b, ℝ) ↦ f t) heq

/-- The endpoint values of the coordinate class are the interval endpoints. -/
-- Evaluate the coordinate before the generic endpoint-evaluation rule expands the trace.
@[simp↓ 1100]
theorem intervalTraceL_intervalCoord (hab : a < b) :
    intervalTraceL hab (intervalCoord (p := p)) = (a, b) := by
  simp only [intervalTraceL_apply, intervalRepresentativeL_intervalCoord]

/-- Bounded affine interpolation of endpoint data in the interval Sobolev space.
Its continuous representative is `z.1 + (z.2 - z.1) * (t - a) / (b - a)`. -/
def intervalLiftL (a b : ℝ) :
    (ℝ × ℝ) →L[ℝ] W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (const 1) +
    ((b - a)⁻¹ • (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight
      (intervalCoord (a := a) (b := b) - a • const 1)

/-- The endpoint lift is affine interpolation at every point of the closed interval. -/
@[simp↓]
theorem intervalRepresentativeL_intervalLiftL (hab : a < b) (z : ℝ × ℝ) (t : Icc a b) :
    intervalRepresentativeL hab (intervalLiftL (p := p) a b z) t =
      z.1 + (z.2 - z.1) * (t.val - a) / (b - a) := by
  simp only [intervalLiftL, add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    map_add, map_smul, map_sub]
  rw [intervalRepresentativeL_const]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, smul_eq_mul]
  rw [intervalRepresentativeL_intervalCoord]
  ring

/-- Affine interpolation is a right inverse of the endpoint trace, also at `p = ∞`. -/
-- Cancel the lift before the generic endpoint-evaluation simplification expands the trace.
@[simp↓ 1100]
theorem intervalTraceL_intervalLiftL (hab : a < b) (z : ℝ × ℝ) :
    intervalTraceL hab (intervalLiftL (p := p) a b z) = z := by
  rw [intervalTraceL_apply]
  apply Prod.ext <;> dsimp only
  · rw [intervalRepresentativeL_intervalLiftL]
    simp
  · rw [intervalRepresentativeL_intervalLiftL]
    simp [sub_ne_zero.mpr hab.ne']

/-- The continuous representative of the restriction to `(a, b)` of a test function on `ℝ` is the
test function itself on `[a, b]`. -/
-- Rewrite before simplification of the open-set coercion inside the Sobolev carrier.
@[simp↓]
theorem intervalRepresentativeL_restrictL_ofTestFunctionₗ (hab : a < b)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (t : Icc a b) :
    intervalRepresentativeL hab (restrictL (le_top : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤)
      (ofTestFunctionₗ volume ⊤ p φ)) t = φ t := by
  have h : intervalRepresentativeL hab (restrictL (le_top : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤)
      (ofTestFunctionₗ volume ⊤ p φ)) = ⟨fun t ↦ φ t, φ.contDiff.continuous.comp
        continuous_subtypeVal⟩ := by
    refine (intervalRepresentativeL_eq_iff hab _ _).2 ?_
    filter_upwards [value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := p)
        (le_top : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤) φ,
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, ContinuousMap.coe_mk, projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)]
  rw [h, ContinuousMap.coe_mk]

/-- The endpoint values of the restriction to `(a, b)` of a test function on `ℝ` are its values
at `a` and `b`. -/
-- Evaluate the restricted test function before the generic endpoint-evaluation rule expands the
-- trace.
@[simp↓ 1100]
theorem intervalTraceL_restrictL_ofTestFunctionₗ (hab : a < b) (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    intervalTraceL hab (restrictL (le_top : (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) ≤ ⊤)
      (ofTestFunctionₗ volume ⊤ p φ)) = (φ a, φ b) := by
  rw [intervalTraceL_apply, intervalRepresentativeL_restrictL_ofTestFunctionₗ,
    intervalRepresentativeL_restrictL_ofTestFunctionₗ]

/-- Every pair of endpoint values is attained by a Sobolev class, including at `p = ∞`. -/
theorem intervalTraceL_surjective (hab : a < b) :
    Function.Surjective (intervalTraceL (p := p) hab) :=
  fun z ↦ ⟨intervalLiftL a b z, intervalTraceL_intervalLiftL hab z⟩

/-- Subtracting the affine lift of prescribed endpoint data gives a zero-boundary class
exactly when the original class has those endpoint values. -/
theorem intervalTraceL_eq_iff_sub_intervalLiftL_mem (hp : p ≠ ⊤) (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) (z : ℝ × ℝ) :
    intervalTraceL hab u = z ↔
      u - intervalLiftL a b z ∈ w1p0Submodule volume ⟨Ioo a b, isOpen_Ioo⟩ p := by
  rw [← intervalTraceL_eq_iff_sub_mem_w1p0Submodule hp hab, intervalTraceL_intervalLiftL]

/-! ### The supremum bound for zero endpoint values -/

/-- **The pointwise bound for zero endpoint values.** If the continuous representative of
`u ∈ W^{1,p}(a, b)` vanishes at both endpoints, then `|u(t)| ≤ (1/2) ∫_a^b |u'|` for every
`t ∈ [a, b]`, since `u(t)` is both `∫_a^t u'` and `-∫_t^b u'`. For `p = 1` this is the
one-dimensional embedding `‖u‖_∞ ≤ ‖u'‖_{L¹(a,b)} / 2` of `W^{1,1}_0(a, b)`, whose constant
`1/2` is attained by `x (1 - x)` on `(0, 1)` at `t = 1/2`. -/
theorem abs_intervalRepresentativeL_le_of_intervalTraceL_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p} (hu : intervalTraceL hab u = 0) (t : Icc a b) :
    |intervalRepresentativeL hab u t| ≤ (∫ s in Ioo a b, |gradient u s|) / 2 := by
  rw [intervalTraceL_apply, Prod.mk_eq_zero] at hu
  have ha := left_mem_Icc.2 hab.le
  have hb := right_mem_Icc.2 hab.le
  -- `u(t)` is the integral of `u'` from `a` to `t`, and minus the integral from `t` to `b`.
  have h₁ : |intervalRepresentativeL hab u t| ≤ ∫ s in a..t, |gradient u s| := by
    have h := integral_gradient_eq_intervalRepresentativeL_sub hab u ⟨a, ha⟩ t
    rw [hu.1, sub_zero] at h
    rw [← h]
    exact intervalIntegral.abs_integral_le_integral_abs t.property.1
  have h₂ : |intervalRepresentativeL hab u t| ≤ ∫ s in t..b, |gradient u s| := by
    have h := integral_gradient_eq_intervalRepresentativeL_sub hab u t ⟨b, hb⟩
    rw [hu.2, zero_sub] at h
    rw [← abs_neg, ← h]
    exact intervalIntegral.abs_integral_le_integral_abs t.property.2
  have hsum : (∫ s in a..t, |gradient u s|) + (∫ s in t..b, |gradient u s|) =
      ∫ s in Ioo a b, |gradient u s| := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_gradient u ha t.property).abs
      (intervalIntegrable_gradient u t.property hb).abs,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  linarith

end TauCeti.W1p
