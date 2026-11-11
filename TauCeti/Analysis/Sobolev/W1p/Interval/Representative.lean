/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
public import Mathlib.Topology.ContinuousMap.Compact
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Continuous representatives and endpoint traces on an interval

For every `1 ≤ p ≤ ∞`, a real Sobolev class on `(a,b)`, with `a < b`, has a unique
continuous representative on `[a,b]`. The map `W1p.intervalRepresentativeL` into the
supremum-normed continuous functions is bounded, with an explicit constant depending only
on the interval length and `p`. Its representative is absolutely continuous and its
classical derivative agrees almost everywhere with the weak gradient. In particular,
evaluating it at the two endpoints defines the bounded trace `W1p.intervalTraceL`.

The construction uses the weak fundamental theorem of calculus in
`TauCeti.Analysis.Sobolev.WeakDeriv.Interval`, not smooth density, so it also applies at
`p = ∞`. Integration by parts is stated for two Sobolev representatives.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorems 8.2 and 8.3.
* G. Leoni, *A First Course in Sobolev Spaces*, Theorem 7.13.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal

namespace TauCeti.W1p

variable {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : IsFiniteMeasure (volume.restrict
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) := ⟨by simp⟩

private theorem exists_intervalRepresentative (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ∃ w : C(Icc a b, ℝ), value u =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ w (projIcc a b hab.le t) := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (value u) (gradient u) 1 := by
    simpa using (hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  obtain ⟨w, hw, hae⟩ := hw.exists_continuousOn_ae_eq ((Lp.memLp _).integrable (by exact Fact.out))
  let wMap : C(Icc a b, ℝ) := ⟨fun t ↦ w t, hw.domRestrict⟩
  have hwMap (t : Icc a b) : wMap t = w t := rfl
  refine ⟨wMap, ?_⟩
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem), hwMap]
  exact ht

private def intervalRepresentative (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) : C(Icc a b, ℝ) :=
  (exists_intervalRepresentative hab u).choose

private theorem intervalRepresentative_ae (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    value u =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ intervalRepresentative hab u (projIcc a b hab.le t) :=
  (exists_intervalRepresentative hab u).choose_spec

private def intervalRepresentativeₗ (hab : a < b) :
    W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p →ₗ[ℝ] C(Icc a b, ℝ) where
  toFun := intervalRepresentative hab
  map_add' u v := by
    have hae := (intervalRepresentative_ae hab (u + v)).symm.trans
      ((value_add_ae u v).trans ((intervalRepresentative_ae hab u).add
        (intervalRepresentative_ae hab v)))
    rw [restrict_Ioo_eq_restrict_Icc] at hae
    have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
      ((intervalRepresentative hab (u + v)).continuous.comp continuous_projIcc).continuousOn
      (((intervalRepresentative hab u).continuous.comp continuous_projIcc).add
        ((intervalRepresentative hab v).continuous.comp continuous_projIcc)).continuousOn
    ext t
    simpa only [Pi.add_apply, projIcc_of_mem hab.le t.property, ContinuousMap.add_apply] using
      heq t.property
  map_smul' c u := by
    have hae := (intervalRepresentative_ae hab (c • u)).symm.trans
      ((value_smul_ae c u).trans ((intervalRepresentative_ae hab u).const_smul c))
    rw [restrict_Ioo_eq_restrict_Icc] at hae
    have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
      ((intervalRepresentative hab (c • u)).continuous.comp continuous_projIcc).continuousOn
      (continuous_const.smul ((intervalRepresentative hab u).continuous.comp
        continuous_projIcc)).continuousOn
    ext t
    simpa only [Pi.smul_apply, projIcc_of_mem hab.le t.property, ContinuousMap.smul_apply,
      RingHom.id_apply] using heq t.property

private theorem norm_intervalRepresentativeₗ_le (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖intervalRepresentativeₗ hab u‖ ≤
      (((b - a)⁻¹ + 1) *
        (ENNReal.ofReal (b - a) ^ (1 - 1 / p.toReal)).toReal) * ‖u‖ := by
  set A := (ENNReal.ofReal (b - a) ^ (1 - 1 / p.toReal)).toReal
  have hv : ∫ t in Ioo a b, ‖value u t‖ ≤ A * ‖u‖ := by
    have h := Lp.integral_norm_le_mul_norm (value u)
    simp only [Measure.restrict_apply_univ, Opens.coe_mk, Real.volume_Ioo] at h
    exact h.trans (mul_le_mul_of_nonneg_left (norm_value_le u) ENNReal.toReal_nonneg)
  have hg : ∫ t in Ioo a b, ‖gradient u t‖ ≤ A * ‖u‖ := by
    have h := Lp.integral_norm_le_mul_norm (gradient u)
    simp only [Measure.restrict_apply_univ, Opens.coe_mk, Real.volume_Ioo] at h
    exact h.trans (mul_le_mul_of_nonneg_left (norm_gradient_le u) ENNReal.toReal_nonneg)
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (value u) (gradient u) 1 := by
    simpa using (hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  have h := hw.norm_le_setAverage_add_integral hab
    ((Lp.memLp _).integrable (by exact Fact.out))
    ((intervalRepresentativeₗ hab u).continuous.comp continuous_projIcc).continuousOn
    (intervalRepresentative_ae hab u) t.property
  simp only [Function.comp_apply, projIcc_of_mem hab.le t.property, setAverage_eq,
    smul_eq_mul, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.2 hab.le)] at h
  calc
    ‖intervalRepresentativeₗ hab u t‖ ≤
        (b - a)⁻¹ * (∫ t in Ioo a b, ‖value u t‖) + ∫ t in Ioo a b, ‖gradient u t‖ := h
    _ ≤ (b - a)⁻¹ * (A * ‖u‖) + A * ‖u‖ := by gcongr
    _ = (((b - a)⁻¹ + 1) * A) * ‖u‖ := by ring

/-- The bounded linear map taking a Sobolev class on `(a,b)` to its unique continuous
representative on `[a,b]`, for every `1 ≤ p ≤ ∞`. -/
def intervalRepresentativeL (hab : a < b) :
    W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p →L[ℝ] C(Icc a b, ℝ) :=
  (intervalRepresentativeₗ (p := p) hab).mkContinuous _ (norm_intervalRepresentativeₗ_le hab)

/-- The continuous representative agrees almost everywhere with the Sobolev value. The
projection only extends the representative outside the closed interval. -/
theorem value_ae_eq_intervalRepresentativeL (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    value u =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t) :=
  intervalRepresentative_ae hab u

/-- Characterization and uniqueness of the continuous representative, including its endpoint
values: it is the unique continuous function agreeing almost everywhere with the class. -/
theorem intervalRepresentativeL_eq_iff (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) (w : C(Icc a b, ℝ)) :
    intervalRepresentativeL hab u = w ↔
      value u =ᵐ[volume.restrict (Ioo a b)] fun t ↦ w (projIcc a b hab.le t) := by
  refine ⟨fun h ↦ h ▸ value_ae_eq_intervalRepresentativeL hab u, fun h ↦ ?_⟩
  have hae := (value_ae_eq_intervalRepresentativeL hab u).symm.trans h
  rw [restrict_Ioo_eq_restrict_Icc] at hae
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hae
    ((intervalRepresentativeL hab u).continuous.comp continuous_projIcc).continuousOn
    (w.continuous.comp continuous_projIcc).continuousOn
  ext t
  simpa only [projIcc_of_mem hab.le t.property] using heq t.property

/-- A continuous representative determines the Sobolev class. -/
theorem intervalRepresentativeL_injective (hab : a < b) :
    Function.Injective (intervalRepresentativeL (p := p) hab) := by
  intro u v h
  apply ext_value
  apply Lp.ext
  exact (value_ae_eq_intervalRepresentativeL hab u).trans
    (h ▸ (value_ae_eq_intervalRepresentativeL hab v).symm)

/-- The representative of a constant class is the same constant on the closed interval. -/
-- Rewrite before simplification of the open-set coercion inside the Sobolev carrier.
@[simp↓]
theorem intervalRepresentativeL_const (hab : a < b) (c : ℝ) :
    intervalRepresentativeL (p := p) hab (const c) = ContinuousMap.const (Icc a b) c := by
  apply (intervalRepresentativeL_eq_iff hab _ _).2
  rw [value_const]
  have h := Lp.coeFn_const p
    (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) c
  simp only [Opens.coe_mk] at h ⊢
  filter_upwards [h] with t ht
  simpa only [ContinuousMap.const_apply, Function.const_apply] using ht

/-- An explicit bound for the supremum norm of the interval representative. At `p = ∞`,
`1 / p.toReal` is interpreted as zero. -/
theorem norm_intervalRepresentativeL_le (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖intervalRepresentativeL hab u‖ ≤
      (((b - a)⁻¹ + 1) *
        (ENNReal.ofReal (b - a) ^ (1 - 1 / p.toReal)).toReal) * ‖u‖ :=
  norm_intervalRepresentativeₗ_le hab u

/-- The representative is absolutely continuous on the closed interval, also at `p = ∞`. -/
theorem absolutelyContinuousOnInterval_intervalRepresentativeL (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    AbsolutelyContinuousOnInterval
      (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) a b := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (value u) (gradient u) 1 := by
    simpa using (hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  exact hw.absolutelyContinuousOnInterval ((Lp.memLp _).integrable (by exact Fact.out))
    ((intervalRepresentativeL hab u).continuous.comp continuous_projIcc).continuousOn
    (value_ae_eq_intervalRepresentativeL hab u) hab.le

/-- The fundamental theorem of calculus for the interval representative, with both endpoints
allowed. -/
theorem integral_gradient_eq_intervalRepresentativeL_sub (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) (s t : Icc a b) :
    ∫ r in s.val..t.val, gradient u r =
      intervalRepresentativeL hab u t - intervalRepresentativeL hab u s := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (value u) (gradient u) 1 := by
    simpa using (hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  simpa only [Function.comp_apply, projIcc_of_mem hab.le s.property,
    projIcc_of_mem hab.le t.property] using
    hw.integral_eq_sub ((Lp.memLp _).integrable (by exact Fact.out))
      ((intervalRepresentativeL hab u).continuous.comp continuous_projIcc).continuousOn
      (value_ae_eq_intervalRepresentativeL hab u) s.property t.property

/-- In the open interval the classical derivative of the representative agrees almost
everywhere with the recorded weak gradient. -/
theorem ae_hasDerivAt_intervalRepresentativeL (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ∀ᵐ t, t ∈ Set.uIoc a b → HasDerivAt
      (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) (gradient u t) t := by
  have hw : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (value u) (gradient u) 1 := by
    simpa using (hasWeakFDerivOn u).hasWeakLineDerivOn (1 : ℝ)
  exact hw.ae_hasDerivAt
    ((intervalRepresentativeL hab u).continuous.comp continuous_projIcc).continuousOn
    (value_ae_eq_intervalRepresentativeL hab u) hab.le

/-- The pair of endpoint values of a Sobolev class as a bounded linear trace. -/
def intervalTraceL (hab : a < b) :
    W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p →L[ℝ] ℝ × ℝ :=
  ((ContinuousMap.evalCLM ℝ (⟨a, left_mem_Icc.2 hab.le⟩ : Icc a b)).comp
    (intervalRepresentativeL hab)).prod
      ((ContinuousMap.evalCLM ℝ (⟨b, right_mem_Icc.2 hab.le⟩ : Icc a b)).comp
        (intervalRepresentativeL hab))

/-- The endpoint trace is evaluation of the continuous representative at `a` and `b`. -/
-- Rewrite before simplification of the open-set coercion inside the Sobolev carrier.
@[simp↓]
theorem intervalTraceL_apply (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    intervalTraceL hab u =
      (intervalRepresentativeL hab u ⟨a, left_mem_Icc.2 hab.le⟩,
        intervalRepresentativeL hab u ⟨b, right_mem_Icc.2 hab.le⟩) := (rfl)

/-- The endpoint trace has the same explicit bound as the continuous representative. -/
theorem norm_intervalTraceL_le (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖intervalTraceL hab u‖ ≤
      (((b - a)⁻¹ + 1) *
        (ENNReal.ofReal (b - a) ^ (1 - 1 / p.toReal)).toReal) * ‖u‖ := by
  rw [intervalTraceL_apply, Prod.norm_def]
  exact (max_le ((intervalRepresentativeL hab u).norm_coe_le_norm _)
    ((intervalRepresentativeL hab u).norm_coe_le_norm _)).trans
    (norm_intervalRepresentativeL_le hab u)

/-- The continuous representatives of two Sobolev classes on `(a,b)` are at supremum distance
at most the distance of their values at `a` plus the `L¹(a,b)` distance of their weak
derivatives. -/
theorem norm_intervalRepresentativeL_sub_le (hab : a < b)
    (u v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖intervalRepresentativeL hab u - intervalRepresentativeL hab v‖ ≤
      |(intervalTraceL hab u).1 - (intervalTraceL hab v).1| +
        ∫ t in Ioo a b, |gradient u t - gradient v t| := by
  have : IsFiniteMeasure (volume.restrict ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo a b
  have hint : ∀ w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p, IntegrableOn (gradient w) (Ioo a b) :=
    fun w ↦ (Lp.memLp (gradient w)).integrable Fact.out
  have h0 : 0 ≤ ∫ t in Ioo a b, |gradient u t - gradient v t| :=
    integral_nonneg fun _ ↦ abs_nonneg _
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t ↦ ?_
  set y : Icc a b := ⟨a, left_mem_Icc.2 hab.le⟩
  -- The difference of the representatives at `t` is their difference at `a` plus `∫_a^t (u' - v')`.
  have hI : ∀ w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p,
      IntervalIntegrable (gradient w) volume a t := fun w ↦
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hint w)).mono_set
      (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hab.le]; exact t.2))
  have heq : intervalRepresentativeL hab u t - intervalRepresentativeL hab v t =
      ((intervalTraceL hab u).1 - (intervalTraceL hab v).1) +
        ∫ s in a..(t : ℝ), (gradient u s - gradient v s) := by
    rw [intervalIntegral.integral_sub (hI u) (hI v),
      integral_gradient_eq_intervalRepresentativeL_sub hab u y t,
      integral_gradient_eq_intervalRepresentativeL_sub hab v y t, intervalTraceL_apply,
      intervalTraceL_apply]
    ring
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs, heq]
  refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
  refine (intervalIntegral.abs_integral_le_integral_abs t.2.1).trans ?_
  -- `(a, t] ⊆ (a, b]`, and `(a, b]` and `(a, b)` differ by a null set.
  rw [intervalIntegral.integral_of_le t.2.1, ← integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_set
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 ((hint u).sub (hint v)).abs).1
    (ae_of_all _ fun _ ↦ abs_nonneg _) (Ioc_subset_Ioc_right t.2.2).eventuallyLE

/-- Integration by parts for two interval Sobolev representatives, allowing different
integrability exponents. The projections extend the representatives outside `[a,b]` only. -/
theorem integral_intervalRepresentativeL_mul_gradient_eq_sub {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hab : a < b) (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p)
    (v : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ q) :
    ∫ t in a..b, intervalRepresentativeL hab u (projIcc a b hab.le t) * gradient v t =
      (intervalTraceL hab u).2 * (intervalTraceL hab v).2 -
        (intervalTraceL hab u).1 * (intervalTraceL hab v).1 -
      ∫ t in a..b, gradient u t * intervalRepresentativeL hab v (projIcc a b hab.le t) := by
  have h := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt
    (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    (absolutelyContinuousOnInterval_intervalRepresentativeL hab v)
    (ae_hasDerivAt_intervalRepresentativeL hab u)
    (ae_hasDerivAt_intervalRepresentativeL hab v)
  simpa only [intervalTraceL_apply, projIcc_of_mem hab.le (left_mem_Icc.2 hab.le),
    projIcc_of_mem hab.le (right_mem_Icc.2 hab.le)] using h

end TauCeti.W1p
