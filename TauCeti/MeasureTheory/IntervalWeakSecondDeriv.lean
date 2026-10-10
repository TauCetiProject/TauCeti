/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weak second derivatives on the unit interval

A square-integrable function `u` on `(0,1]` whose distributional second derivative against the
polynomial test family `t ↦ t^(k+2) (1-t)²` is a square-integrable function `w` must be, almost
everywhere, an affine function plus the second primitive of `w`:

`u t = a + b t + ∫₀¹ max (t - s) 0 · w s ds`.

This is the regularity backbone of the free-beam operator realization for Davis--Kahan 1970
Section 9: it identifies the kernel of the bending form with the affine functions, produces the
compact factorization of the form-space embedding, and starts the eigenfunction bootstrap.

Everything here is stated for an arbitrary `RCLike` scalar field `𝕜`, so the real and the
complex unit-interval `L²` spaces are both instances.

## The test family

`intervalBump k t = t^(k+2) * (1-t)²` vanishes to second order at both endpoints of `[0,1]`,
so integrating a linear weight against `intervalBumpD2 k` twice by parts leaves no boundary
terms.  The monomial expansion of `intervalBumpD2 k` has leading coefficient `(k+3)(k+4) ≠ 0`,
so the family is triangular against the monomials: testing against it controls every monomial
moment beyond the two affine ones, and Weierstrass approximation finishes.

## Main results

* `TauCeti.integral_linear_mul_intervalBumpD2`: `∫_s^1 (x-s) φ''(x) dx = φ(s)` for the bump
  family — the reproducing identity behind the second primitive.
* `TauCeti.secondPrimitive`: the normalized double primitive `t ↦ ∫ max (t-s) 0 · w s ds`.
* `TauCeti.ae_eq_zero_of_forall_integral_pow_eq_zero`: an `L²` function on `(0,1]` with all
  vanishing monomial moments vanishes almost everywhere.
* `TauCeti.eq_affine_add_secondPrimitive_of_forall_integral_bumpD2`: the representation
  theorem.
-/

public section

namespace TauCeti

open MeasureTheory intervalIntegral
open scoped ENNReal InnerProductSpace

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Lebesgue measure of the half-open unit interval, the ambient measure for the
free-beam `L²` model.  Exposed so downstream modules can unfold to the restriction;
the ratchet carve-out is deliberate api design. -/
@[expose] def unitIocMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- Unfolding equation for the ambient measure, exported for downstream modules. -/
theorem unitIocMeasure_def : unitIocMeasure = volume.restrict (Set.Ioc (0 : ℝ) 1) := rfl

/-- The unit-interval measure is a probability-sized finite measure. -/
instance : IsFiniteMeasure unitIocMeasure := by
  constructor
  rw [unitIocMeasure, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc]
  norm_num

/-- The total mass of the unit-interval measure is `1`. -/
theorem unitIocMeasure_univ : unitIocMeasure Set.univ = 1 := by
  rw [unitIocMeasure, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc]
  norm_num

/-- The unit-interval measure is a probability measure. -/
instance : IsProbabilityMeasure unitIocMeasure := ⟨unitIocMeasure_univ⟩

/-- Almost every point for `unitIocMeasure` lies in `(0,1]`. -/
theorem ae_mem_unitIocMeasure : ∀ᵐ t ∂unitIocMeasure, t ∈ Set.Ioc (0 : ℝ) 1 := by
  rw [unitIocMeasure]
  exact ae_restrict_mem measurableSet_Ioc

/-! ## The polynomial test family -/

/-- Polynomial test bump: vanishes to order `k+2` at `0` and to second order at `1`. -/
def intervalBump (k : ℕ) (t : ℝ) : ℝ := t ^ (k + 2) * (1 - t) ^ 2

/-- Closed form of the first derivative of `intervalBump`. -/
def intervalBumpD1 (k : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) + 2) * t ^ (k + 1) * (1 - t) ^ 2 - t ^ (k + 2) * (2 * (1 - t))

/-- Closed form of the second derivative of `intervalBump`. -/
def intervalBumpD2 (k : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) + 2) * ((k : ℝ) + 1) * t ^ k * (1 - t) ^ 2
    - 4 * ((k : ℝ) + 2) * t ^ (k + 1) * (1 - t) + 2 * t ^ (k + 2)

/-- The displayed first derivative of the bump is correct. -/
theorem hasDerivAt_intervalBump (k : ℕ) (t : ℝ) :
    HasDerivAt (intervalBump k) (intervalBumpD1 k t) t := by
  have hone : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := (hasDerivAt_id t).const_sub 1
  have h := (hasDerivAt_pow (k + 2) t).mul (hone.pow 2)
  refine h.congr_deriv ?_
  have e1 : k + 2 - 1 = k + 1 := by omega
  simp only [e1, (show 2 - 1 = 1 from rfl), pow_one, Pi.pow_apply]
  unfold intervalBumpD1
  push_cast
  ring

/-- The displayed second derivative of the bump is correct. -/
theorem hasDerivAt_intervalBumpD1 (k : ℕ) (t : ℝ) :
    HasDerivAt (intervalBumpD1 k) (intervalBumpD2 k t) t := by
  have hone : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := (hasDerivAt_id t).const_sub 1
  have hA := ((hasDerivAt_pow (k + 1) t).const_mul ((k : ℝ) + 2)).mul (hone.pow 2)
  have hdouble : HasDerivAt (fun y : ℝ => 2 * (1 - y)) (2 * (-1)) t := hone.const_mul 2
  have hB := (hasDerivAt_pow (k + 2) t).mul hdouble
  have h := hA.sub hB
  refine h.congr_deriv ?_
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 1 - 1 = k := by omega
  simp only [e1, e2, (show 2 - 1 = 1 from rfl), pow_one, Pi.pow_apply]
  unfold intervalBumpD2
  push_cast
  ring

/-- The bump vanishes at `0`. -/
@[simp] theorem intervalBump_zero (k : ℕ) : intervalBump k 0 = 0 := by
  simp [intervalBump]

/-- The bump vanishes at `1`. -/
@[simp] theorem intervalBump_one (k : ℕ) : intervalBump k 1 = 0 := by
  simp [intervalBump]

/-- The bump derivative vanishes at `0`. -/
@[simp] theorem intervalBumpD1_zero (k : ℕ) : intervalBumpD1 k 0 = 0 := by
  simp [intervalBumpD1]

/-- The bump derivative vanishes at `1`. -/
@[simp] theorem intervalBumpD1_one (k : ℕ) : intervalBumpD1 k 1 = 0 := by
  simp [intervalBumpD1]

/-- Monomial expansion of the second bump derivative.  The leading coefficient
`(k+4)(k+3)` is nonzero, which is what makes the test family triangular against the
monomials. -/
theorem intervalBumpD2_eq_monomials (k : ℕ) (t : ℝ) :
    intervalBumpD2 k t =
      ((k : ℝ) + 2) * ((k : ℝ) + 1) * t ^ k
        - 2 * ((k : ℝ) + 3) * ((k : ℝ) + 2) * t ^ (k + 1)
        + ((k : ℝ) + 4) * ((k : ℝ) + 3) * t ^ (k + 2) := by
  unfold intervalBumpD2
  ring

/-- Continuity of the bump. -/
theorem continuous_intervalBump (k : ℕ) : Continuous (intervalBump k) := by
  unfold intervalBump
  fun_prop

/-- Continuity of the bump derivative. -/
theorem continuous_intervalBumpD1 (k : ℕ) : Continuous (intervalBumpD1 k) := by
  unfold intervalBumpD1
  fun_prop

/-- Continuity of the second bump derivative. -/
theorem continuous_intervalBumpD2 (k : ℕ) : Continuous (intervalBumpD2 k) := by
  unfold intervalBumpD2
  fun_prop

/-! ## Integration by parts against the bump family -/

/-- One integration by parts against a linear weight: for any `s`,
`∫_s^1 (x - s) φ''(x) dx = φ(s)`, using `φ(1) = φ'(1) = 0`. -/
theorem integral_linear_mul_intervalBumpD2 (k : ℕ) (s : ℝ) :
    ∫ x in s..1, (x - s) * intervalBumpD2 k x = intervalBump k s := by
  have hparts :
      ∫ x in s..1, (x - s) * intervalBumpD2 k x =
        (1 - s) * intervalBumpD1 k 1 - (s - s) * intervalBumpD1 k s
          - ∫ x in s..1, 1 * intervalBumpD1 k x :=
    integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (continuous_id.sub continuous_const).continuousOn
      (continuous_intervalBumpD1 k).continuousOn
      (fun x _ => (hasDerivAt_id x).sub_const s)
      (fun x _ => hasDerivAt_intervalBumpD1 k x)
      (continuous_const.intervalIntegrable s 1)
      ((continuous_intervalBumpD2 k).intervalIntegrable s 1)
  have hfund : ∫ x in s..1, intervalBumpD1 k x = intervalBump k 1 - intervalBump k s :=
    integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_intervalBump k x)
      ((continuous_intervalBumpD1 k).intervalIntegrable s 1)
  rw [hparts]
  simp only [one_mul, hfund, intervalBumpD1_one, intervalBump_one]
  ring

/-- The first moment of the second bump derivative vanishes: `∫₀¹ t φ''(t) dt = φ(0) = 0`. -/
theorem integral_id_mul_intervalBumpD2 (k : ℕ) :
    ∫ x in (0 : ℝ)..1, x * intervalBumpD2 k x = 0 := by
  have h := integral_linear_mul_intervalBumpD2 k 0
  simpa using h

/-- The zeroth moment of the second bump derivative vanishes:
`∫₀¹ φ''(t) dt = φ'(1) - φ'(0) = 0`. -/
theorem integral_intervalBumpD2 (k : ℕ) :
    ∫ x in (0 : ℝ)..1, intervalBumpD2 k x = 0 := by
  have hfund : ∫ x in (0 : ℝ)..1, intervalBumpD2 k x
      = intervalBumpD1 k 1 - intervalBumpD1 k 0 :=
    integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_intervalBumpD1 k x)
      ((continuous_intervalBumpD2 k).intervalIntegrable 0 1)
  rw [hfund]
  simp

/-! ## The second primitive kernel -/

/-- Truncated linear kernel: the integral kernel of the normalized double primitive. -/
def secondPrimitiveKernel (t s : ℝ) : ℝ := max (t - s) 0

/-- Joint continuity of the truncated linear kernel. -/
theorem continuous_secondPrimitiveKernel :
    Continuous fun p : ℝ × ℝ => secondPrimitiveKernel p.1 p.2 := by
  unfold secondPrimitiveKernel
  fun_prop

/-- The kernel is nonnegative. -/
theorem secondPrimitiveKernel_nonneg (t s : ℝ) : 0 ≤ secondPrimitiveKernel t s :=
  le_max_right _ _

/-- On the unit square the kernel is bounded by `1`. -/
theorem secondPrimitiveKernel_le_one {t s : ℝ} (ht : t ≤ 1) (hs : 0 ≤ s) :
    secondPrimitiveKernel t s ≤ 1 :=
  max_le (by linarith) zero_le_one

/-- For a nonnegative second argument the kernel is bounded by `|t|`. -/
theorem secondPrimitiveKernel_le_abs {t s : ℝ} (hs : 0 ≤ s) :
    secondPrimitiveKernel t s ≤ |t| :=
  max_le (by
    have : t - s ≤ t := by linarith
    exact this.trans (le_abs_self t)) (abs_nonneg t)

/-- Above the diagonal the kernel is the linear weight. -/
theorem secondPrimitiveKernel_of_le {t s : ℝ} (h : s ≤ t) :
    secondPrimitiveKernel t s = t - s :=
  max_eq_left (by linarith)

/-- Below the diagonal the kernel vanishes. -/
theorem secondPrimitiveKernel_of_ge {t s : ℝ} (h : t ≤ s) :
    secondPrimitiveKernel t s = 0 :=
  max_eq_right (by linarith)

/-- Singletons are null for the unit-interval measure. -/
theorem unitIocMeasure_singleton (t : ℝ) : unitIocMeasure {t} = 0 := by
  rw [unitIocMeasure]
  exact le_antisymm
    ((Measure.restrict_apply_le _ _).trans (le_of_eq Real.volume_singleton))
    zero_le

/-- The kernel is `1`-Lipschitz in its first argument, uniformly in the second. -/
theorem abs_secondPrimitiveKernel_sub_le (t t' s : ℝ) :
    |secondPrimitiveKernel t s - secondPrimitiveKernel t' s| ≤ |t - t'| := by
  have h := abs_max_sub_max_le_abs (t - s) (t' - s) 0
  calc |secondPrimitiveKernel t s - secondPrimitiveKernel t' s|
      ≤ |(t - s) - (t' - s)| := h
    _ = |t - t'| := by congr 1; ring

/-- Second primitive of an integrable function on the unit interval, normalized so that it
and its first derivative vanish at `0`.  Exposed so downstream modules can unfold the
integral form; the ratchet carve-out is deliberate api design. -/
@[expose] def secondPrimitive (w : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s, (secondPrimitiveKernel t s : 𝕜) * w s ∂unitIocMeasure

/-- Unfolding equation for the second primitive, exported for downstream modules. -/
theorem secondPrimitive_def (w : ℝ → 𝕜) (t : ℝ) :
    secondPrimitive w t
      = ∫ s, (secondPrimitiveKernel t s : 𝕜) * w s ∂unitIocMeasure := rfl

/-- The kernel slice against an integrable density is integrable. -/
theorem integrable_secondPrimitiveKernel_mul {w : ℝ → 𝕜}
    (hw : Integrable w unitIocMeasure) (t : ℝ) :
    Integrable (fun s => (secondPrimitiveKernel t s : 𝕜) * w s) unitIocMeasure := by
  refine Integrable.mono' (hw.norm.const_mul |t|) ?_ ?_
  · exact ((RCLike.continuous_ofReal.comp
      (continuous_secondPrimitiveKernel.comp
        (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable).mul
      hw.aestronglyMeasurable
  · filter_upwards [ae_mem_unitIocMeasure] with s hs
    rw [norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (secondPrimitiveKernel_nonneg t s)]
    exact mul_le_mul_of_nonneg_right (secondPrimitiveKernel_le_abs hs.1.le) (norm_nonneg _)

/-- Difference bound: the second primitive is Lipschitz with constant the `L¹` norm of the
density. -/
theorem norm_secondPrimitive_sub_le {w : ℝ → 𝕜} (hw : Integrable w unitIocMeasure)
    (t t' : ℝ) :
    ‖secondPrimitive w t - secondPrimitive w t'‖
      ≤ |t - t'| * ∫ s, ‖w s‖ ∂unitIocMeasure := by
  have hdiff : secondPrimitive w t - secondPrimitive w t'
      = ∫ s, ((secondPrimitiveKernel t s : 𝕜) - (secondPrimitiveKernel t' s : 𝕜)) * w s
          ∂unitIocMeasure := by
    rw [secondPrimitive, secondPrimitive,
      ← integral_sub (integrable_secondPrimitiveKernel_mul hw t)
        (integrable_secondPrimitiveKernel_mul hw t')]
    congr 1 with s
    ring
  rw [hdiff]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _)
    (hw.norm.const_mul _) (Filter.Eventually.of_forall fun s => ?_)
  simp only [norm_mul, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
  exact mul_le_mul_of_nonneg_right (abs_secondPrimitiveKernel_sub_le t t' s) (norm_nonneg _)

/-- The second primitive of an integrable density is continuous. -/
theorem continuous_secondPrimitive {w : ℝ → 𝕜} (hw : Integrable w unitIocMeasure) :
    Continuous (secondPrimitive w) := by
  have hnn : 0 ≤ ∫ s, ‖w s‖ ∂unitIocMeasure := integral_nonneg fun s => norm_nonneg _
  refine (LipschitzWith.of_dist_le_mul (K := ⟨_, hnn⟩) fun t t' => ?_).continuous
  rw [dist_eq_norm]
  calc ‖secondPrimitive w t - secondPrimitive w t'‖
      ≤ |t - t'| * ∫ s, ‖w s‖ ∂unitIocMeasure := norm_secondPrimitive_sub_le hw t t'
    _ = (∫ s, ‖w s‖ ∂unitIocMeasure) * dist t t' := by
        rw [Real.dist_eq, mul_comm]

/-- Almost-everywhere bound for the second primitive on the unit interval. -/
theorem ae_norm_secondPrimitive_le {w : ℝ → 𝕜} (hw : Integrable w unitIocMeasure) :
    ∀ᵐ t ∂unitIocMeasure,
      ‖secondPrimitive w t‖ ≤ ∫ s, ‖w s‖ ∂unitIocMeasure := by
  filter_upwards [ae_mem_unitIocMeasure] with t ht
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _)
    hw.norm ?_
  filter_upwards [ae_mem_unitIocMeasure] with s hs
  simp only [norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (secondPrimitiveKernel_nonneg t s)]
  calc secondPrimitiveKernel t s * ‖w s‖ ≤ 1 * ‖w s‖ :=
        mul_le_mul_of_nonneg_right (secondPrimitiveKernel_le_one ht.2 hs.1.le)
          (norm_nonneg _)
    _ = ‖w s‖ := one_mul _

/-- The second primitive of an integrable density is square-integrable on the unit
interval. -/
theorem memLp_secondPrimitive {w : ℝ → 𝕜} (hw : Integrable w unitIocMeasure) :
    MemLp (secondPrimitive w) 2 unitIocMeasure :=
  MemLp.of_bound (continuous_secondPrimitive hw).aestronglyMeasurable _
    (ae_norm_secondPrimitive_le hw)

/-! ## The second primitive reproduces the weak pairing -/

/-- For `s ∈ (0,1]` the kernel slice against the second bump derivative reproduces the bump:
`∫₀¹ max (t-s) 0 · φ''(t) dt = φ(s)`. -/
theorem integral_secondPrimitiveKernel_mul_intervalBumpD2 {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (k : ℕ) :
    ∫ t, secondPrimitiveKernel t s * intervalBumpD2 k t ∂unitIocMeasure
      = intervalBump k s := by
  have hcont : Continuous fun t => secondPrimitiveKernel t s * intervalBumpD2 k t := by
    unfold secondPrimitiveKernel
    exact ((continuous_id.sub continuous_const).max continuous_const).mul
      (continuous_intervalBumpD2 k)
  have h1 : ∫ t, secondPrimitiveKernel t s * intervalBumpD2 k t ∂unitIocMeasure
      = ∫ t in (0 : ℝ)..1, secondPrimitiveKernel t s * intervalBumpD2 k t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure]
  have hsplit : (∫ t in (0 : ℝ)..s, secondPrimitiveKernel t s * intervalBumpD2 k t)
        + ∫ t in s..1, secondPrimitiveKernel t s * intervalBumpD2 k t
      = ∫ t in (0 : ℝ)..1, secondPrimitiveKernel t s * intervalBumpD2 k t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 s) (hcont.intervalIntegrable s 1)
  have hzero : ∫ t in (0 : ℝ)..s, secondPrimitiveKernel t s * intervalBumpD2 k t = 0 := by
    have hEq : Set.EqOn (fun t => secondPrimitiveKernel t s * intervalBumpD2 k t) 0
        (Set.uIcc 0 s) := by
      intro x hx
      rw [Set.uIcc_of_le hs.1.le] at hx
      have : secondPrimitiveKernel x s = 0 :=
        max_eq_right (sub_nonpos.mpr hx.2)
      simp [this]
    rw [intervalIntegral.integral_congr hEq]
    simp
  have hlin : ∫ t in s..1, secondPrimitiveKernel t s * intervalBumpD2 k t
      = ∫ t in s..1, (t - s) * intervalBumpD2 k t := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hs.2] at hx
    have : secondPrimitiveKernel x s = x - s := max_eq_left (sub_nonneg.mpr hx.1)
    rw [this]
  rw [h1, ← hsplit, hzero, hlin, integral_linear_mul_intervalBumpD2, zero_add]

/-- **The second primitive satisfies the weak second-derivative identity**: for integrable
`w`, `∫ (K w) · φ'' = ∫ w · φ` against every member of the bump family.  Fubini plus the
reproducing identity for the kernel slices. -/
theorem integral_secondPrimitive_mul_intervalBumpD2 {w : ℝ → 𝕜}
    (hw : Integrable w unitIocMeasure) (k : ℕ) :
    ∫ t, secondPrimitive w t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure
      = ∫ s, w s * (intervalBump k s : 𝕜) ∂unitIocMeasure := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖intervalBumpD2 k x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn (continuous_intervalBumpD2 k).continuousOn
  have haeprod : ∀ᵐ p ∂(unitIocMeasure.prod unitIocMeasure),
      p ∈ (Set.Ioc (0 : ℝ) 1) ×ˢ (Set.Ioc (0 : ℝ) 1) := by
    rw [unitIocMeasure, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hFmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (secondPrimitiveKernel p.1 p.2 : 𝕜) * w p.2 * (intervalBumpD2 k p.1 : 𝕜))
      (unitIocMeasure.prod unitIocMeasure) := by
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
    · exact (RCLike.continuous_ofReal.comp
        continuous_secondPrimitiveKernel).aestronglyMeasurable
    · exact hw.aestronglyMeasurable.comp_snd
    · exact (RCLike.continuous_ofReal.comp
        ((continuous_intervalBumpD2 k).comp continuous_fst)).aestronglyMeasurable
  have hFint : Integrable
      (fun p : ℝ × ℝ =>
        (secondPrimitiveKernel p.1 p.2 : 𝕜) * w p.2 * (intervalBumpD2 k p.1 : 𝕜))
      (unitIocMeasure.prod unitIocMeasure) := by
    refine Integrable.mono'
      (g := fun p : ℝ × ℝ => C * ‖w p.2‖)
      (((integrable_const (1 : ℝ)).mul_prod hw.norm).const_mul C |>.congr ?_) hFmeas ?_
    · exact Filter.Eventually.of_forall fun p => by simp
    · filter_upwards [haeprod] with p hp
      have ht := hp.1
      have hs := hp.2
      rw [norm_mul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_nonneg (secondPrimitiveKernel_nonneg p.1 p.2)]
      have hk1 : secondPrimitiveKernel p.1 p.2 ≤ 1 :=
        secondPrimitiveKernel_le_one ht.2 hs.1.le
      have hψ : |intervalBumpD2 k p.1| ≤ C := by
        have := hC p.1 ⟨ht.1.le, ht.2⟩
        rwa [Real.norm_eq_abs] at this
      calc secondPrimitiveKernel p.1 p.2 * ‖w p.2‖ * |intervalBumpD2 k p.1|
          ≤ 1 * ‖w p.2‖ * C := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hk1 (norm_nonneg _)) hψ
              (abs_nonneg _) ?_
            positivity
        _ = C * ‖w p.2‖ := by ring
  have houter : ∀ t, secondPrimitive w t * (intervalBumpD2 k t : 𝕜)
      = ∫ s, (secondPrimitiveKernel t s : 𝕜) * w s * (intervalBumpD2 k t : 𝕜)
          ∂unitIocMeasure := by
    intro t
    rw [secondPrimitive, ← MeasureTheory.integral_mul_const]
  have hinner : ∀ᵐ s ∂unitIocMeasure,
      (∫ t, (secondPrimitiveKernel t s : 𝕜) * w s * (intervalBumpD2 k t : 𝕜)
          ∂unitIocMeasure)
        = w s * (intervalBump k s : 𝕜) := by
    filter_upwards [ae_mem_unitIocMeasure] with s hs
    have hpt : ∀ t : ℝ,
        (secondPrimitiveKernel t s : 𝕜) * w s * (intervalBumpD2 k t : 𝕜)
          = w s * ((secondPrimitiveKernel t s * intervalBumpD2 k t : ℝ) : 𝕜) := by
      intro t
      push_cast
      ring
    calc ∫ t, (secondPrimitiveKernel t s : 𝕜) * w s * (intervalBumpD2 k t : 𝕜)
            ∂unitIocMeasure
        = ∫ t, w s * ((secondPrimitiveKernel t s * intervalBumpD2 k t : ℝ) : 𝕜)
            ∂unitIocMeasure := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = w s * ∫ t, ((secondPrimitiveKernel t s * intervalBumpD2 k t : ℝ) : 𝕜)
            ∂unitIocMeasure := MeasureTheory.integral_const_mul _ _
      _ = w s * ((∫ t, secondPrimitiveKernel t s * intervalBumpD2 k t
            ∂unitIocMeasure : ℝ) : 𝕜) := by rw [_root_.integral_ofReal]
      _ = w s * (intervalBump k s : 𝕜) := by
          rw [integral_secondPrimitiveKernel_mul_intervalBumpD2 hs k]
  calc ∫ t, secondPrimitive w t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure
      = ∫ t, ∫ s, (secondPrimitiveKernel t s : 𝕜) * w s * (intervalBumpD2 k t : 𝕜)
          ∂unitIocMeasure ∂unitIocMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall houter)
    _ = ∫ s, ∫ t, (secondPrimitiveKernel t s : 𝕜) * w s * (intervalBumpD2 k t : 𝕜)
          ∂unitIocMeasure ∂unitIocMeasure := integral_integral_swap hFint
    _ = ∫ s, w s * (intervalBump k s : 𝕜) ∂unitIocMeasure := integral_congr_ae hinner

/-! ## Vanishing moments force vanishing -/

/-- Multiplying an integrable function on `(0,1]` by a monomial keeps it integrable. -/
theorem integrable_mul_pow {h : ℝ → 𝕜} (hh : Integrable h unitIocMeasure) (m : ℕ) :
    Integrable (fun t => h t * (t : 𝕜) ^ m) unitIocMeasure := by
  refine Integrable.mono' hh.norm
    (hh.aestronglyMeasurable.mul
      ((RCLike.continuous_ofReal.pow m).aestronglyMeasurable)) ?_
  filter_upwards [ae_mem_unitIocMeasure] with t ht
  rw [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos ht.1]
  calc ‖h t‖ * t ^ m ≤ ‖h t‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1.le ht.2) (norm_nonneg _)
    _ = ‖h t‖ := mul_one _

/-- Multiplying an integrable function by a member of the bump family keeps it
integrable. -/
theorem integrable_mul_intervalBumpD2 {h : ℝ → 𝕜} (hh : Integrable h unitIocMeasure)
    (k : ℕ) :
    Integrable (fun t => h t * (intervalBumpD2 k t : 𝕜)) unitIocMeasure := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖intervalBumpD2 k x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn (continuous_intervalBumpD2 k).continuousOn
  refine Integrable.mono' (hh.norm.const_mul C)
    (hh.aestronglyMeasurable.mul
      ((RCLike.continuous_ofReal.comp (continuous_intervalBumpD2 k)).aestronglyMeasurable))
    ?_
  filter_upwards [ae_mem_unitIocMeasure] with t ht
  rw [norm_mul, RCLike.norm_ofReal]
  calc ‖h t‖ * ‖intervalBumpD2 k t‖ ≤ ‖h t‖ * C :=
        mul_le_mul_of_nonneg_left (hC t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
    _ = C * ‖h t‖ := mul_comm _ _

/-- **Triangularity of the bump family**: vanishing affine moments together with vanishing
bump-family pairings force every monomial moment to vanish. -/
theorem integral_pow_eq_zero_of_forall_integral_bumpD2 {h : ℝ → 𝕜}
    (hh : Integrable h unitIocMeasure)
    (hbump : ∀ k : ℕ, ∫ t, h t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure = 0)
    (h0 : ∫ t, h t ∂unitIocMeasure = 0)
    (h1 : ∫ t, h t * (t : 𝕜) ∂unitIocMeasure = 0) :
    ∀ m : ℕ, ∫ t, h t * (t : 𝕜) ^ m ∂unitIocMeasure = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | (k + 2), ih =>
      have hexp : ∀ t : ℝ, h t * (intervalBumpD2 k t : 𝕜)
          = ((k : 𝕜) + 2) * ((k : 𝕜) + 1) * (h t * (t : 𝕜) ^ k)
            - 2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2) * (h t * (t : 𝕜) ^ (k + 1))
            + ((k : 𝕜) + 4) * ((k : 𝕜) + 3) * (h t * (t : 𝕜) ^ (k + 2)) := by
        intro t
        rw [intervalBumpD2_eq_monomials]
        push_cast
        ring
      have hsplit : ∫ t, h t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure
          = ((k : 𝕜) + 2) * ((k : 𝕜) + 1)
              * ∫ t, h t * (t : 𝕜) ^ k ∂unitIocMeasure
            - 2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2)
              * ∫ t, h t * (t : 𝕜) ^ (k + 1) ∂unitIocMeasure
            + ((k : 𝕜) + 4) * ((k : 𝕜) + 3)
              * ∫ t, h t * (t : 𝕜) ^ (k + 2) ∂unitIocMeasure := by
        have hint0 : Integrable
            (fun t : ℝ => ((k : 𝕜) + 2) * ((k : 𝕜) + 1) * (h t * (t : 𝕜) ^ k))
            unitIocMeasure := (integrable_mul_pow hh k).const_mul _
        have hint1 : Integrable
            (fun t : ℝ =>
              2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2) * (h t * (t : 𝕜) ^ (k + 1)))
            unitIocMeasure := (integrable_mul_pow hh (k + 1)).const_mul _
        have hint2 : Integrable
            (fun t : ℝ => ((k : 𝕜) + 4) * ((k : 𝕜) + 3) * (h t * (t : 𝕜) ^ (k + 2)))
            unitIocMeasure := (integrable_mul_pow hh (k + 2)).const_mul _
        have hB : ∫ t, (((k : 𝕜) + 2) * ((k : 𝕜) + 1) * (h t * (t : 𝕜) ^ k)
              - 2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2) * (h t * (t : 𝕜) ^ (k + 1))
              + ((k : 𝕜) + 4) * ((k : 𝕜) + 3) * (h t * (t : 𝕜) ^ (k + 2)))
                ∂unitIocMeasure
            = (∫ t, (((k : 𝕜) + 2) * ((k : 𝕜) + 1) * (h t * (t : 𝕜) ^ k)
              - 2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2) * (h t * (t : 𝕜) ^ (k + 1)))
                ∂unitIocMeasure)
              + ∫ t, ((k : 𝕜) + 4) * ((k : 𝕜) + 3) * (h t * (t : 𝕜) ^ (k + 2))
                ∂unitIocMeasure := integral_add (hint0.sub hint1) hint2
        have hA : ∫ t, (((k : 𝕜) + 2) * ((k : 𝕜) + 1) * (h t * (t : 𝕜) ^ k)
              - 2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2) * (h t * (t : 𝕜) ^ (k + 1)))
                ∂unitIocMeasure
            = (∫ t, ((k : 𝕜) + 2) * ((k : 𝕜) + 1) * (h t * (t : 𝕜) ^ k)
                ∂unitIocMeasure)
              - ∫ t, 2 * ((k : 𝕜) + 3) * ((k : 𝕜) + 2) * (h t * (t : 𝕜) ^ (k + 1))
                ∂unitIocMeasure := integral_sub hint0 hint1
        rw [integral_congr_ae (Filter.Eventually.of_forall hexp), hB, hA,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
      have hk2 := hbump k
      rw [hsplit, ih k (by omega), ih (k + 1) (by omega)] at hk2
      simp only [mul_zero, sub_zero, zero_add] at hk2
      have hc2 : ((k : 𝕜) + 4) * ((k : 𝕜) + 3) ≠ 0 := by
        have h4 : ((k : 𝕜) + 4) ≠ 0 := by
          have : ((k + 4 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast at this
          exact this
        have h3 : ((k : 𝕜) + 3) ≠ 0 := by
          have : ((k + 3 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast at this
          exact this
        exact mul_ne_zero h4 h3
      exact (mul_eq_zero.mp hk2).resolve_left hc2

/-- Every continuous function is integrable on the unit interval. -/
theorem integrable_unitIocMeasure_of_continuous {f : ℝ → 𝕜} (hf : Continuous f) :
    Integrable f unitIocMeasure := by
  rw [unitIocMeasure]
  exact (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ioc_subset_Icc_self

/-- Multiplying an integrable function on `(0,1]` by a continuous function keeps it
integrable. -/
theorem integrable_mul_of_continuous {h g : ℝ → 𝕜} (hh : Integrable h unitIocMeasure)
    (hg : Continuous g) : Integrable (fun t => h t * g t) unitIocMeasure := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.mono' (hh.norm.const_mul C)
    (hh.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [ae_mem_unitIocMeasure] with t ht
  rw [norm_mul]
  calc ‖h t‖ * ‖g t‖ ≤ ‖h t‖ * C :=
        mul_le_mul_of_nonneg_left (hC t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
    _ = C * ‖h t‖ := mul_comm _ _

/-- **All vanishing monomial moments force vanishing**: a square-integrable function on
`(0,1]` orthogonal to every monomial is almost everywhere zero.  Weierstrass approximation
against the density of bounded continuous functions in `L²`. -/
theorem ae_eq_zero_of_forall_integral_pow_eq_zero {h : ℝ → 𝕜}
    (hh : MemLp h 2 unitIocMeasure)
    (hmom : ∀ m : ℕ, ∫ t, h t * (t : 𝕜) ^ m ∂unitIocMeasure = 0) :
    h =ᵐ[unitIocMeasure] 0 := by
  have hhInt : Integrable h unitIocMeasure := hh.integrable one_le_two
  -- Every `𝕜`-polynomial function integrates to zero against `h`.
  have hpoly : ∀ p : Polynomial 𝕜,
      ∫ t, h t * Polynomial.eval (t : 𝕜) p ∂unitIocMeasure = 0 := by
    intro p
    have hexp : ∀ t : ℝ, h t * Polynomial.eval (t : 𝕜) p
        = ∑ m ∈ Finset.range (p.natDegree + 1),
            p.coeff m * (h t * (t : 𝕜) ^ m) := by
      intro t
      rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_finsetSum _ fun m _ => (integrable_mul_pow hhInt m).const_mul _]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [MeasureTheory.integral_const_mul, hmom m, mul_zero]
  -- Every continuous function integrates to zero against `h`.
  have hcont : ∀ g : ℝ → 𝕜, Continuous g →
      ∫ t, h t * g t ∂unitIocMeasure = 0 := by
    intro g hg
    refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
    have hL1 : 0 ≤ ∫ t, ‖h t‖ ∂unitIocMeasure := integral_nonneg fun t => norm_nonneg _
    have hden : (0 : ℝ) < 1 + ∫ t, ‖h t‖ ∂unitIocMeasure := by linarith
    set L : ℝ := ∫ t, ‖h t‖ ∂unitIocMeasure with hLdef
    set δ : ℝ := ε / (2 * (1 + L)) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨pre, hpre⟩ := exists_polynomial_near_of_continuousOn 0 1
      (fun t => RCLike.re (g t)) (RCLike.continuous_re.comp hg).continuousOn δ hδ
    obtain ⟨pim, hpim⟩ := exists_polynomial_near_of_continuousOn 0 1
      (fun t => RCLike.im (g t)) (RCLike.continuous_im.comp hg).continuousOn δ hδ
    have hcoe : ∀ r : ℝ, algebraMap ℝ 𝕜 r = ((r : ℝ) : 𝕜) :=
      fun r => congrFun RCLike.algebraMap_eq_ofReal r
    have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
      rcases eq_or_ne (RCLike.I : 𝕜) 0 with hzero | hne
      · rw [hzero, norm_zero]
        exact zero_le_one
      · exact le_of_eq (RCLike.norm_I_of_ne_zero hne)
    set p : Polynomial 𝕜 := pre.map (algebraMap ℝ 𝕜)
      + Polynomial.C (RCLike.I : 𝕜) * pim.map (algebraMap ℝ 𝕜) with hpdef
    have hpeval : ∀ t : ℝ, Polynomial.eval (t : 𝕜) p
        = ((pre.eval t : ℝ) : 𝕜) + (RCLike.I : 𝕜) * ((pim.eval t : ℝ) : 𝕜) := by
      intro t
      have h1 : (pre.map (algebraMap ℝ 𝕜)).eval ((t : ℝ) : 𝕜) = ((pre.eval t : ℝ) : 𝕜) := by
        rw [← hcoe t, Polynomial.eval_map, Polynomial.eval₂_hom, hcoe]
      have h2 : (pim.map (algebraMap ℝ 𝕜)).eval ((t : ℝ) : 𝕜) = ((pim.eval t : ℝ) : 𝕜) := by
        rw [← hcoe t, Polynomial.eval_map, Polynomial.eval₂_hom, hcoe]
      rw [hpdef]
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, h1, h2]
    have hpc : Continuous fun t : ℝ => Polynomial.eval (t : 𝕜) p :=
      p.continuous.comp RCLike.continuous_ofReal
    have hnear : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖g t - Polynomial.eval (t : 𝕜) p‖ ≤ 2 * δ := by
      intro t ht
      rw [hpeval]
      set a : ℝ := RCLike.re (g t) with hadef
      set b : ℝ := RCLike.im (g t) with hbdef
      have hre : |a - pre.eval t| ≤ δ := by
        rw [abs_sub_comm]
        exact (hpre t ht).le
      have him : |b - pim.eval t| ≤ δ := by
        rw [abs_sub_comm]
        exact (hpim t ht).le
      have hz : ((a : ℝ) : 𝕜) + ((b : ℝ) : 𝕜) * (RCLike.I : 𝕜) = g t :=
        RCLike.re_add_im (g t)
      have hsplit :
          g t - (((pre.eval t : ℝ) : 𝕜) + (RCLike.I : 𝕜) * ((pim.eval t : ℝ) : 𝕜))
            = ((a - pre.eval t : ℝ) : 𝕜)
              + ((b - pim.eval t : ℝ) : 𝕜) * (RCLike.I : 𝕜) := by
        rw [RCLike.ofReal_sub, RCLike.ofReal_sub, ← hz]
        ring
      rw [hsplit]
      calc ‖((a - pre.eval t : ℝ) : 𝕜) + ((b - pim.eval t : ℝ) : 𝕜) * (RCLike.I : 𝕜)‖
          ≤ ‖((a - pre.eval t : ℝ) : 𝕜)‖
              + ‖((b - pim.eval t : ℝ) : 𝕜) * (RCLike.I : 𝕜)‖ := norm_add_le _ _
        _ = |a - pre.eval t| + |b - pim.eval t| * ‖(RCLike.I : 𝕜)‖ := by
            rw [RCLike.norm_ofReal, norm_mul, RCLike.norm_ofReal]
        _ ≤ δ + δ * 1 :=
            add_le_add hre (mul_le_mul him hI (norm_nonneg _) hδ.le)
        _ = 2 * δ := by ring
    have hsplitInt : ∫ t, h t * g t ∂unitIocMeasure
        = ∫ t, h t * (g t - Polynomial.eval (t : 𝕜) p) ∂unitIocMeasure := by
      have hpt : ∀ t : ℝ, h t * g t
          = h t * (g t - Polynomial.eval (t : 𝕜) p)
            + h t * Polynomial.eval (t : 𝕜) p := by
        intro t
        ring
      have hgpInt : Integrable
          (fun t : ℝ => h t * (g t - Polynomial.eval ((t : ℝ) : 𝕜) p)) unitIocMeasure :=
        integrable_mul_of_continuous hhInt (hg.sub hpc)
      have hppInt : Integrable
          (fun t : ℝ => h t * Polynomial.eval ((t : ℝ) : 𝕜) p) unitIocMeasure :=
        integrable_mul_of_continuous hhInt hpc
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_add hgpInt hppInt, hpoly p, add_zero]
    rw [hsplitInt, zero_add]
    calc ‖∫ t, h t * (g t - Polynomial.eval (t : 𝕜) p) ∂unitIocMeasure‖
        ≤ ∫ t, ‖h t * (g t - Polynomial.eval (t : 𝕜) p)‖ ∂unitIocMeasure :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, ‖h t‖ * (2 * δ) ∂unitIocMeasure := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (hhInt.norm.mul_const _) ?_
          filter_upwards [ae_mem_unitIocMeasure] with t ht
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hnear t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
      _ = L * (2 * δ) := MeasureTheory.integral_mul_const _ _
      _ ≤ ε := by
          have hqe : δ * (2 * (1 + L)) = ε := by
            rw [hδdef]
            field_simp
          nlinarith [hδ.le, hL1]
  -- Transfer to the `L²` element and use density of bounded continuous functions.
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  set H : Lp 𝕜 2 unitIocMeasure := hh.toLp h with hHdef
  suffices hzero : H = 0 by
    have h1 : h =ᵐ[unitIocMeasure] ⇑H := (MemLp.coeFn_toLp hh).symm
    have h2 : ⇑H =ᵐ[unitIocMeasure] 0 := by
      rw [hzero]
      exact Lp.coeFn_zero 𝕜 2 unitIocMeasure
    exact h1.trans h2
  have hSsub : (Lp.boundedContinuousFunction 𝕜 2 unitIocMeasure : Set (Lp 𝕜 2 unitIocMeasure))
      ⊆ {G : Lp 𝕜 2 unitIocMeasure | ⟪G, H⟫_𝕜 = 0} := by
    intro G hG
    obtain ⟨g, hg⟩ := Lp.mem_boundedContinuousFunction_iff.mp hG
    have hGae : ⇑G =ᵐ[unitIocMeasure] ⇑g := by
      have h1 := ContinuousMap.coeFn_toAEEqFun unitIocMeasure g.toContinuousMap
      rw [hg] at h1
      exact h1
    change ⟪G, H⟫_𝕜 = 0
    rw [MeasureTheory.L2.inner_def]
    have hHae : ⇑H =ᵐ[unitIocMeasure] h := MemLp.coeFn_toLp hh
    have hcongr : ∀ᵐ t ∂unitIocMeasure, ⟪G t, H t⟫_𝕜 = h t * (starRingEnd 𝕜) (g t) := by
      filter_upwards [hGae, hHae] with t hGt hHt
      rw [RCLike.inner_apply, hGt, hHt]
    rw [integral_congr_ae hcongr]
    exact hcont (fun t => (starRingEnd 𝕜) (g t)) (RCLike.continuous_conj.comp g.continuous)
  have hdense : Dense
      (Lp.boundedContinuousFunction 𝕜 2 unitIocMeasure : Set (Lp 𝕜 2 unitIocMeasure)) :=
    Lp.boundedContinuousFunction_dense 𝕜 unitIocMeasure (by norm_num)
  have hclosed : IsClosed {G : Lp 𝕜 2 unitIocMeasure | ⟪G, H⟫_𝕜 = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hHself : ⟪H, H⟫_𝕜 = 0 := by
    have : H ∈ closure
        (Lp.boundedContinuousFunction 𝕜 2 unitIocMeasure : Set (Lp 𝕜 2 unitIocMeasure)) :=
      hdense H
    exact (hclosed.closure_subset_iff.mpr hSsub) this
  exact inner_self_eq_zero.mp hHself

/-! ## The representation theorem -/

/-- Bridge between the ambient measure integral and the interval integral. -/
theorem integral_unitIocMeasure_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ t, f t ∂unitIocMeasure = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), unitIocMeasure]

/-- **The representation theorem for weak second derivatives on the unit interval**: if the
pairing of `u` against the second derivatives of the bump family agrees with the pairing of
`w` against the bumps, then `u` is almost everywhere an affine function plus the second
primitive of `w`. -/
theorem eq_affine_add_secondPrimitive_of_forall_integral_bumpD2
    {u w : ℝ → 𝕜} (hu : MemLp u 2 unitIocMeasure) (hw : MemLp w 2 unitIocMeasure)
    (hweak : ∀ k : ℕ,
      ∫ t, u t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure
        = ∫ t, w t * (intervalBump k t : 𝕜) ∂unitIocMeasure) :
    ∃ a b : 𝕜, u =ᵐ[unitIocMeasure]
      fun t => a + b * (t : 𝕜) + secondPrimitive w t := by
  have huInt := hu.integrable one_le_two
  have hwInt := hw.integrable one_le_two
  have hKmem : MemLp (secondPrimitive w) 2 unitIocMeasure := memLp_secondPrimitive hwInt
  have hKInt : Integrable (secondPrimitive w) unitIocMeasure :=
    hKmem.integrable one_le_two
  set h : ℝ → 𝕜 := fun t => u t - secondPrimitive w t with hhdef
  have hhInt : Integrable h unitIocMeasure := huInt.sub hKInt
  have hhMem : MemLp h 2 unitIocMeasure := hu.sub hKmem
  -- the difference annihilates the bump family
  have hbump0 : ∀ k : ℕ, ∫ t, h t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure = 0 := by
    intro k
    have hψc : Continuous fun t : ℝ => (intervalBumpD2 k t : 𝕜) :=
      RCLike.continuous_ofReal.comp (continuous_intervalBumpD2 k)
    have hpt : ∀ t : ℝ, h t * (intervalBumpD2 k t : 𝕜)
        = u t * (intervalBumpD2 k t : 𝕜)
          - secondPrimitive w t * (intervalBumpD2 k t : 𝕜) := by
      intro t
      simp only [hhdef]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub (integrable_mul_of_continuous huInt hψc)
        (integrable_mul_of_continuous hKInt hψc),
      hweak k, integral_secondPrimitive_mul_intervalBumpD2 hwInt k, sub_self]
  -- affine moment computations
  have hI0 : ∫ _ : ℝ, (1 : 𝕜) ∂unitIocMeasure = 1 := by
    rw [MeasureTheory.integral_const]
    have : unitIocMeasure Set.univ = 1 := by
      rw [unitIocMeasure, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioc]
      norm_num
    simp [measureReal_def, this]
  have hI1 : ∫ t : ℝ, ((t : ℝ) : 𝕜) ∂unitIocMeasure = (1 : 𝕜) / 2 := by
    rw [_root_.integral_ofReal, integral_unitIocMeasure_eq_intervalIntegral,
      integral_id]
    norm_num [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_ofNat]
  have hI2 : ∫ t : ℝ, ((t : ℝ) : 𝕜) * ((t : ℝ) : 𝕜) ∂unitIocMeasure = (1 : 𝕜) / 3 := by
    have hpt : ∀ t : ℝ, ((t : ℝ) : 𝕜) * ((t : ℝ) : 𝕜) = ((t ^ 2 : ℝ) : 𝕜) := by
      intro t
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), _root_.integral_ofReal,
      integral_unitIocMeasure_eq_intervalIntegral]
    rw [integral_pow]
    norm_num [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_ofNat]
  set A : 𝕜 := ∫ t, h t ∂unitIocMeasure with hAdef
  set B : 𝕜 := ∫ t, h t * (t : 𝕜) ∂unitIocMeasure with hBdef
  set a : 𝕜 := 4 * A - 6 * B with hadef
  set b : 𝕜 := 12 * B - 6 * A with hbdef
  set h₀ : ℝ → 𝕜 := fun t => h t - (a + b * (t : 𝕜)) with hh₀def
  have haffc : Continuous fun t : ℝ => a + b * ((t : ℝ) : 𝕜) := by
    fun_prop
  have haffInt : Integrable (fun t : ℝ => a + b * ((t : ℝ) : 𝕜)) unitIocMeasure :=
    integrable_unitIocMeasure_of_continuous haffc
  have hh₀Int : Integrable h₀ unitIocMeasure := hhInt.sub haffInt
  have hh₀Mem : MemLp h₀ 2 unitIocMeasure := by
    refine hhMem.sub (MemLp.of_bound haffc.aestronglyMeasurable (‖a‖ + ‖b‖) ?_)
    filter_upwards [ae_mem_unitIocMeasure] with t ht
    calc ‖a + b * ((t : ℝ) : 𝕜)‖ ≤ ‖a‖ + ‖b * ((t : ℝ) : 𝕜)‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ * 1 := by
          refine add_le_add le_rfl ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [RCLike.norm_ofReal, abs_of_pos ht.1]
          exact ht.2
      _ = ‖a‖ + ‖b‖ := by ring
  have hIc : ∀ c : 𝕜, ∫ _ : ℝ, c ∂unitIocMeasure = c := by
    intro c
    have huniv : unitIocMeasure Set.univ = 1 := by
      rw [unitIocMeasure, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioc]
      norm_num
    rw [MeasureTheory.integral_const]
    simp [measureReal_def, huniv]
  have hbtInt : Integrable (fun t : ℝ => b * ((t : ℝ) : 𝕜)) unitIocMeasure :=
    integrable_unitIocMeasure_of_continuous (by fun_prop)
  -- the affine moments of `h₀` vanish by the choice of `a` and `b`
  have haff0 : ∫ t, (a + b * ((t : ℝ) : 𝕜)) ∂unitIocMeasure = a + b / 2 := by
    rw [integral_add (integrable_const a) hbtInt, hIc,
      MeasureTheory.integral_const_mul, hI1]
    ring
  have haff1 : ∫ t, (a + b * ((t : ℝ) : 𝕜)) * ((t : ℝ) : 𝕜) ∂unitIocMeasure
      = a / 2 + b / 3 := by
    have hpt : ∀ t : ℝ, (a + b * ((t : ℝ) : 𝕜)) * ((t : ℝ) : 𝕜)
        = a * ((t : ℝ) : 𝕜) + b * (((t : ℝ) : 𝕜) * ((t : ℝ) : 𝕜)) := by
      intro t
      ring
    have hatInt : Integrable (fun t : ℝ => a * ((t : ℝ) : 𝕜)) unitIocMeasure :=
      integrable_unitIocMeasure_of_continuous (by fun_prop)
    have hbt2Int : Integrable (fun t : ℝ => b * (((t : ℝ) : 𝕜) * ((t : ℝ) : 𝕜)))
        unitIocMeasure :=
      integrable_unitIocMeasure_of_continuous (by fun_prop)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hatInt hbt2Int, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, hI1, hI2]
    ring
  have h₀0 : ∫ t, h₀ t ∂unitIocMeasure = 0 := by
    simp only [hh₀def]
    rw [integral_sub hhInt haffInt, haff0, ← hAdef, hadef, hbdef]
    ring
  have h₀1 : ∫ t, h₀ t * ((t : ℝ) : 𝕜) ∂unitIocMeasure = 0 := by
    have hpt : ∀ t : ℝ, h₀ t * ((t : ℝ) : 𝕜)
        = h t * ((t : ℝ) : 𝕜) - (a + b * ((t : ℝ) : 𝕜)) * ((t : ℝ) : 𝕜) := by
      intro t
      simp only [hh₀def]
      ring
    have htmulInt : Integrable (fun t : ℝ => h t * ((t : ℝ) : 𝕜)) unitIocMeasure :=
      integrable_mul_of_continuous hhInt (by fun_prop)
    have haffmulInt : Integrable
        (fun t : ℝ => (a + b * ((t : ℝ) : 𝕜)) * ((t : ℝ) : 𝕜)) unitIocMeasure :=
      integrable_unitIocMeasure_of_continuous (by fun_prop)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub htmulInt haffmulInt, haff1, ← hBdef, hadef, hbdef]
    ring
  have h₀bump : ∀ k : ℕ, ∫ t, h₀ t * (intervalBumpD2 k t : 𝕜) ∂unitIocMeasure = 0 := by
    intro k
    have hψ0 : ∫ t, ((intervalBumpD2 k t : ℝ) : 𝕜) ∂unitIocMeasure = 0 := by
      rw [_root_.integral_ofReal, integral_unitIocMeasure_eq_intervalIntegral,
        integral_intervalBumpD2]
      norm_num
    have hψ1 : ∫ t, ((t : ℝ) : 𝕜) * ((intervalBumpD2 k t : ℝ) : 𝕜) ∂unitIocMeasure
        = 0 := by
      have hpt : ∀ t : ℝ, ((t : ℝ) : 𝕜) * ((intervalBumpD2 k t : ℝ) : 𝕜)
          = ((t * intervalBumpD2 k t : ℝ) : 𝕜) := by
        intro t
        push_cast
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), _root_.integral_ofReal,
        integral_unitIocMeasure_eq_intervalIntegral, integral_id_mul_intervalBumpD2]
      norm_num
    have hψc : Continuous fun t : ℝ => (intervalBumpD2 k t : 𝕜) :=
      RCLike.continuous_ofReal.comp (continuous_intervalBumpD2 k)
    have hpt : ∀ t : ℝ, h₀ t * (intervalBumpD2 k t : 𝕜)
        = h t * (intervalBumpD2 k t : 𝕜)
          - (a * (intervalBumpD2 k t : 𝕜)
            + b * (((t : ℝ) : 𝕜) * (intervalBumpD2 k t : 𝕜))) := by
      intro t
      simp only [hh₀def]
      ring
    have h1Int : Integrable (fun t : ℝ => a * (intervalBumpD2 k t : 𝕜)) unitIocMeasure :=
      integrable_unitIocMeasure_of_continuous (by fun_prop)
    have h2Int : Integrable
        (fun t : ℝ => b * (((t : ℝ) : 𝕜) * (intervalBumpD2 k t : 𝕜))) unitIocMeasure :=
      integrable_unitIocMeasure_of_continuous (by fun_prop)
    have h12Int : Integrable
        (fun t : ℝ => a * (intervalBumpD2 k t : 𝕜)
          + b * (((t : ℝ) : 𝕜) * (intervalBumpD2 k t : 𝕜))) unitIocMeasure :=
      h1Int.add h2Int
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub (integrable_mul_of_continuous hhInt hψc) h12Int,
      integral_add h1Int h2Int, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, hψ0, hψ1, hbump0 k]
    ring
  -- all monomial moments of `h₀` vanish, so `h₀` vanishes
  have hmom := integral_pow_eq_zero_of_forall_integral_bumpD2 hh₀Int h₀bump h₀0
    (by simpa using h₀1)
  have hzero : h₀ =ᵐ[unitIocMeasure] 0 :=
    ae_eq_zero_of_forall_integral_pow_eq_zero hh₀Mem hmom
  refine ⟨a, b, ?_⟩
  filter_upwards [hzero] with t ht
  have ht' : h₀ t = 0 := ht
  simp only [hh₀def, hhdef] at ht'
  linear_combination ht'

end

end TauCeti
