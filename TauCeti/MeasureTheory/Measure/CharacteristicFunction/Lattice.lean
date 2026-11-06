/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Frequencies where a characteristic function equals one

A probability law has characteristic function equal to one at a frequency precisely when
its phase is almost surely an integer multiple of `2π`. This concerns equality to one,
not merely modulus one: the latter also allows translated lattices.

The inner-product-space statement identifies the frequencies `t` with `charFun μ t = 1`.
On the real line, its phase condition describes an unshifted lattice.
For a probability law on `ℝ≥0`, the characteristic function of its real pushforward equals
one at `2π/a` exactly when the law is concentrated on `a ℕ`, for `a > 0`. Consequently,
laws not concentrated on any such unshifted lattice are precisely those for which zero is
the only such frequency. These criteria require no moment assumption and permit an atom at zero.

See W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
second edition (1971), Chapter XI, for the renewal-theoretic use of the lattice obstruction.
-/

public section

open Complex
open scoped RealInnerProductSpace

namespace MeasureTheory

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- A characteristic function equals one exactly when its integrand is almost surely one.
Unlike an equality of moduli, this does not permit a nontrivial constant phase. -/
theorem charFun_eq_one_iff (t : E) :
    charFun μ t = 1 ↔ ∀ᵐ x ∂μ, exp (⟪x, t⟫ * I) = 1 := by
  have hi : Integrable (fun x : E => exp (⟪x, t⟫ * I)) μ :=
    ⟨by fun_prop, .of_bounded (C := 1) (ae_of_all _ fun x => by simp)⟩
  constructor
  · intro h
    have hre : (fun x : E => (exp (⟪x, t⟫ * I)).re) =ᵐ[μ] fun _ => 1 := by
      apply (integral_eq_iff_of_ae_le hi.re (integrable_const 1)
        (ae_of_all _ fun x => (re_le_norm _).trans (by simp))).mp
      simp only [integral_re hi, ← charFun_apply, h, RCLike.one_re, integral_const,
        probReal_univ, smul_eq_mul, mul_one]
    filter_upwards [hre] with x hx
    apply Complex.ext hx
    simpa using (abs_re_eq_norm.mp (by simp [hx] :
      |(exp (⟪x, t⟫ * I)).re| = ‖exp (⟪x, t⟫ * I)‖))
  · intro h
    exact integral_eq_const h

/-- The frequencies `t` with `charFun μ t = 1` are those whose inner-product phases
are almost surely integer multiples of `2π`. -/
theorem charFun_eq_one_iff_ae_inner_mem_int_mul (t : E) :
    charFun μ t = 1 ↔ ∀ᵐ x ∂μ, ∃ n : ℤ, ⟪x, t⟫ = n * (2 * Real.pi) := by
  rw [charFun_eq_one_iff]
  apply Filter.eventually_congr
  filter_upwards [] with x
  rw [exp_eq_one_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa using congrArg Complex.im hn
  · simp only [hn, ofReal_mul, ofReal_intCast, ofReal_ofNat]
    ring

end MeasureTheory

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- At a positive reciprocal-span frequency, the characteristic function equals one
exactly when the interarrival law is concentrated on the corresponding nonnegative lattice. -/
theorem charFun_map_coe_eq_one_iff (a : ℝ≥0) (ha : 0 < a) :
    charFun (μ.map NNReal.toReal) (2 * Real.pi / a) = 1 ↔
      μ (range (fun n : ℕ => (n : ℝ≥0) * a))ᶜ = 0 := by
  rw [charFun_eq_one_iff, ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) measurable_const), ← mem_ae_iff]
  apply Filter.eventually_congr
  filter_upwards [] with x
  simp only [RCLike.inner_apply, conj_trivial]
  rw [exp_eq_one_iff_of_im_nonneg (by
    simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, mul_zero, add_zero]
    positivity)]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, NNReal.coe_injective ?_⟩
    have h : 2 * Real.pi / (a : ℝ) * x = n * (2 * Real.pi) := by
      simpa using congrArg Complex.im hn
    field_simp at h
    simpa [mul_comm] using h.symm
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    push_cast
    field_simp

/-- A nonnegative probability law has a nonzero frequency where its characteristic function
equals one exactly when it is concentrated on an unshifted lattice of positive span. -/
theorem exists_ne_zero_charFun_map_coe_eq_one_iff :
    (∃ t : ℝ, t ≠ 0 ∧ charFun (μ.map NNReal.toReal) t = 1) ↔
      ∃ a : ℝ≥0, 0 < a ∧ μ (range (fun n : ℕ => (n : ℝ≥0) * a))ᶜ = 0 := by
  constructor
  · rintro ⟨t, ht, h⟩
    have habs : 0 < |t| := abs_pos.mpr ht
    have habs_eq : charFun (μ.map NNReal.toReal) |t| = 1 := by
      rcases le_total 0 t with ht' | ht'
      · simpa [abs_of_nonneg ht'] using h
      · simp [abs_of_nonpos ht', charFun_neg, h]
    let a : ℝ≥0 := ⟨2 * Real.pi / |t|, by positivity⟩
    have ha : 0 < a := (NNReal.coe_pos).mp (div_pos Real.two_pi_pos habs)
    refine ⟨a, ha, (charFun_map_coe_eq_one_iff μ a ha).mp ?_⟩
    have hfreq : 2 * Real.pi / (a : ℝ) = |t| := by
      have ha_coe : (a : ℝ) = 2 * Real.pi / |t| := rfl
      rw [ha_coe]
      field_simp
    rwa [hfreq]
  · rintro ⟨a, ha, h⟩
    exact ⟨2 * Real.pi / a, ne_of_gt (by positivity),
      (charFun_map_coe_eq_one_iff μ a ha).mpr h⟩

/-- No unshifted lattice `a ℕ` with `a > 0` carries the law if and only if the characteristic
function differs from one at every nonzero frequency. -/
theorem forall_ne_zero_charFun_map_coe_ne_one_iff :
    (∀ t : ℝ, t ≠ 0 → charFun (μ.map NNReal.toReal) t ≠ 1) ↔
      ∀ a : ℝ≥0, 0 < a → μ (range (fun n : ℕ => (n : ℝ≥0) * a))ᶜ ≠ 0 := by
  simpa only [not_exists, not_and] using
    not_congr (exists_ne_zero_charFun_map_coe_eq_one_iff (μ := μ))

end MeasureTheory.Measure
