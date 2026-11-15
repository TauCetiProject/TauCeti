/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Analysis.Normed.Ring.DualNumber
import TauCeti.RingTheory.PowerSeries.CoeffProd
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Eval
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Schwarz

/-!
# Examples and counterexamples for Schwarz contraction of power series

These examples exercise the two-radii Gauss-norm contraction and the characteristic-zero unit-disc
coefficient and evaluation bounds in `TauCeti.RingTheory.PowerSeries.Weierstrass.Schwarz`:

* **Sharpness over `ℚ_[p]`.** For `f = (X - 1) ^ S` over `ℚ_[p]` and any outer radius `r > 1`,
  `‖coeff k f‖ * r ^ k ≤ r ^ S` for all `k` and the iterated formal derivatives of order `j < S`
  vanish at `1`. Both `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` and
  `PowerSeries.norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero` give the bound
  `r ^ S * (r ^ S)⁻¹ = 1`, which is attained at `k = 0` and at `x = 0`.
* **Non-restricted boundary series over `ℚ_[p]`.** The series
  `f = (X - 1) * ∑ p ^ n X ^ n` over `ℚ_[p]` satisfies `‖coeff (n + 1) f‖ * p ^ (n + 1) = p` for
  every `n`, so it is *not* restricted at the outer radius `r = p` and the restricted contraction
  `PowerSeries.IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow` does not apply at `r = p`. Its
  weighted coefficients are nevertheless bounded by `M = p`, it vanishes at `1`, and
  `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` yields the sharp bound
  `‖coeff k f‖ ≤ 1` for all `k`.
* **Necessity of `‖a‖ ≤ 1`.** Over `ℚ_[p]` at radius `r = p > 1`, the polynomial `f = X - p⁻¹` has
  `‖coeff k f‖ * p ^ k ≤ p` for all `k` and vanishes at `a = p⁻¹`, which lies outside the unit disc
  (`‖p⁻¹‖ = p > 1`); its constant coefficient has norm `p > 1 = p * (p ^ 1)⁻¹`.
* **Trivial valuation: non-`NontriviallyNormedField` witness and necessity of `[CharZero K]`.**
  Equipping a field `F` with `AbsoluteValue.trivial` gives a complete ultrametric `NormedField`
  whose norms lie in `{0, 1}`, so it is never nontrivially normed. Taking `F = ℚ` exercises
  `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` outside
  `NontriviallyNormedField`. Taking `F = ZMod p` (`p` prime), the polynomial `f = X ^ p - 1`
  vanishes at `1` and has `(d⁄dX)^[j] f = 0` for every `j ≥ 1`, so all formal derivatives of order
  `< p + 1` vanish at `1`, yet at `r = 2` (`M = 2 ^ p`) we have
  `‖coeff 0 f‖ = 1 > 2⁻¹ = 2 ^ p * (2 ^ (p + 1))⁻¹`; meanwhile `(D⁽ᵖ⁾ f)(1) = 1 ≠ 0` and the
  Hasse-derivative contraction `PowerSeries.IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow_sum`
  applies in characteristic `p` with multiplicity `p`.
* **Integral domains vs. zero divisors.** Over `ℤ_[p]` (a non-field domain), two-radii Gauss-norm
  contraction applies directly; over `MaxDualNumber ℚ_[p]` (`ε ^ 2 = 0`, `‖ε‖ = 1`), the monomial
  `ε X` vanishes at both `0` and `ε` in the unit disc yet `‖ε X‖₁ = 1 > 2 * (1 / 2) ^ 2`, showing
  `[NoZeroDivisors R]` is necessary.
-/

public section

open PowerSeries TauCeti.PowerSeries TauCeti.MaxDualNumber

namespace TauCeti.Examples

section PadicSharpness

/-- For `‖a‖ ≤ r` and `0 < r`, the Gauss norm of `(X - a) ^ S` at `r` over an ultrametric normed
commutative ring with `‖1‖ = 1` is `r ^ S`. -/
private theorem gaussNorm_X_sub_C_pow {R : Type*} [NormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] {r : ℝ} (hr : 0 < r) {a : R} (ha : ‖a‖ ≤ r) (S : ℕ) :
    ((X - C a : R⟦X⟧) ^ S).gaussNorm norm r = r ^ S := by
  induction S with
  | zero =>
    refine le_antisymm ?_ ?_
    · rw [pow_zero, pow_zero, gaussNorm_eq]
      refine Real.iSup_le (fun n ↦ ?_) zero_le_one
      rcases n with _ | n <;> simp
    · simpa using le_gaussNorm norm r (1 : R⟦X⟧)
        (hasGaussNorm_of_isRestricted (isRestricted_one r)) 0
  | succ S ih =>
    have hS : ((X - C a : R⟦X⟧) ^ S).IsRestricted r :=
      (IsRestricted.subring r).pow_mem (isRestricted_X_sub_C a) S
    rw [pow_succ', gaussNorm_X_sub_C_mul hr ha hS, ih, pow_succ']

variable (p : ℕ) [hp : Fact p.Prime]

/-- Over `ℚ_[p]`, both `PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` and
`PowerSeries.norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero` apply to
`f = (X - 1) ^ S` at any radius `r > 1` with `M = r ^ S` and `A = {1}`, and both bounds are
attained (at `k = 0` and at `x = 0`). -/
theorem sharp_X_sub_one_pow (S : ℕ) {r : ℝ} (hr : 1 < r) :
    (∀ k, ‖coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)‖ ≤
        r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹) ∧
      (∀ x : ℚ_[p], ‖x‖ ≤ 1 →
        ‖FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
            (fun k ↦ coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)) x‖ ≤
          r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹) ∧
      ‖coeff 0 ((X - 1 : ℚ_[p]⟦X⟧) ^ S)‖ =
        r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹ ∧
      ‖FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
          (fun k ↦ coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)) 0‖ =
        r ^ S * (r ^ (({1} : Finset ℚ_[p]).card * S))⁻¹ := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hfR : ((X - 1 : ℚ_[p]⟦X⟧) ^ S).IsRestricted r := by
    rw [← map_one C]
    exact (IsRestricted.subring r).pow_mem (isRestricted_X_sub_C (1 : ℚ_[p])) S
  have hM : ∀ k, ‖coeff k ((X - 1 : ℚ_[p]⟦X⟧) ^ S)‖ * r ^ k ≤ r ^ S := fun k ↦ by
    have hg := gaussNorm_X_sub_C_pow hr0 (a := (1 : ℚ_[p])) (by simp [hr.le]) S
    rw [map_one] at hg
    exact hg ▸ le_gaussNorm norm r _ (hasGaussNorm_of_isRestricted hfR) k
  have hA : ∀ a ∈ ({1} : Finset ℚ_[p]), ‖a‖ ≤ 1 := by simp
  have hvan : ∀ a ∈ ({1} : Finset ℚ_[p]), ∀ j < S,
      FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
        (fun k ↦ coeff k ((⇑(derivative (R := ℚ_[p])))^[j] ((X - 1 : ℚ_[p]⟦X⟧) ^ S))) a = 0 := by
    intro a ha j hj
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [← evalAt_eq_ofScalarsSum, evalAt_iterate_derivative_eq_zero_iff, ← map_one C,
      evalAt_hasseDeriv_X_sub_C_pow]
    simp [hj.ne]
  refine ⟨norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero hr hM {1} hA S hvan,
    fun x hx ↦ norm_ofScalarsSum_le_of_ofScalarsSum_iterate_derivative_eq_zero hr hM {1} hA S hvan
      hx, ?_, ?_⟩
  · simp [mul_inv_cancel₀ (pow_ne_zero S hr0.ne')]
  · simp [mul_inv_cancel₀ (pow_ne_zero S hr0.ne')]

end PadicSharpness

section BoundaryNonRestricted

variable (p : ℕ) [hp : Fact p.Prime]

/-- The series `(X - 1) * ∑ₙ pⁿ Xⁿ` over `ℚ_[p]`, whose weighted coefficients at radius `p` all
have norm `p` in positive degrees so that it has bounded Gauss norm at `p` without being restricted
there. -/
noncomputable def boundaryGeom : ℚ_[p]⟦X⟧ :=
  (X - 1) * PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ n

private theorem norm_coeff_succ_boundaryGeom (n : ℕ) :
    ‖coeff (n + 1) (boundaryGeom p)‖ * (p : ℝ) ^ (n + 1) = p := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hunit : ‖(1 - p : ℚ_[p])‖ = 1 := by
    rw [sub_eq_add_neg]
    simpa [Padic.norm_p, inv_le_one_of_one_le₀ hp1.le] using
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ℚ_[p])) (y := -(p : ℚ_[p]))
        (by rw [norm_one, norm_neg, Padic.norm_p]; exact (inv_lt_one_of_one_lt₀ hp1).ne')
  have hcoeff : coeff (n + 1) (boundaryGeom p) = (p : ℚ_[p]) ^ n * (1 - p) := by
    rw [boundaryGeom, ← map_one C, PowerSeries.coeff_succ_X_sub_C_mul, coeff_mk, coeff_mk]
    ring
  rw [hcoeff, norm_mul, hunit, mul_one, norm_pow, Padic.norm_p, inv_pow, pow_succ, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero n hp0), one_mul]

/-- `boundaryGeom p` is not restricted at radius `p`, yet its weighted coefficients at `p` are
bounded by `p`, it vanishes at `1`, and
`PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` bounds all its coefficients
by `1` (attained at `k = 0`). -/
theorem not_isRestricted_and_norm_coeff_le_boundaryGeom :
    ¬ (boundaryGeom p).IsRestricted p ∧
      (∀ k, ‖coeff k (boundaryGeom p)‖ ≤ 1) ∧
      ‖coeff 0 (boundaryGeom p)‖ = 1 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hM : ∀ k, ‖coeff k (boundaryGeom p)‖ * (p : ℝ) ^ k ≤ p := by
    rintro (_ | n)
    · rw [boundaryGeom, ← map_one C, PowerSeries.coeff_zero_X_sub_C_mul, coeff_mk]
      simp [hp1.le]
    · exact (norm_coeff_succ_boundaryGeom p n).le
  refine ⟨fun hrest ↦ ?_, fun k ↦ ?_, ?_⟩
  · have htend := ((PowerSeries.isRestricted_iff' _ _).mp hrest).comp
      (Filter.tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, norm_coeff_succ_boundaryGeom] at htend
    exact hp0.ne (tendsto_nhds_unique htend tendsto_const_nhds)
  · have hg : (PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted 1 := by
      rw [PowerSeries.isRestricted_iff']
      simpa [Padic.norm_p] using tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hp1)
    have hX : (X - 1 : ℚ_[p]⟦X⟧).IsRestricted 1 := by
      simpa using isRestricted_X_sub_C (c := 1) (1 : ℚ_[p])
    have hvan : ∀ a ∈ ({1} : Finset ℚ_[p]), ∀ j < 1,
        FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
          (fun m ↦ coeff m ((⇑(derivative (R := ℚ_[p])))^[j] (boundaryGeom p))) a = 0 := by
      intro a ha j hj
      rw [Finset.mem_singleton] at ha
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      subst ha
      rw [Function.iterate_zero_apply, ← evalAt_eq_ofScalarsSum, boundaryGeom,
        hX.evalAt_mul hg (by simp), ← map_one C, evalAt_X_sub_C]
      simp
    simpa [mul_inv_cancel₀ hp0.ne'] using
      norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero hp1 hM {1} (by simp) 1 hvan k
  · rw [boundaryGeom, ← map_one C, PowerSeries.coeff_zero_X_sub_C_mul, coeff_mk]
    simp

end BoundaryNonRestricted

section RejectionUnitDisc

variable (p : ℕ) [hp : Fact p.Prime]

-- Rejection test for `‖a‖ ≤ 1`: over `ℚ_[p]` at radius `r = p > 1`, the polynomial `f = X - p⁻¹`
-- satisfies `‖coeff k f‖ * p ^ k ≤ p` for all `k` and vanishes at `a = p⁻¹`, which violates
-- `‖a‖ ≤ 1`, and its constant coefficient has norm `p > 1 = p * (p ^ 1)⁻¹`.
example :
    (∀ k, ‖coeff k (X - C (p : ℚ_[p])⁻¹)‖ * (p : ℝ) ^ k ≤ p) ∧
      FormalMultilinearSeries.ofScalarsSum (E := ℚ_[p])
        (fun k ↦ coeff k (X - C (p : ℚ_[p])⁻¹)) (p : ℚ_[p])⁻¹ = 0 ∧
      1 < ‖(p : ℚ_[p])⁻¹‖ ∧
      ¬ (‖coeff 0 (X - C (p : ℚ_[p])⁻¹)‖ ≤
          (p : ℝ) * ((p : ℝ) ^ (({(p : ℚ_[p])⁻¹} : Finset ℚ_[p]).card * 1))⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine ⟨fun k ↦ ?_, ?_, ?_, ?_⟩
  · rcases k with _ | _ | k
    · simp [Padic.norm_p]
    · simp
    · simp [coeff_X, Nat.cast_nonneg]
  · rw [← evalAt_eq_ofScalarsSum, evalAt_X_sub_C]
    simp
  · simpa [Padic.norm_p] using hp1
  · simp [Padic.norm_p, mul_inv_cancel₀ hp0, not_le.mpr hp1]

end RejectionUnitDisc

section TrivialValuationAndCharP

/-- A field `F` equipped with the trivial absolute value `AbsoluteValue.trivial`. -/
abbrev TrivialValField (F : Type*) [Field F] [DecidableEq F] :=
  WithAbs (AbsoluteValue.trivial : AbsoluteValue F ℝ)

private theorem norm_trivialValField_eq_one {F : Type*} [Field F] [DecidableEq F]
    {x : TrivialValField F} (hx : x ≠ 0) : ‖x‖ = 1 := by
  rw [WithAbs.norm_eq_apply_ofAbs, AbsoluteValue.trivial_apply (by simpa using hx)]

private theorem norm_trivialValField_le_one {F : Type*} [Field F] [DecidableEq F]
    (x : TrivialValField F) : ‖x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [norm_trivialValField_eq_one hx]

noncomputable instance instIsUltrametricDistTrivialValField (F : Type*) [Field F] [DecidableEq F] :
    IsUltrametricDist (TrivialValField F) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun _ ↦
    norm_trivialValField_le_one _

noncomputable instance instCompleteSpaceTrivialValField (F : Type*) [Field F] [DecidableEq F] :
    CompleteSpace (TrivialValField F) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (1 / 2) (by positivity)
  refine ⟨u N, tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_⟩
  by_contra hne
  have hd : dist (u n) (u N) = 1 := by
    rw [dist_eq_norm, norm_trivialValField_eq_one (sub_ne_zero.mpr hne)]
  linarith [hN n hn N le_rfl]

instance instCharPTrivialValField (F : Type*) [Field F] [DecidableEq F] (p : ℕ) [CharP F p] :
    CharP (TrivialValField F) p :=
  ⟨fun n ↦ by rw [← (WithAbs.equiv _).map_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff F p]⟩

instance instCharZeroTrivialValField (F : Type*) [Field F] [DecidableEq F] [CharZero F] :
    CharZero (TrivialValField F) :=
  CharP.charP_to_charZero _

/-- `TrivialValField F` never admits an element of norm strictly greater than `1`, so it is not a
`NontriviallyNormedField`; nevertheless, for `F = ℚ`,
`PowerSeries.norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero` applies directly to it. -/
theorem not_exists_one_lt_norm_and_coeff_bound_trivialValRat :
    (¬ ∃ x : TrivialValField ℚ, 1 < ‖x‖) ∧
      ∀ k, ‖coeff k (X - 1 : (TrivialValField ℚ)⟦X⟧)‖ ≤
        (2 : ℝ) * ((2 : ℝ) ^ (({1} : Finset (TrivialValField ℚ)).card * 1))⁻¹ := by
  refine ⟨fun ⟨x, hx⟩ ↦ (norm_trivialValField_le_one x).not_gt hx, fun k ↦ ?_⟩
  refine norm_coeff_le_of_ofScalarsSum_iterate_derivative_eq_zero (by norm_num : (1 : ℝ) < 2)
    (fun m ↦ ?_) {1} (fun a _ ↦ norm_trivialValField_le_one a) 1 (fun a ha j hj ↦ ?_) k
  · rcases m with _ | _ | m
    · simp
    · simp [coeff_X]
    · simp [coeff_X]
  · rw [Finset.mem_singleton] at ha
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    subst ha
    rw [Function.iterate_zero_apply, ← evalAt_eq_ofScalarsSum, ← map_one C, evalAt_X_sub_C]
    simp

-- Rejection test for `[CharZero K]`: over `K = TrivialValField (ZMod p)` (`p` prime), the
-- polynomial `f = X ^ p - 1` has `‖coeff k f‖ * 2 ^ k ≤ 2 ^ p` for all `k` and all iterated formal
-- derivatives of order `j < p + 1` vanish at `1`, yet `‖coeff 0 f‖ = 1 > 2 ^ p * (2 ^ (p + 1))⁻¹`.
-- By contrast, `(D⁽ᵖ⁾ f)(1) = 1 ≠ 0` and the Hasse-derivative contraction bounds `‖f‖₁` by `1`.
example (p : ℕ) [hp : Fact p.Prime] :
    let f : (TrivialValField (ZMod p))⟦X⟧ := X ^ p - 1
    (∀ k, ‖coeff k f‖ * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ p) ∧
      (∀ a ∈ ({1} : Finset (TrivialValField (ZMod p))), ∀ j < p + 1,
        FormalMultilinearSeries.ofScalarsSum (E := TrivialValField (ZMod p))
          (fun k ↦ coeff k ((⇑(derivative (R := TrivialValField (ZMod p))))^[j] f)) a = 0) ∧
      ¬ (‖coeff 0 f‖ ≤
          (2 : ℝ) ^ p *
            ((2 : ℝ) ^ (({1} : Finset (TrivialValField (ZMod p))).card * (p + 1)))⁻¹) ∧
      (hasseDeriv p f).evalAt (1 : TrivialValField (ZMod p)) = 1 ∧
      f.gaussNorm norm 1 ≤ 1 := by
  intro f
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have : CharP (TrivialValField (ZMod p))⟦X⟧ p :=
    ⟨fun n ↦ by
      rw [← map_natCast C, ← CharP.cast_eq_zero_iff (TrivialValField (ZMod p)) p]
      exact ⟨fun h ↦ by simpa using congrArg constantCoeff h, fun h ↦ by simp [h]⟩⟩
  have hsub : f = (X - C (1 : TrivialValField (ZMod p))) ^ p := by
    dsimp [f]
    rw [map_one, sub_pow_char, one_pow]
  have hfR : f.IsRestricted 2 :=
    hsub ▸ (IsRestricted.subring 2).pow_mem (isRestricted_X_sub_C _) p
  have hfg : f.gaussNorm norm 2 = (2 : ℝ) ^ p :=
    hsub ▸ gaussNorm_X_sub_C_pow (by norm_num : (0 : ℝ) < 2)
      ((norm_trivialValField_le_one _).trans (by norm_num)) p
  have hM : ∀ k, ‖coeff k f‖ * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ p := fun k ↦
    hfg ▸ le_gaussNorm norm 2 f (hasGaussNorm_of_isRestricted hfR) k
  have hderiv1 : derivative (R := TrivialValField (ZMod p)) f = 0 :=
    PowerSeries.ext fun n ↦ by
      change coeff n (derivative (R := TrivialValField (ZMod p)) (X ^ p - 1)) = 0
      rw [map_sub, derivative_one, sub_zero, coeff_derivative, coeff_X_pow]
      split_ifs with h
      · rw [one_mul, ← Nat.cast_one, ← Nat.cast_add, h, CharP.cast_eq_zero]
      · simp
  refine ⟨hM, fun a ha j hj ↦ ?_, ?_, ?_, ?_⟩
  · clear hj
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [← evalAt_eq_ofScalarsSum]
    rcases j with _ | j
    · rw [Function.iterate_zero_apply, hsub]
      simpa [hasseDeriv_zero, hp0.symm] using
        evalAt_hasseDeriv_X_sub_C_pow (1 : TrivialValField (ZMod p)) 0 p
    · have h0 : ((⇑(derivative (R := TrivialValField (ZMod p))))^[j]
          (0 : (TrivialValField (ZMod p))⟦X⟧)) = 0 := by
        induction j with
        | zero => rfl
        | succ j ih => rw [Function.iterate_succ_apply', ih, map_zero]
      rw [Function.iterate_succ_apply, hderiv1, h0, evalAt_zero]
  · have hc0 : ‖coeff 0 f‖ = 1 := by simp [hsub]
    have hRHS : (2 : ℝ) ^ p *
        ((2 : ℝ) ^ (({1} : Finset (TrivialValField (ZMod p))).card * (p + 1)))⁻¹ = 2⁻¹ := by
      rw [Finset.card_singleton, one_mul, pow_succ]
      field_simp
    rw [hc0, hRHS]
    norm_num
  · rw [hsub, evalAt_hasseDeriv_X_sub_C_pow]
    simp
  · have hzero : ∀ b ∈ ({1} : Finset (TrivialValField (ZMod p))), ∀ t < p,
        (hasseDeriv t f).evalAt b = 0 := by
      intro b hb t ht
      rw [Finset.mem_singleton] at hb
      subst hb
      rw [hsub, evalAt_hasseDeriv_X_sub_C_pow]
      simp [ht.ne]
    have hg := hfR.gaussNorm_le_gaussNorm_mul_div_pow_sum (by norm_num : (0 : ℝ) < 2) zero_le_one
      (by norm_num) (A := {1}) (T := fun _ ↦ p) (fun b _ ↦ norm_trivialValField_le_one b) hzero
    simpa [hfg, inv_pow, mul_inv_cancel₀ (pow_ne_zero p (two_ne_zero : (2 : ℝ) ≠ 0))] using hg

end TrivialValuationAndCharP

section DomainAndZeroDivisors

variable (p : ℕ) [hp : Fact p.Prime]

-- Non-field domain witness: `ℤ_[p]` is not a field (`p ≠ 0` is not a unit), yet
-- `PowerSeries.IsRestricted.gaussNorm_le_gaussNorm_mul_div_pow_sum` applies directly over `ℤ_[p]`.
example : ¬ IsField ℤ_[p] ∧ (X - 1 : ℤ_[p]⟦X⟧).gaussNorm norm 1 ≤ 1 := by
  refine ⟨fun hF ↦ ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hF.mul_inv_cancel (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : ℤ_[p]) ≠ 0)
    have h1 := congrArg norm hu
    rw [norm_mul, PadicInt.norm_p, norm_one] at h1
    have hle : (p : ℝ)⁻¹ * ‖u‖ ≤ (p : ℝ)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (PadicInt.norm_le_one u) (by positivity)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith [h1, hle, inv_lt_one_of_one_lt₀ hp1]
  · have hX : (X - 1 : ℤ_[p]⟦X⟧).IsRestricted 2 := by
      simpa using isRestricted_X_sub_C (c := 2) (1 : ℤ_[p])
    have hg2 : (X - 1 : ℤ_[p]⟦X⟧).gaussNorm norm 2 = 2 := by
      simpa using gaussNorm_X_sub_C_pow (by norm_num : (0 : ℝ) < 2) (a := (1 : ℤ_[p]))
        (by norm_num) 1
    have hzero : ∀ b ∈ ({1} : Finset ℤ_[p]), ∀ t < 1,
        (hasseDeriv t (X - 1 : ℤ_[p]⟦X⟧)).evalAt b = 0 := by
      intro b hb t ht
      rw [Finset.mem_singleton] at hb
      obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      subst hb
      rw [hasseDeriv_zero, LinearMap.id_apply, ← map_one C, evalAt_X_sub_C]
      simp
    simpa [hg2] using hX.gaussNorm_le_gaussNorm_mul_div_pow_sum (by norm_num : (0 : ℝ) < 2)
      zero_le_one (by norm_num) (A := {1}) (T := fun _ ↦ 1) (by simp) hzero

-- Rejection test for `[NoZeroDivisors R]`: over `R = MaxDualNumber ℚ_[p]` (`ε ^ 2 = 0`, `‖ε‖ = 1`),
-- `f = monomial 1 ε` vanishes at both distinct points `0` and `ε` of the unit disc, yet
-- `‖f‖₁ = 1 > 2⁻¹ = ‖f‖₂ * (1 / 2) ^ ({0, ε}.card)`.
example [DecidableEq (MaxDualNumber ℚ_[p])] :
    let f : (MaxDualNumber ℚ_[p])⟦X⟧ := monomial 1 eps
    f.IsRestricted 2 ∧
      (∀ b ∈ ({0, eps} : Finset (MaxDualNumber ℚ_[p])), ‖b‖ ≤ 1) ∧
      (∀ b ∈ ({0, eps} : Finset (MaxDualNumber ℚ_[p])), ∀ t < 1,
        (hasseDeriv t f).evalAt b = 0) ∧
      ¬ (f.gaussNorm norm 1 ≤
          f.gaussNorm norm 2 * (1 / 2) ^ ∑ _b ∈ ({0, eps} : Finset (MaxDualNumber ℚ_[p])), 1) := by
  intro f
  have h0eps : (0 : MaxDualNumber ℚ_[p]) ≠ eps := fun h ↦ by simpa using congrArg norm h
  have hg (c : ℝ) (hc : 0 ≤ c) : f.gaussNorm norm c = c := by
    refine le_antisymm ?_ ?_
    · rw [gaussNorm_eq]
      refine Real.iSup_le (fun n ↦ ?_) hc
      dsimp [f]
      rw [coeff_monomial]
      split_ifs with hn
      · subst hn; simp
      · simp [hc]
    · simpa [f] using le_gaussNorm norm c f
        (hasGaussNorm_of_isRestricted (isRestricted_monomial c 1 eps)) 1
  refine ⟨isRestricted_monomial 2 1 eps, ?_, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp
    · rw [Finset.mem_singleton.mp hb]; simp
  · intro b hb t ht
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    rw [hasseDeriv_zero, LinearMap.id_apply]
    dsimp [f]
    rw [evalAt_monomial, pow_one, smul_eq_mul]
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp
    · rw [Finset.mem_singleton.mp hb]; simp
  · rw [hg 1 zero_le_one, hg 2 (by norm_num), Finset.sum_const, Finset.card_pair h0eps]
    norm_num

end DomainAndZeroDivisors

end TauCeti.Examples
