/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.ArithmeticDirichletSeries.AbelSummation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Both are stable under deleting finitely many Euler factors, the operation a character family
needs at the bad primes of its modulus. A one-prime recurrence relates the partial sums after
inserting a forbidden prime to two partial sums before the insertion
(`TauCeti.MultiplicativeIdealWeight.idealSummatory_restrict_insert`). Iterating this recurrence
shows that cancellation passes to the restriction (`TauCeti.HasCancellation.restrict`); on
`Re s > 1` the two continued
`L`-functions differ by the entire factor `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))`
(`TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re`), and under cancellation that identity
propagates to the whole half-plane `Re s > 1 - 1 / d`
(`TauCeti.continuedLFunctionOfWeight_restrict`).

In number-field degree greater than one, cancellation is also invariant under purely imaginary
norm twists (`TauCeti.hasCancellation_normTwist_iff`). Abel summation supplies this because the
cancellation exponent `1 - 1 / [K : ℚ]` is then positive. The degree-one case is deliberately not
claimed: the defining bound has exponent zero, while the absolute bound for the Abel integral is
logarithmic.

The continued `L`-function itself follows these operations. Conjugating the weight reflects it
in the real axis, `L(conj χ, conj s) = conj (L(χ, s))`, at every `s`
(`TauCeti.continuedLFunctionOfWeight_conj`). An imaginary norm twist by `N(I) ^ (-z)` translates
it by `z`: on `Re s > 1` for every weight
(`TauCeti.continuedLFunctionOfWeight_normTwist_of_one_lt_re`), and on the whole half-plane
`Re s > 1 - 1 / d` when both the weight and its twist have cancellation
(`TauCeti.continuedLFunctionOfWeight_normTwist`).

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime.

Nor is it automatic, and `TauCeti.not_hasCancellation_of_isNormTwistOnGood` says which weights it
excludes: those agreeing with a norm twist `I ↦ N(I) ^ (u * I)` on the ideals prime to their bad
primes. The `L`-series of such a weight is the Dedekind zeta function with finitely many Euler
factors deleted, read at `s - u * I`, so it has a pole at `s = 1 + u * I`, where cancellation
would instead make `continuedLFunctionOfWeight χ` holomorphic. The trivial weight
(`TauCeti.not_hasCancellation_one`) and its purely imaginary norm twists
(`TauCeti.not_hasCancellation_normTwist_one`) are the cases a character-family argument meets:
it must not assume cancellation for the degenerate members of its family.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

public section

namespace TauCeti

open Filter Asymptotics IsDedekindDomain MeasureTheory
open scoped ComplexConjugate nonZeroDivisors NumberField Topology

variable {K : Type*} [Field K] [NumberField K]

/-- **Cancellation in the ideal partial sums of a unitary weight.** There is a constant `C` with
`‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / [K : ℚ])` for every real cutoff `x ≥ 1`, the sum running
over the nonzero integral ideals of absolute norm at most `x`. -/
def HasCancellation (χ : UnitaryIdealWeight K) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    ‖idealSummatory K χ.toIdealArithmeticFunction x‖ ≤
      C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))

/-- The cancellation exponent `1 - 1 / [K : ℚ]` is less than `1`. -/
theorem cancellationExponent_lt_one : 1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
  have h : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  linarith [one_div_pos.mpr h]

/-- **Cancellation is an asymptotic bound.** A weight has cancellation exactly when its ideal
partial sums are `O(x ^ (1 - 1 / [K : ℚ]))` as `x → ∞`: on any bounded range of cutoffs `x ≥ 1`
the partial sums are bounded by an ideal count, so the eventual bound is uniform. -/
theorem hasCancellation_iff_isBigO {χ : UnitaryIdealWeight K} :
    HasCancellation χ ↔
      (fun x : ℝ ↦ idealSummatory K χ.toIdealArithmeticFunction x) =O[atTop]
        fun x : ℝ ↦ x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  set θ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  constructor
  · rintro ⟨C, hC⟩
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hC x hx
  · intro h
    obtain ⟨c, hc⟩ := h.bound
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hc
    have hθ : 0 ≤ θ := by
      have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
      exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hd)).mpr hd)
    set M : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x₀⌋₊, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    refine ⟨max c M, fun x hx ↦ ?_⟩
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ
    rcases le_total x₀ x with hx₀x | hxx₀
    · have hbound := hx₀ x hx₀x
      rw [Real.norm_of_nonneg (by positivity)] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · calc ‖idealSummatory K χ.toIdealArithmeticFunction x‖
          ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ‖normCoeff K χ.toIdealArithmeticFunction k‖ := by
            rw [idealSummatory_eq_sum_Icc_normCoeff]
            exact norm_sum_le _ _
        _ ≤ M := (Finset.sum_le_sum fun k _ ↦
              UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k).trans
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (Nat.floor_mono hxx₀)) fun _ _ _ ↦ norm_nonneg _)
        _ ≤ max c M * x ^ θ :=
            (le_max_right c M).trans (le_mul_of_one_le_right (hM.trans (le_max_right c M)) hxθ)

/-- The ideal partial sums of the conjugate of a unitary weight are the complex conjugates of
the partial sums of the weight. -/
@[simp]
theorem idealSummatory_conj (χ : UnitaryIdealWeight K) (x : ℝ) :
    idealSummatory K χ.conj.toIdealArithmeticFunction x =
      conj (idealSummatory K χ.toIdealArithmeticFunction x) := by
  simp only [idealSummatory_apply, UnitaryIdealWeight.toIdealArithmeticFunction_apply,
    UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply, map_sum]

/-- A weight has cancellation exactly when its complex conjugate does: conjugation commutes with
the finite partial sums and preserves their modulus. -/
@[simp]
theorem hasCancellation_conj_iff {χ : UnitaryIdealWeight K} :
    HasCancellation χ.conj ↔ HasCancellation χ := by
  simp only [HasCancellation, idealSummatory_conj, Complex.norm_conj]

/-- **Cancellation survives an imaginary norm twist in number-field degree greater than one.**
If the ideal partial sums of `χ` are `O(x ^ (1 - 1 / [K : ℚ]))`, then multiplying the value
at an ideal `I` by `N(I) ^ (-z)` for `Re z = 0` preserves the same bound, provided `[K : ℚ] > 1`.

The degree hypothesis is exactly what makes the cancellation exponent positive: Abel summation
bounds the integral term by a constant times `x ^ (1 - 1 / [K : ℚ])`. -/
theorem HasCancellation.normTwist {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ)
    (z : ℂ) (hz : z.re = 0) (hK : 1 < Module.finrank ℚ K) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ) := by
  set θ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  have hθ : 0 < θ := by
    have hK' : (1 : ℝ) < Module.finrank ℚ K := by exact_mod_cast hK
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hK')
  obtain ⟨C, hC⟩ := hχ
  refine ⟨max C 0 * (1 + ‖z‖ / θ), fun x hx ↦ ?_⟩
  have hC' (t : ℝ) (ht : 1 ≤ t) :
      ‖idealSummatory K χ.toIdealArithmeticFunction t‖ ≤ max C 0 * t ^ θ :=
    by
      simpa only [θ] using (hC t ht).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (by linarith) θ))
  have htwist : (UnitaryIdealWeight.normTwist z hz χ).toIdealArithmeticFunction =
      fun I ↦ χ.toIdealArithmeticFunction I *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-z) := by
    funext I
    rw [UnitaryIdealWeight.toIdealArithmeticFunction_apply,
      UnitaryIdealWeight.toIdealArithmeticFunction_apply, UnitaryIdealWeight.val_normTwist,
      MultiplicativeIdealWeight.normTwist_apply]
  rw [htwist]
  simpa only [θ] using
    norm_idealSummatory_mul_cpow_le_of_summatory_le K χ.toIdealArithmeticFunction hx hθ z hz
      fun t ht ↦ hC' t ht.1

/-- **Cancellation is invariant under imaginary norm twists in degree greater than one.**
Cancellation may be transported freely across an imaginary norm twist in either direction, so a
character-family argument can normalize away such a twist when `[K : ℚ] > 1`. -/
@[simp]
theorem hasCancellation_normTwist_iff {χ : UnitaryIdealWeight K} (z : ℂ) (hz : z.re = 0)
    (hK : 1 < Module.finrank ℚ K) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ) ↔ HasCancellation χ := by
  have hnz : (-z).re = 0 := by simp [hz]
  constructor
  · intro h
    have := h.normTwist (-z) hnz hK
    simpa only [UnitaryIdealWeight.normTwist_normTwist, neg_add_cancel,
      UnitaryIdealWeight.normTwist_zero] using this
  · exact fun h ↦ h.normTwist z hz hK

/-!
### Deleting finitely many Euler factors
-/

/-- **Cancellation survives the deletion of finitely many Euler factors.** If the ideal partial
sums of a unitary weight `χ` are `O(x ^ (1 - 1 / [K : ℚ]))`, so are those of its restriction away
from a finite set of primes: each prime removed splits the partial sum into two partial sums of
the same order, at the cutoffs `x` and `x / N(𝔭)`.

Character-family arguments use this to pass between a weight and the one whose Euler factors at a
finite set of bad primes have been deleted. -/
theorem HasCancellation.restrict {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    HasCancellation (χ.restrict S hS) := by
  set θ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  have hθ : 0 ≤ θ := by
    have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hd)).mpr hd)
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa using hχ
  | @insert 𝔭 T h𝔭 hT ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨2 * max C 0, fun x hx ↦ ?_⟩
      have hN : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := two_le_absNorm_asIdeal_real 𝔭
      have hxpow : (0 : ℝ) ≤ x ^ θ := Real.rpow_nonneg (zero_le_one.trans hx) θ
      have hkey : idealSummatory K
          (χ.restrict (insert 𝔭 T) (hT.insert 𝔭)).toIdealArithmeticFunction x =
          idealSummatory K (χ.restrict T hT).toIdealArithmeticFunction x -
            χ.1 𝔭.asIdeal * idealSummatory K (χ.restrict T hT).toIdealArithmeticFunction
              (x / Ideal.absNorm 𝔭.asIdeal) := by
        rw [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
          UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_restrict,
          UnitaryIdealWeight.val_restrict]
        exact χ.1.idealSummatory_restrict_insert hT h𝔭 x
      have hsecond : ‖idealSummatory K (χ.restrict T hT).toIdealArithmeticFunction
          (x / Ideal.absNorm 𝔭.asIdeal)‖ ≤ max C 0 * x ^ θ := by
        rcases lt_or_ge (x / (Ideal.absNorm 𝔭.asIdeal : ℝ)) 1 with hy | hy
        · rw [idealSummatory_eq_zero_of_lt_one K _ hy, norm_zero]
          positivity
        · have hxN : x / (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x :=
            div_le_self (zero_le_one.trans hx) (by linarith)
          exact (hC _ hy).trans (mul_le_mul (le_max_left C 0)
            (Real.rpow_le_rpow (by linarith) hxN hθ) (Real.rpow_nonneg (by linarith) θ)
            (le_max_right C 0))
      calc ‖idealSummatory K
            (χ.restrict (insert 𝔭 T) (hT.insert 𝔭)).toIdealArithmeticFunction x‖
          ≤ max C 0 * x ^ θ + 1 * (max C 0 * x ^ θ) := by
            rw [hkey]
            refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
            · exact (hC x hx).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) hxpow)
            · rw [norm_mul]
              exact mul_le_mul (χ.norm_le_one _) hsecond (norm_nonneg _) zero_le_one
        _ = 2 * max C 0 * x ^ θ := by ring

/-- **Cancellation bounds the partial sums of the norm coefficients**, in the `O(n ^ r)` form of
Mathlib's `LSeries_eq_mul_integral`. -/
theorem HasCancellation.isBigO_sum_normCoeff {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC⟩ := hχ
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← Nat.floor_natCast (R := ℝ) n, ← idealSummatory_eq_sum_Icc_normCoeff, Nat.floor_natCast,
    Real.norm_of_nonneg (by positivity)]
  exact hC n (by exact_mod_cast hn)

/-- **The continued L-function of a unitary weight**, defined by partial summation:
`s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

On `Re s > 1` it is the norm-regrouped L-series of `χ`
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`); under `TauCeti.HasCancellation χ` it is
holomorphic on `Re s > 1 - 1 / [K : ℚ]` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`).
Where the integral does not converge it takes the junk value of Mathlib's Bochner integral. -/
noncomputable def continuedLFunctionOfWeight (χ : UnitaryIdealWeight K) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ),
    idealSummatory K χ.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1))

/-- The continued L-function as the integral of Mathlib's `LSeries_eq_mul_integral`, over the
partial sums of the norm coefficients. -/
theorem continuedLFunctionOfWeight_eq_mul_integral (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, normCoeff K χ.toIdealArithmeticFunction k) *
        (t : ℂ) ^ (-(s + 1)) := by
  simp only [continuedLFunctionOfWeight, idealSummatory_eq_sum_Icc_normCoeff]

/-- **The continued L-function is the L-series on `Re s > 1`.** For every unitary weight, with or
without cancellation, `continuedLFunctionOfWeight χ` agrees with the `LSeries` of the norm
coefficients of `χ` to the right of `1`, where that series converges absolutely. -/
theorem continuedLFunctionOfWeight_eq_LSeries (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s = LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [continuedLFunctionOfWeight_eq_mul_integral]
  refine (LSeries_eq_mul_integral' _ zero_le_one (by simpa using hs) ?_).symm
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)).trans
    (isBigO_sum_norm_normCoeff_one K)
  rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  exact Finset.sum_le_sum fun k _ ↦
    UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k

/-- **Cancellation continues the L-series of a weight.** If `χ` has cancellation, its continued
L-function is holomorphic on the half-plane `Re s > 1 - 1 / [K : ℚ]`, which contains the line
`Re s = 1`. -/
theorem differentiableOn_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) :
    DifferentiableOn ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  rw [funext (continuedLFunctionOfWeight_eq_mul_integral χ)]
  exact LSeries.differentiableOn_mul_integral_of_isBigO _ hχ.isBigO_sum_normCoeff

/-- **Deleting finitely many Euler factors, to the right of `1`.** Where the norm-regrouped series
converge absolutely, restricting a unitary weight away from a finite set `S` of primes multiplies
its continued `L`-function by the reciprocals `∏ 𝔭 ∈ S, (1 - χ(𝔭) N(𝔭) ^ (-s))` of the deleted
local factors. -/
theorem continuedLFunctionOfWeight_restrict_of_one_lt_re (χ : UnitaryIdealWeight K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight
        (χ.restrict (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet) s =
      continuedLFunctionOfWeight χ s *
        ∏ 𝔭 ∈ S, (1 - χ.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) := by
  rw [continuedLFunctionOfWeight_eq_LSeries _ hs, continuedLFunctionOfWeight_eq_LSeries _ hs,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_restrict]
  exact χ.1.LSeries_restrict S (by
    rw [← UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
    exact summable_idealTerm_of_unitary_of_one_lt_re χ hs)

/-- Two functions holomorphic on the half-plane `Re s > 1 - 1 / [K : ℚ]` that agree to the right
of `1` agree on the whole half-plane, since it is connected. This is how identities between
continued `L`-functions pass from the region of absolute convergence across the line `Re s = 1`. -/
private theorem eq_of_differentiableOn_of_one_lt_re {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re})
    (hg : DifferentiableOn ℂ g {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re})
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) {s : ℂ}
    (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) : f s = g s := by
  have hUopen : IsOpen {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUopen)
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 2) ?_ ?_ hs
  · simpa using (cancellationExponent_lt_one (K := K)).trans one_lt_two
  · have htwo : (1 : ℝ) < (2 : ℂ).re := by norm_num
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds htwo] with z hz
    exact hfg z hz

/-- **Deleting finitely many Euler factors, across the line `Re s = 1`.** Under cancellation both
sides of `TauCeti.continuedLFunctionOfWeight_restrict_of_one_lt_re` are holomorphic on the
half-plane `Re s > 1 - 1 / [K : ℚ]`, which is connected, so the identity propagates there from
the half-plane `Re s > 1` where it was proved. The correction factor is entire. -/
theorem continuedLFunctionOfWeight_restrict {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ}
    (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) :
    continuedLFunctionOfWeight
        (χ.restrict (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet) s =
      continuedLFunctionOfWeight χ s *
        ∏ 𝔭 ∈ S, (1 - χ.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) := by
  have hcorr : Differentiable ℂ
      fun s : ℂ ↦ ∏ 𝔭 ∈ S, (1 - χ.1 𝔭.asIdeal / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) := by
    refine Differentiable.fun_finsetProd fun 𝔭 _ ↦ ?_
    have h𝔭 : ((Ideal.absNorm 𝔭.asIdeal : ℂ)) ≠ 0 := by
      have h := NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
      exact Nat.cast_ne_zero.mpr (by omega)
    exact (differentiable_const 1).sub ((differentiable_const _).div
      (differentiable_id.const_cpow (.inl h𝔭))
      fun s ↦ by simp [Complex.cpow_eq_zero_iff, h𝔭])
  exact eq_of_differentiableOn_of_one_lt_re
    (differentiableOn_continuedLFunctionOfWeight (hχ.restrict _ S.finite_toSet))
    ((differentiableOn_continuedLFunctionOfWeight hχ).mul hcorr.differentiableOn)
    (fun z hz ↦ continuedLFunctionOfWeight_restrict_of_one_lt_re χ S hz) hs

/-!
### Conjugation and imaginary norm twists
-/

/-- **The continued L-function of the conjugate weight** is the reflection of the continued
L-function of the weight in the real axis: `L(conj χ, conj s) = conj (L(χ, s))`.
This holds at every `s`,
including the junk values off the region where the defining integral converges, because complex
conjugation commutes with the Bochner integral. -/
@[simp]
theorem continuedLFunctionOfWeight_conj (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ.conj (conj s) = conj (continuedLFunctionOfWeight χ s) := by
  simp only [continuedLFunctionOfWeight, map_mul, ← integral_conj]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) ↦ ?_
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by linarith)]
    exact Real.pi_ne_zero.symm
  have hpow := Complex.cpow_conj (t : ℂ) (-(s + 1)) harg
  rw [Complex.conj_ofReal, map_neg, map_add, map_one] at hpow
  rw [idealSummatory_conj, hpow]

/-- **Imaginary norm twists translate the continued L-function, to the right of `1`.** Twisting
a unitary weight by `N(I) ^ (-z)` with `Re z = 0` translates its continued L-function by `z` on
the half-plane `Re s > 1`, where both sides are the norm-regrouped L-series. -/
@[simp]
theorem continuedLFunctionOfWeight_normTwist_of_one_lt_re (χ : UnitaryIdealWeight K) {z : ℂ}
    (hz : z.re = 0) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight (UnitaryIdealWeight.normTwist z hz χ) s =
      continuedLFunctionOfWeight χ (s + z) := by
  have hsz : 1 < (s + z).re := by simpa [hz] using hs
  rw [continuedLFunctionOfWeight_eq_LSeries _ hs, continuedLFunctionOfWeight_eq_LSeries _ hsz,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_normTwist]
  rw [funext (MultiplicativeIdealWeight.normCoeff_normTwist z χ.1)]
  exact LSeries.LSeries_mul_natCast_cpow_neg _ z s

/-- **Imaginary norm twists translate the continued L-function, across the line `Re s = 1`.**
If both a unitary weight and its twist by `N(I) ^ (-z)`, with `Re z = 0`, have cancellation,
then the continued L-function of the twist at `s` is the continued L-function of the weight at
`s + z`, throughout the half-plane `Re s > 1 - 1 / [K : ℚ]`.

In degree `[K : ℚ] > 1` the second cancellation hypothesis follows from the first, by
`TauCeti.HasCancellation.normTwist`. -/
@[simp]
theorem continuedLFunctionOfWeight_normTwist {χ : UnitaryIdealWeight K} {z : ℂ} (hz : z.re = 0)
    (hχ : HasCancellation χ) (hχz : HasCancellation (UnitaryIdealWeight.normTwist z hz χ))
    {s : ℂ} (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) :
    continuedLFunctionOfWeight (UnitaryIdealWeight.normTwist z hz χ) s =
      continuedLFunctionOfWeight χ (s + z) := by
  have hshift : DifferentiableOn ℂ (fun s ↦ continuedLFunctionOfWeight χ (s + z))
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
    (differentiableOn_continuedLFunctionOfWeight hχ).comp
      (differentiable_id.add_const z).differentiableOn fun s hs ↦ by simpa [hz] using hs
  exact eq_of_differentiableOn_of_one_lt_re (differentiableOn_continuedLFunctionOfWeight hχz)
    hshift (fun w hw ↦ continuedLFunctionOfWeight_normTwist_of_one_lt_re χ hz hw) hs

/-!
### The rejection test: weights that are norm twists on their good ideals
-/

/-- **A weight that is a norm twist on its good ideals has no cancellation.** Its norm
coefficients are those of the indicator of the ideals prime to its bad primes, twisted by
`n ^ (u * I)`, so its `L`-series is the Dedekind zeta function with finitely many Euler factors
deleted, read at `s - u * I`. That series has a pole at `s = 1 + u * I`, a point at which
cancellation would make `TauCeti.continuedLFunctionOfWeight` holomorphic.

This is a rejection test for character-family arguments: these weights are degenerate examples
for which cancellation may not be assumed. -/
theorem not_hasCancellation_of_isNormTwistOnGood {χ : UnitaryIdealWeight K} {u : ℝ}
    (hχ : χ.1.IsNormTwistOnGood u) : ¬ HasCancellation χ := by
  intro hcanc
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      χ.1.badPrimes = (S : Set (HeightOneSpectrum (𝓞 K))) :=
    ⟨χ.1.finite_badPrimes.toFinset, χ.1.finite_badPrimes.coe_toFinset.symm⟩
  -- cancellation makes the continued `L`-function continuous at `1 + u * I`, so multiplying it
  -- by `t - 1` kills it as `t → 1⁺` along the horizontal ray through that point
  have hcontAt : ContinuousAt (continuedLFunctionOfWeight χ) (1 + (u : ℂ) * Complex.I) := by
    refine (differentiableOn_continuedLFunctionOfWeight hcanc).continuousOn.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_)
    simpa using cancellationExponent_lt_one (K := K)
  have hzero : Tendsto (fun t : ℝ ↦ ((t : ℂ) - 1) *
      continuedLFunctionOfWeight χ ((t : ℂ) + (u : ℂ) * Complex.I)) (𝓝[>] 1) (𝓝 0) := by
    have hray : Tendsto (fun t : ℝ ↦ ((t : ℂ) + (u : ℂ) * Complex.I)) (𝓝[>] (1 : ℝ))
        (𝓝 (1 + (u : ℂ) * Complex.I)) := by
      have hc : Continuous fun t : ℝ ↦ ((t : ℂ) + (u : ℂ) * Complex.I) :=
        Complex.continuous_ofReal.add continuous_const
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    have hsub : Tendsto (fun t : ℝ ↦ ((t : ℂ) - 1)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun t : ℝ ↦ ((t : ℂ) - 1) :=
        Complex.continuous_ofReal.sub continuous_const
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using hsub.mul (hcontAt.tendsto.comp hray)
  -- but on the ray the continued `L`-function is the `L`-series, which has a pole at `1 + u * I`
  have heq : (fun t : ℝ ↦ ((t : ℂ) - 1) *
      LSeries (normCoeff K χ.1.toIdealArithmeticFunction) ((t : ℂ) + (u : ℂ) * Complex.I))
      =ᶠ[𝓝[>] 1] fun t : ℝ ↦ ((t : ℂ) - 1) *
        continuedLFunctionOfWeight χ ((t : ℂ) + (u : ℂ) * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : (1 : ℝ) < t)
    have hre : (1 : ℝ) < ((t : ℂ) + (u : ℂ) * Complex.I).re := by simpa using ht
    rw [continuedLFunctionOfWeight_eq_LSeries χ hre,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val]
  have hne : (NumberField.dedekindZeta_residue K : ℂ) *
      ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (NumberField.dedekindZeta_residue_pos K).ne')
      (prod_one_sub_absNorm_cpow_neg_ne_zero S (by simp))
  exact hne (tendsto_nhds_unique ((hχ.tendsto_sub_one_mul_LSeries hS).congr' heq) hzero)

/-- **A weight that is trivial on its good ideals has no cancellation**: its `L`-series is the
Dedekind zeta function with finitely many Euler factors deleted, which has a pole at `s = 1`. -/
theorem not_hasCancellation_of_isTrivialOnGood {χ : UnitaryIdealWeight K}
    (hχ : χ.1.IsTrivialOnGood) : ¬ HasCancellation χ :=
  not_hasCancellation_of_isNormTwistOnGood
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr hχ)

/-- **The trivial weight has no cancellation.** Its `L`-series is the Dedekind zeta function,
which has a pole at `s = 1`. -/
theorem not_hasCancellation_one : ¬ HasCancellation (1 : UnitaryIdealWeight K) :=
  not_hasCancellation_of_isTrivialOnGood
    (by rw [UnitaryIdealWeight.val_one]; exact MultiplicativeIdealWeight.isTrivialOnGood_one)

/-- **No imaginary norm twist of the trivial weight has cancellation.** Its `L`-series is the
Dedekind zeta function read at `s + z`, which has a pole at `s = 1 - z`. -/
theorem not_hasCancellation_normTwist_one {z : ℂ} (hz : z.re = 0) :
    ¬ HasCancellation (UnitaryIdealWeight.normTwist z hz (1 : UnitaryIdealWeight K)) := by
  have hzz : -(((-z.im : ℝ) : ℂ) * Complex.I) = z := by
    apply Complex.ext <;> simp [hz]
  have h0 : (1 : MultiplicativeIdealWeight K).IsNormTwistOnGood 0 :=
    (MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr
      MultiplicativeIdealWeight.isTrivialOnGood_one
  have h1 := h0.normTwist (-z.im)
  rw [zero_add, hzz] at h1
  exact not_hasCancellation_of_isNormTwistOnGood
    (by rwa [UnitaryIdealWeight.val_normTwist, UnitaryIdealWeight.val_one])

end TauCeti
