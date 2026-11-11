/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Analysis.Calculus.Bilinear
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Square roots near the identity in a Banach algebra

Every element `a` of a real Banach algebra with `‖a - 1‖ < 1` has a canonical square root, the sum
of the binomial series `∑ (1/2 choose n) (a - 1) ^ n`. This file packages it as
`TauCeti.sqrtNearOne` together with the facts downstream arguments need: it fixes `1`, it is
analytic, hence smooth, at `1`, and it is a two-sided inverse of squaring on a neighbourhood of
`1`. The two-sided statements are phrased as `Filter.Eventually` assertions rather than by
exhibiting a neighbourhood, since that is how they get used.

Squaring, `a ↦ a * a`, has invertible derivative `x ↦ 2 * x` at `1`, so by the inverse function
theorem it is injective near `1`. Hence the binomial square root is the *only* square root near
`1` (`TauCeti.eventually_sqrtNearOne_mul_self`).

Because it is the sum of a power series with scalar coefficients, the square root commutes with
every continuous algebra equivalence (`TauCeti.map_sqrtNearOne`), with no smallness hypothesis:
the summability of a series, and its sum, only depend on the topology. In particular it commutes
with conjugation by a continuous linear equivalence. A square root obtained as a local inverse of
squaring would instead have a domain depending on the norm, and so would only be natural near
`1`, with a neighbourhood depending on the equivalence.

The motivating application is the Morse lemma, in
`TauCeti.Analysis.Calculus.Morse.NormalForm`: the operator `(D²f x)⁻¹ ∘ B v` comparing the
averaged Hessian along a segment with the Hessian at a nondegenerate critical point is close to
the identity, and the change of coordinates flattening `f` is built from its square root. The
exact naturality makes that change of coordinates independent of the linear coordinates in which
it is computed. Nothing here is a substitute for the continuous functional calculus: `CFC.sqrt`
computes the *positive* square root of a positive element of a C⋆-algebra, whereas what is needed
here is a square root near `1` in a bare Banach algebra, with smooth dependence on the element.

## Main declarations

* `TauCeti.sqrtNearOne`: the binomial square root, with `TauCeti.sqrtNearOne_eq_tsum`.
* `TauCeti.sqrtNearOne_one`, `TauCeti.analyticAt_sqrtNearOne`, `TauCeti.contDiffAt_sqrtNearOne`:
  it fixes `1` and is analytic, hence smooth, there.
* `TauCeti.sqrtNearOne_mul_self`: on the unit ball around `1` it is a square root.
* `TauCeti.eventually_mul_self_sqrtNearOne`: near `1` it is a right inverse of squaring.
* `TauCeti.eventually_sqrtNearOne_mul_self`: near `1` it is a left inverse of squaring, which is
  the uniqueness statement: an element close to `1` is recovered from its square.
* `TauCeti.eventually_sqrtNearOne_eq_of_tendsto`: the same uniqueness along an arbitrary filter,
  for a family of square roots tending to `1`.
* `TauCeti.eventually_sqrtNearOne_fixed`: a map continuous at `1` and reversing products
  fixes the square root of every fixed element sufficiently close to `1`.
* `TauCeti.map_sqrtNearOne`: continuous algebra equivalences commute with the square root.

## References

The uniqueness is the inverse function theorem in Banach spaces, as in
S. Lang, *Real and Functional Analysis*, Chapter XIV.
-/

public section

open Filter Topology

open scoped ContDiff

namespace TauCeti

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

private theorem hasStrictFDerivAt_mul_self_one :
    HasStrictFDerivAt (fun a : A ↦ a * a)
      ((ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) :
        A →L[ℝ] A) 1 := by
  have h := ContinuousLinearMap.hasStrictFDerivAt_apply_self
    (ContinuousLinearMap.mul ℝ A) 1
  have he : (ContinuousLinearMap.mul ℝ A).flip 1 + ContinuousLinearMap.mul ℝ A 1 =
      ((ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) :
        A →L[ℝ] A) := by
    ext a
    simp [two_smul]
  rw [he] at h
  exact h

/-- The binomial series of exponent `1/2` converges on the unit ball of any normed algebra: its
coefficients are those of the scalar series, of radius `1`. -/
private theorem one_le_radius_binomialSeries :
    1 ≤ (binomialSeries A (2⁻¹ : ℝ)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hR : (r : ENNReal) < (binomialSeries ℝ (2⁻¹ : ℝ)).radius :=
    hr.trans_le binomialSeries_radius_ge_one
  refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
  refine Summable.of_norm_bounded_eventually
    ((binomialSeries ℝ (2⁻¹ : ℝ)).summable_norm_mul_pow hR) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  rw [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
  gcongr
  calc ‖binomialSeries A (2⁻¹ : ℝ) n‖ ≤ ‖Ring.choose (2⁻¹ : ℝ) n‖ :=
        FormalMultilinearSeries.ofScalars_norm_le A _ n (Nat.pos_of_ne_zero hn)
    _ = ‖binomialSeries ℝ (2⁻¹ : ℝ) n‖ := by
        rw [binomialSeries, FormalMultilinearSeries.ofScalars_norm]

/-- The **square root near the identity** of a Banach algebra: the sum of the binomial series
`∑ (1/2 choose n) (a - 1) ^ n` (`TauCeti.sqrtNearOne_eq_tsum`). It is a square root when
`‖a - 1‖ < 1` (`TauCeti.sqrtNearOne_mul_self`), and the only one near `1`
(`TauCeti.eventually_sqrtNearOne_mul_self`); it is only meaningful there. -/
noncomputable def sqrtNearOne (a : A) : A :=
  (binomialSeries A (2⁻¹ : ℝ)).sum (a - 1)

variable {A}

/-- The square root near the identity is the sum of the binomial series of exponent `1/2`. -/
theorem sqrtNearOne_eq_tsum (a : A) :
    sqrtNearOne A a = ∑' n, Ring.choose (2⁻¹ : ℝ) n • (a - 1) ^ n := by
  rw [sqrtNearOne, binomialSeries, ← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalarsSum_eq_tsum]

/-- The square root near the identity fixes the identity. -/
@[simp]
theorem sqrtNearOne_one : sqrtNearOne A 1 = 1 := by
  rw [sqrtNearOne, sub_self, binomialSeries, ← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalarsSum_zero, Ring.choose_zero_right, one_smul]

/-- On the unit ball around `1`, the terms of the binomial series are absolutely summable. -/
private theorem summable_norm_binomial_term {a : A} (ha : ‖a - 1‖ < 1) :
    Summable fun n ↦ ‖Ring.choose (2⁻¹ : ℝ) n • (a - 1) ^ n‖ := by
  have hmem : a - 1 ∈ Metric.eball (0 : A) (binomialSeries A (2⁻¹ : ℝ)).radius := by
    refine lt_of_lt_of_le ?_ (one_le_radius_binomialSeries A)
    rwa [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq] using
    (binomialSeries A (2⁻¹ : ℝ)).summable_norm_apply hmem

variable [CompleteSpace A]

/-- **The binomial square root is a square root on the unit ball around `1`.** The Cauchy square
of the binomial series of exponent `1/2` is the binomial series of exponent `1`, by the
Chu–Vandermonde identity, and that series is `1 + x`. -/
theorem sqrtNearOne_mul_self {a : A} (ha : ‖a - 1‖ < 1) :
    sqrtNearOne A a * sqrtNearOne A a = a := by
  have hs := summable_norm_binomial_term ha
  rw [sqrtNearOne_eq_tsum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs hs]
  have hterm (n : ℕ) : ∑ kl ∈ Finset.antidiagonal n,
      Ring.choose (2⁻¹ : ℝ) kl.1 • (a - 1) ^ kl.1 * Ring.choose (2⁻¹ : ℝ) kl.2 • (a - 1) ^ kl.2 =
        (Nat.choose 1 n : ℝ) • (a - 1) ^ n := by
    have hv := Ring.add_choose_eq (r := (2⁻¹ : ℝ)) (s := 2⁻¹) n (Commute.refl _)
    rw [show (2⁻¹ : ℝ) + 2⁻¹ = ((1 : ℕ) : ℝ) by norm_num, Ring.choose_natCast] at hv
    rw [hv, Finset.sum_smul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [smul_mul_smul_comm, ← pow_add, Finset.mem_antidiagonal.mp hkl]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range 2) fun n hn ↦ by
    rw [Nat.choose_eq_zero_of_lt (by simpa using hn), Nat.cast_zero, zero_smul]]
  simp [Finset.sum_range_succ]

/-- The square root near the identity is analytic at the identity.  This gives a single
neighborhood on which it is smooth to every finite order. -/
theorem analyticAt_sqrtNearOne : AnalyticAt ℝ (sqrtNearOne A) 1 := by
  have hp : AnalyticAt ℝ (binomialSeries A (2⁻¹ : ℝ)).sum 0 :=
    ((binomialSeries A (2⁻¹ : ℝ)).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le (one_le_radius_binomialSeries A))).analyticAt
  have hsub : AnalyticAt ℝ (fun a : A ↦ a - 1) 1 := analyticAt_id.sub analyticAt_const
  exact hp.comp_of_eq hsub (sub_self _)

/-- The square root near the identity is smooth at the identity. -/
theorem contDiffAt_sqrtNearOne : ContDiffAt ℝ ∞ (sqrtNearOne A) 1 :=
  analyticAt_sqrtNearOne.contDiffAt

/-- The square root near the identity is continuous at the identity. -/
theorem continuousAt_sqrtNearOne : ContinuousAt (sqrtNearOne A) 1 :=
  contDiffAt_sqrtNearOne.continuousAt

/-- Near the identity, `TauCeti.sqrtNearOne` really produces a square root. -/
theorem eventually_mul_self_sqrtNearOne :
    ∀ᶠ a in 𝓝 (1 : A), sqrtNearOne A a * sqrtNearOne A a = a := by
  filter_upwards [Metric.ball_mem_nhds (1 : A) one_pos] with a ha
  exact sqrtNearOne_mul_self (by rwa [← dist_eq_norm])

/-- Near the identity, an element is recovered from its square by `TauCeti.sqrtNearOne`.  This is
the uniqueness half: two elements close to `1` with the same square are equal. Squaring is
injective near `1` by the inverse function theorem. -/
theorem eventually_sqrtNearOne_mul_self :
    ∀ᶠ b in 𝓝 (1 : A), sqrtNearOne A (b * b) = b := by
  set g := (hasStrictFDerivAt_mul_self_one A).localInverse (fun a : A ↦ a * a)
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) 1
  -- The local inverse `g` of squaring recovers every element near `1` from its square.
  have hg : ∀ᶠ b in 𝓝 (1 : A), g (b * b) = b := by
    simpa [g] using (hasStrictFDerivAt_mul_self_one A).eventually_left_inverse
      (f := fun a : A ↦ a * a)
      (f' := (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A))
        (a := 1)
  have hsq : Tendsto (fun b : A ↦ b * b) (𝓝 1) (𝓝 1) := by
    simpa using (tendsto_id (x := 𝓝 (1 : A))).mul tendsto_id
  have hroot : Tendsto (sqrtNearOne A) (𝓝 1) (𝓝 1) := by
    simpa only [sqrtNearOne_one] using (continuousAt_sqrtNearOne (A := A)).tendsto
  -- Both `b` and the binomial square root of `b * b` are square roots of `b * b` near `1`.
  filter_upwards [hg, hsq.eventually (hroot.eventually hg), hsq.eventually
    eventually_mul_self_sqrtNearOne] with b hb hb' hb''
  rw [← hb', hb'', hb]


/-- **Uniqueness of the square root near the identity, along a filter.** If `r` tends to `1` and
eventually squares to `x`, then `TauCeti.sqrtNearOne` eventually recovers `r` from `x`. -/
theorem eventually_sqrtNearOne_eq_of_tendsto {α : Type*} {l : Filter α} {r x : α → A}
    (hr : Tendsto r l (𝓝 1)) (hx : ∀ᶠ t in l, r t * r t = x t) :
    ∀ᶠ t in l, sqrtNearOne A (x t) = r t := by
  filter_upwards [hr.eventually eventually_sqrtNearOne_mul_self, hx] with t ht hxt
  rwa [← hxt]

/-- A map continuous at `1` and reversing products fixes the square root near the identity of
every fixed element sufficiently close to `1`. If the map does not fix `1`, it has no fixed
points near `1`, so the statement is vacuous. -/
theorem eventually_sqrtNearOne_fixed {adj : A → A} (hc : ContinuousAt adj 1)
    (hmul : ∀ x y, adj (x * y) = adj y * adj x) :
    ∀ᶠ a in 𝓝 (1 : A), adj a = a → adj (sqrtNearOne A a) = sqrtNearOne A a := by
  by_cases h1 : adj 1 = 1
  swap
  · filter_upwards [(hc.sub continuousAt_id).eventually_ne (sub_ne_zero.2 h1)] with a ha hfix
    exact (ha (sub_eq_zero.2 hfix)).elim
  have hroot : Tendsto (sqrtNearOne A) (𝓝 1) (𝓝 1) := by
    simpa only [sqrtNearOne_one] using (continuousAt_sqrtNearOne (A := A)).tendsto
  have hadj : Tendsto (fun a ↦ adj (sqrtNearOne A a)) (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def, h1] using hc.tendsto.comp hroot
  filter_upwards [eventually_mul_self_sqrtNearOne,
    hadj.eventually eventually_sqrtNearOne_mul_self] with a hs hu ha
  rw [← hmul, hs, ha] at hu
  exact hu.symm

omit [CompleteSpace A] in
/-- **The square root near the identity commutes with continuous algebra equivalences.** No
smallness hypothesis is needed: an equivalence maps the binomial series of `a - 1` termwise to
that of `φ a - 1`, and preserves its summability and sum. In particular the square root commutes
with conjugation by a continuous linear equivalence
(`ContinuousLinearEquiv.conjContinuousAlgEquiv`). -/
theorem map_sqrtNearOne {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    (φ : A ≃A[ℝ] B) (a : A) : φ (sqrtNearOne A a) = sqrtNearOne B (φ a) := by
  rw [sqrtNearOne_eq_tsum, sqrtNearOne_eq_tsum,
    ← ContinuousAlgEquiv.toContinuousLinearEquiv_apply, ContinuousLinearEquiv.map_tsum]
  simp [map_sub, map_pow]

end TauCeti
