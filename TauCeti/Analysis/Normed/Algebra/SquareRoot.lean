/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Analysis.Analytic.Binomial

/-!
# Square roots near the identity in a Banach algebra

Every element `x` of a Banach algebra over `ℝ` with `‖x - 1‖ < 1` has a square root, the sum of the
binomial series of `(1 + y) ^ (1 / 2)` (Mathlib's `binomialSeries`) at `y = x - 1`:

`√x = ∑ₙ (1/2 choose n) (x - 1)ⁿ`.

This file packages it as `TauCeti.sqrtNearOne`. It is a square root on the whole open unit ball
about `1` (`TauCeti.sqrtNearOne_mul_self`), analytic there (`TauCeti.analyticOnNhd_sqrtNearOne`),
and it fixes `1`. It is the *only* square root near `1`: two elements whose distances to `1` add up
to less than `2` and which have the same square are equal
(`TauCeti.eq_of_mul_self_eq_mul_self`), so near `1` it is a two-sided inverse of squaring. These
two-sided statements are also phrased as `Filter.Eventually` assertions, since that is how they get
used.

Since it is given by a power series with scalar coefficients, the square root near the identity is
natural: a continuous algebra homomorphism `φ` satisfies `φ (√x) = √(φ x)` whenever `‖x - 1‖ < 1`
(`ContinuousAlgHom.map_sqrtNearOne`), and a continuous algebra isomorphism commutes with it at every
element (`ContinuousAlgEquiv.map_sqrtNearOne`). In particular, for a continuous linear equivalence
`e`, conjugation by `e` (`ContinuousLinearEquiv.conjContinuousAlgEquiv`) carries the square root of
an operator to the square root of its conjugate, with no smallness condition depending on `e`.

The motivating application is the Morse lemma, in
`TauCeti.Analysis.Calculus.Morse.NormalForm`: the operator `(D²f x)⁻¹ ∘ B v` comparing the
averaged Hessian along a segment with the Hessian at a nondegenerate critical point is close to
the identity, and the change of coordinates flattening `f` is built from its square root. The
naturality makes that change of coordinates independent of the linear coordinates in which it is
computed. Nothing here is a substitute for the continuous functional calculus: `CFC.sqrt` computes
the *positive* square root of a positive element of a C⋆-algebra, whereas what is needed here is a
square root near `1` in a bare Banach algebra, with smooth dependence on the element.

## Main declarations

* `TauCeti.sqrtNearOne`: the binomial-series square root near the identity.
* `TauCeti.sqrtNearOne_mul_self`: it is a square root on the open unit ball about `1`.
* `TauCeti.analyticOnNhd_sqrtNearOne`: it is analytic on the open unit ball about `1`.
* `TauCeti.eq_of_mul_self_eq_mul_self`: uniqueness of square roots near `1`.
* `TauCeti.eventually_mul_self_sqrtNearOne`, `TauCeti.eventually_sqrtNearOne_mul_self`: near `1`
  it is a right and a left inverse of squaring.
* `TauCeti.eventually_sqrtNearOne_eq_of_tendsto`: the same uniqueness along an arbitrary filter,
  for a family of square roots tending to `1`.
* `TauCeti.eventually_sqrtNearOne_fixed`: a map continuous at `1` and reversing products
  fixes the square root of every fixed element sufficiently close to `1`.
* `ContinuousAlgHom.map_sqrtNearOne`, `ContinuousAlgEquiv.map_sqrtNearOne`: naturality under
  continuous algebra homomorphisms and isomorphisms.
-/

public section

open Filter Topology

open scoped ContDiff

namespace TauCeti

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

/-- The **square root near the identity** of a normed algebra over `ℝ`: the sum of the binomial
series of `(1 + y) ^ (1 / 2)` at `y = x - 1`, that is `∑ₙ (1/2 choose n) (x - 1)ⁿ`. In a Banach
algebra it is a square root of `x` whenever `‖x - 1‖ < 1` (`TauCeti.sqrtNearOne_mul_self`); outside
the open unit ball about `1` it has no meaning. -/
noncomputable def sqrtNearOne (x : A) : A :=
  (binomialSeries A (2⁻¹ : ℝ)).sum (x - 1)

variable {A}

/-- The square root near the identity is the binomial series of `(1 + y) ^ (1 / 2)` at
`y = x - 1`. -/
theorem sqrtNearOne_def (x : A) :
    sqrtNearOne A x = (binomialSeries A (2⁻¹ : ℝ)).sum (x - 1) := (rfl)

/-- The square root near the identity is the sum of the terms `(1/2 choose n) • (x - 1)ⁿ`. -/
theorem sqrtNearOne_eq_tsum (x : A) :
    sqrtNearOne A x = ∑' n, Ring.choose (2⁻¹ : ℝ) n • (x - 1) ^ n :=
  binomialSeries_sum_eq_tsum _ _

/-- The square root near the identity fixes the identity. -/
@[simp]
theorem sqrtNearOne_one : sqrtNearOne A 1 = 1 := by
  rw [sqrtNearOne_eq_tsum, tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp

/-- **Uniqueness of square roots near the identity.** Two elements of a normed algebra over `ℝ`
whose distances to `1` add up to less than `2` and which have the same square are equal. -/
theorem eq_of_mul_self_eq_mul_self {r s : A} (h : r * r = s * s)
    (hrs : ‖r - 1‖ + ‖s - 1‖ < 2) : r = s := by
  -- With `r * r = s * s`, the difference `d = r - s` satisfies `2 d = (1 - r) d + d (1 - s)`,
  -- which is too short to hold for `d ≠ 0`.
  have hkey : (1 - r) * (r - s) + (r - s) * (1 - s) = (2 : ℝ) • (r - s) := by
    have hexp : (1 - r) * (r - s) + (r - s) * (1 - s) = (r - s) + (r - s) - (r * r - s * s) := by
      noncomm_ring
    rw [hexp, h, sub_self, sub_zero, two_smul]
  have hle : 2 * ‖r - s‖ ≤ (‖r - 1‖ + ‖s - 1‖) * ‖r - s‖ := by
    calc 2 * ‖r - s‖ = ‖(2 : ℝ) • (r - s)‖ := by rw [norm_smul, Real.norm_two]
      _ ≤ ‖1 - r‖ * ‖r - s‖ + ‖r - s‖ * ‖1 - s‖ := by
        rw [← hkey]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ = (‖r - 1‖ + ‖s - 1‖) * ‖r - s‖ := by rw [norm_sub_rev 1 r, norm_sub_rev 1 s]; ring
  by_contra hne
  have hpos : 0 < ‖r - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

omit [NormedAlgebra ℝ A] in
/-- A map tending to `1` eventually stays in the open unit ball about `1`. -/
private theorem eventually_norm_sub_one_lt {α : Type*} {l : Filter α} {r : α → A}
    (hr : Tendsto r l (𝓝 1)) : ∀ᶠ t in l, ‖r t - 1‖ < 1 := by
  simpa only [Metric.mem_ball, dist_eq_norm] using hr.eventually (Metric.ball_mem_nhds 1 one_pos)

variable [CompleteSpace A]

/-- On the open unit ball about `1`, the binomial series of the square root near the identity
converges to it. -/
theorem hasSum_sqrtNearOne {x : A} (hx : ‖x - 1‖ < 1) :
    HasSum (fun n ↦ Ring.choose (2⁻¹ : ℝ) n • (x - 1) ^ n) (sqrtNearOne A x) :=
  hasSum_binomialSeries _ hx

/-- **The square root near the identity is a square root** of every element of the open unit ball
about `1`. -/
theorem sqrtNearOne_mul_self {x : A} (hx : ‖x - 1‖ < 1) :
    sqrtNearOne A x * sqrtNearOne A x = x := by
  rw [sqrtNearOne_def, binomialSeries_sum_mul_binomialSeries_sum _ _ hx,
    show (2⁻¹ + 2⁻¹ : ℝ) = ((1 : ℕ) : ℝ) by norm_num, binomialSeries_sum_natCast, pow_one,
    add_sub_cancel]

/-- The square root near the identity is analytic on the open unit ball about `1`. -/
theorem analyticOnNhd_sqrtNearOne : AnalyticOnNhd ℝ (sqrtNearOne A) (Metric.ball 1 1) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hsum := ((binomialSeries A (2⁻¹ : ℝ)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (binomialSeries_radius_ge_one_of_normedRing _))).analyticAt_of_mem
      (mem_eball_binomialSeries_radius hx _)
  have hsub : AnalyticAt ℝ (fun z : A ↦ z - 1) x := analyticAt_id.sub analyticAt_const
  simpa only [Function.comp_def, ← sqrtNearOne_def] using hsum.comp_of_eq hsub rfl

/-- The square root near the identity is analytic at the identity.  This gives a single
neighborhood on which it is smooth to every finite order. -/
theorem analyticAt_sqrtNearOne : AnalyticAt ℝ (sqrtNearOne A) 1 :=
  analyticOnNhd_sqrtNearOne 1 (Metric.mem_ball_self one_pos)

/-- The square root near the identity is smooth at the identity. -/
theorem contDiffAt_sqrtNearOne : ContDiffAt ℝ ∞ (sqrtNearOne A) 1 :=
  analyticAt_sqrtNearOne.contDiffAt

/-- The square root near the identity is continuous at the identity. -/
theorem continuousAt_sqrtNearOne : ContinuousAt (sqrtNearOne A) 1 :=
  contDiffAt_sqrtNearOne.continuousAt

/-- Near the identity, `TauCeti.sqrtNearOne` really produces a square root. -/
theorem eventually_mul_self_sqrtNearOne :
    ∀ᶠ a in 𝓝 (1 : A), sqrtNearOne A a * sqrtNearOne A a = a := by
  filter_upwards [eventually_norm_sub_one_lt (tendsto_id (x := 𝓝 (1 : A)))] with a ha
  exact sqrtNearOne_mul_self ha

/-- Near the identity, an element is recovered from its square by `TauCeti.sqrtNearOne`.  This is
the uniqueness half: two elements close to `1` with the same square are equal. -/
theorem eventually_sqrtNearOne_mul_self :
    ∀ᶠ b in 𝓝 (1 : A), sqrtNearOne A (b * b) = b := by
  have hsq : Tendsto (fun b : A ↦ b * b) (𝓝 1) (𝓝 1) := by
    simpa using (tendsto_id (x := 𝓝 (1 : A))).mul tendsto_id
  have hroot : Tendsto (fun b : A ↦ sqrtNearOne A (b * b)) (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def, sqrtNearOne_one] using continuousAt_sqrtNearOne.tendsto.comp hsq
  filter_upwards [eventually_norm_sub_one_lt hsq, eventually_norm_sub_one_lt hroot,
    eventually_norm_sub_one_lt (tendsto_id (x := 𝓝 (1 : A)))] with b hb hroot hb'
  exact eq_of_mul_self_eq_mul_self (sqrtNearOne_mul_self hb) (by simp only [id] at hb'; linarith)

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

end TauCeti

open TauCeti

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]

/-- **The square root near the identity commutes with continuous algebra homomorphisms** on the
open unit ball about `1` of a Banach algebra, where its binomial series converges. The target
need not be complete. -/
theorem ContinuousAlgHom.map_sqrtNearOne [CompleteSpace A] (φ : A →A[ℝ] B) {x : A}
    (hx : ‖x - 1‖ < 1) : φ (sqrtNearOne A x) = sqrtNearOne B (φ x) := by
  rw [sqrtNearOne_eq_tsum (φ x)]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [Function.comp_def, map_smul, map_pow, map_sub, map_one] using
    (hasSum_sqrtNearOne hx).map φ φ.continuous

/-- **The square root near the identity commutes with continuous algebra isomorphisms**, at every
element: the binomial series of `x` converges exactly when that of its image does. For instance,
conjugating an operator by a continuous linear equivalence `e`
(`ContinuousLinearEquiv.conjContinuousAlgEquiv`) conjugates its square root near the identity by
`e`. -/
theorem ContinuousAlgEquiv.map_sqrtNearOne (e : A ≃A[ℝ] B) (x : A) :
    e (sqrtNearOne A x) = sqrtNearOne B (e x) := by
  rw [sqrtNearOne_eq_tsum, sqrtNearOne_eq_tsum, ← e.toContinuousLinearEquiv_apply,
    e.toContinuousLinearEquiv.map_tsum]
  simp only [ContinuousAlgEquiv.toContinuousLinearEquiv_apply, map_smul, map_pow, map_sub,
    map_one]
