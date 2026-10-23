/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Evaluating integral coefficient series in non-archimedean normed rings

Every integer has norm at most `‖1‖` in a non-archimedean seminormed ring. Thus a series with
arbitrary integer coefficients converges at any parameter of norm below one, provided the ring is
complete. This includes complete valued fields with nondiscrete valuations or positive
characteristic. More generally, `TauCeti.summable_norm_mul_pow_of_norm_le` applies to any bounded
sequence of coefficients, without requiring a normalized norm.

In a complete normed commutative ring, `RingHom.evalBoundedSeries` evaluates a power series after
applying a coefficient ring homomorphism whose image has norm at most one. For a non-archimedean
target with `‖1‖ = 1`, `evalIntSeries` specializes this to integer coefficients. Both constructions
are ring homomorphisms. In a non-archimedean target, evaluation has norm at most one, at most the
norm of the parameter for an integral series without constant term, and multiplication by an
evaluated integral formal unit preserves norms, even when the ring norm is only submultiplicative.

Iterating these evaluations, `evalIntBivariateSeries` evaluates an integral power series in two
variables at a pair of parameters in the open unit ball. Likewise an integral polynomial has value
of norm at most one at every point of the closed unit ball (`Polynomial.norm_aeval_le_one`), so
evaluating the coefficients of a series in `ℤ[X]⟦Y⟧` at such a point is a valid coefficient map
for `RingHom.evalBoundedSeries`.
-/

public section

open PowerSeries

namespace Polynomial

/-- An integral polynomial evaluated at a point of the closed unit ball of a non-archimedean
normed ring with `‖1‖ = 1` has norm at most one. -/
theorem norm_aeval_le_one {K : Type*} [NormedRing K] [NormOneClass K] [IsUltrametricDist K]
    (p : ℤ[X]) {x : K} (hx : ‖x‖ ≤ 1) : ‖aeval x p‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
  rw [zsmul_eq_mul]
  calc ‖(p.coeff i : K) * x ^ i‖ ≤ ‖(p.coeff i : K)‖ * ‖x ^ i‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (IsUltrametricDist.norm_intCast_le_one K _)
        ((norm_pow_le x i).trans (pow_le_one₀ (norm_nonneg _) hx)) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Polynomial

namespace RingHom

/-- Evaluation of a formal power series after applying a coefficient ring homomorphism whose
image has norm at most one. The defining sum converges at every parameter of norm less than one,
without requiring a linear topology on the target. -/
noncomputable def evalBoundedSeries {R K : Type*} [Semiring R]
    [NormedCommRing K] [CompleteSpace K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (q : K) (hq : ‖q‖ < 1) : R⟦X⟧ →+* K where
  toFun f := ∑' n : ℕ, φ (coeff n f) * q ^ n
  map_zero' := by
    simp
  map_one' := by
    simp [PowerSeries.coeff_one]
  map_add' f g := by
    simp_rw [map_add, add_mul]
    exact (TauCeti.summable_mul_pow_of_norm_le (fun n ↦ hφ (coeff n f)) hq).tsum_add
      (TauCeti.summable_mul_pow_of_norm_le (fun n ↦ hφ (coeff n g)) hq)
  map_mul' f g := by
    let a : ℕ → K := fun n ↦ φ (coeff n f) * q ^ n
    let b : ℕ → K := fun n ↦ φ (coeff n g) * q ^ n
    have han : Summable (fun n ↦ ‖a n‖) :=
      TauCeti.summable_norm_mul_pow_of_norm_le (fun n ↦ hφ (coeff n f)) hq
    have hbn : Summable (fun n ↦ ‖b n‖) :=
      TauCeti.summable_norm_mul_pow_of_norm_le (fun n ↦ hφ (coeff n g)) hq
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm han hbn]
    apply tsum_congr fun n ↦ ?_
    rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p.1 + p.2 = n := by simpa using hp
    simp only [map_mul, a, b]
    rw [← hp', pow_add]
    ring

/-- Bounded-coefficient evaluation is the convergent sum of the mapped coefficients times powers
of the parameter. -/
theorem evalBoundedSeries_apply {R K : Type*} [Semiring R]
    [NormedCommRing K] [CompleteSpace K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (q : K) (hq : ‖q‖ < 1) (f : R⟦X⟧) :
    evalBoundedSeries φ hφ q hq f = ∑' n : ℕ, φ (coeff n f) * q ^ n := by
  rw [evalBoundedSeries]
  rfl

/-- Bounded-coefficient evaluation sends a constant series through the coefficient map. -/
@[simp]
theorem evalBoundedSeries_C {R K : Type*} [Semiring R]
    [NormedCommRing K] [CompleteSpace K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (q : K) (hq : ‖q‖ < 1) (r : R) :
    evalBoundedSeries φ hφ q hq (C r) = φ r := by
  rw [evalBoundedSeries_apply]
  rw [tsum_eq_single 0]
  · simp [PowerSeries.coeff_C]
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

/-- Bounded-coefficient evaluation sends the formal parameter to the chosen element. -/
@[simp]
theorem evalBoundedSeries_X {R K : Type*} [Semiring R]
    [NormedCommRing K] [CompleteSpace K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (q : K) (hq : ‖q‖ < 1) :
    evalBoundedSeries φ hφ q hq (X : R⟦X⟧) = q := by
  rw [evalBoundedSeries_apply]
  simp [PowerSeries.coeff_X]

/-- Bounded-coefficient evaluation has norm at most one. -/
theorem norm_evalBoundedSeries_le_one {R K : Type*} [Semiring R]
    [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (q : K) (hq : ‖q‖ < 1) (f : R⟦X⟧) :
    ‖evalBoundedSeries φ hφ q hq f‖ ≤ 1 := by
  rw [evalBoundedSeries_apply]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hφ (coeff 0 f)
  calc
    ‖φ (coeff n f) * q ^ n‖ ≤ ‖φ (coeff n f)‖ * ‖q ^ n‖ := norm_mul_le _ _
    _ ≤ 1 * ‖q ^ n‖ := mul_le_mul_of_nonneg_right (hφ _) (norm_nonneg _)
    _ ≤ 1 * ‖q‖ ^ n := by
      simpa only [one_mul] using norm_pow_le' q (Nat.pos_of_ne_zero hn)
    _ ≤ 1 := by simpa only [one_mul] using pow_le_one₀ (norm_nonneg q) hq.le

end RingHom

namespace TauCeti

/-- The terms of an integer-coefficient power series are absolutely summable at a parameter of
norm below one in a non-archimedean seminormed ring. -/
theorem summable_norm_intCast_mul_pow {K : Type*} [SeminormedRing K]
    [IsUltrametricDist K] (a : ℕ → ℤ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(a n : K) * q ^ n‖) :=
  summable_norm_mul_pow_of_norm_le
    (fun n ↦ IsUltrametricDist.norm_intCast_le_norm_one (a n)) hq

/-- An arbitrary integer-coefficient power series converges at a parameter of norm below one in
a complete non-archimedean seminormed ring. -/
theorem summable_intCast_mul_pow {K : Type*} [SeminormedRing K]
    [CompleteSpace K]
    [IsUltrametricDist K] (a : ℕ → ℤ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (a n : K) * q ^ n) :=
  (summable_norm_intCast_mul_pow a hq).of_norm

/-- A bivariate family with arbitrary integer coefficients is absolutely summable when both
parameters have norm below one in a non-archimedean seminormed ring. -/
theorem summable_norm_intCast_mul_pow_mul_pow {K : Type*} [SeminormedRing K]
    [IsUltrametricDist K] (c : ℕ × ℕ → ℤ) {u v : K} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    Summable (fun p : ℕ × ℕ ↦ ‖(c p : K) * u ^ p.1 * v ^ p.2‖) := by
  have hs := (summable_norm_pow_of_norm_lt_one hu).mul_of_nonneg
    (summable_norm_pow_of_norm_lt_one hv) (fun _ ↦ norm_nonneg _)
    (fun _ ↦ norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) (hs.mul_left ‖(1 : K)‖)
  calc
    ‖(c p : K) * u ^ p.1 * v ^ p.2‖ ≤ ‖(c p : K) * u ^ p.1‖ * ‖v ^ p.2‖ := norm_mul_le _ _
    _ ≤ (‖(1 : K)‖ * ‖u ^ p.1‖) * ‖v ^ p.2‖ := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (IsUltrametricDist.norm_intCast_le_norm_one (c p)) (norm_nonneg _))
    _ = ‖(1 : K)‖ * (‖u ^ p.1‖ * ‖v ^ p.2‖) := mul_assoc _ _ _

/-- Evaluation of an integral formal power series at a parameter of norm below one in a complete
non-archimedean normed commutative ring. Integer coefficients are bounded in norm, so the defining
sum converges without requiring a linear topology on the target. -/
noncomputable def evalIntSeries {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) : ℤ⟦X⟧ →+* K :=
  RingHom.evalBoundedSeries (Int.castRingHom K) (IsUltrametricDist.norm_intCast_le_one K) q hq

/-- The evaluation map is the convergent sum of the coefficients times powers of the
parameter. -/
theorem evalIntSeries_apply {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) (f : ℤ⟦X⟧) :
    evalIntSeries q hq f = ∑' n : ℕ, ((PowerSeries.coeff n f : ℤ) : K) * q ^ n :=
  (rfl)

/-- Evaluating the formal parameter gives the chosen element. -/
@[simp]
theorem evalIntSeries_X {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) :
    evalIntSeries q hq (PowerSeries.X : ℤ⟦X⟧) = q := by
  exact RingHom.evalBoundedSeries_X _ _ q hq

/-- Evaluation of an integral series inside the open unit ball has norm at most one. -/
theorem norm_evalIntSeries_le_one {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) (f : ℤ⟦X⟧) :
    ‖evalIntSeries q hq f‖ ≤ 1 := by
  exact RingHom.norm_evalBoundedSeries_le_one _ _ q hq f

/-- An integral series without constant term evaluates inside the open unit ball to an element of
norm at most that of the parameter. -/
theorem norm_evalIntSeries_le_of_constantCoeff_eq_zero {K : Type*} [NormedCommRing K]
    [NormOneClass K] [CompleteSpace K] [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) {f : ℤ⟦X⟧}
    (hf : constantCoeff f = 0) : ‖evalIntSeries q hq f‖ ≤ ‖q‖ := by
  obtain ⟨g, rfl⟩ := X_dvd_iff.mpr hf
  rw [map_mul, evalIntSeries_X]
  exact (norm_mul_le_of_le le_rfl (norm_evalIntSeries_le_one q hq g)).trans_eq (mul_one _)

/-- Multiplication by an integral formal unit evaluated inside the open unit ball preserves norms
in a complete non-archimedean normed commutative ring with `‖1‖ = 1`. -/
@[simp] theorem norm_mul_evalIntSeries_of_isUnit {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (x q : K) (hq : ‖q‖ < 1) {f : ℤ⟦X⟧} (hf : IsUnit f) :
    ‖x * evalIntSeries q hq f‖ = ‖x‖ := by
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  have hmul : evalIntSeries q hq f * evalIntSeries q hq g = 1 := by
    rw [← map_mul, hfg, map_one]
  apply le_antisymm
  · exact (norm_mul_le_of_le le_rfl (norm_evalIntSeries_le_one q hq f)).trans_eq (mul_one _)
  · calc
      ‖x‖ = ‖(x * evalIntSeries q hq f) * evalIntSeries q hq g‖ := by
        rw [mul_assoc, hmul, mul_one]
      _ ≤ ‖x * evalIntSeries q hq f‖ :=
        (norm_mul_le_of_le le_rfl (norm_evalIntSeries_le_one q hq g)).trans_eq (mul_one _)

/-- An integral formal unit evaluates to an element of norm one inside the open unit ball. -/
@[simp] theorem norm_evalIntSeries_eq_one_of_isUnit {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) {f : ℤ⟦X⟧} (hf : IsUnit f) :
    ‖evalIntSeries q hq f‖ = 1 := by
  simpa only [one_mul, norm_one] using norm_mul_evalIntSeries_of_isUnit 1 q hq hf

/-- Iterated evaluation of an integral bivariate power series at two parameters in the open unit
ball. The inner variable is evaluated at `u`, and the outer variable at `v`. -/
noncomputable def evalIntBivariateSeries {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) : ℤ⟦X⟧⟦X⟧ →+* K :=
  RingHom.evalBoundedSeries (evalIntSeries u hu) (norm_evalIntSeries_le_one u hu) v hv

/-- Bivariate integral evaluation is the iterated convergent sum of the coefficients. -/
theorem evalIntBivariateSeries_apply {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) (f : ℤ⟦X⟧⟦X⟧) :
    evalIntBivariateSeries u hu v hv f =
      ∑' b : ℕ, (∑' a : ℕ, ((coeff a (coeff b f) : ℤ) : K) * u ^ a) * v ^ b := by
  rw [evalIntBivariateSeries, RingHom.evalBoundedSeries_apply]
  apply tsum_congr
  intro b
  rw [evalIntSeries_apply]

/-- Bivariate evaluation is also the joint sum over the two coefficient indices. Absolute
summability permits reindexing this family without retaining the order of evaluation. -/
theorem evalIntBivariateSeries_eq_tsum {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) (f : ℤ⟦X⟧⟦X⟧) :
    evalIntBivariateSeries u hu v hv f =
      ∑' p : ℕ × ℕ, ((coeff p.1 (coeff p.2 f) : ℤ) : K) * u ^ p.1 * v ^ p.2 := by
  have hs := (summable_norm_intCast_mul_pow_mul_pow (K := K)
    (fun p ↦ coeff p.1 (coeff p.2 f)) hu hv).of_norm
  rw [evalIntBivariateSeries_apply]
  calc
    _ = ∑' b : ℕ, ∑' a : ℕ, ((coeff a (coeff b f) : ℤ) : K) * u ^ a * v ^ b := by
      apply tsum_congr
      intro b
      exact ((summable_intCast_mul_pow (fun a ↦ coeff a (coeff b f)) hu).tsum_mul_right
        (v ^ b)).symm
    _ = _ := hs.tsum_comm.trans hs.tsum_prod.symm

/-- Bivariate evaluation of a series constant in the outer variable is its evaluation at the
inner parameter. -/
@[simp]
theorem evalIntBivariateSeries_C {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) (f : ℤ⟦X⟧) :
    evalIntBivariateSeries u hu v hv (C f) = evalIntSeries u hu f := by
  exact RingHom.evalBoundedSeries_C _ _ v hv f

/-- Bivariate evaluation sends the outer formal parameter to the outer chosen element. -/
@[simp]
theorem evalIntBivariateSeries_X {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (hu : ‖u‖ < 1) (v : K) (hv : ‖v‖ < 1) :
    evalIntBivariateSeries u hu v hv (X : ℤ⟦X⟧⟦X⟧) = v := by
  exact RingHom.evalBoundedSeries_X _ _ v hv

end TauCeti

end
