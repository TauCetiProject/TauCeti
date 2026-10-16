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
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Evaluating integral coefficient series in non-archimedean normed rings

Every integer has norm at most one in a non-archimedean normed ring with `‖1‖ = 1`. Thus a series
with arbitrary integer coefficients converges at any parameter of norm below one, provided the ring
is complete. This includes complete valued fields with nondiscrete valuations or positive
characteristic.

More generally, `RingHom.evalBoundedSeries` evaluates a power series after applying a coefficient
ring homomorphism whose image has norm at most one. In a commutative target ring, both
constructions are ring homomorphisms. Evaluation has norm at most one, at most the norm of the
parameter for an integral series without constant term, and multiplication by an evaluated formal
unit preserves norms, even when the ring norm is only submultiplicative.

Iterating these evaluations, `evalIntBivariateSeries` evaluates an integral power series in two
variables at a pair of parameters in the open unit ball.
-/

public section

open PowerSeries

namespace RingHom

/-- The terms of a power series are absolutely summable after applying a coefficient map with
image in the closed unit ball, provided the parameter belongs to the open unit ball. -/
theorem summable_norm_map_coeff_mul_pow {R K : Type*} [Semiring R]
    [NormedRing K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (a : ℕ → R) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖φ (a n) * q ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_norm_geometric_of_norm_lt_one hq)
  calc
    ‖φ (a n) * q ^ n‖ ≤ ‖φ (a n)‖ * ‖q ^ n‖ := norm_mul_le _ _
    _ ≤ 1 * ‖q ^ n‖ := mul_le_mul_of_nonneg_right (hφ (a n)) (norm_nonneg _)
    _ = ‖q ^ n‖ := one_mul _

/-- A power series becomes summable after applying a coefficient map with image in the closed unit
ball and evaluating at a parameter in the open unit ball. -/
theorem summable_map_coeff_mul_pow {R K : Type*} [Semiring R]
    [NormedRing K] [CompleteSpace K]
    (φ : R →+* K) (hφ : ∀ r, ‖φ r‖ ≤ 1) (a : ℕ → R) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ φ (a n) * q ^ n) :=
  (summable_norm_map_coeff_mul_pow φ hφ a hq).of_norm

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
    exact (summable_map_coeff_mul_pow φ hφ (fun n ↦ coeff n f) hq).tsum_add
      (summable_map_coeff_mul_pow φ hφ (fun n ↦ coeff n g) hq)
  map_mul' f g := by
    let a : ℕ → K := fun n ↦ φ (coeff n f) * q ^ n
    let b : ℕ → K := fun n ↦ φ (coeff n g) * q ^ n
    have han : Summable (fun n ↦ ‖a n‖) :=
      summable_norm_map_coeff_mul_pow φ hφ (fun n ↦ coeff n f) hq
    have hbn : Summable (fun n ↦ ‖b n‖) :=
      summable_norm_map_coeff_mul_pow φ hφ (fun n ↦ coeff n g) hq
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
norm below one in a non-archimedean normed ring. -/
theorem summable_norm_intCast_mul_pow {K : Type*} [NormedRing K] [NormOneClass K]
    [IsUltrametricDist K] (a : ℕ → ℤ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(a n : K) * q ^ n‖) :=
  RingHom.summable_norm_map_coeff_mul_pow (Int.castRingHom K)
    (IsUltrametricDist.norm_intCast_le_one K) a hq

/-- An arbitrary integer-coefficient power series converges at a parameter of norm below one in
a complete non-archimedean normed ring. -/
theorem summable_intCast_mul_pow {K : Type*} [NormedRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (a : ℕ → ℤ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (a n : K) * q ^ n) :=
  (summable_norm_intCast_mul_pow a hq).of_norm

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
