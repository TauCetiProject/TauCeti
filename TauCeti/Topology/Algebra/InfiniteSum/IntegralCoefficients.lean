/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
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

In a commutative target ring, `evalIntSeries` evaluates these series as a ring homomorphism.
Evaluation has norm at most one, at most the norm of the parameter for a series without constant
term, and multiplication by an evaluated formal unit preserves norms, even when the ring norm is
only submultiplicative.
-/

public section

open PowerSeries

namespace TauCeti

/-- The terms of an integer-coefficient power series are absolutely summable at a parameter of
norm below one in a non-archimedean normed ring. -/
theorem summable_norm_intCast_mul_pow {K : Type*} [NormedRing K] [NormOneClass K]
    [IsUltrametricDist K] (a : ℕ → ℤ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(a n : K) * q ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_norm_geometric_of_norm_lt_one hq)
  calc
    ‖(a n : K) * q ^ n‖ ≤ ‖(a n : K)‖ * ‖q ^ n‖ := norm_mul_le _ _
    _ ≤ 1 * ‖q ^ n‖ :=
      mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K (a n))
        (norm_nonneg (q ^ n))
    _ = ‖q ^ n‖ := one_mul _

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
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) : ℤ⟦X⟧ →+* K where
  toFun f := ∑' n : ℕ, ((PowerSeries.coeff n f : ℤ) : K) * q ^ n
  map_zero' := by
    simp
  map_one' := by
    simp [PowerSeries.coeff_one]
  map_add' f g := by
    simp_rw [map_add, Int.cast_add, add_mul]
    exact (summable_intCast_mul_pow (fun n ↦ PowerSeries.coeff n f) hq).tsum_add
      (summable_intCast_mul_pow (fun n ↦ PowerSeries.coeff n g) hq)
  map_mul' f g := by
    let a : ℕ → K := fun n ↦ ((PowerSeries.coeff n f : ℤ) : K) * q ^ n
    let b : ℕ → K := fun n ↦ ((PowerSeries.coeff n g : ℤ) : K) * q ^ n
    have han : Summable (fun n ↦ ‖a n‖) :=
      summable_norm_intCast_mul_pow (fun n ↦ PowerSeries.coeff n f) hq
    have hbn : Summable (fun n ↦ ‖b n‖) :=
      summable_norm_intCast_mul_pow (fun n ↦ PowerSeries.coeff n g) hq
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm han hbn]
    apply tsum_congr fun n ↦ ?_
    rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    simp only [Int.cast_mul, a, b]
    rw [← hp', pow_add]
    ring

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
  rw [evalIntSeries_apply]
  simp [PowerSeries.coeff_X]

/-- Evaluation of an integral series inside the open unit ball has norm at most one. -/
theorem norm_evalIntSeries_le_one {K : Type*} [NormedCommRing K] [NormOneClass K]
    [CompleteSpace K]
    [IsUltrametricDist K] (q : K) (hq : ‖q‖ < 1) (f : ℤ⟦X⟧) :
    ‖evalIntSeries q hq f‖ ≤ 1 := by
  rw [evalIntSeries_apply]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  calc
    _ ≤ ‖((coeff n f : ℤ) : K)‖ * ‖q ^ n‖ := norm_mul_le _ _
    _ ≤ 1 * ‖q ^ n‖ :=
      mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K (coeff n f))
        (norm_nonneg (q ^ n))
    _ ≤ 1 * ‖q‖ ^ n := by simpa only [one_mul] using norm_pow_le q n
    _ ≤ 1 := by simpa only [one_mul] using pow_le_one₀ (norm_nonneg q) hq.le

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

end TauCeti

end
