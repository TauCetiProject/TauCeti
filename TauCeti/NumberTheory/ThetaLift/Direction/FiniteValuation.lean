/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.Direction.Matrices
public import TauCeti.Algebra.Order.WithTop.Nsmul
import Mathlib.Algebra.BigOperators.WithTop

/-!
# The finite valuation budget for changes of theta directions

Dividing the scaled deduction by the Frobenius degree recovers the deduction in units
of the valuation of the modulus. For a nonnegative additive valuation into `WithTop F`,
a finite value of the modulus then gives a finite budget in the ordered field `F`.
-/

public section

open Finset Matrix

namespace TauCeti

/-- Dividing the scaled cost by `q` gives the two normalized minima and the normalized
ordinary source column count. Marked places contribute no distinguished columns. -/
theorem directionDeductionCost_div {F ι : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Fintype ι] (height : ι → ℕ) (a b : Option ι → ℕ) (q : ℕ) (markL markR : Bool) :
    (directionDeductionCost height a b q markL markR : F) / q =
      min ((if markL then 0 else (a none : F)) / q)
        ((∑ i, (b (some i) : F)) + if markR then 0 else (b none : F)) +
      (∑ i, (a (some i) : F)) / q +
      min ((∑ i, (a (some i) : F) * height i) / q) (∑ i, (b (some i) : F) * height i) := by
  rcases q.eq_zero_or_pos with rfl | hq
  · have h₁ : 0 ≤ (∑ i, (b (some i) : F)) + if markR then 0 else (b none : F) :=
      add_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (by split <;> positivity)
    have h₂ : 0 ≤ ∑ i, (b (some i) : F) * height i :=
      Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    simp [min_eq_left h₁, min_eq_left h₂]
  have hq₀ : 0 < (q : F) := Nat.cast_pos.mpr hq
  simp only [directionDeductionCost_def, Nat.cast_add, Nat.cast_min, Nat.cast_mul,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, add_div, ← min_div_div_right hq₀.le,
    mul_div_cancel_left₀ _ hq₀.ne']

end TauCeti

namespace AddValuation

open TauCeti (DirectionPairExempt directionDeductionCost
  exists_direction_matrices_with_dvd_frobenius_pairings)

/-- For a nonnegative additive valuation into `WithTop F`, if the modulus `π` has finite
value `w`, the simultaneous direction matrices can be chosen with weighted determinant
valuation at most `w` times the sum of the normalized deductions in `F`. -/
theorem exists_direction_matrices_with_det_valuation_le_finite_budget
    {R F ι n τ I : Type*} [CommRing R] [PreValuationRing R] [Fintype ι] [Fintype n] [Fintype τ]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] {height : ι → ℕ}
    (v : AddValuation R (WithTop F)) (hv : ∀ x, 0 ≤ v x) {p : ℕ} (hp : p.Prime)
    {π : R} (hπ : π ∣ (p : R)) {w : F} (hw : v π = w)
    (s : Finset I) (e : I → ℕ) (partner : I → τ → τ) (mark : τ → Bool)
    (a : τ → Option ι → ℕ)
    (Y : ∀ (_ : τ) (h : Option ι), (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (d : I → R) (hd : ∀ i ∈ s, Associated (d i ^ (p ^ e i)) π)
    (hroot : ∀ i ∈ s, ∀ t j, ∃ x : R, π ∣ Y (partner i t) none 1 j - x ^ (p ^ e i)) :
    ∃ g : ∀ (_ : τ) (h : Option ι), Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
      (∀ i ∈ s, ∀ t h j, ¬DirectionPairExempt (mark t) (mark (partner i t)) h j →
        ∀ k k', π ∣ (fun u ↦ (Y t h (g t h k) u) ^ (p ^ e i)) ⬝ᵥ
          Y (partner i t) j (g (partner i t) j k')) ∧
      (∑ t, ∑ h, a t h • v (g t h).det) ≤ ↑(w * ∑ i ∈ s, ∑ t,
        (directionDeductionCost height (a t) (a (partner i t)) (p ^ e i)
          (mark t) (mark (partner i t)) : F) / (p : F) ^ e i) := by
  obtain ⟨g, hg, hdvd⟩ :=
    exists_direction_matrices_with_dvd_frobenius_pairings hp hπ s e partner mark a Y d hd hroot
  have hval (i : I) (hi : i ∈ s) : v (d i) ≤ ↑(w / (p : F) ^ e i) := by
    have hle := AddValuation.map_le_map_of_dvd hv (hd i hi).dvd
    rw [v.map_pow, hw] at hle
    have hq : 0 < p ^ e i := pow_pos hp.pos _
    simpa only [Nat.cast_pow] using (WithTop.nsmul_le_coe_iff hq).mp hle
  have hdet := AddValuation.map_le_map_of_dvd hv hdvd
  simp only [v.map_prod, v.map_pow] at hdet
  refine ⟨g, hg, hdet.trans ?_⟩
  simp only [Finset.mul_sum, WithTop.coe_sum]
  refine Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun t _ ↦ ?_
  refine (nsmul_le_nsmul_right (hval i hi) _).trans_eq ?_
  rw [← WithTop.coe_nsmul, nsmul_eq_mul]
  congr 1
  ring

end AddValuation
