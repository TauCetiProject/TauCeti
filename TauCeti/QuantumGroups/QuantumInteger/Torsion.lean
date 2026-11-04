/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.QuantumOrder
public import TauCeti.QuantumGroups.QuantumInteger.RootOfUnity

import Mathlib.Algebra.Field.ZMod

/-!
# Quantum order and multiplicative order

For a unit `u ≠ ±1` in a commutative ring without zero divisors, the vanishing indices of
`qInt R (u + u⁻¹)` are exactly the multiples of `orderOf (u ^ 2)`. Consequently the quantum
order of `u + u⁻¹` is `orderOf (u ^ 2)` when `u` has finite order, and is infinite otherwise.
In particular, a unit of even order `2ℓ` gives quantum order `ℓ`, whereas a unit of odd
order `ℓ` gives quantum order `ℓ`. This distinction translates root-of-unity hypotheses
into the first-vanishing-index hypotheses used for Jones–Wenzl projections.

These comparisons hold in positive characteristic too, provided `u ≠ ±1`. At the excluded
units, the evaluations at `±2` are instead governed by the characteristic of the ring.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {u : Rˣ}

/-- For a finite-order unit other than `±1`, the quantum order is the multiplicative order
of its square. -/
theorem quantumOrder_add_inv_eq_orderOf_sq (hu₁ : u ≠ 1) (hu₂ : u ≠ -1)
    (hu : IsOfFinOrder u) :
    quantumOrder ((u : R) + ↑u⁻¹) = (orderOf (u ^ 2) : ℕ∞) := by
  apply (quantumOrder_eq_natCast_iff _ _).mpr
  refine ⟨hu.pow.orderOf_pos, ?_, ?_⟩
  · exact (qInt_add_inv_eq_zero_iff_orderOf_sq_dvd hu₁ hu₂ _).mpr dvd_rfl
  · intro k hk hkl hz
    have hd := (qInt_add_inv_eq_zero_iff_orderOf_sq_dvd hu₁ hu₂ k).mp hz
    exact (not_le_of_gt hkl) (Nat.le_of_dvd hk hd)

/-- Away from `±1`, the quantum order is infinite exactly when the unit has infinite
multiplicative order. -/
theorem quantumOrder_add_inv_eq_top_iff (hu₁ : u ≠ 1) (hu₂ : u ≠ -1) :
    quantumOrder ((u : R) + ↑u⁻¹) = ⊤ ↔ ¬ IsOfFinOrder u := by
  rw [quantumOrder_eq_top_iff]
  constructor
  · intro h hu
    exact h (orderOf (u ^ 2)) hu.pow.orderOf_pos
      ((qInt_add_inv_eq_zero_iff_orderOf_sq_dvd hu₁ hu₂ _).mpr dvd_rfl)
  · intro hu n hn hz
    have hp := pow_two_mul_eq_one_of_qInt_add_inv_eq_zero hz
    exact hu ((isOfFinOrder_iff_pow_eq_one).mpr ⟨2 * n, by omega, hp⟩)

/-- In the finite-order case, the quantum order is the order of `u` divided by its gcd
with two. No characteristic-zero assumption is needed. -/
theorem quantumOrder_add_inv_eq_div_gcd (hu₁ : u ≠ 1) (hu₂ : u ≠ -1)
    (hu : IsOfFinOrder u) :
    quantumOrder ((u : R) + ↑u⁻¹) = (orderOf u / (orderOf u).gcd 2 : ℕ) := by
  rw [quantumOrder_add_inv_eq_orderOf_sq hu₁ hu₂ hu, orderOf_pow' _ (by decide : 2 ≠ 0)]

/-- A unit of even finite order `2ℓ`, other than `-1`, gives quantum order `ℓ`. -/
theorem quantumOrder_add_inv_of_orderOf_eq_two_mul (hu₂ : u ≠ -1)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hu : orderOf u = 2 * ℓ) :
    quantumOrder ((u : R) + ↑u⁻¹) = ℓ := by
  have hu₁ : u ≠ 1 := by
    rintro rfl
    simp only [orderOf_one] at hu
    omega
  have hfin : IsOfFinOrder u := orderOf_pos_iff.mp (by omega)
  rw [quantumOrder_add_inv_eq_orderOf_sq hu₁ hu₂ hfin,
    orderOf_pow_of_dvd (by decide : 2 ≠ 0) (by simp [hu]), hu, Nat.mul_div_right _ (by decide)]

/-- A unit of odd finite order, other than `1`, gives the same quantum order. -/
theorem quantumOrder_add_inv_of_odd_orderOf (hu₁ : u ≠ 1)
    (hu : Odd (orderOf u)) : quantumOrder ((u : R) + ↑u⁻¹) = (orderOf u : ℕ∞) := by
  have hu₂ : u ≠ -1 := by
    intro h
    have hp := pow_orderOf_eq_one u
    rw [h] at hu hp
    rw [hu.neg_one_pow] at hp
    exact hu₁ (h.trans hp)
  have hfin : IsOfFinOrder u := orderOf_pos_iff.mp hu.pos
  rw [quantumOrder_add_inv_eq_orderOf_sq hu₁ hu₂ hfin, hu.coprime_two_right.orderOf_pow]

/-- In the finite-order case, a quantum integer vanishes exactly at the multiples of the
quantum order. The first vanishing index determines every vanishing index. -/
theorem qInt_add_inv_eq_zero_iff_of_quantumOrder_eq (hu₁ : u ≠ 1) (hu₂ : u ≠ -1)
    {ℓ : ℕ} (hℓ : quantumOrder ((u : R) + ↑u⁻¹) = ℓ) (n : ℕ) :
    qInt R (u + ↑u⁻¹) n = 0 ↔ ℓ ∣ n := by
  have hfin : IsOfFinOrder u := by
    by_contra h
    have ht := (quantumOrder_add_inv_eq_top_iff hu₁ hu₂).mpr h
    simp [hℓ] at ht
  have heq : orderOf (u ^ 2) = ℓ := by
    exact_mod_cast (quantumOrder_add_inv_eq_orderOf_sq hu₁ hu₂ hfin).symm.trans hℓ
  rw [qInt_add_inv_eq_zero_iff_orderOf_sq_dvd hu₁ hu₂, heq]

/-- A primitive sixth root and a primitive third root in `𝔽₇` have the same quantum order,
although their multiplicative orders differ by a factor of two. -/
example : quantumOrder (1 : ZMod 7) = 3 ∧ quantumOrder (-1 : ZMod 7) = 3 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let u : (ZMod 7)ˣ := ⟨3, 5, by decide, by decide⟩
  let v : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩
  have hu : orderOf u = 6 := (orderOf_eq_iff (by decide : 0 < 6)).mpr
    ⟨by decide, by intro m hm hp; interval_cases m <;> decide⟩
  have hv : orderOf v = 3 := (orderOf_eq_iff (by decide : 0 < 3)).mpr
    ⟨by decide, by intro m hm hp; interval_cases m <;> decide⟩
  constructor
  · have h := quantumOrder_add_inv_of_orderOf_eq_two_mul
      (by decide : u ≠ -1) (by decide : 0 < 3) hu
    have hδ : (u : ZMod 7) + ↑u⁻¹ = 1 := by decide
    rw [hδ] at h
    exact_mod_cast h
  · have h := quantumOrder_add_inv_of_odd_orderOf
      (by decide : v ≠ 1) (by rw [hv]; decide)
    have hδ : (v : ZMod 7) + ↑v⁻¹ = -1 := by decide
    rw [hδ, hv] at h
    exact_mod_cast h

end TauCeti
