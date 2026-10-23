/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Complete

/-!
# The Teichmüller splitting and units of Witt vectors over a perfect ring

A Teichmüller representative `[a]` and a Verschiebung `V x` have disjoint supports, so `[a] + V x`
has Witt coordinates `a, x₀, x₁, …`. Over a ring of characteristic `p` the Verschiebung of `F u` is
`p u`, so a sum `[a] + p u` has Witt coordinates `a` in degree `0` and `u_n ^ p` in degree `n + 1`
(`WittVector.teichmuller_add_p_mul_coeff_succ`).

Over a perfect ring `R` of characteristic `p` every Witt vector is `[x₀] + p u`
(`WittVector.exists_eq_teichmuller_add_p_mul`), and since `𝕎 R` is `p`-adically complete,
`x` is a unit exactly when its zeroth Witt coordinate `x₀` is a unit of `R`
(`WittVector.isUnit_iff_isUnit_coeff_zero`). Mathlib proves the unit criterion only over a field
(`WittVector.isUnit_of_coeff_zero_ne_zero`).

## Main results

* `WittVector.teichmuller_add_verschiebung_coeff_zero`,
  `WittVector.teichmuller_add_verschiebung_coeff_succ`: the Witt coordinates of `[a] + V x`.
* `WittVector.teichmuller_add_p_mul_coeff_zero`, `WittVector.teichmuller_add_p_mul_coeff_succ`:
  the Witt coordinates of `[a] + p u` in characteristic `p`.
* `WittVector.exists_eq_teichmuller_add_p_mul`: over a perfect ring, `x = [x₀] + p u`.
* `WittVector.isUnit_iff_isUnit_coeff_zero`: over a perfect ring, `x` is a unit iff `x₀` is.

## References

* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Example 6.1.6.
-/

public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

local notation "𝕎" => WittVector p

/-- The zeroth Witt coordinate of `[a] + V x` is `a`. -/
@[simp]
theorem teichmuller_add_verschiebung_coeff_zero (a : R) (x : 𝕎 R) :
    (teichmuller p a + verschiebung x).coeff 0 = a := by
  rw [add_coeff_zero, teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]

/-- The `(n + 1)`-st Witt coordinate of `[a] + V x` is the `n`-th Witt coordinate of `x`: the
Teichmüller representative and the Verschiebung have disjoint supports. -/
@[simp]
theorem teichmuller_add_verschiebung_coeff_succ (a : R) (x : 𝕎 R) (n : ℕ) :
    (teichmuller p a + verschiebung x).coeff (n + 1) = x.coeff n := by
  rw [coeff_add_of_disjoint, teichmuller_coeff_pos p a _ n.succ_pos, verschiebung_coeff_succ,
    zero_add]
  rintro (_ | k)
  · exact .inr (verschiebung_coeff_zero x)
  · exact .inl (teichmuller_coeff_pos p a _ k.succ_pos)

section CharP

variable [CharP R p]

/-- In characteristic `p`, the zeroth Witt coordinate of `[a] + p u` is `a`. -/
@[simp]
theorem teichmuller_add_p_mul_coeff_zero (a : R) (u : 𝕎 R) :
    (teichmuller p a + p * u).coeff 0 = a := by
  rw [mul_comm, ← verschiebung_frobenius, teichmuller_add_verschiebung_coeff_zero]

/-- In characteristic `p`, the `(n + 1)`-st Witt coordinate of `[a] + p u` is `u_n ^ p`. -/
@[simp]
theorem teichmuller_add_p_mul_coeff_succ (a : R) (u : 𝕎 R) (n : ℕ) :
    (teichmuller p a + p * u).coeff (n + 1) = u.coeff n ^ p := by
  rw [mul_comm, ← verschiebung_frobenius, teichmuller_add_verschiebung_coeff_succ,
    coeff_frobenius_charP]

variable [PerfectRing R p]

/-- Over a perfect ring of characteristic `p`, every Witt vector is `[x₀] + p u`. -/
theorem exists_eq_teichmuller_add_p_mul (x : 𝕎 R) :
    ∃ u : 𝕎 R, x = teichmuller p (x.coeff 0) + p * u := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp <|
    (mem_span_p_iff_coeff_zero_eq_zero (x - teichmuller p (x.coeff 0))).mpr <| by
      rw [← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply,
        teichmuller_coeff_zero, sub_self]
  exact ⟨u, by rw [← hu, add_sub_cancel]⟩

/-- **Units of Witt vectors over a perfect ring.** Over a perfect ring `R` of characteristic `p`, a
Witt vector is a unit exactly when its zeroth Witt coordinate is a unit of `R`. -/
theorem isUnit_iff_isUnit_coeff_zero {x : 𝕎 R} : IsUnit x ↔ IsUnit (x.coeff 0) := by
  refine ⟨fun h ↦ by simpa using h.map (constantCoeff (p := p) (R := R)), fun ⟨a, ha⟩ ↦ ?_⟩
  obtain ⟨u, hu⟩ := exists_eq_teichmuller_add_p_mul x
  have hp : (p : 𝕎 R) ∈ (⊥ : Ideal (𝕎 R)).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self _)
  have h : x = teichmuller p (a : R) *
      ((p : 𝕎 R) * (teichmuller p ((a⁻¹ : Rˣ) : R) * u) + 1) := by
    rw [hu, ← ha, mul_add, mul_one, add_comm, mul_left_comm, ← mul_assoc (teichmuller p _),
      ← map_mul, Units.mul_inv, map_one, one_mul]
  rw [h]
  exact (a.isUnit.map (teichmuller p)).mul (Ideal.mem_jacobson_bot.mp hp _)

end CharP

end WittVector
