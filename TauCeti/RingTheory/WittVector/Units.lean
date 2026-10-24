/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# The Teichmüller splitting and units of Witt vectors

A Teichmüller representative `[a]` and a Verschiebung `V x` have disjoint supports, so `[a] + V x`
has Witt coordinates `a, x₀, x₁, …`, and every Witt vector is `[x₀] + V u`
(`WittVector.exists_eq_teichmuller_add_verschiebung`). Expanding a product of two such sums with
the projection formula gives the first Witt coordinate of a product,
`(x y)₁ = x₀ ^ p y₁ + y₀ ^ p x₁ + p x₁ y₁` (`WittVector.mul_coeff_one`).

Over a ring of characteristic `p`, `x` is a unit exactly when its zeroth Witt coordinate `x₀` is a
unit of `R` (`WittVector.isUnit_iff_isUnit_coeff_zero`); the inverse is Mathlib's
`WittVector.mkUnit`. Mathlib states the criterion only over a field
(`WittVector.isUnit_of_coeff_zero_ne_zero`). In characteristic `p` the Verschiebung of `F u` is
`p u`, so a sum `[a] + p u` has Witt coordinates `a` in degree `0` and `u_n ^ p` in degree `n + 1`
(`WittVector.teichmuller_add_p_mul_coeff_succ`), and over a perfect ring every Witt vector is
`[x₀] + p u` (`WittVector.exists_eq_teichmuller_add_p_mul`).

## Main results

* `WittVector.teichmuller_add_verschiebung_coeff_zero`,
  `WittVector.teichmuller_add_verschiebung_coeff_succ`: the Witt coordinates of `[a] + V x`.
* `WittVector.exists_eq_teichmuller_add_verschiebung`: every Witt vector is `[x₀] + V u`.
* `WittVector.coeff_frobenius_zero`, `WittVector.mul_coeff_one`: the zeroth Witt coordinate of
  `F x` and the first Witt coordinate of `x y`.
* `WittVector.teichmuller_add_p_mul_coeff_zero`, `WittVector.teichmuller_add_p_mul_coeff_succ`:
  the Witt coordinates of `[a] + p u` in characteristic `p`.
* `WittVector.isUnit_iff_isUnit_coeff_zero`: in characteristic `p`, `x` is a unit iff `x₀` is.
* `WittVector.exists_eq_teichmuller_add_p_mul`: over a perfect ring, `x = [x₀] + p u`.

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

/-- Every Witt vector is `[x₀] + V u`. -/
theorem exists_eq_teichmuller_add_verschiebung (x : 𝕎 R) :
    ∃ u : 𝕎 R, x = teichmuller p (x.coeff 0) + verschiebung u := by
  refine ⟨(x - teichmuller p (x.coeff 0)).shift 1, ?_⟩
  rw [← Function.iterate_one verschiebung, ← eq_iterate_verschiebung, add_sub_cancel]
  intro i hi
  rw [Nat.lt_one_iff.mp hi, ← constantCoeff_apply, map_sub, constantCoeff_apply,
    constantCoeff_apply, teichmuller_coeff_zero, sub_self]

/-- The zeroth Witt coordinate of `F x` is `x₀ ^ p + p x₁`, the first ghost component of `x`. -/
theorem coeff_frobenius_zero (x : 𝕎 R) :
    (frobenius x).coeff 0 = x.coeff 0 ^ p + p * x.coeff 1 := by
  simpa [ghostComponent_apply, wittPolynomial, Finset.sum_range_succ, MvPolynomial.aeval_monomial,
    mul_comm] using ghostComponent_frobenius 0 x

/-- The first Witt coordinate of a product: `(x y)₁ = x₀ ^ p y₁ + y₀ ^ p x₁ + p x₁ y₁`. -/
theorem mul_coeff_one (x y : 𝕎 R) :
    (x * y).coeff 1 =
      x.coeff 0 ^ p * y.coeff 1 + y.coeff 0 ^ p * x.coeff 1 + p * x.coeff 1 * y.coeff 1 := by
  obtain ⟨a, ha⟩ := exists_eq_teichmuller_add_verschiebung x
  obtain ⟨b, hb⟩ := exists_eq_teichmuller_add_verschiebung y
  have h : x * y = teichmuller p (x.coeff 0 * y.coeff 0) +
      verschiebung (b * frobenius (teichmuller p (x.coeff 0)) +
        a * frobenius (teichmuller p (y.coeff 0)) + a * (b * (p : 𝕎 R))) := by
    rw [map_add, map_add, verschiebung_mul_frobenius, verschiebung_mul_frobenius,
      ← frobenius_verschiebung, verschiebung_mul_frobenius, map_mul]
    linear_combination y * ha + (teichmuller p (x.coeff 0) + verschiebung a) * hb
  have hx : x.coeff 1 = a.coeff 0 := by rw [ha, teichmuller_add_verschiebung_coeff_succ]
  have hy : y.coeff 1 = b.coeff 0 := by rw [hb, teichmuller_add_verschiebung_coeff_succ]
  rw [h, teichmuller_add_verschiebung_coeff_succ, hx, hy, ← constantCoeff_apply]
  simp only [map_add, map_mul, map_natCast, constantCoeff_apply, coeff_frobenius_zero,
    teichmuller_coeff_zero, teichmuller_coeff_pos p _ 1 one_pos, mul_zero, add_zero]
  ring

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

/-- **Units of Witt vectors in characteristic `p`.** Over a ring `R` of characteristic `p`, a
Witt vector is a unit exactly when its zeroth Witt coordinate is a unit of `R`. -/
theorem isUnit_iff_isUnit_coeff_zero {x : 𝕎 R} : IsUnit x ↔ IsUnit (x.coeff 0) :=
  ⟨fun h ↦ by simpa using h.map (constantCoeff (p := p) (R := R)),
    fun ⟨_, ha⟩ ↦ (mkUnit ha.symm).isUnit⟩

variable [PerfectRing R p]

/-- Over a perfect ring of characteristic `p`, every Witt vector is `[x₀] + p u`. -/
theorem exists_eq_teichmuller_add_p_mul (x : 𝕎 R) :
    ∃ u : 𝕎 R, x = teichmuller p (x.coeff 0) + p * u := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp <|
    (mem_span_p_iff_coeff_zero_eq_zero (x - teichmuller p (x.coeff 0))).mpr <| by
      rw [← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply,
        teichmuller_coeff_zero, sub_self]
  exact ⟨u, by rw [← hu, add_sub_cancel]⟩

end CharP

end WittVector
