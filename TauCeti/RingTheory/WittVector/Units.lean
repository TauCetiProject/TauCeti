/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import TauCeti.RingTheory.DeltaRing.Basic

/-!
# The Teichmüller splitting and units of Witt vectors

A Teichmüller representative `[a]` and a Verschiebung `V x` have disjoint supports, so `[a] + V x`
has Witt coordinates `a, x₀, x₁, …`, and every Witt vector is `[x₀] + V u`
(`WittVector.exists_eq_teichmuller_add_verschiebung`). Expanding a product of two such sums with
the projection formula gives the first Witt coordinate of a product,
`(x y)₁ = x₀ ^ p y₁ + y₀ ^ p x₁ + p x₁ y₁` (`WittVector.mul_coeff_one`), which in characteristic `p`
is `x₀ ^ p y₁ + y₀ ^ p x₁` (`WittVector.mul_coeff_one_charP`). The first Witt coordinate of a sum,
`(x + y)₁ = x₁ + y₁ + C_p(x₀, y₀)` with `C_p = TauCeti.DeltaRing.addCorrection p`
(`WittVector.add_coeff_one`), is computed from Mathlib's universal Witt addition polynomial
`WittVector.wittAdd p 1`, cancelling `p` in the `p`-torsion-free ring `ℤ[X₀, X₁, Y₀, Y₁]` before
evaluating in `R`.

Over a ring of characteristic `p`, `x` is a unit exactly when its zeroth Witt coordinate `x₀` is a
unit of `R` (`WittVector.isUnit_iff_isUnit_coeff_zero`); the inverse is Mathlib's
`WittVector.mkUnit`. Mathlib states the criterion only over a field
(`WittVector.isUnit_of_coeff_zero_ne_zero`). In characteristic `p` the Verschiebung of `F u` is
`p u`, so a sum `[a] + p u` has Witt coordinates `a` in degree `0` and `u_n ^ p` in degree `n + 1`
(`WittVector.teichmuller_add_p_mul_coeff_succ`).

## Main results

* `WittVector.teichmuller_add_verschiebung_coeff_zero`,
  `WittVector.teichmuller_add_verschiebung_coeff_succ`: the Witt coordinates of `[a] + V x`.
* `WittVector.exists_eq_teichmuller_add_verschiebung`: every Witt vector is `[x₀] + V u`.
* `WittVector.sub_coeff_zero`: the zeroth Witt coordinate of `x - y` is `x₀ - y₀`.
* `WittVector.ghostComponent_one`: the first ghost component is `x₀ ^ p + p * x₁`.
* `WittVector.coeff_frobenius_zero`, `WittVector.mul_coeff_one`: the zeroth Witt coordinate of
  `F x` and the first Witt coordinate of `x y`.
* `WittVector.wittAdd_one`, `WittVector.add_coeff_one`: the first Witt coordinate of `x + y`.
* `WittVector.mul_coeff_one_charP`: in characteristic `p`, `(x y)₁ = x₀ ^ p y₁ + y₀ ^ p x₁`.
* `WittVector.teichmuller_add_p_mul_coeff_zero`, `WittVector.teichmuller_add_p_mul_coeff_succ`:
  the Witt coordinates of `[a] + p u` in characteristic `p`.
* `WittVector.isUnit_iff_isUnit_coeff_zero`: in characteristic `p`, `x` is a unit iff `x₀` is.

## References

* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Example 6.1.6.
-/

public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

local notation "𝕎" => WittVector p

/-- The zeroth Witt coordinate of `x - y` is `x₀ - y₀`. -/
theorem sub_coeff_zero (x y : 𝕎 R) : (x - y).coeff 0 = x.coeff 0 - y.coeff 0 :=
  map_sub (constantCoeff (p := p) (R := R)) x y

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
  rw [Nat.lt_one_iff.mp hi, sub_coeff_zero, teichmuller_coeff_zero, sub_self]

/-- The first ghost component of a Witt vector is `x₀ ^ p + p * x₁`. -/
theorem ghostComponent_one (x : 𝕎 R) :
    ghostComponent 1 x = x.coeff 0 ^ p + p * x.coeff 1 := by
  simp [ghostComponent_apply, add_comm]

/-- The zeroth Witt coordinate of `F x` is `x₀ ^ p + p x₁`, the first ghost component of `x`. -/
theorem coeff_frobenius_zero (x : 𝕎 R) :
    (frobenius x).coeff 0 = x.coeff 0 ^ p + p * x.coeff 1 := by
  have h := ghostComponent_frobenius 0 x
  rw [ghostComponent_apply, ghostComponent_apply, wittPolynomial_zero, wittPolynomial_one] at h
  simp only [MvPolynomial.aeval_X, map_add, map_mul, map_pow, map_natCast] at h
  rw [h, add_comm]

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

open MvPolynomial in
/-- The Witt polynomial computing the first coordinate of a sum:
`(x + y)₁ = x₁ + y₁ + C_p(x₀, y₀)`. -/
theorem wittAdd_one :
    wittAdd p 1 =
      X (0, 1) + X (1, 1) + TauCeti.DeltaRing.addCorrection p (X (0, 0)) (X (1, 0)) := by
  have h := wittStructureInt_prop p (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) 1
  simp only [wittPolynomial_one, map_add, map_mul, map_pow, bind₁_X_right, algHom_C,
    rename_X, ← wittAdd.eq_1] at h
  have hc := TauCeti.DeltaRing.natCast_mul_addCorrection (p := p)
    (X (0, 0) : MvPolynomial (Fin 2 × ℕ) ℤ) (X (1, 0))
  rw [wittAdd_zero] at h
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : MvPolynomial _ ℤ) ≠ 0)
  simp only [eq_intCast, Int.cast_natCast] at h
  linear_combination h - hc

/-- The first coordinate of a sum of Witt vectors is `x₁ + y₁ + C_p(x₀, y₀)`, where
`C_p = TauCeti.DeltaRing.addCorrection p` is the polynomial `(X ^ p + Y ^ p - (X + Y) ^ p) / p`. -/
theorem add_coeff_one (x y : 𝕎 R) :
    (x + y).coeff 1 =
      x.coeff 1 + y.coeff 1 + TauCeti.DeltaRing.addCorrection p (x.coeff 0) (y.coeff 0) := by
  simp [add_coeff, wittAdd_one, peval, TauCeti.DeltaRing.addCorrection_def]

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

/-- In characteristic `p`, the first Witt coordinate of a product is
`(x y)₁ = x₀ ^ p y₁ + y₀ ^ p x₁`. -/
theorem mul_coeff_one_charP (x y : 𝕎 R) :
    (x * y).coeff 1 = x.coeff 0 ^ p * y.coeff 1 + y.coeff 0 ^ p * x.coeff 1 := by
  simp [mul_coeff_one]

/-- **Units of Witt vectors in characteristic `p`.** Over a ring `R` of characteristic `p`, a
Witt vector is a unit exactly when its zeroth Witt coordinate is a unit of `R`. -/
theorem isUnit_iff_isUnit_coeff_zero {x : 𝕎 R} : IsUnit x ↔ IsUnit (x.coeff 0) :=
  ⟨fun h ↦ by simpa using h.map (constantCoeff (p := p) (R := R)),
    fun ⟨_, ha⟩ ↦ (mkUnit ha.symm).isUnit⟩

end CharP

end WittVector
