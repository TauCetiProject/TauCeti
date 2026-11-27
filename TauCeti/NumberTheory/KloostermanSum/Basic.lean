/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum
public import TauCeti.NumberTheory.HyperKloosterman.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Kloosterman sums over a finite commutative ring

For a finite commutative ring `R`, a multiplicative character `χ : MulChar R R'`, an additive
character `ψ : AddChar R R'` and `a, b ∈ R`, the Kloosterman sum is

  `K(χ, ψ; a, b) = ∑_{x ∈ Rˣ} χ(x) ψ(a x + b x⁻¹)`.

The sum runs over the units of `R`. On a finite field it is the Kloosterman sum of Weil's bound
`|K(χ; a, b)| ≤ 2 √q`, and on `ZMod c` with `ZMod.stdAddChar` it is the sum `S_χ(a, b; c)`.

This file proves the elementary identities. With `b = 0` the sum is the Gauss sum of `χ` and
`x ↦ ψ(a x)`, since `χ` vanishes off the units. The substitution `x ↦ x⁻¹` exchanges `a` and `b`
and inverts `χ`, and the substitution `x ↦ u⁻¹ x` for a unit `u` gives
`K(χ; u a, u⁻¹ b) = χ⁻¹(u) K(χ; a, b)`. Over `ℂ`, conjugation inverts both characters, so the sum
with `χ = 1` is real, and the sum with a quadratic `χ` is real or purely imaginary according as
`χ(-1) = 1` or `χ(-1) = -1`. For units `a, b` the sum with `χ = 1` is the rank-two
hyper-Kloosterman sum `TauCeti.hyperKloosterman R 2 ψ (a b)`, through the bijection
`x ↦ (a x, b x⁻¹)` from `Rˣ` onto the pairs of units with product `a b`.

## Main definitions

* `TauCeti.kloostermanSum χ ψ a b`: the Kloosterman sum `∑_{x ∈ Rˣ} χ(x) ψ(a x + b x⁻¹)`.

## Main results

* `TauCeti.kloostermanSum_zero_right`: `K(χ, ψ; a, 0)` is the Gauss sum of `χ` and `ψ.mulShift a`.
* `TauCeti.kloostermanSum_units_zero`, `TauCeti.kloostermanSum_zero_units`: for a unit `u`,
  `K(χ; u, 0) = χ⁻¹(u) g(χ, ψ)` and `K(χ; 0, u) = χ(u) g(χ⁻¹, ψ)`.
* `TauCeti.kloostermanSum_one_zero_right`: over a finite field, with values in a domain,
  `K(1; a, 0) = -1` for `a ≠ 0` and `ψ ≠ 1`.
* `TauCeti.kloostermanSum_inv`: `K(χ⁻¹; b, a) = K(χ; a, b)`.
* `TauCeti.kloostermanSum_mul_mul_inv`: `K(χ; u a, u⁻¹ b) = χ⁻¹(u) K(χ; a, b)` for a unit `u`.
* `TauCeti.kloostermanSum_units`: `K(χ; u, b) = χ⁻¹(u) K(χ; 1, u b)` for a unit `u`.
* `TauCeti.kloostermanSum_neg_neg`, `TauCeti.kloostermanSum_inv_addChar`:
  `K(χ; -a, -b) = χ(-1) K(χ; a, b)`, and `ψ⁻¹` in place of `ψ` replaces `(a, b)` by `(-a, -b)`.
* `TauCeti.star_kloostermanSum_eq`, `TauCeti.kloostermanSum_inv_eq_conj`: over `ℂ`,
  `conj K(χ, ψ; a, b) = K(χ⁻¹, ψ⁻¹; a, b)` and `K(χ⁻¹, ψ; a, b) = χ(-1) conj K(χ, ψ; a, b)`, as
  Mathlib's `star_gaussSum_eq` and `gaussSum_inv_eq_conj` for Gauss sums.
* `TauCeti.star_kloostermanSum_one`, `TauCeti.star_kloostermanSum_of_isQuadratic`: `K(1; a, b)`
  is real, and `conj K(χ; a, b) = χ(-1) K(χ; a, b)` for a quadratic `χ`.
* `TauCeti.kloostermanSum_one_eq_hyperKloosterman`: for units `a, b`, `K(1, ψ; a, b)` is the
  rank-two hyper-Kloosterman sum at `a b`.
* `TauCeti.kloostermanSum_one_zero_zero`, `TauCeti.kloostermanSum_zero_zero_eq_zero`,
  `TauCeti.kloostermanSum_one_addChar_one`, `TauCeti.kloostermanSum_addChar_one_eq_zero`: the
  degenerate parameters. `K(χ; 0, 0)` and `K(χ, 1; a, b)` are `#Rˣ` for `χ = 1`, and `0` otherwise
  when the values lie in a domain.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §11.7.
* R. Lidl and H. Niederreiter, *Finite Fields*, 2nd ed., Encyclopedia of Mathematics and its
  Applications 20, Cambridge University Press, 1997, Chapter 5, §5.5.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [CommRing R] [Fintype R]

section Semiring

variable {R' : Type*} [CommSemiring R']

/-- The Kloosterman sum `K(χ, ψ; a, b) = ∑_{x ∈ Rˣ} χ(x) ψ(a x + b x⁻¹)` over the units of a finite
commutative ring `R`. -/
noncomputable def kloostermanSum (χ : MulChar R R') (ψ : AddChar R R') (a b : R) : R' := by
  classical
  exact ∑ x : Rˣ, χ x * ψ (a * x + b * ↑x⁻¹)

/-- The defining sum of `kloostermanSum`, for any `Fintype` instance on `Rˣ`. -/
theorem kloostermanSum_def [Fintype Rˣ] (χ : MulChar R R') (ψ : AddChar R R') (a b : R) :
    kloostermanSum χ ψ a b = ∑ x : Rˣ, χ x * ψ (a * x + b * ↑x⁻¹) := by
  unfold kloostermanSum
  congr!

/-- **Symmetry.** The substitution `x ↦ x⁻¹` gives `K(χ⁻¹; b, a) = K(χ; a, b)`. -/
theorem kloostermanSum_inv (χ : MulChar R R') (ψ : AddChar R R') (a b : R) :
    kloostermanSum χ⁻¹ ψ b a = kloostermanSum χ ψ a b := by
  classical
  rw [kloostermanSum_def, kloostermanSum_def]
  refine Fintype.sum_equiv (Equiv.inv Rˣ) _ _ fun x ↦ ?_
  rw [Equiv.inv_apply, MulChar.inv_apply_coe, inv_inv, add_comm]

/-- **Scaling.** For a unit `u`, the substitution `x ↦ u⁻¹ x` gives
`K(χ; u a, u⁻¹ b) = χ⁻¹(u) K(χ; a, b)`. -/
theorem kloostermanSum_mul_mul_inv (χ : MulChar R R') (ψ : AddChar R R') (u : Rˣ) (a b : R) :
    kloostermanSum χ ψ (u * a) (↑u⁻¹ * b) = χ⁻¹ u * kloostermanSum χ ψ a b := by
  classical
  rw [kloostermanSum_def, kloostermanSum_def, mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun x ↦ ?_
  have hχ : χ⁻¹ u * χ ↑(u * x) = χ x := by
    rw [MulChar.inv_apply_coe, ← map_mul, ← Units.val_mul, inv_mul_cancel_left]
  have harg : a * ↑(u * x) + b * ↑(u * x)⁻¹ = u * a * x + ↑u⁻¹ * b * ↑x⁻¹ := by
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    ring
  rw [Equiv.coe_mulLeft, ← mul_assoc, hχ, harg]

/-- For a unit `u`, `K(χ; u, b) = χ⁻¹(u) K(χ; 1, u b)`: the sum depends on `u b` and on `χ(u)`. -/
theorem kloostermanSum_units (χ : MulChar R R') (ψ : AddChar R R') (u : Rˣ) (b : R) :
    kloostermanSum χ ψ u b = χ⁻¹ u * kloostermanSum χ ψ 1 (u * b) := by
  rw [← kloostermanSum_mul_mul_inv, mul_one, ← mul_assoc, Units.inv_mul, one_mul]

/-- The substitution `x ↦ -x` gives `K(χ; -a, -b) = χ(-1) K(χ; a, b)`. -/
theorem kloostermanSum_neg_neg (χ : MulChar R R') (ψ : AddChar R R') (a b : R) :
    kloostermanSum χ ψ (-a) (-b) = χ (-1) * kloostermanSum χ ψ a b := by
  classical
  rw [kloostermanSum_def, kloostermanSum_def, mul_sum]
  have h1 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  refine Fintype.sum_equiv (Equiv.neg Rˣ) _ _ fun x ↦ ?_
  have hx : χ (-(x : R)) = χ (-1) * χ x := by rw [← map_mul, neg_one_mul]
  have harg : a * -(x : R) + b * -↑x⁻¹ = -a * x + -b * ↑x⁻¹ := by ring
  rw [Equiv.neg_apply, Units.val_neg, inv_neg, Units.val_neg, harg, hx, ← mul_assoc, ← mul_assoc,
    h1, one_mul]

/-- Replacing `ψ` by `ψ⁻¹` replaces `(a, b)` by `(-a, -b)`. -/
theorem kloostermanSum_inv_addChar (χ : MulChar R R') (ψ : AddChar R R') (a b : R) :
    kloostermanSum χ ψ⁻¹ a b = kloostermanSum χ ψ (-a) (-b) := by
  classical
  simp only [kloostermanSum_def, AddChar.inv_apply, neg_add, neg_mul]

/-- For units `a, b`, the Kloosterman sum with the trivial multiplicative character is the
rank-two hyper-Kloosterman sum at `a b`: `x ↦ (a x, b x⁻¹)` maps `Rˣ` onto the pairs of units
with product `a b`. -/
theorem kloostermanSum_one_eq_hyperKloosterman (ψ : AddChar R R') (a b : Rˣ) :
    kloostermanSum 1 ψ a b = hyperKloosterman R 2 ψ (a * b) := by
  classical
  rw [kloostermanSum_def, ← sum_add_mul_prod_inv_eq_hyperKloosterman]
  -- Identify a tuple `y` of length one with the unit `a⁻¹ y₀`.
  refine (Fintype.sum_equiv ((Equiv.funUnique (Fin 1) Rˣ).trans (Equiv.mulLeft a⁻¹)) _ _
    fun y ↦ ?_).symm
  simp only [Equiv.trans_apply, Equiv.funUnique_apply, Equiv.coe_mulLeft, Fin.default_eq_zero,
    Fin.sum_univ_one, Fin.prod_univ_one, MulChar.one_apply_coe, one_mul]
  -- In `Rˣ`: `a (a⁻¹ y₀) = y₀` and `b (a⁻¹ y₀)⁻¹ = (a b) y₀⁻¹`.
  have h1 : a * (a⁻¹ * y 0) = y 0 := mul_inv_cancel_left a (y 0)
  have h2 : b * (a⁻¹ * y 0)⁻¹ = a * b * (y 0)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    ac_rfl
  rw [← Units.val_mul, ← Units.val_mul, h1, h2]

/-- `K(1; 0, 0) = #Rˣ`. -/
@[simp]
theorem kloostermanSum_one_zero_zero (ψ : AddChar R R') :
    kloostermanSum (1 : MulChar R R') ψ 0 0 = Nat.card Rˣ := by
  classical
  simp [kloostermanSum_def, Nat.card_eq_fintype_card]

/-- With the trivial additive character, `K(1, 1; a, b) = #Rˣ`. -/
@[simp]
theorem kloostermanSum_one_addChar_one (a b : R) :
    kloostermanSum (1 : MulChar R R') (1 : AddChar R R') a b = Nat.card Rˣ := by
  classical
  simp [kloostermanSum_def, Nat.card_eq_fintype_card]

end Semiring

section Ring

variable {R' : Type*} [CommRing R']

/-- With `b = 0` the Kloosterman sum is the Gauss sum of `χ` and `x ↦ ψ(a x)`: the terms off the
units vanish because `χ` does. -/
theorem kloostermanSum_zero_right (χ : MulChar R R') (ψ : AddChar R R') (a : R) :
    kloostermanSum χ ψ a 0 = gaussSum χ (ψ.mulShift a) := by
  classical
  rw [kloostermanSum_def, gaussSum, MulChar.sum_mul_eq_sum_units]
  simp [AddChar.mulShift_apply]

/-- For a unit `u`, `K(χ; u, 0) = χ⁻¹(u) g(χ, ψ)`. -/
theorem kloostermanSum_units_zero (χ : MulChar R R') (ψ : AddChar R R') (u : Rˣ) :
    kloostermanSum χ ψ u 0 = χ⁻¹ u * gaussSum χ ψ := by
  rw [kloostermanSum_zero_right, gaussSum_mulShift_eq]

/-- For a unit `u`, `K(χ; 0, u) = χ(u) g(χ⁻¹, ψ)`. -/
theorem kloostermanSum_zero_units (χ : MulChar R R') (ψ : AddChar R R') (u : Rˣ) :
    kloostermanSum χ ψ 0 u = χ u * gaussSum χ⁻¹ ψ := by
  rw [← kloostermanSum_inv, ← inv_inv χ, kloostermanSum_units_zero, inv_inv, inv_inv]

/-- For `χ ≠ 1` with values in a domain, `K(χ; 0, 0) = 0`. -/
theorem kloostermanSum_zero_zero_eq_zero [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1)
    (ψ : AddChar R R') : kloostermanSum χ ψ 0 0 = 0 := by
  classical
  have h := MulChar.sum_mul_eq_sum_units χ 1
  simp only [Pi.one_apply, mul_one, MulChar.sum_eq_zero_of_ne_one hχ] at h
  simp [kloostermanSum_def, ← h]

/-- For `χ ≠ 1` with values in a domain, the Kloosterman sum with the trivial additive character
vanishes. -/
theorem kloostermanSum_addChar_one_eq_zero [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1)
    (a b : R) : kloostermanSum χ (1 : AddChar R R') a b = 0 := by
  rw [← kloostermanSum_zero_zero_eq_zero hχ (1 : AddChar R R')]
  classical
  simp [kloostermanSum_def]

/-- Over a finite field, with values in a domain, `K(1; a, 0) = -1` for `a ≠ 0` and a nontrivial
`ψ`. -/
theorem kloostermanSum_one_zero_right {F : Type*} [Field F] [Fintype F] [IsDomain R']
    {ψ : AddChar F R'} (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) :
    kloostermanSum (1 : MulChar F R') ψ a 0 = -1 := by
  rw [kloostermanSum_zero_right, gaussSum_one_left (AddChar.IsPrimitive.of_ne_one hψ ha)]

end Ring

section Complex

/-- **Conjugation.** Over `ℂ`, conjugation inverts both characters:
`conj K(χ, ψ; a, b) = K(χ⁻¹, ψ⁻¹; a, b)`. -/
theorem star_kloostermanSum_eq (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (a b : R) :
    star (kloostermanSum χ ψ a b) = kloostermanSum χ⁻¹ ψ⁻¹ a b := by
  classical
  simp only [kloostermanSum_def, star_sum, star_mul', MulChar.star_apply', AddChar.inv_apply,
    AddChar.map_neg_eq_conj, RCLike.star_def]

/-- Over `ℂ`, `K(χ⁻¹, ψ; a, b) = χ(-1) conj K(χ, ψ; a, b)`. -/
theorem kloostermanSum_inv_eq_conj (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (a b : R) :
    kloostermanSum χ⁻¹ ψ a b = χ (-1) * starRingEnd ℂ (kloostermanSum χ ψ a b) := by
  rw [starRingEnd_apply, star_kloostermanSum_eq, kloostermanSum_inv_addChar,
    kloostermanSum_neg_neg, ← mul_assoc, ← MulChar.mul_apply, mul_inv_cancel,
    MulChar.one_apply isUnit_neg_one, one_mul]

/-- Over `ℂ`, the Kloosterman sum with the trivial multiplicative character is real. -/
theorem star_kloostermanSum_one (ψ : AddChar R ℂ) (a b : R) :
    star (kloostermanSum 1 ψ a b) = kloostermanSum 1 ψ a b := by
  have h := kloostermanSum_inv_eq_conj (1 : MulChar R ℂ) ψ a b
  rw [inv_one, MulChar.one_apply isUnit_neg_one, one_mul, starRingEnd_apply] at h
  exact h.symm

/-- Over `ℂ`, for a quadratic `χ`, `conj K(χ; a, b) = χ(-1) K(χ; a, b)`: the sum is real if
`χ(-1) = 1` and purely imaginary if `χ(-1) = -1`. -/
theorem star_kloostermanSum_of_isQuadratic {χ : MulChar R ℂ} (hχ : χ.IsQuadratic)
    (ψ : AddChar R ℂ) (a b : R) :
    star (kloostermanSum χ ψ a b) = χ (-1) * kloostermanSum χ ψ a b := by
  have h := kloostermanSum_inv_eq_conj χ ψ a b
  rw [hχ.inv, starRingEnd_apply] at h
  calc star (kloostermanSum χ ψ a b)
      = χ (-1) * (χ (-1) * star (kloostermanSum χ ψ a b)) := by
        rw [← mul_assoc, χ.apply_neg_one_mul_self, one_mul]
    _ = χ (-1) * kloostermanSum χ ψ a b := by rw [← h]

end Complex

end TauCeti
