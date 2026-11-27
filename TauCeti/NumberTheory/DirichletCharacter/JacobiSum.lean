/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum

/-!
# Jacobi sums of Dirichlet characters

For Dirichlet characters `χ` and `ψ` modulo `N`, Mathlib's `jacobiSum χ ψ` is
`J(χ, ψ) = ∑_r χ(r) ψ(1 - r)`. Over a finite field, Mathlib relates it to Gauss sums by
`J(χ, ψ) g(χ ψ) = g(χ) g(ψ)` when `χ ψ ≠ 1`. This file proves the same relation modulo any `N`
when `χ ψ` is primitive.

The product of the Gauss sums is `∑_t e(t) ∑_x χ(x) ψ(t - x)`. At a unit `t`, the substitution
`x = t r` turns the inner sum into `(χ ψ)(t) J(χ, ψ)`. At a nonunit `t`, the inner sum vanishes:
a unit `u ≡ 1` modulo `N / gcd(t, N)` fixes `t`, so the substitution `x = u x'` multiplies the
inner sum by `(χ ψ)(u)`, and primitivity gives such a `u` with `(χ ψ)(u) ≠ 1`. The relation
needs the primitivity: for `N = 9`, a primitive `χ` of order `6` and `ψ = χ⁻¹`, the sum
`J(χ, χ⁻¹)` is `0`, but `g(χ) g(χ⁻¹) = -9`.

## Main results

* `jacobiSum_one_right`: on a finite commutative ring, `J(χ, 1) = ∑_{1 - r unit} χ(r)`.
* `DirichletCharacter.sum_mul_apply_sub_eq_zero_of_isPrimitive`: if `χ ψ` is primitive, then
  `∑_x χ(x) ψ(t - x) = 0` at every nonunit `t`.
* `DirichletCharacter.gaussSum_mul_jacobiSum_of_isPrimitive`: if `χ ψ` is primitive, then
  `g(χ ψ) J(χ, ψ) = g(χ) g(ψ)` for every additive character.
* `DirichletCharacter.jacobiSum_eq_gaussSum_div_of_isPrimitive`: if `χ ψ` is primitive, then
  `J(χ, ψ) = g(χ) g(ψ) / g(χ ψ)` for a primitive additive character.
-/

public section

open Finset

/-- The Jacobi sum of `χ` and the trivial character is the sum of `χ` over the `r` with `1 - r` a
unit. -/
theorem jacobiSum_one_right {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']
    [DecidablePred (IsUnit : R → Prop)] (χ : MulChar R R') :
    jacobiSum χ 1 = ∑ r with IsUnit (1 - r), χ r := by
  rw [jacobiSum, sum_filter]
  refine sum_congr rfl fun r _ ↦ ?_
  by_cases hr : IsUnit (1 - r)
  · simp [MulChar.one_apply hr, hr]
  · simp [MulChar.map_nonunit _ hr, hr]

namespace DirichletCharacter

variable {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]
  {χ ψ : DirichletCharacter R N}

/-- If `χ ψ` is primitive, then the convolution `∑_x χ(x) ψ(t - x)` vanishes at every nonunit
`t`. -/
theorem sum_mul_apply_sub_eq_zero_of_isPrimitive (h : (χ * ψ).IsPrimitive) {t : ZMod N}
    (ht : ¬IsUnit t) : ∑ x, χ x * ψ (t - x) = 0 := by
  -- The units `u ≡ 1` modulo `N / g`, with `g = gcd(t, N)`, fix `t`.
  set g := t.val.gcd N
  have hg : g ∣ N := Nat.gcd_dvd_right _ _
  have hd : N / g ∣ N := Nat.div_dvd_of_dvd hg
  have hg1 : 1 < g := by
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (NeZero.pos N)
    have hg1 : g ≠ 1 := fun h1 ↦ ht <| by
      rw [← ZMod.natCast_zmod_val t]
      exact (ZMod.isUnit_iff_coprime _ _).mpr h1
    omega
  -- Since `χ ψ` is primitive, it does not factor through `N / g < N`.
  have hnf : ¬(χ * ψ).FactorsThrough (N / g) := fun hf ↦
    ((Nat.sInf_le hf).trans_lt (Nat.div_lt_self (NeZero.pos N) hg1)).ne h
  obtain ⟨u, hu, hχψu⟩ : ∃ u ∈ (ZMod.unitsMap hd).ker, (χ * ψ) (u : ZMod N) ≠ 1 := by
    by_contra! hall
    refine hnf ((factorsThrough_iff_ker_unitsMap hd).mpr fun u hu ↦ ?_)
    rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
    exact hall u hu
  have hut : (u : ZMod N) * t = t := by
    rw [MonoidHom.mem_ker, ← Units.val_inj, ZMod.unitsMap_val, Units.val_one] at hu
    have hdvd : N / g ∣ ((u : ZMod N) - 1).val := by
      rw [← ZMod.natCast_eq_zero_iff, ← ZMod.cast_eq_val, ZMod.cast_sub hd, hu, ZMod.cast_one hd,
        sub_self]
    rw [← sub_eq_zero, ← sub_one_mul, ← ZMod.natCast_zmod_val ((u : ZMod N) - 1),
      ← ZMod.natCast_zmod_val t, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact (dvd_of_eq (Nat.div_mul_cancel hg).symm).trans
      (Nat.mul_dvd_mul hdvd (Nat.gcd_dvd_left _ _))
  -- The substitution `x = u x'` multiplies the sum by `(χ ψ)(u)`.
  have key : ∑ x, χ x * ψ (t - x) = (χ * ψ) (u : ZMod N) * ∑ x, χ x * ψ (t - x) := by
    rw [mul_sum]
    refine (Fintype.sum_bijective _ (Units.mulLeft_bijective u) _ _ fun x ↦ ?_).symm
    rw [MulChar.mul_apply]
    conv_rhs => rw [← hut, ← mul_sub, map_mul, map_mul]
    ring
  have hsub : (1 - (χ * ψ) (u : ZMod N)) * ∑ x, χ x * ψ (t - x) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hχψu.symm)

/-- **The Gauss–Jacobi relation modulo `N`**: if `χ ψ` is primitive, then
`g(χ ψ) J(χ, ψ) = g(χ) g(ψ)` for every additive character `e` of `ZMod N`. -/
theorem gaussSum_mul_jacobiSum_of_isPrimitive (h : (χ * ψ).IsPrimitive) (e : AddChar (ZMod N) R) :
    gaussSum (χ * ψ) e * jacobiSum χ ψ = gaussSum χ e * gaussSum ψ e := by
  rw [gaussSum_mul, gaussSum, sum_mul]
  refine sum_congr rfl fun t _ ↦ ?_
  by_cases ht : IsUnit t
  · -- At a unit `t`, the substitution `x = t r`.
    obtain ⟨v, rfl⟩ := ht
    rw [jacobiSum, mul_sum]
    refine Fintype.sum_bijective _ (Units.mulLeft_bijective v) _ _ fun r ↦ ?_
    rw [MulChar.mul_apply, ← mul_one_sub, map_mul, map_mul]
    ring
  · rw [MulChar.map_nonunit _ ht, zero_mul, zero_mul, ← sum_mul,
      sum_mul_apply_sub_eq_zero_of_isPrimitive h ht, zero_mul]

/-- **The Gauss–Jacobi relation modulo `N`**: if `χ ψ` is primitive, then
`J(χ, ψ) = g(χ) g(ψ) / g(χ ψ)` for every primitive additive character `e` of `ZMod N`. -/
theorem jacobiSum_eq_gaussSum_div_of_isPrimitive {F : Type*} [Field F]
    {χ ψ : DirichletCharacter F N} (h : (χ * ψ).IsPrimitive) {e : AddChar (ZMod N) F}
    (he : e.IsPrimitive) :
    jacobiSum χ ψ = gaussSum χ e * gaussSum ψ e / gaussSum (χ * ψ) e := by
  rw [eq_div_iff (gaussSum_ne_zero_of_isPrimitive h he), mul_comm]
  exact gaussSum_mul_jacobiSum_of_isPrimitive h e

end DirichletCharacter
