/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# The exponent of a finite purely inseparable extension: degree bound and denominators

Let `L / K` be a finite purely inseparable extension in exponential characteristic `p`. If
`[L : K] ≤ p ^ n`, then every `p ^ n`-th power of `L` lies in `K`, and so the exponent of `L / K`
is at most `n`. In particular a purely inseparable extension of degree `p ^ n` is cut out by
`p ^ n`-th powers.

Mathlib's `IsPurelyInseparable.hasExponent_of_finiteDimensional` shows that a finite purely
inseparable extension *has* an exponent, but keeps the bound inside the instance proof. This file
states the bound, in the pointwise form a caller holding a degree uses and as a bound on
`IsPurelyInseparable.exponent`.

When `K` is the fraction field of a ring `A`, the exponent also clears denominators: any `K`-basis
of `L` can be rescaled to one whose `p ^ n`-th powers all come from `A`. This needs only an
exponent, not finite dimensionality.

## Main results

* `TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow`: if `[L : K] ≤ p ^ n`, every `p ^ n`-th
  power of `L` lies in `K`.
* `TauCeti.IsPurelyInseparable.exponent_le_of_finrank_le_pow`: if `[L : K] ≤ p ^ n`, the exponent
  of `L / K` is at most `n`.
* `TauCeti.IsPurelyInseparable.exists_iterateFrobenius_unitsSMul_eq_algebraMap`: over the
  fraction field of a ring `A`, any basis rescales to one whose `p ^ n`-th powers lie in the image
  of `A`.
* `TauCeti.isPurelyInseparable_enlargement_of_finrank_eq_prime`: in a degree-`p` purely
  inseparable extension over an integrally closed base `k` in `F`, any algebraic enlargement
  `k'' / k'` inside `F'` is purely inseparable over `k'`.
-/

public section

namespace TauCeti.IsPurelyInseparable

open _root_.IsPurelyInseparable

/-- **Rescaling a basis so that its `p ^ n`-th powers come from the base ring.** Let `K` be the
fraction field of `A` and `L / K` a purely inseparable extension of exponent at most `n`. Every
`K`-basis `b` of `L` can be rescaled by units `w` of `K` so that the `p ^ n`-th power of each
rescaled vector is the image of an element `g j` of `A`. -/
theorem exists_iterateFrobenius_unitsSMul_eq_algebraMap (A K L : Type*) [CommRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [HasExponent K L] (p : ℕ)
    [ExpChar K p] {n : ℕ} (hn : exponent K L ≤ n) {ι : Type*} (b : Module.Basis ι K L) :
    ∃ (w : ι → Kˣ) (g : ι → A), ∀ j,
      iterateFrobenius K L p hn (b.unitsSMul w j) = algebraMap A K (g j) := by
  -- write the `p ^ n`-th power of `b j` as a fraction `a / s` and rescale `b j` by `s`
  choose x hx using fun j ↦
    IsLocalization.surj (nonZeroDivisors A) (iterateFrobenius K L p hn (b j))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (pow_pos (expChar_pos K p) n).ne'
  refine ⟨fun j ↦ (IsLocalization.map_units K (x j).2).unit, fun j ↦ (x j).2 ^ k * (x j).1,
    fun j ↦ ?_⟩
  simp only [Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, Algebra.smul_def,
    map_mul, map_pow, iterateFrobenius_algebraMap]
  rw [hk, ← hx j]
  ring

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
  [FiniteDimensional K L] (p : ℕ) [ExpChar K p]

/-- **A purely inseparable extension of degree at most `p ^ n` is cut out by `p ^ n`-th powers**:
every `a ^ p ^ n` lies in the base field. -/
theorem pow_mem_of_finrank_le_pow {n : ℕ} (h : Module.finrank K L ≤ p ^ n) (a : L) :
    a ^ p ^ n ∈ (algebraMap K L).range := by
  -- the minimal polynomial of `a` is `X ^ p ^ e - c` with `e` its exponent, of degree at most
  -- `[L : K] ≤ p ^ n`, so `e ≤ n`
  have he : elemExponent K a ≤ n := by
    rcases ‹ExpChar K p› with _ | ⟨hp⟩
    · simp [elemExponent_eq_zero_of_charZero]
    · exact (Nat.pow_le_pow_iff_right hp.one_lt).1 <|
        minpoly_natDegree_eq' K p a ▸ (minpoly.natDegree_le a).trans h
  rw [← Nat.add_sub_cancel' he, pow_add, pow_mul]
  exact pow_mem (elemExponent_def' K p a) _

/-- **The exponent of a purely inseparable extension of degree at most `p ^ n` is at most `n`.** -/
theorem exponent_le_of_finrank_le_pow {n : ℕ} (h : Module.finrank K L ≤ p ^ n) :
    exponent K L ≤ n :=
  not_lt.1 fun hn ↦ (exponent_min' p hn).elim fun a ha ↦ ha (pow_mem_of_finrank_le_pow K L p h a)

end TauCeti.IsPurelyInseparable

namespace TauCeti

/-- In a degree-`p` purely inseparable field extension `F' / F` over a field `k` integrally closed
in `F`, any algebraic enlargement `k'' / k'` inside `F'` (with `k' / k` algebraic) is purely
inseparable over `k'`. -/
theorem isPurelyInseparable_enlargement_of_finrank_eq_prime {k k' F F' : Type*}
    [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F']
    [Algebra k' F'] [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    {p : ℕ} (hp : p.Prime) [CharP k p] [Algebra.IsAlgebraic k k'] [IsPurelyInseparable F F']
    (hex : IsIntegrallyClosedIn k F) (hFF' : Module.finrank F F' = p) {k'' : Type*} [Field k'']
    [Algebra k' k''] [Algebra k'' F'] [IsScalarTower k' k'' F'] [Algebra.IsAlgebraic k' k''] :
    _root_.IsPurelyInseparable k' k'' := by
  have : FiniteDimensional F F' := Module.finite_of_finrank_pos (hFF' ▸ hp.pos)
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have : ExpChar F p := .prime hp
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have : ExpChar k' p := .prime hp
  let _ : Algebra k k'' := RingHom.toAlgebra ((algebraMap k' k'').comp (algebraMap k k'))
  have : IsScalarTower k k' k'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k k'' F' := .of_algebraMap_eq fun c ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  rw [isPurelyInseparable_iff_pow_mem k' p]
  intro c
  obtain ⟨y, hy⟩ := TauCeti.IsPurelyInseparable.pow_mem_of_finrank_le_pow F F' p (n := 1)
    (by simp [hFF']) (algebraMap k'' F' c)
  rw [pow_one] at hy
  have hy_int : IsIntegral k y := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom k F F') (algebraMap F F').injective).1 ?_
    rw [IsScalarTower.toAlgHom_apply, hy, ← map_pow]
    exact (Algebra.IsIntegral.isIntegral (R := k) (c ^ p)).map (IsScalarTower.toAlgHom k k'' F')
  obtain ⟨c₀, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hy_int
  refine ⟨1, algebraMap k k' c₀, (algebraMap k'' F').injective ?_⟩
  rw [pow_one, map_pow, ← hy, ← IsScalarTower.algebraMap_apply k F F',
    ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']

end TauCeti

end
