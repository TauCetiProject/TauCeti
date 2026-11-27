/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.Expand
import TauCeti.RingTheory.AlgebraTower

/-!
# Polynomials and prime-degree subextensions in purely inseparable extensions

Over a purely inseparable extension `L / K` in exponential characteristic `p`, taking a common
`p`-power exponent across the coefficients of any `Q : L[X]` shows that some `Q ^ p ^ n` is mapped
from `K[X]` (`Polynomial.exists_map_eq_pow_expChar_pow_of_isPurelyInseparable`).

Inside any nontrivial purely inseparable field extension `M / K` in exponential characteristic `p`
(finite or infinite), taking an element `x ∉ K` with minimal polynomial `X ^ p ^ (d + 1) - y`
produces the element `z = x ^ p ^ d ∉ K` satisfying `z ^ p = y ∈ K`, so `K⟮z⟯` is an intermediate
field of degree `p` over `K`
(`TauCeti.IsPurelyInseparable.exists_intermediateField_finrank_eq_expChar`).

## Main results

* `Polynomial.exists_map_eq_pow_expChar_pow_of_isPurelyInseparable`: some `p ^ n`-th power of any
  polynomial over `L` is mapped from `K[X]`.
* `TauCeti.IsPurelyInseparable.exists_intermediateField_finrank_eq_expChar`: every nontrivial
  purely inseparable field extension in exponential characteristic `p` contains an intermediate
  field of degree `p`.
* `TauCeti.IsPurelyInseparable.charP_of_prime_dvd_finrank`: if a prime `p` divides the degree of
  a finite purely inseparable field extension `M / K`, then `K` has characteristic `p`.
* `TauCeti.IsPurelyInseparable.of_isIntegrallyClosedIn`: in a purely inseparable extension `F' / F`
  over a field `k` integrally closed in `F`, any algebraic enlargement `k'' / k'` inside `F'` (with
  `k' / k` algebraic) is purely inseparable over `k'`.
-/

public section

namespace Polynomial

/-- Over a purely inseparable extension `L / K` in exponential characteristic `p`, some `p ^ n`-th
power of any polynomial `Q : L[X]` is mapped from a polynomial over `K`. -/
theorem exists_map_eq_pow_expChar_pow_of_isPurelyInseparable {L : Type*} [CommRing L] [IsDomain L]
    (Q : L[X]) (K : Type*) [Field K] [Algebra K L] [IsPurelyInseparable K L]
    (p : ℕ) [ExpChar K p] :
    ∃ (n : ℕ) (R : K[X]), R.map (algebraMap K L) = Q ^ p ^ n := by
  classical
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  choose m a ha using fun i ↦ IsPurelyInseparable.pow_mem K p (Q.coeff i)
  set n : ℕ := Q.support.sup m
  have hq : p ^ n ≠ 0 := (pow_pos (expChar_pos K p) n).ne'
  obtain ⟨Q₀, hQ₀⟩ : Q.map (iterateFrobenius L p n) ∈ (mapRingHom (algebraMap K L)).range :=
    (mem_map_range (algebraMap K L)).mpr fun i ↦ by
      rw [coeff_map, iterateFrobenius_def]
      by_cases hi : i ∈ Q.support
      · exact ⟨a i ^ p ^ (n - m i), by
          rw [map_pow, ha i, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (Finset.le_sup hi)]⟩
      · exact ⟨0, by rw [notMem_support_iff.mp hi, zero_pow hq, map_zero]⟩
  refine ⟨n, expand K (p ^ n) Q₀, ?_⟩
  rw [coe_mapRingHom] at hQ₀; rw [map_expand, hQ₀, ← map_expand, map_iterateFrobenius_expand]

end Polynomial

namespace TauCeti.IsPurelyInseparable

open IntermediateField Polynomial

/-- **Prime divisor of the degree determines the characteristic**: if `M / K` is a finite purely
inseparable field extension whose degree is divisible by a prime `p`, then `K` has characteristic
`p`. -/
theorem charP_of_prime_dvd_finrank {K M : Type*} [Field K] [Field M] [Algebra K M]
    [_root_.IsPurelyInseparable K M] [FiniteDimensional K M] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Module.finrank K M) : CharP K p := by
  obtain ⟨q, hq⟩ := ExpChar.exists K
  obtain ⟨r, hr⟩ := _root_.IsPurelyInseparable.finrank_eq_pow K M q
  rcases hq with _ | hq_prime
  · exact absurd (by simpa [hr] using hdvd) hp.not_dvd_one
  · obtain rfl : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp (hp.dvd_of_dvd_pow (hr ▸ hdvd))
    infer_instance

/-- **Prime-degree subextension of a nontrivial purely inseparable extension**: if `M / K` is a
purely inseparable extension in exponential characteristic `p` that is not trivial
(`¬ Function.Surjective (algebraMap K M)`), then `M` contains an intermediate field of degree `p`
over `K`. -/
theorem exists_intermediateField_finrank_eq_expChar {K M : Type*} [Field K] [Field M] [Algebra K M]
    (p : ℕ) [ExpChar K p] [_root_.IsPurelyInseparable K M]
    (h : ¬Function.Surjective (algebraMap K M)) :
    ∃ L : IntermediateField K M, Module.finrank K L = p := by
  rcases ‹ExpChar K p› with _ | hp
  · exact False.elim <| h fun x ↦
      let ⟨_, a, ha⟩ := _root_.IsPurelyInseparable.pow_mem K 1 x; ⟨a, by simpa using ha⟩
  · have : ExpChar K p := .prime hp
    have hne : (⊥ : IntermediateField K M) ≠ ⊤ := fun hbot ↦ h fun x ↦
      IntermediateField.mem_bot.1 (hbot ▸ IntermediateField.mem_top)
    obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.2 hne.symm)
    obtain ⟨m, y, hmin⟩ := _root_.IsPurelyInseparable.minpoly_eq_X_pow_sub_C K p x
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hx (IntermediateField.mem_bot.2
        ⟨y, Eq.symm <| sub_eq_zero.1 <| by simpa [hmin] using minpoly.aeval K x⟩)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    let z : M := x ^ p ^ d
    have hz_not_bot : z ∉ (⊥ : IntermediateField K M) := by
      rintro ⟨c, hc⟩
      have hle := minpoly.min K x (monic_X_pow_sub_C c (pow_ne_zero d hp.ne_zero))
        (by simp [z, ← hc])
      rw [hmin, degree_X_pow_sub_C (pow_pos hp.pos _) y, degree_X_pow_sub_C (pow_pos hp.pos _) c,
        Nat.cast_le] at hle
      exact (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self d)).not_ge hle
    have hzp : aeval z (X ^ p - C y : K[X]) = 0 := by
      simpa [z, hmin, pow_succ, pow_mul] using minpoly.aeval K x
    have hz_int : IsIntegral K z := Algebra.IsIntegral.isIntegral z
    have : FiniteDimensional K K⟮z⟯ := IntermediateField.adjoin.finiteDimensional hz_int
    have hz_le : Module.finrank K K⟮z⟯ ≤ p := by
      rw [IntermediateField.adjoin.finrank hz_int]
      exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K z hzp)
        (X_pow_sub_C_ne_zero hp.pos y)).trans (by rw [natDegree_X_pow_sub_C])
    have hz_ne1 : Module.finrank K K⟮z⟯ ≠ 1 := fun heq ↦
      hz_not_bot ((IntermediateField.finrank_eq_one_iff.1 heq).le (mem_adjoin_simple_self K z))
    have : _root_.IsPurelyInseparable K K⟮z⟯ := _root_.IsPurelyInseparable.tower_bot K K⟮z⟯ M
    obtain ⟨r, hr⟩ := _root_.IsPurelyInseparable.finrank_eq_pow K K⟮z⟯ p
    have hr0 : r ≠ 0 := fun h0 ↦ hz_ne1 (by rw [hr, h0, pow_zero])
    have hr1 : r = 1 := le_antisymm
      ((Nat.pow_le_pow_iff_right hp.one_lt).1 (by simpa [hr] using hz_le)) (Nat.pos_of_ne_zero hr0)
    exact ⟨K⟮z⟯, by rw [hr, hr1, pow_one]⟩

/-- In a purely inseparable field extension `F' / F` over a field `k` integrally closed in `F`,
any algebraic enlargement `k'' / k'` inside `F'` (with `k' / k` algebraic) is purely inseparable
over `k'`. -/
theorem of_isIntegrallyClosedIn {k k' F : Type*} (F' : Type*) {k'' : Type*}
    [Field k] [Field k'] [Field F] [Field F'] [Field k'']
    [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
    [Algebra k' k''] [Algebra k'' F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] [IsScalarTower k' k'' F']
    [Algebra.IsAlgebraic k k'] [_root_.IsPurelyInseparable F F']
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsAlgebraic k' k''] :
    _root_.IsPurelyInseparable k' k'' := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  have : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective p
  let _ := compAlgebra k k' k''; have := isScalarTower_compAlgebra_left k k' k''
  have := isScalarTower_compAlgebra_right k k' k'' F'
  have : Algebra.IsAlgebraic k k'' := Algebra.IsAlgebraic.trans k k' k''
  rw [isPurelyInseparable_iff_pow_mem k' p]
  intro c
  obtain ⟨n, y, hy⟩ := _root_.IsPurelyInseparable.pow_mem F p (algebraMap k'' F' c)
  obtain ⟨c₀, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 <|
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom k F F') (algebraMap F F').injective).1 <| by
      rw [IsScalarTower.toAlgHom_apply, hy, ← map_pow]
      exact (Algebra.IsIntegral.isIntegral (R := k) (c ^ p ^ n)).map
        (IsScalarTower.toAlgHom k k'' F')
  refine ⟨n, algebraMap k k' c₀, (algebraMap k'' F').injective ?_⟩
  simp only [map_pow, ← hy, ← IsScalarTower.algebraMap_apply k F F',
    ← IsScalarTower.algebraMap_apply k' k'' F', ← IsScalarTower.algebraMap_apply k k' F']

end TauCeti.IsPurelyInseparable
