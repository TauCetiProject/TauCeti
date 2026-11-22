/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.KummerPolynomial
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

In prime characteristic `p`, an element `x ∉ Set.range (algebraMap E k)` of a field extension
`k / E` whose `p`-th power lies in `Set.range (algebraMap E k)` has `X ^ p - C (x ^ p)` irreducible
over `E` (via Mathlib's `irreducible_X_pow_sub_C_of_prime` in
`Mathlib.FieldTheory.KummerPolynomial`), so `1, x, …, x ^ (p - 1)` are linearly independent
over `E`.

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
* `TauCeti.linearIndependent_pow_of_notMem_range`: in a field extension `k / E` where `k` has
  characteristic `p` for a prime `p`, an element `x ∉ Set.range (algebraMap E k)` with
  `x ^ p ∈ Set.range (algebraMap E k)` has `1, x, …, x ^ (p - 1)` linearly independent over `E`.
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

/-- In a field extension `k / E` where `k` has characteristic `p` for a prime `p`, an element
`x ∉ Set.range (algebraMap E k)` with `x ^ p ∈ Set.range (algebraMap E k)` has
`1, x, …, x ^ (p - 1)` linearly independent over `E`. -/
theorem linearIndependent_pow_of_notMem_range {p : ℕ} [Fact p.Prime] {E k : Type*}
    [Field E] [Field k] [Algebra E k] [ExpChar k p] {x : k}
    (hx : x ∉ Set.range (algebraMap E k)) (hxp : x ^ p ∈ Set.range (algebraMap E k)) :
    LinearIndependent E (fun n : Fin p ↦ x ^ (n : ℕ)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha_eq⟩ := hxp
  have ha : ∀ y : E, y ^ p ≠ a := by
    intro y hy
    have hy' : algebraMap E k y ^ p = x ^ p := by rw [← map_pow, hy, ha_eq]
    exact hx ⟨y, frobenius_inj k p hy'⟩
  let f : Polynomial E := Polynomial.X ^ p - Polynomial.C a
  have hirr : Irreducible f := irreducible_X_pow_sub_C_of_prime hp ha
  have hmonic : f.Monic := Polynomial.monic_X_pow_sub_C a hp.ne_zero
  have haeval : Polynomial.aeval x f = 0 := by
    simp only [f, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ha_eq, sub_self]
  have hmin : minpoly E x = f := (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm
  have hdeg : (minpoly E x).natDegree = p := by
    rw [hmin]
    exact Polynomial.natDegree_X_pow_sub_C a
  have hcomp : (fun n : Fin p ↦ x ^ (n : ℕ)) =
      (fun i : Fin (minpoly E x).natDegree ↦ x ^ (i : ℕ)) ∘ finCongr hdeg.symm :=
    funext fun n ↦ by simp only [Function.comp_apply, finCongr_apply_coe]
  rw [hcomp, linearIndependent_equiv]
  exact linearIndependent_pow (K := E) x

end TauCeti

end
