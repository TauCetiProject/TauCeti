/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.Basic
import Mathlib.Data.Nat.Factorization.Induction
import TauCeti.Data.ZMod.Divisibility

/-!
# The product formula for the explicit cyclotomic symbols

For `m ≥ 1`, the explicit local symbols of `ℚ(μ_m)/ℚ` are `cyclotomicSymbol m ℓ : ℚ_ℓˣ →* (ℤ/m)ˣ`
at a prime `ℓ`, sending `ℓ^k w` with `w ∈ ℤ_ℓˣ` to the class that is `w⁻¹` modulo the `ℓ`-primary
part of `m` and `ℓ^k` modulo its prime-to-`ℓ` part, and the sign `realCyclotomicSymbol m` at the
real place. This file proves their product formula: for `a ∈ ℚˣ`, the real symbol of `a` times the
symbols of `a` at the primes dividing `m · a` is `1` (`prod_cyclotomicSymbol`).

Both sides are multiplicative in `a` once the set of primes is fixed, so the formula is proved for
an arbitrary finite set `T` of primes containing those of `m` and of `a`
(`prod_cyclotomicSymbol_of_subset`), and there it reduces to the generators `-1` and the primes
`q ∈ T` of the group of rationals supported on `T`. A unit of `ℤ/m` is determined by its reductions
modulo the prime powers `p ^ k ∣ m` (`ZMod.units_eq_of_forall_unitsMap_eq_of_prime_pow_dvd`), and
modulo `p ^ k` each generator has at most two nontrivial factors, which cancel:

* at `a = -1`, the real symbol is `-1` and the symbol at `p` is `(-1)⁻¹ = -1`;
* at `a = p`, every factor is trivial;
* at a prime `a = q ≠ p`, the symbol at `p` is `q⁻¹` and the symbol at `q` is `q`.

## Main results

* `TauCeti.prod_cyclotomicSymbol`: the product formula.
* `TauCeti.prod_cyclotomicSymbol_of_subset`: the product formula over any finite set of primes
  containing the primes dividing `m · a`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Example 8.2, with the values above taken as the
  definition of the local factors.
-/

public section

namespace TauCeti

open ZMod

variable (m : ℕ) [NeZero m]

variable (T : Finset ℕ) (hT : ∀ ℓ ∈ T, ℓ.Prime)

/-- The real symbol times the symbols at the primes of `T`, as a character of `ℚˣ`. -/
private noncomputable def symbolProd : ℚˣ →* (ZMod m)ˣ :=
  (realCyclotomicSymbol m).comp (Units.map (algebraMap ℚ ℝ).toMonoidHom) *
    ∏ ℓ ∈ T.attach,
      haveI : Fact (ℓ : ℕ).Prime := ⟨hT ℓ ℓ.2⟩
      (cyclotomicSymbol m ℓ).comp (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom)

private theorem symbolProd_apply (b : ℚˣ) :
    symbolProd m T hT b = realCyclotomicSymbol m (Units.map (algebraMap ℚ ℝ).toMonoidHom b) *
      (∏ ℓ ∈ T.attach,
        haveI : Fact (ℓ : ℕ).Prime := ⟨hT ℓ ℓ.2⟩
        cyclotomicSymbol m ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom b)) := by
  simp only [symbolProd, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.comp_apply]

/-- At `-1`, modulo every `p ^ k ∣ m`, the real symbol and the symbol at `p` are both `-1`, and
the other symbols are trivial. -/
private theorem symbolProd_of_eq_neg_one (hm : m.primeFactors ⊆ T) {u : ℚˣ}
    (hu : (u : ℚ) = -1) : symbolProd m T hT u = 1 := by
  rw [symbolProd_apply]
  refine units_eq_of_forall_unitsMap_eq_of_prime_pow_dvd fun p k hp hk hpk ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  have hpT : p ∈ T :=
    hm (Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p hk).trans hpk, NeZero.ne m⟩)
  rw [map_one, map_mul, map_prod, realCyclotomicSymbol_of_neg m _ (by simp [hu]),
    Finset.prod_eq_single_of_mem ⟨p, hpT⟩ (Finset.mem_attach _ _)]
  · rw [unitsMap_cyclotomicSymbol_primePow_of_eq_unit m p hpk (w := -1) (by simp [hu]),
      RingHom.toMonoidHom_eq_coe, unitsMap_def, Units.map_neg_one, Units.map_neg_one,
      mul_inv_cancel]
  · rintro ⟨ℓ, hℓ⟩ - hne
    have : Fact ℓ.Prime := ⟨hT ℓ hℓ⟩
    exact unitsMap_cyclotomicSymbol_of_coprime_of_eq_unit m ℓ hpk
      (((Nat.coprime_primes (hT ℓ hℓ) hp).2 fun h ↦ hne (Subtype.ext h)).pow_right k) (w := -1)
      (by simp [hu])

/-- At a prime `q ∈ T`, modulo every `p ^ k ∣ m`, all symbols are trivial if `p = q`; otherwise
the symbol at `p` is `q⁻¹`, the symbol at `q` is `q`, and the others are trivial. -/
private theorem symbolProd_of_eq_prime (hm : m.primeFactors ⊆ T) {q : ℕ} (hq : q.Prime)
    (hqT : q ∈ T) {u : ℚˣ} (hu : (u : ℚ) = q) : symbolProd m T hT u = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  -- `q` as an `ℓ`-adic unit, for `ℓ ≠ q`
  let unit (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ q) : ℤ_[ℓ]ˣ :=
    (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
      ((Nat.coprime_primes Fact.out hq).2 hℓ))).unit
  have hunit (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ q) : (unit ℓ hℓ : ℤ_[ℓ]) = q :=
    IsUnit.unit_spec _
  rw [symbolProd_apply]
  refine units_eq_of_forall_unitsMap_eq_of_prime_pow_dvd fun p k hp hk hpk ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  have hpT : p ∈ T :=
    hm (Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p hk).trans hpk, NeZero.ne m⟩)
  have hcop {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ p) : Nat.Coprime ℓ (p ^ k) :=
    ((Nat.coprime_primes hℓ hp).2 hne).pow_right k
  rw [map_one, map_mul, map_prod, realCyclotomicSymbol_of_pos m _ (by simp [hu, hq.pos]),
    map_one, one_mul]
  rcases eq_or_ne p q with hpq | hpq
  · refine Finset.prod_eq_one fun ⟨ℓ, hℓ⟩ _ ↦ ?_
    have : Fact ℓ.Prime := ⟨hT ℓ hℓ⟩
    by_cases hℓq : ℓ = q
    · subst hℓq hpq
      exact unitsMap_cyclotomicSymbol_self_primePow m p hpk (by simp [hu])
    · exact unitsMap_cyclotomicSymbol_of_coprime_of_eq_unit m ℓ hpk
        (hcop (hT ℓ hℓ) (hpq ▸ hℓq)) (w := unit ℓ hℓq) (by simp [hu, hunit])
  rw [Finset.prod_eq_mul ⟨p, hpT⟩ ⟨q, hqT⟩ (by simpa using hpq) (fun ⟨ℓ, hℓ⟩ _ hne ↦ ?_)
    (fun h ↦ absurd (Finset.mem_attach _ _) h) (fun h ↦ absurd (Finset.mem_attach _ _) h)]
  · rw [unitsMap_cyclotomicSymbol_primePow_of_eq_unit m p hpk (w := unit p hpq)
        (by simp [hu, hunit]),
      unitsMap_cyclotomicSymbol_self_of_coprime m q hpk (hcop hq hpq.symm) (by simp [hu]),
      inv_mul_eq_one]
    ext
    simp [hunit]
  · have : Fact ℓ.Prime := ⟨hT ℓ hℓ⟩
    have hℓq : ℓ ≠ q := fun h ↦ hne.2 (Subtype.ext h)
    exact unitsMap_cyclotomicSymbol_of_coprime_of_eq_unit m ℓ hpk
      (hcop (hT ℓ hℓ) fun h ↦ hne.1 (Subtype.ext h)) (w := unit ℓ hℓq) (by simp [hu, hunit])

/-- At a positive integer whose primes lie in `T`, by multiplicativity from the primes. -/
private theorem symbolProd_of_eq_natCast (hm : m.primeFactors ⊆ T) (n : ℕ) :
    n ≠ 0 → n.primeFactors ⊆ T → ∀ u : ℚˣ, (u : ℚ) = n → symbolProd m T hT u = 1 := by
  induction n using Nat.recOnMul with
  | zero => exact fun h ↦ absurd rfl h
  | one =>
    intro _ _ u hu
    have hu1 : u = 1 := Units.ext (by simpa using hu)
    rw [hu1, map_one]
  | prime q hq =>
    exact fun _ hqT u hu ↦ symbolProd_of_eq_prime m T hT hm hq (hqT (by simp [hq])) hu
  | mul a b iha ihb =>
    intro hab hab' u hu
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    rw [Nat.primeFactors_mul ha hb, Finset.union_subset_iff] at hab'
    have hu' : u = Units.mk0 (a : ℚ) (by exact_mod_cast ha) * Units.mk0 (b : ℚ)
        (by exact_mod_cast hb) := Units.ext (by simp [hu])
    rw [hu', map_mul, iha ha hab'.1 _ rfl, ihb hb hab'.2 _ rfl, one_mul]

/-- **The product formula over a set of primes.** If `T` is a finite set of primes containing the
primes dividing `m`, the numerator and the denominator of `a ∈ ℚˣ`, then the real symbol of `a`
times the symbols of `a` at the primes of `T` is `1`. -/
theorem prod_cyclotomicSymbol_of_subset (hm : m.primeFactors ⊆ T) (a : ℚˣ)
    (hnum : (a : ℚ).num.natAbs.primeFactors ⊆ T) (hden : (a : ℚ).den.primeFactors ⊆ T) :
    realCyclotomicSymbol m (Units.map (algebraMap ℚ ℝ).toMonoidHom a) *
        (∏ ℓ ∈ T.attach,
          haveI : Fact (ℓ : ℕ).Prime := ⟨hT ℓ ℓ.2⟩
          cyclotomicSymbol m ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)) = 1 := by
  -- `a · den(a) = ± |num(a)|`, and both `den(a)` and `|num(a)|` are supported on `T`
  have hnum0 : (a : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 a.ne_zero)
  let N : ℚˣ := Units.mk0 _ (Nat.cast_ne_zero.2 hnum0)
  let D : ℚˣ := Units.mk0 _ (Nat.cast_ne_zero.2 (a : ℚ).den_ne_zero)
  have hfN := symbolProd_of_eq_natCast m T hT hm _ hnum0 hnum N rfl
  have hfD := symbolProd_of_eq_natCast m T hT hm _ (a : ℚ).den_ne_zero hden D rfl
  have hfaD : symbolProd m T hT (a * D) = 1 := by
    rcases Int.natAbs_eq (a : ℚ).num with h | h
    · have haD : a * D = N := Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Rat.mul_den_eq_num,
          congrArg (Int.cast : ℤ → ℚ) h, Int.cast_natCast])
      rw [haD, hfN]
    · have haD : a * D = -1 * N := Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mul, Units.val_mk0, Rat.mul_den_eq_num,
          congrArg (Int.cast : ℤ → ℚ) h, Int.cast_neg, Int.cast_natCast, Units.val_neg,
          Units.val_one, neg_one_mul])
      rw [haD, map_mul, symbolProd_of_eq_neg_one m T hT hm (by simp), hfN, one_mul]
  rw [map_mul, hfD, mul_one, symbolProd_apply] at hfaD
  exact hfaD

/-- **The product formula for the explicit cyclotomic symbols** (Milne VII Example 8.2, with these
values as the definition of the local factors). For `a ∈ ℚˣ`, the real symbol times the symbols at
the primes dividing `m · a` is `1`: `prod_cyclotomicSymbol_of_subset` for those primes. -/
theorem prod_cyclotomicSymbol (a : ℚˣ) :
    realCyclotomicSymbol m (Units.map (algebraMap ℚ ℝ).toMonoidHom a) *
        (∏ ℓ ∈ (m * (a : ℚ).num.natAbs * (a : ℚ).den).primeFactors.attach,
          haveI : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
          cyclotomicSymbol m ℓ (Units.map (algebraMap ℚ ℚ_[ℓ]).toMonoidHom a)) = 1 := by
  have hS : m * (a : ℚ).num.natAbs * (a : ℚ).den ≠ 0 :=
    mul_ne_zero (mul_ne_zero (NeZero.ne m)
      (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 a.ne_zero))) (a : ℚ).den_ne_zero
  exact prod_cyclotomicSymbol_of_subset m _
    (fun _ hℓ ↦ Nat.prime_of_mem_primeFactors hℓ)
    (Nat.primeFactors_mono ((dvd_mul_right m _).mul_right _) hS) a
    (Nat.primeFactors_mono ((dvd_mul_left _ m).mul_right _) hS)
    (Nat.primeFactors_mono (dvd_mul_left _ _) hS)

end TauCeti
