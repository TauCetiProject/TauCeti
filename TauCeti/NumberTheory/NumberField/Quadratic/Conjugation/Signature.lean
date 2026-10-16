/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.UnitSignature
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.NarrowClassGroup
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# Real quadratic fields whose units miss a sign pattern

Every sign pattern at the real places of a number field is the signature of an element of `Kˣ`
(`NumberField.fieldUnitSignature_surjective`), but the signature map on the units of `𝓞 K`
need not be surjective. This file shows how this happens for real quadratic fields, records the
consequence for the narrow class group, and checks it on `ℚ(√3)`.

For a real quadratic field the units of `𝓞 K` realize every sign pattern exactly when some unit has
norm `-1`, since both conditions say that `Cl⁺(K) → Cl(K)` is injective
(`TauCeti.NumberField.NarrowClassGroup.toClassGroup_injective_iff_unitSignature_surjective` and
`NumberField.NarrowClassGroup.toClassGroup_injective_iff_exists_norm_eq_neg_one`). When there is
no such unit the narrow class number is exactly twice the class number
(`NumberField.NarrowClassGroup.card_eq_two_mul_card_classGroup_of_forall_norm_ne_neg_one`).

Let `K = ℚ(√d)` with `d` squarefree. The norm of an algebraic integer has the form
`(A² - d B²) / 4` (`NumberField.exists_sq_sub_mul_sq_eq_four_mul_norm`). If a prime `p` divides
`d`, an algebraic integer of norm `-1` therefore gives `A² ≡ -4 (mod p)`, so `-1` is a square
modulo `p`. For `p ≡ 3 (mod 4)` it is not, and no algebraic integer of `K` has norm `-1`.

The simplest instance is `ℚ(√3)`, the first real quadratic field without a unit of norm `-1`
(`1 + √2` has norm `-1`). Its class number is `1`, so its narrow class group has order `2`.

## Main results

* `TauCeti.NumberField.isSquare_neg_one_of_norm_eq_neg_one`: an algebraic integer of norm `-1`
  makes `-1` a square modulo every prime dividing the radicand.
* `TauCeti.NumberField.norm_ne_neg_one_of_prime_dvd`: if a prime `p ≡ 3 (mod 4)` divides the
  radicand, no algebraic integer has norm `-1`.
* `TauCeti.NumberField.unitSignature_surjective_iff_exists_norm_eq_neg_one`: for a real quadratic
  field the units realize every sign pattern exactly when some unit has norm `-1`.
* `TauCeti.NumberField.not_surjective_unitSignature_sqrtThree`: the units of `ℚ(√3)` miss a sign
  pattern.
* `TauCeti.NumberField.card_narrowClassGroup_sqrtThree`: the narrow class group of `ℚ(√3)` has
  order `2`.

## References

* H. Cohn, *A Classical Invitation to Algebraic Numbers and Class Fields*, Chapter 8.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open Polynomial NumberField NumberField.NarrowClassGroup

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **An algebraic integer of norm `-1` makes `-1` a square modulo every prime dividing the
radicand.** For `p ∣ d`, the norm `(A² - d B²) / 4` of an algebraic integer is congruent to the
square `(A / 2)²` modulo an odd prime `p`. -/
theorem isSquare_neg_one_of_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) {p : ℕ} [Fact p.Prime]
    (hpd : (p : ℤ) ∣ d) {z : 𝓞 K} (hz : Algebra.norm ℚ (z : K) = -1) :
    IsSquare (-1 : ZMod p) := by
  obtain ⟨A, B, hAB⟩ := exists_sq_sub_mul_sq_eq_four_mul_norm hmin hgen hsf z
  have hzℤ : Algebra.norm ℤ z = -1 := by exact_mod_cast (Algebra.coe_norm_int z).trans hz
  have hd : (d : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd
  have hA : (A : ZMod p) ^ 2 = -4 := by
    have h := congrArg (Int.cast : ℤ → ZMod p) hAB
    push_cast [hzℤ, hd] at h
    linear_combination h
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨1, rfl⟩
  · have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h2p : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2p)
    refine ⟨A / 2, ?_⟩
    field_simp
    linear_combination -hA

/-- **No algebraic integer has norm `-1` when a prime `p ≡ 3 (mod 4)` divides the radicand**,
since `-1` is not a square modulo such a prime. In particular no unit of `𝓞 K` has norm `-1`. -/
theorem norm_ne_neg_one_of_prime_dvd (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) (hpd : (p : ℤ) ∣ d) (z : 𝓞 K) : Algebra.norm ℚ (z : K) ≠ -1 := fun hz =>
  ZMod.exists_sq_eq_neg_one_iff.mp (isSquare_neg_one_of_norm_eq_neg_one hmin hgen hsf hpd hz) hp

/-- **The units of a real quadratic field realize every sign pattern exactly when some unit has
norm `-1`.** Both conditions are equivalent to injectivity of `Cl⁺(K) → Cl(K)`. -/
theorem unitSignature_surjective_iff_exists_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) :
    Function.Surjective (unitSignature (K := K)) ↔
      ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 :=
  NarrowClassGroup.toClassGroup_injective_iff_unitSignature_surjective.symm.trans
    (toClassGroup_injective_iff_exists_norm_eq_neg_one hmin hgen hd)

/-! ### The field `ℚ(√3)` -/

/-- `3` is not a square in `ℚ`, so `ℚ[√3]` is a field. -/
instance fact_not_isSquare_three : Fact (¬ IsSquare (3 : ℚ)) := ⟨by
  rw [Rat.isSquare_ofNat_iff]
  rintro ⟨r, hr⟩
  have h : r ≤ 2 := by nlinarith
  interval_cases r <;> omega⟩

/-- The generator `√3` of `ℚ(√3)`, as an algebraic integer with minimal polynomial `X² - 3`. -/
private theorem exists_gen_sqrtThree :
    ∃ θ : 𝓞 (QuadraticAlgebra ℚ 3 0), minpoly ℤ θ = X ^ 2 - C 3 ∧
      Algebra.adjoin ℚ {(θ : QuadraticAlgebra ℚ 3 0)} = ⊤ := by
  refine exists_gen_of_sq_eq_intCast (z := QuadraticAlgebra.omega) ?_ ?_
  · rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  · rintro ⟨q, hq⟩
    simpa using congrArg QuadraticAlgebra.im hq

/-- **The units of `ℚ(√3)` miss a sign pattern.** No unit of `ℤ[√3]` is positive at one real
place and negative at the other, since no unit has norm `-1`. -/
theorem not_surjective_unitSignature_sqrtThree :
    ¬ Function.Surjective (unitSignature (K := QuadraticAlgebra ℚ 3 0)) := by
  obtain ⟨θ, hmin, hgen⟩ := exists_gen_sqrtThree
  rw [unitSignature_surjective_iff_exists_norm_eq_neg_one hmin hgen (by norm_num)]
  rintro ⟨u, hu⟩
  exact norm_ne_neg_one_of_prime_dvd (p := 3) hmin hgen Int.prime_three.squarefree (by norm_num)
    dvd_rfl (u : 𝓞 _) hu

/-- **The narrow class group of `ℚ(√3)` has order `2`.** The ring `ℤ[√3]` is a principal ideal
domain, since the discriminant `12` is small enough for the Minkowski bound, and no unit has
norm `-1`, so `h⁺ = 2 h = 2`. -/
theorem card_narrowClassGroup_sqrtThree :
    Nat.card (NarrowClassGroup (QuadraticAlgebra ℚ 3 0)) = 2 := by
  obtain ⟨θ, hmin, hgen⟩ := exists_gen_sqrtThree
  have hsf : Squarefree (3 : ℤ) := Int.prime_three.squarefree
  have : IsTotallyReal (QuadraticAlgebra ℚ 3 0) :=
    isTotallyReal_of_minpoly_eq_X_sq_sub_C_of_nonneg hmin hgen (by norm_num)
  have hpid : IsPrincipalIdealRing (𝓞 (QuadraticAlgebra ℚ 3 0)) := by
    apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    rw [discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf (by norm_num),
      IsTotallyReal.nrComplexPlaces_eq_zero, finrank_rat_eq_two hmin hgen]
    norm_num [Nat.factorial]
  have hcl : Nat.card (ClassGroup (𝓞 (QuadraticAlgebra ℚ 3 0))) = 1 := by
    rw [Nat.card_eq_fintype_card, ← classNumber, classNumber_eq_one_iff.mpr hpid]
  rw [NarrowClassGroup.card_eq_two_mul_card_classGroup_of_forall_norm_ne_neg_one hmin hgen
    (by norm_num) fun u => norm_ne_neg_one_of_prime_dvd (p := 3) hmin hgen hsf (by norm_num)
      dvd_rfl (u : 𝓞 _), hcl]

end TauCeti.NumberField
