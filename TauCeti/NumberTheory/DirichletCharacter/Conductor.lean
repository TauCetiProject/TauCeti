/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
import TauCeti.Algebra.GroupWithZero.Divisibility
import TauCeti.Data.Nat.GCD

/-!
# Dirichlet character conductors

Inversion preserves primitivity, and a primitive character is trivial exactly at level one;
accordingly `χ.primitiveCharacter = 1 ↔ χ = 1`, while `χ.primitiveCharacter` vanishes at every
prime dividing `χ.conductor`. Writing `n = p ^ k * m` with `p` prime and `¬ p ∣ m`, a character
modulo `n` factors through `m` iff `p` does not divide its conductor; at prime-power level `p ^ k`,
`p ∣ χ.conductor ↔ χ ≠ 1`, so every nonprincipal character of prime level is primitive.

An injective change of coefficient ring preserves factorization through a lower level, hence the
conductor and primitivity of a Dirichlet character. The conductor of a product of Dirichlet
characters with pairwise coprime conductors is the product of their conductors. A character can be
cancelled by multiplying by a character of a prescribed level exactly when its conductor divides
that level.

## Main results

* `DirichletCharacter.instNeZeroConductor`: `NeZero χ.conductor` when `[NeZero n]`.
* `DirichletCharacter.IsPrimitive.eq_one_iff`, `DirichletCharacter.primitiveCharacter_eq_one_iff`:
  a primitive character at nonzero level is principal iff the level is `1`, and
  `χ.primitiveCharacter = 1 ↔ χ = 1`.
* `DirichletCharacter.primitiveCharacter_apply_prime_eq_zero`: `χ.primitiveCharacter p = 0` when
  `p` is prime and `p ∣ χ.conductor`.
* `DirichletCharacter.factorsThrough_iff_not_dvd_conductor`: for `n = p ^ k * m` with `p` prime and
  `¬ p ∣ m`, `χ.FactorsThrough m ↔ ¬ p ∣ χ.conductor`.
* `DirichletCharacter.dvd_conductor_iff_ne_one_of_prime_pow`: for `χ` modulo `p ^ k`,
  `p ∣ χ.conductor ↔ χ ≠ 1`.
* `DirichletCharacter.isPrimitive_of_ne_one_of_prime`: every nonprincipal character modulo a prime
  `p` is primitive.
* `DirichletCharacter.conductor_ringHomComp`, `DirichletCharacter.isPrimitive_ringHomComp_iff`:
  injective ring homomorphisms preserve conductor and primitivity.
* `DirichletCharacter.conductor_mul_of_coprime`,
  `DirichletCharacter.conductor_prod_of_pairwise_coprime`: multiplicativity of conductors across
  coprime products.
* `DirichletCharacter.exists_mul_eq_one_iff_conductor_dvd`: a character can be cancelled at a
  prescribed level iff its conductor divides that level.
-/

public section

namespace DirichletCharacter

/-- The conductor of a Dirichlet character of nonzero level is nonzero. -/
instance instNeZeroConductor {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter R n) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- A primitive character is principal exactly when its level is one. -/
theorem IsPrimitive.eq_one_iff {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} (hχ : χ.IsPrimitive) : χ = 1 ↔ n = 1 := by
  rw [eq_one_iff_conductor_eq_one, (isPrimitive_def _).mp hχ]

/-- The primitive character associated to `χ` is principal if and only if `χ` is principal. -/
@[simp]
theorem primitiveCharacter_eq_one_iff {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  obtain rfl | _ := eq_zero_or_neZero n
  · have hinj {d : ℕ} (hd : d ∣ 0) (hc : d = 0) : Function.Injective (changeLevel hd (R := R)) := by
      subst hc
      intro _ _ h
      simpa only [changeLevel_self] using h
    rw [← (hinj χ.conductor_dvd_level (conductor_eq_zero_iff_level_eq_zero.mpr rfl)).eq_iff,
      χ.changeLevel_primitiveCharacter, map_one]
  · exact χ.primitiveCharacter_isPrimitive.eq_one_iff.trans χ.eq_one_iff_conductor_eq_one.symm

/-- The primitive character associated to `χ` vanishes at every prime dividing `χ.conductor`. -/
theorem primitiveCharacter_apply_prime_eq_zero {R : Type*} [CommMonoidWithZero R] {n p : ℕ}
    (χ : DirichletCharacter R n) (hp : p.Prime) (h : p ∣ χ.conductor) :
    χ.primitiveCharacter p = 0 :=
  χ.primitiveCharacter.map_nonunit fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hp).mp hu h

/-- **Factoring through the prime-to-`p` part of the level.** If `n = p ^ k * m` with `p` prime and
`¬ p ∣ m`, a Dirichlet character `χ` modulo `n` factors through `m` if and only if `p` does not
divide its conductor. -/
theorem factorsThrough_iff_not_dvd_conductor {R : Type*} [CommMonoidWithZero R] {n p k m : ℕ}
    (hp : p.Prime) (hn : n = p ^ k * m) (hm : ¬ p ∣ m) (χ : DirichletCharacter R n) :
    χ.FactorsThrough m ↔ ¬ p ∣ χ.conductor := by
  have := NeZero.of_not_dvd_right hm
  have : NeZero n := ⟨hn ▸ mul_ne_zero (pow_ne_zero k hp.ne_zero) (NeZero.ne m)⟩
  have hmn : m ∣ n := ⟨p ^ k, by rw [hn, mul_comm]⟩
  rw [← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd χ hmn]
  exact ⟨fun hdvd hpc ↦ hm (hpc.trans hdvd), fun hnpc ↦
    ((hp.coprime_iff_not_dvd.mpr hnpc).pow_left k).symm.dvd_of_dvd_mul_left
      (hn ▸ χ.conductor_dvd_level)⟩

/-- **Prime-power conductor dichotomy.** For a prime `p` and a character `χ` modulo `p ^ k`, the
prime `p` divides `χ.conductor` if and only if `χ` is nonprincipal. -/
theorem dvd_conductor_iff_ne_one_of_prime_pow {R : Type*} [CommMonoidWithZero R] {p k : ℕ}
    (hp : p.Prime) (χ : DirichletCharacter R (p ^ k)) :
    p ∣ χ.conductor ↔ χ ≠ 1 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp χ.conductor_dvd_level
  rw [Ne, eq_one_iff_conductor_eq_one, hj]
  rcases eq_or_ne j 0 with rfl | hj0
  · simp [hp.not_dvd_one]
  · exact ⟨fun _ ↦ (one_lt_pow₀ hp.one_lt hj0).ne', fun _ ↦ dvd_pow_self p hj0⟩

/-- Every nonprincipal Dirichlet character of prime level is primitive. -/
theorem isPrimitive_of_ne_one_of_prime {R : Type*} [CommMonoidWithZero R] {p : ℕ} (hp : p.Prime)
    {χ : DirichletCharacter R p} (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [isPrimitive_def]
  rcases hp.eq_one_or_self_of_dvd _ χ.conductor_dvd_level with h1 | hp'
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h1) hχ
  · exact hp'

/-! ### Injective changes of the coefficient ring -/

/-- Factoring a Dirichlet character through a lower level is unchanged by an injective change of
coefficient ring. -/
theorem factorsThrough_ringHomComp_iff {R R' : Type*} [CommRing R] [CommRing R']
    {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Function.Injective f) :
    FactorsThrough (χ.ringHomComp f) d ↔ FactorsThrough χ d := by
  by_cases hd : d ∣ n
  · rw [factorsThrough_iff_ker_unitsMap hd, factorsThrough_iff_ker_unitsMap hd]
    suffices (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker by rw [this]
    ext u
    simp [Units.ext_iff, hf.eq_iff' (map_one f)]
  · exact iff_of_false (mt FactorsThrough.dvd hd) (mt FactorsThrough.dvd hd)

/-- An injective change of coefficient ring preserves the conductor of a Dirichlet character. -/
theorem conductor_ringHomComp {R R' : Type*} [CommRing R] [CommRing R']
    {n : ℕ} (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Function.Injective f) : conductor (χ.ringHomComp f) = conductor χ := by
  obtain rfl | _ := eq_zero_or_neZero n
  · simp only [conductor_eq_zero_iff_level_eq_zero.mpr]
  exact congrArg sInf (Set.ext fun _ ↦ factorsThrough_ringHomComp_iff χ f hf)

/-- An injective change of coefficient ring preserves primitivity of a Dirichlet character. -/
theorem isPrimitive_ringHomComp_iff {R R' : Type*} [CommRing R] [CommRing R']
    {n : ℕ} (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Function.Injective f) : IsPrimitive (χ.ringHomComp f) ↔ IsPrimitive χ := by
  rw [isPrimitive_def, isPrimitive_def, conductor_ringHomComp χ f hf]

/-! ### Products with coprime conductors -/

/-- The conductor of a product of two Dirichlet characters with coprime conductors is the product
of their conductors. -/
theorem conductor_mul_of_coprime {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    {χ ψ : DirichletCharacter R N} (hcop : χ.conductor.Coprime ψ.conductor) :
    (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  -- Each factor's conductor divides that of the product, since `χ = (χ * ψ) * ψ⁻¹`.
  have key {χ ψ : DirichletCharacter R N} (h : χ.conductor.Coprime ψ.conductor) :
      χ.conductor ∣ (χ * ψ).conductor := by
    refine h.dvd_of_dvd_mul_right ?_
    simpa only [mul_inv_cancel_right, conductor_inv] using
      (conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹).trans (Nat.lcm_dvd_mul _ _)
  refine Nat.dvd_antisymm ((conductor_mul_dvd_lcm_conductor χ ψ).trans (Nat.lcm_dvd_mul _ _)) ?_
  exact hcop.mul_dvd_of_dvd_of_dvd (key hcop) (mul_comm ψ χ ▸ key hcop.symm)

/-- The conductor of a finite product of Dirichlet characters with pairwise coprime conductors is
the product of their conductors, provided the index set is nonempty or the level is nonzero. -/
theorem conductor_prod_of_pairwise_coprime {R ι : Type*} [CommMonoidWithZero R]
    {N : ℕ} {s : Finset ι} {χ : ι → DirichletCharacter R N}
    (hcop : (s : Set ι).Pairwise fun i j ↦ (χ i).conductor.Coprime (χ j).conductor)
    (hlevel : s.Nonempty ∨ N ≠ 0) :
    (∏ i ∈ s, χ i).conductor = ∏ i ∈ s, (χ i).conductor := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : NeZero N := ⟨hlevel.resolve_left (by simp)⟩
    simp [conductor_one]
  | @insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp
    have ih := ih (hcop.mono (by simp)) (Or.inl hsne)
    have hc : (χ i).conductor.Coprime (∏ j ∈ s, (χ j).conductor) :=
      Nat.Coprime.prod_right fun j hj ↦ hcop (by simp) (by simp [hj])
        (ne_of_mem_of_not_mem hj hi).symm
    rw [Finset.prod_insert hi, conductor_mul_of_coprime (ih ▸ hc), ih, Finset.prod_insert hi]

/-- There is a character modulo `q` whose product with `ψ` is principal at the least common
multiple of the levels if and only if `ψ` has conductor dividing `q`. -/
theorem exists_mul_eq_one_iff_conductor_dvd {R : Type*} [CommMonoidWithZero R]
    {d q : ℕ} [NeZero d] (ψ : DirichletCharacter R d) :
    (∃ χ : DirichletCharacter R q, χ.mul ψ = 1) ↔ ψ.conductor ∣ q := by
  obtain rfl | _ := eq_zero_or_neZero q
  · refine iff_of_true ?_ (dvd_zero _)
    refine ⟨(changeLevel (dvd_zero d) ψ)⁻¹, ?_⟩
    simp only [DirichletCharacter.mul, map_inv, ← changeLevel_trans, inv_mul_cancel]
  constructor
  · rintro ⟨χ, h⟩
    rw [DirichletCharacter.mul] at h
    have heq := eq_inv_of_mul_eq_one_right h
    rw [← map_inv] at heq
    rw [← conductor_changeLevel ψ (Nat.dvd_lcm_right q d), heq,
      conductor_changeLevel, conductor_inv]
    exact χ.conductor_dvd_level
  · intro h
    refine ⟨(changeLevel h) ψ.primitiveCharacter⁻¹, ?_⟩
    have hlevel : changeLevel (Nat.dvd_lcm_right q d) ψ =
        changeLevel (h.trans (Nat.dvd_lcm_left q d)) ψ.primitiveCharacter := by
      rw [changeLevel_trans ψ.primitiveCharacter ψ.conductor_dvd_level,
        changeLevel_primitiveCharacter]
    rw [DirichletCharacter.mul, ← changeLevel_trans, map_inv, ← hlevel, inv_mul_cancel]

end DirichletCharacter
