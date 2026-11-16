/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Dirichlet character conductors

The conductor of a character of nonzero level is nonzero, a primitive character of nonzero level is
principal exactly when its level is one (`DirichletCharacter.IsPrimitive.eq_one_iff`), and a
character of nonzero level is trivial exactly when its primitive character is trivial (equivalently,
when its conductor is one).

Primitive characters are determined by their lifts to a common nonzero level
(`DirichletCharacter.IsPrimitive.changeLevel_eq_changeLevel_iff`), which in particular identifies
any primitive lift of `χ` with `χ.primitiveCharacter`
(`DirichletCharacter.IsPrimitive.exists_eq_primitiveCharacter_of_changeLevel_eq`). A prime `p`
fails to divide `χ.conductor` if and only if `χ` factors through the prime-to-`p` part
`ordCompl[p] N` (`DirichletCharacter.not_dvd_conductor_iff_factorsThrough_ordCompl`), and lifting a
character from level `M` to a nonzero multiple level `N` and taking its primitive character
preserves evaluation at integers coprime to `M`
(`DirichletCharacter.primitiveCharacter_changeLevel_apply_of_isCoprime`).

An injective change of coefficient ring preserves factorization through a lower level, hence the
conductor and primitivity of a Dirichlet character. The conductor of a product of Dirichlet
characters with pairwise coprime conductors is the product of their conductors.
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

/-- The primitive character of a character of nonzero level is principal if and only if the
character itself is principal. -/
@[simp]
theorem primitiveCharacter_eq_one_iff {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} : χ.primitiveCharacter = 1 ↔ χ = 1 := by
  rw [χ.primitiveCharacter_isPrimitive.eq_one_iff, ← eq_one_iff_conductor_eq_one]

/-- Two primitive characters have equal lifts to a common nonzero level exactly when their levels
and characters agree. The existential equality transports the first character to the second
level. -/
theorem IsPrimitive.changeLevel_eq_changeLevel_iff {R : Type*} [CommMonoidWithZero R]
    {N M L : ℕ} [NeZero L] {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hN : N ∣ L) (hM : M ∣ L) :
    changeLevel hN χ = changeLevel hM ψ ↔ ∃ h : N = M, h ▸ χ = ψ := by
  constructor
  · intro h
    have hlevel : N = M := by
      simpa only [conductor_changeLevel, (isPrimitive_def χ).mp hχ,
        (isPrimitive_def ψ).mp hψ] using congrArg conductor h
    subst M
    exact ⟨rfl, changeLevel_injective hN h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- If a primitive character `ψ` lifts to `χ` at a nonzero multiple level, then the level of `ψ`
equals the conductor of `χ` and `ψ` equals `χ.primitiveCharacter` after transporting along the
level equality. -/
theorem IsPrimitive.exists_eq_primitiveCharacter_of_changeLevel_eq
    {R : Type*} [CommMonoidWithZero R] {M N : ℕ} [NeZero N]
    {ψ : DirichletCharacter R M} {χ : DirichletCharacter R N}
    (hψ : ψ.IsPrimitive) (hMN : M ∣ N) (hχ : changeLevel hMN ψ = χ) :
    ∃ h : M = χ.conductor, h ▸ ψ = χ.primitiveCharacter :=
  (hψ.changeLevel_eq_changeLevel_iff χ.primitiveCharacter_isPrimitive
    hMN χ.conductor_dvd_level).mp (hχ.trans χ.changeLevel_primitiveCharacter.symm)

/-- For a prime `p` and a nonzero level `N`, `p` fails to divide the conductor of `χ` if and only
if `χ` factors through the prime-to-`p` part `ordCompl[p] N` of `N`. -/
theorem not_dvd_conductor_iff_factorsThrough_ordCompl {R : Type*} [CommMonoidWithZero R]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ χ.conductor ↔ χ.FactorsThrough (ordCompl[p] N) := by
  rw [← mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd χ (Nat.ordCompl_dvd N p)]
  exact ⟨Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level,
    fun h hd ↦ Nat.not_dvd_ordCompl hp (NeZero.ne N) (hd.trans h)⟩

/-- Lifting a character `ψ` from level `M` to a nonzero multiple level `N` and taking its
primitive character preserves evaluation at any integer coprime to `M`. -/
theorem primitiveCharacter_changeLevel_apply_of_isCoprime {R : Type*} [CommMonoidWithZero R]
    {M N : ℕ} [NeZero N] (hMN : M ∣ N) (ψ : DirichletCharacter R M) {a : ℤ}
    (ha : IsCoprime a M) :
    (changeLevel hMN ψ).primitiveCharacter a = ψ a := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [primitiveCharacter_changeLevel_apply, primitiveCharacter_apply_of_isCoprime ψ ha]

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

end DirichletCharacter
