/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Factoring a Dirichlet character through a divisor

Facts about when a Dirichlet character `χ` mod `N` factors through a divisor of `N`, stated for
characters valued in any `CommMonoidWithZero`, which is the generality of
`DirichletCharacter.factorsThrough_iff_ker_unitsMap` and of the conductor.

If `χ` does not factor through `d ∣ N`, then knowing a unit's reduction modulo `d` does not
determine its character value: every unit has a partner in the same fibre of `ZMod.unitsMap` on
which `χ` takes a different value. This is the form the level-lowering argument for the
conductor theorem consumes.

If the lift of `χ` to a multiple level factors through `d`, then `χ` itself factors through
`gcd (N, d)`: `changeLevel` preserves the conductor, which then divides both. This is how a
factorisation found at an auxiliary level is brought back to the level of `χ`; the arithmetic
case the descent uses is `d = L N / p` with `p ∣ N` coprime to `L`, where the gcd is `N / p`.

## Main results

* `DirichletCharacter.exists_alt_unit_in_coset_with_char_separation`: character separation within
  a fibre of the reduction map.
* `DirichletCharacter.factorsThrough_gcd_of_changeLevel_factorsThrough`: a factorisation of the
  lift to a multiple level through `d` descends to a factorisation of `χ` through `gcd (N, d)`,
  and `DirichletCharacter.factorsThrough_div_of_changeLevel_factorsThrough`: its arithmetic
  specialisation, from `L N / p` to `N / p`.
* `DirichletCharacter.exists_eq_comp_unitsMap_of_factorsThrough`: a factorisation of
  `MulChar.ofUnitHom χ` through `d`, read back on unit homomorphisms as `χ = χ₀ ∘ unitsMap`.
* `DirichletCharacter.factorsThroughEquiv`: the characters at level `N` factoring through
  `d ∣ N` correspond to the characters modulo `d`.
* `DirichletCharacter.changeLevel_natCast_of_coprime`: changing the level preserves the values
  at naturals prime to the new level.
* `DirichletCharacter.changeLevel_apply_neg_one`, `DirichletCharacter.even_changeLevel_iff`:
  changing the level preserves the value at `-1`, hence parity.
* `DirichletCharacter.conductor_eq_prime_pow_of_emod_eq_of_apply_ne_apply`: a primitivity
  criterion at a prime-power level, obtained by comparing values on congruent units, and its
  specialisations `DirichletCharacter.conductor_eq_four_of_apply_one_ne_apply_three` and
  `DirichletCharacter.conductor_eq_eight_of_apply_one_ne_apply_five`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declaration
`exists_alt_unit_in_coset_with_char_separation` (:656). The source reaches it through an
intermediate shift form (`exists_kernel_unit_with_char_shift`, :646) and a separate
non-factorisation witness (`exists_unit_of_not_factorsThrough`, :542); each is a one-line
consequence of the other, so only this form is ported and the extraction is done inline.

`factorsThrough_div_of_changeLevel_factorsThrough` is extracted from the same project at commit
`eb9621e7bcb0ce220ad53983ec45d987cb5b9002`, file
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/InductiveStep.lean`: the
conductor step inside the proof of `miyake_4_6_8_factor_dichotomy`, which the source carries as
the private lemmas `conductor_dvd_of_factorsThrough`, `factorsThrough_of_conductor_dvd` and
`conductor_changeLevel` specialised to `L N / p`. Here those three are Mathlib's
`conductor_dvd_of_mem_conductorSet`, `mem_conductorSet_iff_conductor_dvd` and
`conductor_changeLevel`, so what is ported is the arithmetic of the descent — the conductor
divides `gcd (N, L N / p) = N / p` — stated once for characters valued in any
`CommMonoidWithZero`.
-/

public section

namespace DirichletCharacter

/-- A character which factors through `d` takes the same value on level-units congruent modulo
`d`. -/
theorem apply_eq_apply_of_factorsThrough {R : Type*} [CommMonoidWithZero R] {N d : ℕ}
    (chi : DirichletCharacter R N) (hfac : chi.FactorsThrough d) {a b : ℤ}
    (ha : IsCoprime a N) (hb : IsCoprime b N) (hab : a % d = b % d) :
    chi a = chi b := by
  obtain ⟨hd, psi, rfl⟩ := hfac
  rw [changeLevel_eq_cast_of_dvd' psi hd ha, changeLevel_eq_cast_of_dvd' psi hd hb]
  exact congrArg psi ((ZMod.intCast_eq_intCast_iff' a b d).2 hab)

/-- **A primitivity criterion at a prime-power level.** A character of level `p ^ k` taking
different values on two level-units congruent modulo `p ^ (k - 1)` cannot factor through a proper
divisor of its level, so its conductor is the full level `p ^ k`. -/
theorem conductor_eq_prime_pow_of_emod_eq_of_apply_ne_apply {R : Type*} [CommMonoidWithZero R]
    {p k : ℕ} (hp : p.Prime) (chi : DirichletCharacter R (p ^ k)) {a b : ℤ}
    (ha : IsCoprime a (p ^ k : ℕ)) (hb : IsCoprime b (p ^ k : ℕ))
    (hab : a % (p ^ (k - 1) : ℕ) = b % (p ^ (k - 1) : ℕ)) (hdist : chi a ≠ chi b) :
    chi.conductor = p ^ k := by
  obtain ⟨j, hjk, hc⟩ := (Nat.dvd_prime_pow hp).mp chi.conductor_dvd_level
  rcases hjk.lt_or_eq with hlt | rfl
  · -- A smaller conductor divides `p ^ (k - 1)`, so `a` and `b` are congruent modulo it.
    have hdvd : chi.conductor ∣ p ^ (k - 1) := hc ▸ pow_dvd_pow p (by omega)
    exact absurd (apply_eq_apply_of_factorsThrough _ (factorsThrough_conductor chi) ha hb
      (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hdvd) hab)) hdist
  · exact hc

/-- A character of level four which distinguishes `1` and `3` is primitive. -/
theorem conductor_eq_four_of_apply_one_ne_apply_three {R : Type*} [CommMonoidWithZero R]
    (chi : DirichletCharacter R 4) (hdist : chi (1 : ℤ) ≠ chi (3 : ℤ)) :
    chi.conductor = 4 :=
  conductor_eq_prime_pow_of_emod_eq_of_apply_ne_apply (p := 2) (k := 2) Nat.prime_two chi
    isCoprime_one_left ⟨-1, 1, by norm_num⟩ (by norm_num) hdist

/-- A character of level eight which distinguishes `1` and `5` is primitive. -/
theorem conductor_eq_eight_of_apply_one_ne_apply_five {R : Type*} [CommMonoidWithZero R]
    (chi : DirichletCharacter R 8) (hdist : chi (1 : ℤ) ≠ chi (5 : ℤ)) :
    chi.conductor = 8 :=
  conductor_eq_prime_pow_of_emod_eq_of_apply_ne_apply (p := 2) (k := 3) Nat.prime_two chi
    isCoprime_one_left ⟨5, -3, by norm_num⟩ (by norm_num) hdist

/-- **Character separation within a coset.** If `χ` does not factor through `d ∣ N`, then every
unit `u` has a partner `u'` with the same reduction modulo `d` but a different character value —
so the character cannot be read off the reduction alone. -/
theorem exists_alt_unit_in_coset_with_char_separation {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    [NeZero N] {d : ℕ} (hd : d ∣ N) {χ : DirichletCharacter R N}
    (h_not_fac : ¬ χ.FactorsThrough d) (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧ χ.toUnitHom u' ≠ χ.toUnitHom u := by
  rw [factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨v, hv_ker, hv_chi⟩ := IsConcreteLE.not_le_iff_exists.mp h_not_fac
  have hv_ker' : ZMod.unitsMap hd v = 1 := MonoidHom.mem_ker.mp hv_ker
  have hv_chi' : χ.toUnitHom v ≠ 1 := hv_chi ∘ MonoidHom.mem_ker.mpr
  exact ⟨u * v, by rw [map_mul, hv_ker', mul_one],
    by rw [map_mul, Ne, mul_eq_left]; exact hv_chi'⟩

/-- **A factorisation found at a multiple level descends to the gcd.** If the lift of `ψ` mod `N`
to a multiple level `M` factors through `d`, then `ψ` factors through `gcd (N, d)`:
`changeLevel` preserves the conductor, which then divides both the level `N` and `d`. -/
theorem factorsThrough_gcd_of_changeLevel_factorsThrough {R : Type*} [CommMonoidWithZero R]
    {N M d : ℕ} [NeZero M] (hNM : N ∣ M) {ψ : DirichletCharacter R N}
    (hfac : (changeLevel hNM ψ).FactorsThrough d) : ψ.FactorsThrough (Nat.gcd N d) := by
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ hNM))⟩
  have hc : ψ.conductor ∣ d := by
    have := conductor_dvd_of_mem_conductorSet _ hfac
    rwa [conductor_changeLevel] at this
  exact (mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left N d)).mpr
    (Nat.dvd_gcd ψ.conductor_dvd_level hc)

/-- **A factorisation found at an auxiliary level descends.** If the lift of `ψ` mod `N` to level
`L N` factors through `L N / p`, for `p ∣ N` coprime to `L`, then `ψ` factors through `N / p`.
This is `factorsThrough_gcd_of_changeLevel_factorsThrough` at the gcd
`gcd (N, L N / p) = gcd (p, L) · (N / p) = N / p`. -/
theorem factorsThrough_div_of_changeLevel_factorsThrough {R : Type*} [CommMonoidWithZero R]
    {N p L : ℕ} [NeZero N] [NeZero L] (hpN : p ∣ N) (hpL : Nat.Coprime p L)
    {ψ : DirichletCharacter R N}
    (hfac : (changeLevel (Nat.dvd_mul_left N L) ψ).FactorsThrough (L * N / p)) :
    ψ.FactorsThrough (N / p) := by
  have : NeZero (L * N) := ⟨mul_ne_zero (NeZero.ne L) (NeZero.ne N)⟩
  have hgcd : Nat.gcd N (L * N / p) = N / p := by
    rw [Nat.mul_div_assoc L hpN]
    calc Nat.gcd N (L * (N / p)) = Nat.gcd (p * (N / p)) (L * (N / p)) := by
          rw [Nat.mul_div_cancel' hpN]
      _ = Nat.gcd p L * (N / p) := Nat.gcd_mul_right p (N / p) L
      _ = N / p := by rw [hpL.gcd_eq_one, one_mul]
  rw [← hgcd]
  exact factorsThrough_gcd_of_changeLevel_factorsThrough _ hfac

/-- **A factorisation, read on unit homomorphisms.** If the Dirichlet character
`MulChar.ofUnitHom χ` factors through `d ∣ N`, the unit homomorphism `χ` is itself a composition
`χ₀ ∘ ZMod.unitsMap` with a unit homomorphism modulo `d` — the form in which a lowered
nebentypus is consumed, by the descent lemmas of `Newforms/Descent` and by the Main Lemma's
induction. -/
theorem exists_eq_comp_unitsMap_of_factorsThrough {R : Type*} [CommMonoidWithZero R] {N d : ℕ}
    (hd : d ∣ N) {χ : (ZMod N)ˣ →* Rˣ}
    (hfac : FactorsThrough (MulChar.ofUnitHom χ : DirichletCharacter R N) d) :
    ∃ χ₀ : (ZMod d)ˣ →* Rˣ, χ = χ₀.comp (ZMod.unitsMap hd) := by
  refine ⟨hfac.χ₀.toUnitHom, ?_⟩
  have h := congrArg MulChar.toUnitHom hfac.eq_changeLevel
  rw [changeLevel_toUnitHom] at h
  simpa using h

/-- **Characters factoring through a divisor.** For `d ∣ N`, the Dirichlet characters at level
`N` which factor through `d` are exactly the raises of the characters modulo `d`:
`FactorsThrough.χ₀` and `changeLevel` are inverse bijections. -/
noncomputable def factorsThroughEquiv {R : Type*} [CommMonoidWithZero R] {N d : ℕ}
    [NeZero N] (h : d ∣ N) :
    {χ : DirichletCharacter R N // χ.FactorsThrough d} ≃ DirichletCharacter R d where
  toFun χ := χ.2.χ₀
  invFun ψ := ⟨changeLevel h ψ, changeLevel_factorsThrough ψ h⟩
  left_inv χ := Subtype.ext χ.2.eq_changeLevel.symm
  right_inv ψ := (changeLevel_injective h (changeLevel_factorsThrough ψ h).eq_changeLevel).symm

/-- `factorsThroughEquiv` sends a character to the character modulo `d` it factors through. -/
@[simp]
theorem factorsThroughEquiv_apply {R : Type*} [CommMonoidWithZero R] {N d : ℕ} [NeZero N]
    (h : d ∣ N) (χ : {χ : DirichletCharacter R N // χ.FactorsThrough d}) :
    factorsThroughEquiv h χ = χ.2.χ₀ :=
  (rfl)

/-- The inverse of `factorsThroughEquiv` raises a character modulo `d` to level `N`. -/
@[simp]
theorem coe_factorsThroughEquiv_symm_apply {R : Type*} [CommMonoidWithZero R] {N d : ℕ}
    [NeZero N] (h : d ∣ N) (ψ : DirichletCharacter R d) :
    ((factorsThroughEquiv h).symm ψ : DirichletCharacter R N) = changeLevel h ψ :=
  (rfl)

/-- Raising the level of a Dirichlet character does not change its value at a natural number
prime to the new level. -/
theorem changeLevel_natCast_of_coprime {R : Type*} [CommMonoidWithZero R] {d n : ℕ} (h : d ∣ n)
    (χ : DirichletCharacter R d) {m : ℕ} (hm : m.Coprime n) : changeLevel h χ m = χ m := by
  simpa using changeLevel_eq_cast_of_dvd' χ h (a := (m : ℤ)) (Nat.isCoprime_iff_coprime.mpr hm)

/-- Raising the level of a Dirichlet character does not change its value at `-1`. -/
@[simp]
theorem changeLevel_apply_neg_one {R : Type*} [CommMonoidWithZero R] {d n : ℕ} (h : d ∣ n)
    (χ : DirichletCharacter R d) : changeLevel h χ (-1) = χ (-1) := by
  simpa using changeLevel_eq_cast_of_dvd' χ h (a := -1) (IsCoprime.neg_left isCoprime_one_left)

/-- **Changing the level preserves parity**: the value at `-1` of a Dirichlet character is the
value at `-1` of its lift to any multiple level. -/
@[simp]
theorem even_changeLevel_iff {S : Type*} [CommRing S] {d n : ℕ} (h : d ∣ n)
    (χ : DirichletCharacter S d) : (changeLevel h χ).Even ↔ χ.Even := by
  rw [Even, Even, changeLevel_apply_neg_one]

end DirichletCharacter
