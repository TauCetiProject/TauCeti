/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.Data.ZMod.ExactDivisor

/-!
# The prime-to-p part of a Dirichlet character

For a prime `p` and a character `χ` of conductor `c`, the Chinese remainder theorem splits
`ZMod c` into its factors at `p ^ c.factorization p` and `ordCompl[p] c`. Restricting the
primitive character of `χ` to the second factor defines `primeToPart p χ`. In particular,
this uses the conductor, not the possibly larger level of `χ`.

The value of this character at `p` is nonzero. It is the factor denoted by `χ⁽ᵖ⁾(p)` in
the bad-prime Hecke eigenvalue formulas for newforms.

## References

* T. Miyake, *Modular Forms*, Theorem 4.6.17.
-/

public noncomputable section

namespace TauCeti

variable {R : Type*} [CommMonoidWithZero R] {N p : ℕ}

/-- The prime-to-`p` part of `χ`, obtained by restricting its primitive character to the
prime-to-`p` CRT factor of its conductor. For nonprime `p`, the primary factor is trivial. -/
def primeToPart (p : ℕ) (χ : DirichletCharacter R N) :
    DirichletCharacter R (ordCompl[p] χ.conductor) :=
  MulChar.ofUnitHom <| (χ.primitiveCharacter.toUnitHom.comp
    (Nat.isExactDivisor_primePow (N := χ.conductor)).unitsEquivProd.symm.toMonoidHom).comp
      (MonoidHom.inr (ZMod (p ^ χ.conductor.factorization p))ˣ
        (ZMod (ordCompl[p] χ.conductor))ˣ)

/-- On units, the prime-to-`p` part is the restriction of the primitive character along
`u ↦ CRT⁻¹(1, u)`. -/
@[simp]
theorem equivToUnitHom_primeToPart (p : ℕ) (χ : DirichletCharacter R N) :
    MulChar.equivToUnitHom (primeToPart p χ) = ((MulChar.equivToUnitHom χ.primitiveCharacter).comp
      (Nat.isExactDivisor_primePow (N := χ.conductor)).unitsEquivProd.symm.toMonoidHom).comp
        (MonoidHom.inr (ZMod (p ^ χ.conductor.factorization p))ˣ
          (ZMod (ordCompl[p] χ.conductor))ˣ) := by
  simp [primeToPart]

/-- Evaluation of the prime-to-`p` part at a unit uses the CRT lift with `p`-primary
component equal to `1`. -/
theorem primeToPart_apply_unit (p : ℕ) (χ : DirichletCharacter R N)
    (u : (ZMod (ordCompl[p] χ.conductor))ˣ) :
    primeToPart p χ u = χ.primitiveCharacter
      ((Nat.isExactDivisor_primePow (N := χ.conductor)).unitsEquivProd.symm (1, u) :
        ZMod χ.conductor) := by
  rw [← MulChar.coe_toUnitHom, MulChar.toUnitHom_eq, equivToUnitHom_primeToPart]
  simp

/-- The prime-to-`p` part is primitive at the prime-to-`p` factor of the conductor. -/
@[simp]
theorem conductor_primeToPart (p : ℕ) (χ : DirichletCharacter R N) :
    (primeToPart p χ).conductor = ordCompl[p] χ.conductor := by
  by_cases hc : χ.conductor = 0
  · have hlevel : ordCompl[p] χ.conductor = 0 := by simp [hc]
    exact (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mpr hlevel).trans hlevel.symm
  have : NeZero χ.conductor := ⟨hc⟩
  let h := Nat.isExactDivisor_primePow (N := χ.conductor) (p := p)
  let ψ : DirichletCharacter R (p ^ χ.conductor.factorization p) := MulChar.ofUnitHom
    ((χ.primitiveCharacter.toUnitHom.comp h.unitsEquivProd.symm.toMonoidHom).comp
      (MonoidHom.inl (ZMod (p ^ χ.conductor.factorization p))ˣ
        (ZMod (ordCompl[p] χ.conductor))ˣ))
  have hχ : χ.primitiveCharacter = ψ.changeLevel h.dvd *
      (primeToPart p χ).changeLevel (Nat.div_dvd_of_dvd h.dvd) := by
    apply MulChar.ext
    intro u
    have hu := congrArg Units.val (DFunLike.congr_fun
      (h.eq_mul_comp_unitsMap χ.primitiveCharacter.toUnitHom) u)
    simpa [ψ, DirichletCharacter.changeLevel_def, primeToPart] using hu
  have hc := (DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (ψ.changeLevel h.dvd) ((primeToPart p χ).changeLevel
      (Nat.div_dvd_of_dvd h.dvd))).trans (Nat.lcm_dvd_mul _ _)
  rw [← hχ, χ.primitiveCharacter_isPrimitive,
    DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_changeLevel] at hc
  apply Nat.dvd_antisymm (primeToPart p χ).conductor_dvd_level
  exact (h.coprime.symm.of_dvd_right ψ.conductor_dvd_level).dvd_of_dvd_mul_left
    ((Nat.ordCompl_dvd χ.conductor p).trans hc)

/-- The prime-to-`p` part is nonzero at `p`, even when the original character vanishes there. -/
theorem primeToPart_apply_prime_ne_zero [NeZero N] [Nontrivial R]
    (hp : p.Prime) (χ : DirichletCharacter R N) :
    primeToPart p χ (p : ZMod (ordCompl[p] χ.conductor)) ≠ 0 := by
  apply MulChar.apply_ne_zero_iff.mpr
  exact (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_ordCompl hp χ.conductor_ne_zero)

/-- The bad-prime factor `χ⁽ᵖ⁾(p)` is evaluated by the primitive character at the CRT unit
with components `1` and `p`. -/
theorem primeToPart_apply_prime [NeZero N] (hp : p.Prime) (χ : DirichletCharacter R N) :
    primeToPart p χ (p : ZMod (ordCompl[p] χ.conductor)) = χ.primitiveCharacter
      ((Nat.isExactDivisor_primePow (N := χ.conductor)).unitsEquivProd.symm
        (1, ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp χ.conductor_ne_zero)) :
          ZMod χ.conductor) := by
  simpa using primeToPart_apply_unit p χ
    (ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp χ.conductor_ne_zero))

end TauCeti
