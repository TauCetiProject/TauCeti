/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GL2.Cuspidal.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Complex
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Irreducibility of the cuspidal character of `GL₂(𝔽_q)`

The cuspidal virtual character attached to a character `θ` of the multiplicative group of a
quadratic extension is the difference of two induced characters.  Combining their self-pairings
with the mutual pairing computed here gives values `q`, `q - 1`, and `q - 1` when `θ` is not fixed
by the `q`-power map.  Bilinearity therefore gives norm `1` for the difference.

Since the difference is already known to be a virtual character, the norm-one criterion identifies
it, up to sign, with an irreducible character.  Its positive value `q - 1` at the identity rules out
the negative sign.  The resulting representation is the cuspidal representation of `GL₂(𝔽_q)`.

## Main results

* `TauCeti.characterPairing_GL2CuspidalVirtualCharacter_self`: the cuspidal virtual character has
  norm `1` for `θ^q ≠ θ` and a nontrivial additive character.
* `TauCeti.GL2CuspidalVirtualCharacter_mem_irreducibleCharacters`: the virtual character is an
  irreducible character.
* `TauCeti.GL2Cuspidal`: the corresponding irreducible representation, using Mathlib's canonical
  primitive additive character internally.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for `GL(2)`*,
  Springer (2006), §6, for the induced-character difference construction and its irreducibility.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] [Finite F]
variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

variable [Fintype F]

section

variable [DecidableEq F]

private theorem scalarUnipotent_elliptic_pairing_term (theta : Eˣ →* ℂˣ)
    (psi : AddChar F ℂ) (a : Fˣ) (t : Multiplicative F) :
    (GL2ScalarUnipotentRep F
        (theta.comp (Units.map (algebraMap F E : F →* E))) psi).character
        (GL2ScalarUnipotent.mulEquiv F (a, t)) *
      (GL2EllipticInduction F E hE theta).character
        (((GL2ScalarUnipotent.mulEquiv F (a, t) : GL2ScalarUnipotent F) :
          GL (Fin 2) F)⁻¹) =
      if t = 1 then (Fintype.card F : ℂ) * ((Fintype.card F : ℂ) - 1) else 0 := by
  rw [character_GL2ScalarUnipotentRep, GL2ScalarUnipotent.linearChar_mulEquiv]
  have hinv :
      (((GL2ScalarUnipotent.mulEquiv F (a, t) : GL2ScalarUnipotent F) :
          GL (Fin 2) F)⁻¹) =
        ((GL2ScalarUnipotent.mulEquiv F (a⁻¹, t⁻¹) : GL2ScalarUnipotent F) :
          GL (Fin 2) F) := by
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [hinv, GL2ScalarUnipotent.coe_mulEquiv_apply_eq_jordanGL]
  split_ifs with ht
  · subst t
    have ht_one : Multiplicative.toAdd (1 : Multiplicative F) = 0 := rfl
    rw [inv_one, ht_one, mul_zero, jordanGL_zero, character_GL2EllipticInduction_scalar]
    simp only [MonoidHom.comp_apply, map_one, map_inv, Units.val_inv_eq_inv_val]
    have htheta : (theta ((Units.map (algebraMap F E : F →* E)) a) : ℂ) ≠ 0 :=
      Units.ne_zero _
    field_simp [htheta]
    simp only [mul_one]
    rw [Nat.card_eq_fintype_card]
  · have ht0 : Multiplicative.toAdd t⁻¹ ≠ 0 := by
      simpa using ht
    rw [character_GL2EllipticInduction_jordanGL _ _ _ _ a⁻¹
      (mul_ne_zero a⁻¹.ne_zero ht0), mul_zero]

end

open scoped Classical in
/-- **The mutual pairing of the scalar--unipotent and elliptic inductions is `q - 1`.** Only
the scalar elements of the scalar--unipotent subgroup contribute, because the elliptic induction
vanishes on nontrivial Jordan blocks. -/
@[simp]
theorem characterPairing_GL2ScalarUnipotentInduction_GL2EllipticInduction
    (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ) :
    ClassFunction.characterPairing
        (ClassFunction.ofFDRep
          (GL2ScalarUnipotentInduction F
            (theta.comp (Units.map (algebraMap F E : F →* E))) psi))
        (ClassFunction.ofFDRep (GL2EllipticInduction F E hE theta)) =
      Fintype.card F - 1 := by
  classical
  let hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.card_pos.ne')
  rw [GL2ScalarUnipotentInduction_def]
  rw [← ClassFunction.ind_ofFDRep, characterPairing_ind hG]
  rw [ClassFunction.characterPairing_apply]
  simp only [ClassFunction.comap_subtype_ofFDRep,
    ClassFunction.ofFDRep_apply, character_resFDRep]
  rw [← (GL2ScalarUnipotent.mulEquiv F).toEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Subgroup.coe_inv]
  simp_rw [scalarUnipotent_elliptic_pairing_term hE theta psi]
  -- Only `t = 1` contributes. Thus the subgroup sum is `|Fˣ| · q(q - 1)`; dividing by
  -- `|Fˣ × F| = q(q - 1)` leaves `q - 1`.
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [natCard_gl2ScalarUnipotent, Nat.card_eq_fintype_card, Fintype.card_units]
  push_cast [Fintype.one_lt_card.le]
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩).ne'
  have hq1 : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast Fintype.one_lt_card.ne')
  field_simp [hq, hq1]

open scoped Classical in
/-- **The cuspidal virtual character has norm one in general position.** -/
@[simp]
theorem characterPairing_GL2CuspidalVirtualCharacter_self (theta : Eˣ →* ℂˣ)
    {psi : AddChar F ℂ} (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Fintype.card F)) ≠ theta) :
    ClassFunction.characterPairing (GL2CuspidalVirtualCharacter F E hE theta psi)
      (GL2CuspidalVirtualCharacter F E hE theta psi) = 1 := by
  classical
  rw [GL2CuspidalVirtualCharacter_def]
  simp only [map_sub, LinearMap.sub_apply]
  have hcross : ClassFunction.characterPairing
      (ClassFunction.ofFDRep (GL2EllipticInduction F E hE theta))
      (ClassFunction.ofFDRep
        (GL2ScalarUnipotentInduction F
          (theta.comp (Units.map (algebraMap F E : F →* E))) psi)) =
        Fintype.card F - 1 := by
    rw [ClassFunction.characterPairing_symm]
    exact characterPairing_GL2ScalarUnipotentInduction_GL2EllipticInduction hE theta psi
  rw [characterPairing_GL2ScalarUnipotentInduction_self
      (theta.comp (Units.map (algebraMap F E : F →* E))) hpsi,
    characterPairing_GL2ScalarUnipotentInduction_GL2EllipticInduction hE theta psi,
    hcross, characterPairing_GL2EllipticInduction_self F E hE theta htheta]
  ring

variable [DecidableEq F]

omit [DecidableEq F] in
/-- **The cuspidal virtual character is an irreducible character in general position.** The
norm-one criterion gives an irreducible character up to sign, and its degree `q - 1 > 0` fixes the
positive sign. -/
theorem GL2CuspidalVirtualCharacter_mem_irreducibleCharacters (theta : Eˣ →* ℂˣ)
    {psi : AddChar F ℂ} (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (GL2CuspidalVirtualCharacter F E hE theta psi).1 ∈
      irreducibleCharacters ℂ (GL (Fin 2) F) := by
  classical
  let _ : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  obtain ⟨i, hi⟩ := exists_eq_irreducibleCharacter_or_neg
    (GL2CuspidalVirtualCharacter_mem_virtualCharacters hE theta psi)
    (characterPairing_GL2CuspidalVirtualCharacter_self hE theta hpsi (by
      simpa only [Nat.card_eq_fintype_card] using htheta))
  rcases hi with hi | hi
  · rw [hi]
    exact irreducibleCharacter_mem ℂ i
  · exfalso
    have hval := congrFun hi (1 : GL (Fin 2) F)
    rw [GL2CuspidalVirtualCharacter_apply_one, Pi.neg_apply, irreducibleCharacter_one] at hval
    have hsum :
        (((Fintype.card F - 1) + characterDegree ℂ i : ℕ) : ℂ) = 0 := by
      push_cast [Fintype.one_lt_card.le]
      linear_combination hval
    rw [Nat.cast_eq_zero] at hsum
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have hdeg := characterDegree_pos ℂ i
    omega

omit [DecidableEq F] in
private theorem exists_gl2Cuspidal (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ)
    (hpsi : psi ≠ 1) (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    ∃ (n : ℕ) (rho : Representation ℂ (GL (Fin 2) F) (Fin n → ℂ)),
      rho.IsIrreducible ∧
        rho.character = (GL2CuspidalVirtualCharacter F E hE theta psi).1 :=
  mem_irreducibleCharacters_iff.mp
    (GL2CuspidalVirtualCharacter_mem_irreducibleCharacters hE theta hpsi htheta)

omit [DecidableEq F] in
private noncomputable def gl2CuspidalDimension (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ)
    (hpsi : psi ≠ 1) (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) : ℕ :=
  (exists_gl2Cuspidal hE theta psi hpsi htheta).choose

omit [DecidableEq F] in
private noncomputable def gl2CuspidalRepresentation (theta : Eˣ →* ℂˣ)
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    Representation ℂ (GL (Fin 2) F) (Fin (gl2CuspidalDimension hE theta psi hpsi htheta) → ℂ) :=
  (exists_gl2Cuspidal hE theta psi hpsi htheta).choose_spec.choose

omit [DecidableEq F] in
private theorem gl2CuspidalRepresentation_spec (theta : Eˣ →* ℂˣ) (psi : AddChar F ℂ)
    (hpsi : psi ≠ 1) (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (gl2CuspidalRepresentation hE theta psi hpsi htheta).IsIrreducible ∧
      (gl2CuspidalRepresentation hE theta psi hpsi htheta).character =
        (GL2CuspidalVirtualCharacter F E hE theta psi).1 :=
  (exists_gl2Cuspidal hE theta psi hpsi htheta).choose_spec.choose_spec

omit [DecidableEq F] in
/-- **The cuspidal representation of `GL₂(𝔽_q)` attached to a general-position character
`θ : Eˣ → ℂˣ`.** The auxiliary additive character is Mathlib's canonical primitive complex
character of `F`, so it does not appear in the public cuspidal datum. -/
noncomputable def GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) : FDRep ℂ (GL (Fin 2) F) :=
  FDRep.of (gl2CuspidalRepresentation hE theta
    (AddChar.FiniteField.primitiveChar_to_Complex F)
    (AddChar.FiniteField.primitiveChar_to_Complex_ne_one F) htheta)

omit [DecidableEq F] in
/-- The character of `TauCeti.GL2Cuspidal` is the cuspidal virtual character from which it was
constructed. -/
@[simp]
theorem character_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (GL2Cuspidal hE theta htheta).character =
      (GL2CuspidalVirtualCharacter F E hE theta
        (AddChar.FiniteField.primitiveChar_to_Complex F)).1 := by
  exact (gl2CuspidalRepresentation_spec hE theta
    (AddChar.FiniteField.primitiveChar_to_Complex F)
    (AddChar.FiniteField.primitiveChar_to_Complex_ne_one F) htheta).2

omit [DecidableEq F] in
/-- The cuspidal representation has degree `q - 1`. -/
@[simp]
theorem finrank_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    Module.finrank ℂ (GL2Cuspidal hE theta htheta) = Fintype.card F - 1 := by
  have hchar := congrFun (character_GL2Cuspidal hE theta htheta)
    (1 : GL (Fin 2) F)
  rw [FDRep.char_one, GL2CuspidalVirtualCharacter_apply_one] at hchar
  apply Nat.cast_injective (R := ℂ)
  push_cast [Fintype.one_lt_card.le]
  exact hchar

omit [DecidableEq F] in
/-- The character of the cuspidal representation has value `q - 1` at the identity. -/
theorem character_one_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    (GL2Cuspidal hE theta htheta).character 1 = (Fintype.card F : ℂ) - 1 := by
  rw [character_GL2Cuspidal, GL2CuspidalVirtualCharacter_apply_one]

omit [DecidableEq F] in
/-- The cuspidal representation attached to a general-position character is simple. -/
theorem simple_GL2Cuspidal (theta : Eˣ →* ℂˣ)
    (htheta : theta.comp (powMonoidHom (Nat.card F)) ≠ theta) :
    CategoryTheory.Simple (GL2Cuspidal hE theta htheta) := by
  let _ : Representation.IsIrreducible (GL2Cuspidal hE theta htheta).ρ := by
    rw [GL2Cuspidal, FDRep.of_ρ']
    exact (gl2CuspidalRepresentation_spec hE theta
      (AddChar.FiniteField.primitiveChar_to_Complex F)
      (AddChar.FiniteField.primitiveChar_to_Complex_ne_one F) htheta).1
  exact FDRep.simple_of_isIrreducible _

end TauCeti
