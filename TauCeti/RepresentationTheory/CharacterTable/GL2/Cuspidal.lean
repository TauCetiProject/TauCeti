/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2EllipticInduction` is the subtrahend of the construction below.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.EllipticInduction
-- `TauCeti.GL2ScalarUnipotentInduction` is the minuend of the construction below.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.ScalarUnipotentInduction
-- `TauCeti.ClassFunction.eq_of_forall_gl2NormalForm` proves the two symmetries below.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.ClassFunction
-- `TauCeti.virtualCharacters` occurs in the statement that the difference is a virtual character.
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
-- Non-public: the `q`-power map on a finite field and on a quadratic extension of it is used only
-- inside the proofs of the two symmetries.
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The cuspidal virtual character of `GL₂(𝔽_q)`

Let `F` be a finite field with `q` elements, `E/F` a degree-`2` extension, `θ` a character of `Eˣ`
and `ψ` a nontrivial additive character of `F`.  The **cuspidal virtual character**

`TauCeti.GL2CuspidalVirtualCharacter F E hE θ ψ
  = χ(Ind_{Z U}^{GL₂(F)} (θ|_{Fˣ} ⊗ ψ)) - χ(Ind_{Eˣ}^{GL₂(F)} θ)`

is the difference of the two induced characters computed in
`TauCeti/RepresentationTheory/CharacterTable/GL2/ScalarUnipotentInduction.lean` and
`TauCeti/RepresentationTheory/CharacterTable/GL2/EllipticInduction.lean`.  The subtracted degrees
are `[GL₂(F) : Z U] = q² - 1` and `[GL₂(F) : Eˣ] = q (q - 1)`, so the difference has degree `q - 1`,
and its four values on the conjugacy classes of `GL₂(F)` are

* `(q - 1) θ(a)` at the central scalar `a`;
* `0` on the split regular semisimple classes;
* `-θ(a)` at a nontrivial Jordan block with eigenvalue `a`;
* `-(θ(u) + θ(u^q))` at the elliptic class of `u : Eˣ` outside `F`.

Classically, for `θ` in general position -- that is, `θ^q ≠ θ` -- these are the character values of
the cuspidal (discrete series) representation attached to `θ`.  That identification is not made
here, and neither the construction of the representation nor the norm computation showing the
difference to be `±` an irreducible character is carried out: what is established below is that the
difference is a virtual character (`TauCeti.GL2CuspidalVirtualCharacter_mem_virtualCharacters`)
with those four values and degree `q - 1`, together with the two symmetries the parametrization
rests on.

## The two symmetries

The four values do not mention `ψ`, so the difference does not depend on which nontrivial additive
character was used to build it: the `q - 1` summands of the Gelfand-Graev term at a Jordan block
are the values of `ψ` on `Fˣ`, and those sum to `-1` whatever nontrivial `ψ` is.  Nor does it
change when `θ` is replaced by `θ^q`: the `q`-power map fixes `Fˣ`, so the central and Jordan
values are unchanged, and on the elliptic classes it exchanges the two summands `θ(u)` and
`θ(u^q)`.  It is this second symmetry that makes the cuspidal series parametrized by the orbits
`{θ, θ^q}` rather than by the characters themselves.

Both are proved by evaluating at the four normal forms, which is enough by
`TauCeti.ClassFunction.eq_of_forall_gl2NormalForm`.

## Main definitions

* `TauCeti.GL2CuspidalVirtualCharacter`: the difference of the two induced characters.

## Main results

* `TauCeti.GL2CuspidalVirtualCharacter_def` and `TauCeti.coe_GL2CuspidalVirtualCharacter`: the
  defining equation, as class functions and as functions on `GL₂(F)`.
* `TauCeti.GL2CuspidalVirtualCharacter_apply_scalar`,
  `TauCeti.GL2CuspidalVirtualCharacter_apply_diagGL`,
  `TauCeti.GL2CuspidalVirtualCharacter_apply_jordanGL` and
  `TauCeti.GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom`: **the four values**.
* `TauCeti.GL2CuspidalVirtualCharacter_apply_one`: **the degree is `q - 1`**.
* `TauCeti.GL2CuspidalVirtualCharacter_mem_virtualCharacters`: the difference is a virtual
  character.
* `TauCeti.GL2CuspidalVirtualCharacter_eq_of_addChar_ne_one` and
  `TauCeti.GL2CuspidalVirtualCharacter_comp_powMonoidHom`: **the two symmetries**, in `ψ` and in
  `θ`.

## Implementation notes

The four values and the degree are `simp` lemmas, as the character values of the two inductions
(`TauCeti.character_GL2ScalarUnipotentInduction_scalar`,
`TauCeti.character_GL2EllipticInduction_scalar` and their siblings) are; the defining equations
`TauCeti.GL2CuspidalVirtualCharacter_def`, `TauCeti.coe_GL2CuspidalVirtualCharacter` and
`TauCeti.GL2CuspidalVirtualCharacter_apply` are not, since rewriting with them would undo the
values.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

variable (F : Type*) [Field F] [Fintype F] (E : Type*) [Field E] [Algebra F E]
  (hE : Module.finrank F E = 2)

/-- **The cuspidal virtual character of `GL₂(𝔽_q)`** attached to a character `θ` of `Eˣ` and an
additive character `ψ` of `F`: the character induced from the scalar--unipotent subgroup by
`(a, t) ↦ θ(a) ψ(t)`, less the character induced from the non-split torus by `θ`.  For `ψ`
nontrivial and `θ` in general position it is, classically, the character of the cuspidal
representation attached to `θ`; that identification is not proved here. -/
noncomputable def GL2CuspidalVirtualCharacter (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    ClassFunction ℂ (GL (Fin 2) F) :=
  ClassFunction.ofFDRep
      (GL2ScalarUnipotentInduction F (θ.comp (Units.map (algebraMap F E : F →* E))) ψ) -
    ClassFunction.ofFDRep (GL2EllipticInduction F E hE θ)

variable {F E}

/-- The defining equation of the cuspidal virtual character, as class functions: it is the
difference of the class functions of the two induced representations. -/
theorem GL2CuspidalVirtualCharacter_def (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    GL2CuspidalVirtualCharacter F E hE θ ψ =
      ClassFunction.ofFDRep
          (GL2ScalarUnipotentInduction F (θ.comp (Units.map (algebraMap F E : F →* E))) ψ) -
        ClassFunction.ofFDRep (GL2EllipticInduction F E hE θ) :=
  (rfl)

/-- The defining equation of the cuspidal virtual character, as functions on `GL₂(F)`: it is the
difference of the two induced characters. -/
theorem coe_GL2CuspidalVirtualCharacter (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 =
      (GL2ScalarUnipotentInduction F (θ.comp (Units.map (algebraMap F E : F →* E))) ψ).character -
        (GL2EllipticInduction F E hE θ).character := by
  rw [GL2CuspidalVirtualCharacter_def, Submodule.coe_sub]
  exact congrArg₂ (· - ·) (funext (ClassFunction.ofFDRep_apply _))
    (funext (ClassFunction.ofFDRep_apply _))

/-- The defining equation of the cuspidal virtual character, pointwise. -/
theorem GL2CuspidalVirtualCharacter_apply (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) (g : GL (Fin 2) F) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 g =
      (GL2ScalarUnipotentInduction F (θ.comp (Units.map (algebraMap F E : F →* E))) ψ).character g -
        (GL2EllipticInduction F E hE θ).character g := by
  rw [coe_GL2CuspidalVirtualCharacter, Pi.sub_apply]

/-- **The cuspidal virtual character is a virtual character**, being a difference of two
characters.  This is what makes the classical norm-`1` test available for it. -/
theorem GL2CuspidalVirtualCharacter_mem_virtualCharacters (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 ∈ virtualCharacters ℂ (GL (Fin 2) F) := by
  rw [coe_GL2CuspidalVirtualCharacter]
  exact sub_mem (character_mem_virtualCharacters _) (character_mem_virtualCharacters _)

/-! ### The four values -/

/-- **The cuspidal virtual character at a central element** is `(q - 1) θ(a)`: the two induced
characters contribute `(q² - 1) θ(a)` and `q (q - 1) θ(a)`. -/
@[simp]
theorem GL2CuspidalVirtualCharacter_apply_scalar (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) (a : Fˣ) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      ((Fintype.card F : ℂ) - 1) * θ (Units.map (algebraMap F E : F →* E) a) := by
  rw [GL2CuspidalVirtualCharacter_apply, character_GL2ScalarUnipotentInduction_scalar,
    character_GL2EllipticInduction_scalar, MonoidHom.comp_apply, Nat.card_eq_fintype_card]
  ring

/-- **The cuspidal virtual character vanishes on the split regular semisimple classes**, both
induced characters doing so. -/
@[simp]
theorem GL2CuspidalVirtualCharacter_apply_diagGL (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ)
    {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 (diagGL t) = 0 := by
  rw [GL2CuspidalVirtualCharacter_apply, character_GL2ScalarUnipotentInduction_diagGL _ _ ht,
    character_GL2EllipticInduction_diagGL _ _ _ _ ht, sub_zero]

/-- **The cuspidal virtual character at a nontrivial Jordan block** is `-θ(a)`: only the
Gelfand-Graev term contributes, and its value there is `-θ(a)` for every nontrivial `ψ`. -/
@[simp]
theorem GL2CuspidalVirtualCharacter_apply_jordanGL (θ : Eˣ →* ℂˣ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (a : Fˣ) {b : F} (hb : b ≠ 0) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 (jordanGL a b) =
      -(θ (Units.map (algebraMap F E : F →* E) a) : ℂ) := by
  rw [GL2CuspidalVirtualCharacter_apply, character_GL2ScalarUnipotentInduction_jordanGL _ _ hψ a hb,
    character_GL2EllipticInduction_jordanGL _ _ _ _ a hb, sub_zero, MonoidHom.comp_apply]

/-- **The cuspidal virtual character at an elliptic element** is `-(θ(u) + θ(u^q))`: only the
torus term contributes, and it contributes the two torus elements conjugate to the given one. -/
@[simp]
theorem GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ)
    {u : Eˣ} (hu : (u : E) ∉ Set.range (algebraMap F E)) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 (GL2NonSplitTorusHom F E hE u) =
      -((θ u : ℂ) + θ (u ^ Fintype.card F)) := by
  rw [GL2CuspidalVirtualCharacter_apply,
    character_GL2ScalarUnipotentInduction_gl2NonSplitTorusHom _ _ hE hu,
    character_GL2EllipticInduction_gl2NonSplitTorusHom _ _ _ _ hu, zero_sub,
    Nat.card_eq_fintype_card]

/-- **The cuspidal virtual character has degree `q - 1`**, the difference `(q² - 1) - q (q - 1)`
of the two inducing indices.  It is the dimension the cuspidal representation attached to `θ`
classically has. -/
@[simp]
theorem GL2CuspidalVirtualCharacter_apply_one (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    (GL2CuspidalVirtualCharacter F E hE θ ψ).1 1 = (Fintype.card F : ℂ) - 1 := by
  have hone : (1 : GL (Fin 2) F) = Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : Fˣ) :=
    (map_one _).symm
  rw [hone, GL2CuspidalVirtualCharacter_apply_scalar]
  simp

/-! ### The two symmetries -/

/-- **The cuspidal virtual character does not depend on the nontrivial additive character** used
to build its Gelfand-Graev term: the four values do not mention `ψ`. -/
theorem GL2CuspidalVirtualCharacter_eq_of_addChar_ne_one (θ : Eˣ →* ℂˣ) {ψ ψ' : AddChar F ℂ}
    (hψ : ψ ≠ 1) (hψ' : ψ' ≠ 1) :
    GL2CuspidalVirtualCharacter F E hE θ ψ = GL2CuspidalVirtualCharacter F E hE θ ψ' := by
  refine ClassFunction.eq_of_forall_gl2NormalForm E hE (fun a => ?_) (fun a b hab => ?_)
    (fun a => ?_) (fun x hx => ?_)
  · rw [GL2CuspidalVirtualCharacter_apply_scalar, GL2CuspidalVirtualCharacter_apply_scalar]
  · rw [GL2CuspidalVirtualCharacter_apply_diagGL _ _ _ (by simpa using hab),
      GL2CuspidalVirtualCharacter_apply_diagGL _ _ _ (by simpa using hab)]
  · rw [GL2CuspidalVirtualCharacter_apply_jordanGL _ _ hψ a one_ne_zero,
      GL2CuspidalVirtualCharacter_apply_jordanGL _ _ hψ' a one_ne_zero]
  · rw [GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ _ hx,
      GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ _ hx]

/-- **The cuspidal virtual character of `θ^q` is that of `θ`**: the `q`-power map fixes `Fˣ`, so
the central and Jordan values are unchanged, and it is an involution on `Eˣ` exchanging the two
elliptic summands.  So the cuspidal series is parametrized by the orbits `{θ, θ^q}`. -/
theorem GL2CuspidalVirtualCharacter_comp_powMonoidHom (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    GL2CuspidalVirtualCharacter F E hE (θ.comp (powMonoidHom (Fintype.card F))) ψ =
      GL2CuspidalVirtualCharacter F E hE θ ψ := by
  -- the restriction of `θ^q` to `Fˣ` is that of `θ`, so the Gelfand-Graev terms coincide
  have hcomp : (θ.comp (powMonoidHom (Fintype.card F))).comp
      (Units.map (algebraMap F E : F →* E)) = θ.comp (Units.map (algebraMap F E : F →* E)) :=
    MonoidHom.ext fun a => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, powMonoidHom_apply,
        ← Nat.card_eq_fintype_card, FiniteField.units_map_algebraMap_pow_natCard]
  refine ClassFunction.eq_of_forall_gl2NormalForm E hE (fun a => ?_) (fun a b hab => ?_)
    (fun a => ?_) (fun x hx => ?_)
  · rw [GL2CuspidalVirtualCharacter_apply, GL2CuspidalVirtualCharacter_apply, hcomp,
      character_GL2EllipticInduction_scalar, character_GL2EllipticInduction_scalar,
      MonoidHom.comp_apply, powMonoidHom_apply, ← Nat.card_eq_fintype_card,
      FiniteField.units_map_algebraMap_pow_natCard]
  · rw [GL2CuspidalVirtualCharacter_apply_diagGL _ _ _ (by simpa using hab),
      GL2CuspidalVirtualCharacter_apply_diagGL _ _ _ (by simpa using hab)]
  · rw [GL2CuspidalVirtualCharacter_apply, GL2CuspidalVirtualCharacter_apply, hcomp,
      character_GL2EllipticInduction_jordanGL _ _ _ _ a one_ne_zero,
      character_GL2EllipticInduction_jordanGL _ _ _ _ a one_ne_zero]
  · rw [GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ _ hx,
      GL2CuspidalVirtualCharacter_apply_gl2NonSplitTorusHom _ _ _ hx,
      MonoidHom.comp_apply, MonoidHom.comp_apply, powMonoidHom_apply, powMonoidHom_apply,
      ← Nat.card_eq_fintype_card, FiniteField.units_pow_natCard_pow_natCard hE x, add_comm]

end TauCeti
