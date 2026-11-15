/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Induction.Basic
public import TauCeti.RepresentationTheory.Induction.Projection

/-!
# Induction and twisting by a linear character

For a group homomorphism `φ : G →* H`, a linear character `χ : H →* kˣ` and a representation `ρ`
of `G`, inducing the twist of `ρ` by the restriction `χ ∘ φ` is the same as twisting the induced
representation by `χ`:

`Ind_φ (χ ∘ φ ⊗ ρ) ≃ χ ⊗ Ind_φ ρ`.

This is the projection formula `TauCeti.indProjectionEquiv` applied to the one-dimensional
representation of `χ`, with both lines absorbed by
`Representation.tprodOfLinearCharacterEquivCharTwist`. The first absorption happens inside the
induced representation, through `Representation.Equiv.ind`.

## Main definitions

* `TauCeti.indCharTwistEquiv`: **`Ind_φ (charTwist (χ ∘ φ) ρ) ≃ charTwist χ (Ind_φ ρ)`**.

## Main statements

* `TauCeti.indCharTwistEquiv_mk`, `TauCeti.indCharTwistEquiv_symm_mk`: the twist comparison sends
  `⟦h ⊗ₜ a⟧` to `χ(h)⁻¹ ⟦h ⊗ₜ a⟧`, and its inverse sends it to `χ(h) ⟦h ⊗ₜ a⟧`.

## Implementation notes

As in `TauCeti/RepresentationTheory/Induction/Projection.lean`, the generator lemmas are stated
with the reducible abbreviation `Representation.IndV.mk`, which `simp` unfolds, so they are not
`simp` lemmas and are applied by `rw`.
-/

public section

open TensorProduct Representation

namespace TauCeti

variable {k G H A : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H)
  [AddCommGroup A] [Module k A] (χ : H →* kˣ) (ρ : Representation k G A)

/-- **Induction commutes with twisting by a linear character**: inducing the twist of `ρ` by the
restriction `χ ∘ φ` gives the twist of the induced representation by `χ`. It is the projection
formula `TauCeti.indProjectionEquiv` for the line of `χ`, with the line absorbed on both sides by
`Representation.tprodOfLinearCharacterEquivCharTwist`, and sends `⟦h ⊗ₜ a⟧` to
`χ(h)⁻¹ ⟦h ⊗ₜ a⟧` (`TauCeti.indCharTwistEquiv_mk`). -/
noncomputable def indCharTwistEquiv :
    (ind φ (charTwist (χ.comp φ) ρ)).Equiv (charTwist χ (ind φ ρ)) :=
  ((((tprodOfLinearCharacterEquivCharTwist (χ.comp φ) ρ).symm.trans
      -- the restricted line produced by the projection formula is the line of `χ ∘ φ`
      (.mk (LinearEquiv.refl k _) fun _ => by rw [ofLinearCharacter_comp]; rfl :
        (ρ.tprod (ofLinearCharacter (χ.comp φ))).Equiv (ρ.tprod ((ofLinearCharacter χ).comp φ))))
      |>.ind φ).trans (indProjectionEquiv φ ρ (ofLinearCharacter χ))).trans
    (tprodOfLinearCharacterEquivCharTwist χ (ind φ ρ))

/-- The twist comparison on generators: `⟦h ⊗ₜ a⟧ ↦ χ(h)⁻¹ ⟦h ⊗ₜ a⟧`. The factor `χ(h)⁻¹` is the
twist of the coefficient `a` that the projection formula moves out of the induced
representation. -/
theorem indCharTwistEquiv_mk (h : H) (a : A) :
    indCharTwistEquiv φ χ ρ (IndV.mk φ _ h a) = ((χ h⁻¹ : kˣ) : k) • IndV.mk φ ρ h a := by
  rw [indCharTwistEquiv, Representation.Equiv.trans_apply, Representation.Equiv.trans_apply,
    Representation.Equiv.ind_mk, Representation.Equiv.trans_apply,
    tprodOfLinearCharacterEquivCharTwist_symm_apply, Representation.Equiv.mk_apply,
    LinearEquiv.refl_apply, indProjectionEquiv_apply, indProjectionHom_apply_mk,
    tprodOfLinearCharacterEquivCharTwist_tmul, ofLinearCharacter_apply, mul_one]

/-- The inverse twist comparison on generators: `⟦h ⊗ₜ a⟧ ↦ χ(h) ⟦h ⊗ₜ a⟧`. -/
theorem indCharTwistEquiv_symm_mk (h : H) (a : A) :
    (indCharTwistEquiv φ χ ρ).symm (IndV.mk φ ρ h a) = ((χ h : kˣ) : k) • IndV.mk φ _ h a := by
  rw [← (indCharTwistEquiv φ χ ρ).symm_apply_apply (((χ h : kˣ) : k) • IndV.mk φ _ h a),
    map_smul, indCharTwistEquiv_mk, smul_smul, map_inv, Units.mul_inv, one_smul]

end TauCeti
