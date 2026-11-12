/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.Induction.Projection

/-!
# Induction and twisting by a linear character

For a group homomorphism `φ : G →* H`, a linear character `χ : H →* kˣ` and a representation `ρ`
of `G`, inducing the twist of `ρ` by the restriction `χ ∘ φ` is the same as twisting the induced
representation by `χ`:

`Ind_φ (χ ∘ φ ⊗ ρ) ≃ χ ⊗ Ind_φ ρ`.

This is the projection formula `TauCeti.indProjectionLEquiv` applied to the one-dimensional
representation of `χ`, with both lines absorbed by
`Representation.tprodOfLinearCharacterEquivCharTwist`. The first absorption happens inside the
induced representation, so it needs induction to act on equivalences of representations; that
is the unbundled form of Mathlib's `Rep.indMap`, recorded here for intertwining maps and
equivalences.

## Main definitions

* `Representation.IntertwiningMap.ind`: induction of an intertwining map along `φ`.
* `Representation.Equiv.ind`: induction of an equivalence of representations along `φ`.
* `TauCeti.indCharTwistEquiv`: **`Ind_φ (charTwist (χ ∘ φ) ρ) ≃ charTwist χ (Ind_φ ρ)`**.

## Main statements

* `Representation.IntertwiningMap.ind_mk`, `Representation.Equiv.ind_mk`: induced maps act on the
  coefficient of each generator `⟦h ⊗ₜ a⟧`.
* `Representation.IntertwiningMap.ind_id`, `Representation.IntertwiningMap.ind_comp`: induction
  of intertwining maps is functorial.
* `TauCeti.indCharTwistEquiv_mk`: the twist comparison sends `⟦h ⊗ₜ a⟧` to `χ(h)⁻¹ ⟦h ⊗ₜ a⟧`.

## Implementation notes

As in `TauCeti/RepresentationTheory/Induction/Projection.lean`, the generator lemmas are stated
with the reducible abbreviation `Representation.IndV.mk`, which `simp` unfolds, so they are not
`simp` lemmas and are applied by `rw`.
-/

public section

open TensorProduct

namespace Representation

variable {k G H A B : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H)
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  {ρ : Representation k G A} {σ : Representation k G B}

namespace IntertwiningMap

/-- **Induction of an intertwining map** along `φ : G →* H`: the map `⟦h ⊗ₜ a⟧ ↦ ⟦h ⊗ₜ f a⟧`.
This is the unbundled form of `Rep.indMap`. -/
noncomputable def ind (f : IntertwiningMap ρ σ) :
    IntertwiningMap (Representation.ind φ ρ) (Representation.ind φ σ) where
  toLinearMap := Coinvariants.map _ _ ⟨f.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.2, LinearMap.map_comp_lTensor]⟩
  isIntertwining' _ := by ext; simp

theorem ind_mk (f : IntertwiningMap ρ σ) (h : H) (a : A) :
    f.ind φ (IndV.mk φ ρ h a) = IndV.mk φ σ h (f a) :=
  (rfl)

@[simp]
theorem ind_id : (IntertwiningMap.id ρ).ind φ = IntertwiningMap.id (Representation.ind φ ρ) :=
  IntertwiningMap.ext <| IndV.hom_ext φ _ fun _ => rfl

theorem ind_comp {C : Type*} [AddCommGroup C] [Module k C] {τ : Representation k G C}
    (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f.comp g).ind φ = (f.ind φ).comp (g.ind φ) :=
  IntertwiningMap.ext <| IndV.hom_ext φ _ fun _ => rfl

end IntertwiningMap

namespace Equiv

/-- **Induction of an equivalence of representations** along `φ : G →* H`: the equivalence
`⟦h ⊗ₜ a⟧ ↦ ⟦h ⊗ₜ e a⟧`, with inverse induced by `e.symm`. -/
noncomputable def ind (e : Equiv ρ σ) : Equiv (Representation.ind φ ρ) (Representation.ind φ σ) :=
  .mk (LinearEquiv.ofLinearMap (e.toIntertwiningMap.ind φ).toLinearMap
      (e.symm.toIntertwiningMap.ind φ).toLinearMap
      (by ext; simp [IntertwiningMap.ind])
      (by ext; simp [IntertwiningMap.ind]))
    (e.toIntertwiningMap.ind φ).isIntertwining'

theorem ind_mk (e : Equiv ρ σ) (h : H) (a : A) :
    e.ind φ (IndV.mk φ ρ h a) = IndV.mk φ σ h (e a) :=
  (rfl)

theorem ind_symm_mk (e : Equiv ρ σ) (h : H) (b : B) :
    (e.ind φ).symm (IndV.mk φ σ h b) = IndV.mk φ ρ h (e.symm b) :=
  (rfl)

end Equiv

end Representation

namespace TauCeti

open Representation

variable {k G H A : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H)
  [AddCommGroup A] [Module k A] (χ : H →* kˣ) (ρ : Representation k G A)

/-- The line of `χ` restricted along `φ`, absorbed into `ρ` on the right: the
equivalence `Representation.tprodOfLinearCharacterEquivCharTwist` for `χ ∘ φ`, stated for the
restricted representation `(ofLinearCharacter χ).comp φ` that the projection formula produces. -/
private noncomputable def tprodCompEquivCharTwist :
    (ρ.tprod ((ofLinearCharacter χ).comp φ)).Equiv (charTwist (χ.comp φ) ρ) :=
  .mk (TensorProduct.rid k A) fun g => LinearMap.ext fun x => by
    rw [ofLinearCharacter_comp, LinearMap.comp_apply, LinearMap.comp_apply, charTwist_apply_apply]
    exact rid_tprod_ofLinearCharacter_apply (χ.comp φ) ρ g x

/-- The underlying linear equivalence of `TauCeti.indCharTwistEquiv`: absorb the line of `χ ∘ φ`
inside the induced representation, apply the projection formula `TauCeti.indProjectionLEquiv`, and
absorb the line of `χ` outside. -/
private noncomputable def indCharTwistLinearEquiv :
    IndV φ (charTwist (χ.comp φ) ρ) ≃ₗ[k] IndV φ ρ :=
  ((tprodCompEquivCharTwist φ χ ρ).symm.ind φ).toLinearEquiv ≪≫ₗ
    indProjectionLEquiv φ ρ (ofLinearCharacter χ) ≪≫ₗ TensorProduct.rid k _

private theorem indCharTwistLinearEquiv_mk (h : H) (a : A) :
    indCharTwistLinearEquiv φ χ ρ (IndV.mk φ _ h a) = ((χ h⁻¹ : kˣ) : k) • IndV.mk φ ρ h a := by
  rw [indCharTwistLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.ind_mk]
  have h1 : (tprodCompEquivCharTwist φ χ ρ).symm a = a ⊗ₜ[k] (1 : k) := rfl
  rw [h1, indProjectionLEquiv_apply, indProjectionHom_apply_mk, TensorProduct.rid_tmul,
    ofLinearCharacter_apply, mul_one]

/-- **Induction commutes with twisting by a linear character**: inducing the twist of `ρ` by the
restriction `χ ∘ φ` gives the twist of the induced representation by `χ`. It is the projection
formula `TauCeti.indProjectionLEquiv` for the line of `χ`, with the line absorbed on both sides,
and sends `⟦h ⊗ₜ a⟧` to `χ(h)⁻¹ ⟦h ⊗ₜ a⟧` (`TauCeti.indCharTwistEquiv_mk`). -/
noncomputable def indCharTwistEquiv :
    (ind φ (charTwist (χ.comp φ) ρ)).Equiv (charTwist χ (ind φ ρ)) :=
  .mk (indCharTwistLinearEquiv φ χ ρ) fun h₁ =>
    IndV.hom_ext φ _ fun h => LinearMap.ext fun a => by
      conv_lhs => rw [LinearMap.comp_apply, LinearMap.comp_apply]
      conv_rhs => rw [LinearMap.comp_apply, LinearMap.comp_apply]
      rw [ind_mk, LinearEquiv.coe_coe, indCharTwistLinearEquiv_mk,
        indCharTwistLinearEquiv_mk, charTwist_apply_apply, map_smul, ind_mk, smul_smul,
        ← Units.val_mul, ← map_mul, mul_inv_rev, inv_inv]

/-- The twist comparison on generators: `⟦h ⊗ₜ a⟧ ↦ χ(h)⁻¹ ⟦h ⊗ₜ a⟧`. The factor `χ(h)⁻¹` is the
twist of the coefficient `a` that the projection formula moves out of the induced
representation. -/
theorem indCharTwistEquiv_mk (h : H) (a : A) :
    indCharTwistEquiv φ χ ρ (IndV.mk φ _ h a) = ((χ h⁻¹ : kˣ) : k) • IndV.mk φ ρ h a :=
  indCharTwistLinearEquiv_mk φ χ ρ h a

end TauCeti
