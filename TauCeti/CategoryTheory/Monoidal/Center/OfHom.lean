/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.Center.Basic

/-!
# Half-braidings in a left rigid category are automatically invertible

A half-braiding on an object `X` of a monoidal category is a family of *isomorphisms*
`X ⊗ U ≅ U ⊗ X`, natural and monoidal in `U`. In a left rigid category invertibility is
automatic: a family of morphisms `γ U : X ⊗ U ⟶ U ⊗ X` that is natural and monoidal in `U` and
is the composite of the unitors at `U = 𝟙_ C` has inverses built from its own components.
For an exact pairing of `Y` and `U` (so that `Y` is a left dual of `U`), the inverse of `γ U` is

`U ⊗ X ⟶ U ⊗ X ⊗ Y ⊗ U ⟶ U ⊗ Y ⊗ X ⊗ U ⟶ X ⊗ U`,

which inserts the coevaluation of the pairing, moves `X` past `Y` with `γ Y`, and evaluates.
Naturality of `γ` at the evaluation and at the coevaluation, together with monoidality, reduces
the two composites to the zigzag identities of the pairing.

The unit condition cannot be dropped: in a preadditive monoidal category the zero family is
natural and monoidal. With it, a half-braiding can be specified by its forward components
alone, which is how half-braidings given by explicit formulas, such as sums over bases of
morphism spaces, are constructed.

## Main declarations

* `CategoryTheory.HalfBraiding.invOfHom`: the candidate inverse of `γ U`, with respect to an exact
  pairing of `Y` and `U`;
* `CategoryTheory.HalfBraiding.hom_comp_invOfHom` and
  `CategoryTheory.HalfBraiding.invOfHom_comp_hom`: it is a two-sided inverse;
* `CategoryTheory.HalfBraiding.ofHom`: the half-braiding with forward components `γ`, in a left
  rigid category;
* `CategoryTheory.HalfBraiding.β_inv_eq_invOfHom`: the inverse components of any half-braiding
  are computed from its forward components at left duals.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory.HalfBraiding

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Inverse

variable {X : C} (γ : ∀ U : C, X ⊗ U ⟶ U ⊗ X)

/-- The candidate inverse of `γ U : X ⊗ U ⟶ U ⊗ X`, with respect to an exact pairing of `Y` and
`U`: insert the coevaluation of the pairing, move `X` past `Y` with `γ Y`, and evaluate. -/
def invOfHom (Y U : C) [ExactPairing Y U] : U ⊗ X ⟶ X ⊗ U :=
  𝟙 _ ⊗≫ U ◁ X ◁ η_ Y U ⊗≫ U ◁ γ Y ▷ U ⊗≫ ε_ Y U ▷ X ▷ U ⊗≫ 𝟙 _

variable {γ} (unit : γ (𝟙_ C) = (ρ_ X).hom ≫ (λ_ X).inv)
  (monoidal : ∀ U U' : C,
    γ (U ⊗ U') = (α_ _ _ _).inv ≫ γ U ▷ U' ≫ (α_ _ _ _).hom ≫ U ◁ γ U' ≫ (α_ _ _ _).inv)
  (naturality : ∀ {U U' : C} (f : U ⟶ U'), X ◁ f ≫ γ U' = γ U ≫ f ▷ X)
include unit monoidal naturality

/-- `invOfHom γ Y U` is a left inverse of `γ U` for a unital, monoidal and natural family `γ`. -/
@[reassoc (attr := simp)]
theorem hom_comp_invOfHom (Y U : C) [ExactPairing Y U] : γ U ≫ invOfHom γ Y U = 𝟙 (X ⊗ U) := by
  have h := naturality (ε_ Y U)
  rw [monoidal, unit] at h
  simp only [Category.assoc] at h
  calc
    _ = 𝟙 _ ⊗≫ (γ U ▷ 𝟙_ C ≫ (U ⊗ X) ◁ η_ Y U) ⊗≫ U ◁ γ Y ▷ U ⊗≫ ε_ Y U ▷ X ▷ U ⊗≫ 𝟙 _ := by
      rw [invOfHom]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ U ◁ η_ Y U ⊗≫
          ((α_ _ _ _).inv ≫ γ U ▷ Y ≫ (α_ _ _ _).hom ≫ U ◁ γ Y ≫ (α_ _ _ _).inv ≫
            ε_ Y U ▷ X) ▷ U ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (U ◁ η_ Y U ⊗≫ ε_ Y U ▷ U) ⊗≫ 𝟙 _ := by
      rw [← h]; monoidal
    _ = _ := by rw [ExactPairing.coevaluation_evaluation'']; monoidal

/-- `invOfHom γ Y U` is a right inverse of `γ U` for a unital, monoidal and natural family `γ`. -/
@[reassoc (attr := simp)]
theorem invOfHom_comp_hom (Y U : C) [ExactPairing Y U] : invOfHom γ Y U ≫ γ U = 𝟙 (U ⊗ X) := by
  have h := naturality (η_ Y U)
  rw [monoidal, unit] at h
  calc
    _ = 𝟙 _ ⊗≫ U ◁ X ◁ η_ Y U ⊗≫ U ◁ γ Y ▷ U ⊗≫
          (ε_ Y U ▷ (X ⊗ U) ≫ 𝟙_ C ◁ γ U) ⊗≫ 𝟙 _ := by
      rw [invOfHom]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ (X ◁ η_ Y U ≫ (α_ _ _ _).inv ≫ γ Y ▷ U ≫ (α_ _ _ _).hom ≫ Y ◁ γ U ≫
          (α_ _ _ _).inv) ⊗≫ ε_ Y U ▷ U ▷ X ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ (U ◁ η_ Y U ⊗≫ ε_ Y U ▷ U) ▷ X ⊗≫ 𝟙 _ := by
      rw [h]; monoidal
    _ = _ := by rw [ExactPairing.coevaluation_evaluation'']; monoidal

/-- The half-braiding on `X` whose components are a family `γ U : X ⊗ U ⟶ U ⊗ X` that is natural
and monoidal in `U` and is the composite of the unitors at the unit object. In a left rigid
category such a family is automatically invertible, with inverse `invOfHom γ (ᘁU) U`. -/
def ofHom [LeftRigidCategory C] : HalfBraiding X where
  β U :=
    { hom := γ U
      inv := invOfHom γ (ᘁU) U
      hom_inv_id := hom_comp_invOfHom unit monoidal naturality (ᘁU) U
      inv_hom_id := invOfHom_comp_hom unit monoidal naturality (ᘁU) U }
  monoidal := monoidal
  naturality := naturality

/-- The components of `HalfBraiding.ofHom` are the given family. -/
@[simp]
theorem ofHom_β_hom [LeftRigidCategory C] (U : C) :
    ((ofHom unit monoidal naturality).β U).hom = γ U :=
  (rfl)

/-- The inverse components of `HalfBraiding.ofHom` are computed from the family at left duals. -/
theorem ofHom_β_inv [LeftRigidCategory C] (U : C) :
    ((ofHom unit monoidal naturality).β U).inv = invOfHom γ (ᘁU) U :=
  (rfl)

end Inverse

/-- The inverse components of a half-braiding are computed from its forward components: for an
exact pairing of `Y` and `U`, the inverse of `b.β U` is `invOfHom` of the components of `b`. -/
theorem β_inv_eq_invOfHom {X : C} (b : HalfBraiding X) (Y U : C) [ExactPairing Y U] :
    (b.β U).inv = invOfHom (fun V ↦ (b.β V).hom) Y U := by
  rw [← cancel_epi (b.β U).hom, Iso.hom_inv_id,
    hom_comp_invOfHom b.β_tensorUnit_hom b.monoidal b.naturality]

end CategoryTheory.HalfBraiding
