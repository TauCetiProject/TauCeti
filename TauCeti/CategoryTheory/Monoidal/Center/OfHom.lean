/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Half-braidings from natural monoidal families in a left rigid category

A half-braiding on an object `X` of a monoidal category `C` is a family of *isomorphisms*
`X ⊗ U ≅ U ⊗ X`, natural and monoidal in `U`. When every object of `C` has a left dual, the
invertibility is automatic: a family of morphisms `σ U : X ⊗ U ⟶ U ⊗ X` which is natural and
monoidal in `U`, and whose component at the unit is the composite of the unitors, consists of
isomorphisms. The inverse of `σ U` is

`U ⊗ X ⟶ U ⊗ X ⊗ ᘁU ⊗ U ⟶ U ⊗ ᘁU ⊗ X ⊗ U ⟶ X ⊗ U`,

which inserts the coevaluation of `ᘁU` and `U`, moves `X` past `ᘁU` with `σ (ᘁU)`, and evaluates
`U ⊗ ᘁU`. That the two composites are identities follows from monoidality of `σ` at `U ⊗ ᘁU` and
at `ᘁU ⊗ U`, naturality of `σ` at the evaluation and the coevaluation, the unit condition, and the
zigzag identities. In other words, the lax centre of a left rigid monoidal category is its
Drinfeld centre.

This is how half-braidings are built when the components are given by formulas whose inverses are
not apparent, such as the canonical half-braiding of the object `⨁ S, S ⊗ X ⊗ Sᘁ` of a fusion
category.

## Main declarations

* `CategoryTheory.HalfBraiding.ofHom`: the half-braiding whose components are a natural, monoidal
  and unital family `σ U : X ⊗ U ⟶ U ⊗ X`, in a left rigid category;
* `CategoryTheory.HalfBraiding.ofHom_β_hom` and `CategoryTheory.HalfBraiding.ofHom_β_inv`: its
  components and their inverses.

## References

* B. Day, R. Street, *Centres of monoidal categories of functors*, in: Categories in algebra,
  geometry and mathematical physics, Contemp. Math. **431** (2007), 187–202
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

namespace HalfBraiding

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X : C}
  (σ : ∀ U, X ⊗ U ⟶ U ⊗ X)

/-- The inverse of the component `σ U` of a natural, monoidal and unital family: insert the
coevaluation of `ᘁU` and `U`, move `X` past `ᘁU` with `σ (ᘁU)`, and evaluate `U ⊗ ᘁU`. -/
def invOfHom (U : C) [HasLeftDual U] : U ⊗ X ⟶ X ⊗ U :=
  𝟙 _ ⊗≫ (U ⊗ X) ◁ η_ (ᘁU) U ⊗≫ U ◁ σ (ᘁU) ▷ U ⊗≫ ε_ (ᘁU) U ▷ (X ⊗ U) ⊗≫ 𝟙 _

section Inverse

variable {σ}
  (unit : σ (𝟙_ C) = (ρ_ X).hom ≫ (λ_ X).inv)
  (monoidal : ∀ U U', σ (U ⊗ U') =
    (α_ _ _ _).inv ≫ σ U ▷ U' ≫ (α_ _ _ _).hom ≫ U ◁ σ U' ≫ (α_ _ _ _).inv)
  (naturality : ∀ {U U'} (f : U ⟶ U'), X ◁ f ≫ σ U' = σ U ≫ f ▷ X)

include unit monoidal naturality

/-- `HalfBraiding.invOfHom σ U` is a right inverse of `σ U`. -/
theorem hom_comp_invOfHom (U : C) [HasLeftDual U] : σ U ≫ invOfHom σ U = 𝟙 (X ⊗ U) := by
  have hε := naturality (ε_ (ᘁU : C) U)
  rw [monoidal, unit] at hε
  simp only [Category.assoc] at hε
  calc
    _ = 𝟙 _ ⊗≫ (X ⊗ U) ◁ η_ (ᘁU : C) U ⊗≫ σ U ▷ ((ᘁU : C) ⊗ U) ⊗≫ U ◁ σ (ᘁU : C) ▷ U ⊗≫
          ε_ (ᘁU : C) U ▷ (X ⊗ U) ⊗≫ 𝟙 _ := by
      rw [invOfHom]
      calc
        _ = 𝟙 _ ⊗≫ (σ U ▷ 𝟙_ C ≫ (U ⊗ X) ◁ η_ (ᘁU : C) U) ⊗≫ U ◁ σ (ᘁU : C) ▷ U ⊗≫
              ε_ (ᘁU : C) U ▷ (X ⊗ U) ⊗≫ 𝟙 _ := by monoidal
        _ = _ := by rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ (X ⊗ U) ◁ η_ (ᘁU : C) U ⊗≫
          ((α_ _ _ _).inv ≫ σ U ▷ (ᘁU : C) ≫ (α_ _ _ _).hom ≫ U ◁ σ (ᘁU : C) ≫ (α_ _ _ _).inv ≫
            ε_ (ᘁU : C) U ▷ X) ▷ U ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ X ◁ (U ◁ η_ (ᘁU : C) U ⊗≫ ε_ (ᘁU : C) U ▷ U) ⊗≫ 𝟙 _ := by
      rw [← hε]; monoidal
    _ = 𝟙 _ := by
      rw [ExactPairing.coevaluation_evaluation'']; monoidal

/-- `HalfBraiding.invOfHom σ U` is a left inverse of `σ U`. -/
theorem invOfHom_comp_hom (U : C) [HasLeftDual U] : invOfHom σ U ≫ σ U = 𝟙 (U ⊗ X) := by
  have hη := naturality (η_ (ᘁU : C) U)
  rw [monoidal, unit] at hη
  calc
    _ = 𝟙 _ ⊗≫ (U ⊗ X) ◁ η_ (ᘁU : C) U ⊗≫ U ◁ σ (ᘁU : C) ▷ U ⊗≫ (U ⊗ (ᘁU : C)) ◁ σ U ⊗≫
          ε_ (ᘁU : C) U ▷ (U ⊗ X) ⊗≫ 𝟙 _ := by
      rw [invOfHom]
      calc
        _ = 𝟙 _ ⊗≫ (U ⊗ X) ◁ η_ (ᘁU : C) U ⊗≫ U ◁ σ (ᘁU : C) ▷ U ⊗≫
              (ε_ (ᘁU : C) U ▷ (X ⊗ U) ≫ 𝟙_ C ◁ σ U) ⊗≫ 𝟙 _ := by monoidal
        _ = _ := by rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ (X ◁ η_ (ᘁU : C) U ≫ (α_ _ _ _).inv ≫ σ (ᘁU : C) ▷ U ≫ (α_ _ _ _).hom ≫
          (ᘁU : C) ◁ σ U ≫ (α_ _ _ _).inv) ⊗≫ ε_ (ᘁU : C) U ▷ (U ⊗ X) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (U ◁ η_ (ᘁU : C) U ⊗≫ ε_ (ᘁU : C) U ▷ U) ▷ X ⊗≫ 𝟙 _ := by
      rw [hη]; monoidal
    _ = 𝟙 _ := by
      rw [ExactPairing.coevaluation_evaluation'']; monoidal

end Inverse

variable [LeftRigidCategory C] {σ}
  (unit : σ (𝟙_ C) = (ρ_ X).hom ≫ (λ_ X).inv)
  (monoidal : ∀ U U', σ (U ⊗ U') =
    (α_ _ _ _).inv ≫ σ U ▷ U' ≫ (α_ _ _ _).hom ≫ U ◁ σ U' ≫ (α_ _ _ _).inv)
  (naturality : ∀ {U U'} (f : U ⟶ U'), X ◁ f ≫ σ U' = σ U ≫ f ▷ X)

/-- In a left rigid category, a family of morphisms `σ U : X ⊗ U ⟶ U ⊗ X`, natural and monoidal in
`U` and given at the unit by the unitors, is a half-braiding: each `σ U` is invertible, with
inverse `HalfBraiding.invOfHom σ U`. -/
def ofHom : HalfBraiding X where
  β U :=
    { hom := σ U
      inv := invOfHom σ U
      hom_inv_id := hom_comp_invOfHom unit monoidal naturality U
      inv_hom_id := invOfHom_comp_hom unit monoidal naturality U }
  monoidal := monoidal
  naturality := naturality

/-- The components of `HalfBraiding.ofHom` are the given morphisms. -/
@[simp]
theorem ofHom_β_hom (U : C) : ((ofHom unit monoidal naturality).β U).hom = σ U :=
  (rfl)

/-- The inverses of the components of `HalfBraiding.ofHom` are given by
`HalfBraiding.invOfHom`. -/
theorem ofHom_β_inv (U : C) :
    ((ofHom unit monoidal naturality).β U).inv = invOfHom σ U :=
  (rfl)

end HalfBraiding

end CategoryTheory
