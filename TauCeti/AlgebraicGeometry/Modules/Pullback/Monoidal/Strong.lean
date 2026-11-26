/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Monoidal
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Identity

/-!
# Strong symmetric monoidal pullback of modules on schemes

For every morphism of schemes `f : X ⟶ Y` and all sheaves of `𝒪_Y`-modules `M` and `N`, the
canonical oplax tensor comparison `δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism
(`AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ`), with no flatness, finiteness, or
quasi-coherence hypothesis on `M` or `N` (Stacks Project, Tag 01CD).

Combined with the unit isomorphism `f^* 𝒪_Y ≅ 𝒪_X` (`Scheme.Modules.pullbackObjUnitIso`), this
equips `Scheme.Modules.pullback f` with a strong symmetric monoidal structure
(`AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
`AlgebraicGeometry.Scheme.Modules.pullbackBraided`). The canonical identity and composition
isomorphisms `Scheme.Modules.pullbackId` and `Scheme.Modules.pullbackComp` respect this strong
monoidal structure (`AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackId_hom` and
`AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackComp_hom`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ`: invertibility of the oplax tensor
  comparison for pullback of arbitrary `𝒪_Y`-modules along a scheme morphism;
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` and
  `AlgebraicGeometry.Scheme.Modules.pullbackBraided`: strong symmetric monoidal structure on
  `Scheme.Modules.pullback f`, with `pullback_μ` and `pullback_ε`;
* `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackId_hom` and
  `AlgebraicGeometry.Scheme.Modules.isMonoidal_pullbackComp_hom`: monoidality of
  `Scheme.Modules.pullbackId` and `Scheme.Modules.pullbackComp`, with unit and tensor formulas
  `pullback_id_ε`, `pullback_id_μ`, `pullback_comp_ε`, and `pullback_comp_μ`.

## References

* The Stacks Project, *Sheaves of Modules*, Tag 01CD (pullback of tensor products).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry TauCeti

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

/-- **Invertibility of the pullback tensor comparison.** For every morphism of schemes `f : X ⟶ Y`
and all `𝒪_Y`-modules `M` and `N`, the canonical oplax tensor comparison
`δ : f^* (M ⊗ N) ⟶ f^* M ⊗ f^* N` is an isomorphism, with no flatness, finiteness, or
quasi-coherence assumption on `M` or `N` (Stacks Project, Tag 01CD). -/
instance isIso_pullback_δ (f : X ⟶ Y) (M N : Y.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  TauCeti.SheafOfModules.isIso_pullback_δ f.toRingCatSheafHom M N

/-- Pullback of sheaves of modules along a morphism of schemes is strong monoidal, with inverse
comparisons inherited from `Scheme.Modules.pullbackOplaxMonoidal`. -/
@[instance_reducible]
def pullbackMonoidal (f : X ⟶ Y) : (pullback f).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (pullback f)

attribute [instance] pullbackMonoidal

/-- Pullback of sheaves of modules along a morphism of schemes is strong symmetric monoidal. -/
@[instance_reducible]
def pullbackBraided (f : X ⟶ Y) : (pullback f).Braided :=
  (pullbackPushforwardAdjunction f).leftAdjointBraided

attribute [instance] pullbackBraided

/-- The strong monoidal tensor map of scheme-module pullback inverts the canonical oplax tensor
comparison. -/
theorem pullback_μ (f : X ⟶ Y) (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) M N = inv (Functor.OplaxMonoidal.δ (pullback f) M N) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ (pullback f) M N)

/-- The strong monoidal unit map of scheme-module pullback inverts `pullbackObjUnitIso`. -/
@[simp]
theorem pullback_ε (f : X ⟶ Y) :
    Functor.LaxMonoidal.ε (pullback f) = (pullbackObjUnitIso f).inv :=
  (Iso.comp_hom_eq_id _).mp
    ((congrArg (_ ≫ ·) (pullback_η f).symm).trans (Functor.Monoidal.ε_η (pullback f)))

/-- Mathlib's identity isomorphism `Scheme.Modules.pullbackId` respects the strong monoidal
structure on pullback. -/
instance isMonoidal_pullbackId_hom (X : Scheme.{u}) :
    NatTrans.IsMonoidal (pullbackId X).hom where
  unit := by
    rw [← pullbackObjUnitIso_id X, ← pullback_η (𝟙 X)]
    exact Functor.Monoidal.ε_η (pullback (𝟙 X))
  tensor M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback (𝟙 X)) M N)]
    simp only [Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id,
      pullback_id_δ]

/-- The strong monoidal unit map of identity pullback inverts `Scheme.Modules.pullbackId` at
`𝒪_X`. -/
theorem pullback_id_ε (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε (pullback (𝟙 X)) = (pullbackId X).inv.app (𝟙_ X.Modules) := by
  rw [← cancel_mono ((pullbackId X).hom.app (𝟙_ X.Modules))]
  have hu := NatTrans.IsMonoidal.unit (τ := (pullbackId X).hom)
  exact hu.trans (by simp)

/-- The strong monoidal tensor map of identity pullback intertwines `Scheme.Modules.pullbackId`
with the tensor product of identity comparisons. -/
@[reassoc (attr := simp)]
theorem pullback_id_μ (X : Scheme.{u}) (M N : X.Modules) :
    Functor.LaxMonoidal.μ (pullback (𝟙 X)) M N ≫ (pullbackId X).hom.app (M ⊗ N) =
      (pullbackId X).hom.app M ⊗ₘ (pullbackId X).hom.app N :=
  (NatTrans.IsMonoidal.tensor (τ := (pullbackId X).hom) M N).trans (by simp)

/-- Mathlib's composition isomorphism `Scheme.Modules.pullbackComp` respects the strong monoidal
structures on pullbacks along scheme morphisms. -/
instance isMonoidal_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (pullbackComp f g).hom where
  unit := by
    rw [← cancel_mono (Functor.OplaxMonoidal.η (pullback (f ≫ g))), Category.assoc]
    have hη :
        (pullbackComp f g).hom.app (𝟙_ Z.Modules) ≫
            Functor.OplaxMonoidal.η (pullback (f ≫ g)) =
          Functor.OplaxMonoidal.η (pullback g ⋙ pullback f) := by
      rw [Functor.OplaxMonoidal.comp_η,
        ← cancel_epi ((pullbackComp f g).inv.app (𝟙_ Z.Modules)), Iso.inv_hom_id_app_assoc]
      simp only [pullback_η]
      exact (pullbackObjUnitIso_comp f g).symm
    rw [hη]
    exact (Functor.Monoidal.ε_η (pullback g ⋙ pullback f)).trans
      (Functor.Monoidal.ε_η (pullback (f ≫ g))).symm
  tensor M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback g ⋙ pullback f) M N),
      ← cancel_mono (Functor.OplaxMonoidal.δ (pullback (f ≫ g)) M N)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    rw [Functor.OplaxMonoidal.comp_δ,
      ← cancel_epi ((pullbackComp f g).inv.app (M ⊗ N)), Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc] using pullback_comp_δ f g M N

/-- The strong monoidal unit map of a composite pullback is the composite of the unit maps through
`Scheme.Modules.pullbackComp`. -/
@[reassoc]
theorem pullback_comp_ε (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.LaxMonoidal.ε (pullback f) ≫ (pullback f).map (Functor.LaxMonoidal.ε (pullback g)) ≫
        (pullbackComp f g).hom.app (𝟙_ Z.Modules) =
      Functor.LaxMonoidal.ε (pullback (f ≫ g)) := by
  have hu := NatTrans.IsMonoidal.unit (τ := (pullbackComp f g).hom)
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc] at hu
  exact hu

/-- The strong monoidal tensor map of a composite pullback is the composite of the tensor maps
through `Scheme.Modules.pullbackComp`. -/
@[reassoc (attr := simp)]
theorem pullback_comp_μ (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    Functor.LaxMonoidal.μ (pullback f) _ _ ≫
        (pullback f).map (Functor.LaxMonoidal.μ (pullback g) M N) ≫
        (pullbackComp f g).hom.app (M ⊗ N) =
      ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) ≫
        Functor.LaxMonoidal.μ (pullback (f ≫ g)) M N := by
  have ht := NatTrans.IsMonoidal.tensor (τ := (pullbackComp f g).hom) M N
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc] at ht
  exact ht

end

end AlgebraicGeometry.Scheme.Modules
