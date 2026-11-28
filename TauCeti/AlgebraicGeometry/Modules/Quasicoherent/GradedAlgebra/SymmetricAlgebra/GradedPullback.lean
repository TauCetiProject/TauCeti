/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Adjunction
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Pullback

/-!
# Pullback of the graded symmetric algebra

For a morphism of schemes `g : X ⟶ Y` and a quasicoherent sheaf `F` on `Y`, the pullback of the
graded symmetric algebra of `F` is the graded symmetric algebra of the pullback of `F`:

`g^* (Sym F) ≅ Sym (g^* F)`

as graded quasicoherent algebras on `X`. This refines the isomorphism
`TauCeti.AlgebraicGeometry.pullbackSymmetricAlgebraIso` of the underlying (ungraded) quasicoherent
algebras: the morphism `Sym (g^* F) ⟶ g^* (Sym F)` of graded algebras extends the pullback of
`F ≅ Sym¹ F`, and its direct sum is the inverse of `pullbackSymmetricAlgebraIso`
(`toQuasicoherentAlgebra_map_symmetricAlgebraPullbackToPullback`), so it is an isomorphism because
a morphism of graded quasicoherent algebras whose direct sum is an isomorphism is one
(`GradedQuasicoherentAlgebra.isIso_of_isIso_toQuasicoherentAlgebra_map`).

## Main declarations

* `TauCeti.AlgebraicGeometry.pullbackGradedSymmetricAlgebraIso`: the isomorphism
  `g^* (Sym F) ≅ Sym (g^* F)` of graded quasicoherent algebras.
* `TauCeti.AlgebraicGeometry.symmetricAlgebraPullbackToPullback_degreeOne`: in degree one, the
  inverse `Sym (g^* F) ⟶ g^* (Sym F)` of this isomorphism is the pullback of `F ≅ Sym¹ F`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

open GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (F : QuasicoherentSheaf Y)

/-- The pullback of the identification `F ≅ Sym¹ F`, as a morphism from `g^* F` to the degree-one
component of `g^* (Sym F)`. -/
abbrev pullbackDegreeOneSymmetricAlgebra :
    (QuasicoherentSheaf.pullback g).obj F ⟶
      degreeOne.obj
        ((GradedQuasicoherentAlgebra.pullback g).obj ((gradedSymmetricAlgebra Y).obj F)) :=
  (QuasicoherentSheaf.pullback g).map ((gradedSymmetricAlgebraDegreeOneIso Y).inv.app F) ≫
    (pullbackDegreeIso g 1).inv.app _

/-- The morphism of graded quasicoherent algebras `Sym (g^* F) ⟶ g^* (Sym F)` extending the
pullback of the identification `F ≅ Sym¹ F`. -/
def symmetricAlgebraPullbackToPullback :
    (gradedSymmetricAlgebra X).obj ((QuasicoherentSheaf.pullback g).obj F) ⟶
      (GradedQuasicoherentAlgebra.pullback g).obj ((gradedSymmetricAlgebra Y).obj F) :=
  gradedSymmetricAlgebraLift (pullbackDegreeOneSymmetricAlgebra g F)

/-- On generators, the direct sum of `symmetricAlgebraPullbackToPullback`, followed by the
comparison `⨁ₙ g^* Symⁿ F ≅ g^* (⨁ₙ Symⁿ F)`, is the pullback of the inclusion `F ⟶ Sym F`. -/
theorem symmetricAlgebraι_comp_symmetricAlgebraPullbackToPullback :
    symmetricAlgebraι ((QuasicoherentSheaf.pullback g).obj F) ≫
        (toQuasicoherentAlgebra.map (symmetricAlgebraPullbackToPullback g F)).hom.hom.hom ≫
          ((pullbackToQuasicoherentAlgebraIso g).inv.app
            ((gradedSymmetricAlgebra Y).obj F)).hom.hom.hom =
      eqToHom (QuasicoherentSheaf.pullback_obj_obj g F) ≫
        (Scheme.Modules.pullback g).map (symmetricAlgebraι F) ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X g _).symm := by
  have h := congrArg InducedCategory.Hom.hom
    (gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift
      (pullbackDegreeOneSymmetricAlgebra g F))
  rw [symmetricAlgebraι_def, symmetricAlgebraι_def]
  rw [ObjectProperty.FullSubcategory.comp_hom, degree_map_hom] at h
  simp only [ObjectProperty.FullSubcategory.comp_hom, QuasicoherentSheaf.pullback_map_hom,
    pullbackDegreeIso_inv_app_hom] at h
  -- The goal composes `ιTotal` (typed in `X.Modules`) with the direct sums of morphisms of
  -- quasicoherent algebras (typed in `SheafOfModules X.ringCatSheaf`). These categories agree only
  -- up to unfolding `Scheme.Modules`, so already the first `Category.assoc` fails under `rw`, and
  -- every rewrite of this chain needs `erw`.
  erw [Category.assoc, Category.assoc, ιTotal_toQuasicoherentAlgebra_map_assoc, Category.assoc,
    ιTotal_pullbackToQuasicoherentAlgebraIso_inv_app, Functor.map_comp, Functor.map_comp,
    eqToHom_map]
  -- The same mismatch defeats `simp only [eqToHom_trans, ...]` on the remaining carrier
  -- transports, so they are cancelled for abstract modules, as in
  -- `pullbackToQuasicoherentAlgebraIso`: once every transport is substituted away, `key` is `h`
  -- post-composed with the pullback of the inclusion `ιTotal _ 1`.
  have key {P Q Q' R R' S T T' U V W : X.Modules} (a : P ⟶ Q) (e₁ : Q = Q') (θ : Q' ⟶ R)
      (e₂ : R = R') (e₃ : P = S) (m : S ⟶ T) (e₄ : T = T') (e₅ : T' = R') (e₆ : R = U)
      (n : U ⟶ V) (e₇ : V = W) (e₉ : T = U)
      (h : a ≫ eqToHom e₁ ≫ θ ≫ eqToHom e₂ = (eqToHom e₃ ≫ m ≫ eqToHom e₄) ≫ eqToHom e₅) :
      a ≫ eqToHom e₁ ≫ θ ≫ eqToHom e₆ ≫ n ≫ eqToHom e₇ =
        eqToHom e₃ ≫ (m ≫ eqToHom e₉ ≫ n) ≫ eqToHom e₇ := by
    subst e₁ e₃ e₄ e₇ e₉ e₂ e₅
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
    rw [reassoc_of% h]
  exact key _ _ _ _ _ _ _ _ _ _ _ _ h

/-- The direct sum of `symmetricAlgebraPullbackToPullback`, followed by the comparison
`⨁ₙ g^* Symⁿ F ≅ g^* (⨁ₙ Symⁿ F)`, is the inverse of `pullbackSymmetricAlgebraIso`. -/
theorem toQuasicoherentAlgebra_map_symmetricAlgebraPullbackToPullback :
    toQuasicoherentAlgebra.map (symmetricAlgebraPullbackToPullback g F) ≫
        (pullbackToQuasicoherentAlgebraIso g).inv.app ((gradedSymmetricAlgebra Y).obj F) =
      (pullbackSymmetricAlgebraIso g F).inv := by
  refine ObjectProperty.hom_ext _ (symmetricAlgebra_hom_ext ?_)
  rw [symmetricAlgebraι_comp_pullbackSymmetricAlgebraIso_inv]
  exact symmetricAlgebraι_comp_symmetricAlgebraPullbackToPullback g F

/-- The morphism `Sym (g^* F) ⟶ g^* (Sym F)` is an isomorphism, since its direct sum is. -/
instance isIso_symmetricAlgebraPullbackToPullback :
    IsIso (symmetricAlgebraPullbackToPullback g F) := by
  have : IsIso (toQuasicoherentAlgebra.map (symmetricAlgebraPullbackToPullback g F)) := by
    have h := toQuasicoherentAlgebra_map_symmetricAlgebraPullbackToPullback g F
    have h' : toQuasicoherentAlgebra.map (symmetricAlgebraPullbackToPullback g F) =
        (pullbackSymmetricAlgebraIso g F).inv ≫
          (pullbackToQuasicoherentAlgebraIso g).hom.app ((gradedSymmetricAlgebra Y).obj F) := by
      rw [← h, Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm
    rw [h']
    infer_instance
  exact isIso_of_isIso_toQuasicoherentAlgebra_map _

/-- **Pullback of the graded symmetric algebra.** For a morphism of schemes `g : X ⟶ Y` and a
quasicoherent sheaf `F` on `Y`, the pullback `g^* (Sym F)` of the graded symmetric algebra of `F`
is isomorphic, as a graded quasicoherent algebra on `X`, to the graded symmetric algebra
`Sym (g^* F)` of the pullback of `F`. -/
def pullbackGradedSymmetricAlgebraIso :
    (GradedQuasicoherentAlgebra.pullback g).obj ((gradedSymmetricAlgebra Y).obj F) ≅
      (gradedSymmetricAlgebra X).obj ((QuasicoherentSheaf.pullback g).obj F) :=
  (asIso (symmetricAlgebraPullbackToPullback g F)).symm

/-- The inverse of `pullbackGradedSymmetricAlgebraIso` is the comparison morphism
`symmetricAlgebraPullbackToPullback : Sym (g^* F) ⟶ g^* (Sym F)`. -/
@[simp]
theorem pullbackGradedSymmetricAlgebraIso_inv :
    (pullbackGradedSymmetricAlgebraIso g F).inv = symmetricAlgebraPullbackToPullback g F :=
  (rfl)

/-- In degree one, `symmetricAlgebraPullbackToPullback : Sym (g^* F) ⟶ g^* (Sym F)` (the inverse
of `pullbackGradedSymmetricAlgebraIso`) is the pullback of the identification `F ≅ Sym¹ F`, through
`g^* F ≅ Sym¹ (g^* F)`. -/
@[reassoc]
theorem symmetricAlgebraPullbackToPullback_degreeOne :
    (gradedSymmetricAlgebraDegreeOneIso X).inv.app _ ≫
        degreeOne.map (symmetricAlgebraPullbackToPullback g F) =
      pullbackDegreeOneSymmetricAlgebra g F :=
  gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift _

/-- Taking the direct sum of `pullbackGradedSymmetricAlgebraIso` recovers the isomorphism
`pullbackSymmetricAlgebraIso` of quasicoherent algebras, through the comparison
`g^* (⨁ₙ Symⁿ F) ≅ ⨁ₙ g^* Symⁿ F`. -/
theorem pullbackToQuasicoherentAlgebraIso_hom_app_comp_map_pullbackGradedSymmetricAlgebraIso_hom :
    (pullbackToQuasicoherentAlgebraIso g).hom.app ((gradedSymmetricAlgebra Y).obj F) ≫
        toQuasicoherentAlgebra.map (pullbackGradedSymmetricAlgebraIso g F).hom =
      (pullbackSymmetricAlgebraIso g F).hom := by
  rw [← cancel_epi (pullbackSymmetricAlgebraIso g F).inv, Iso.inv_hom_id,
    ← toQuasicoherentAlgebra_map_symmetricAlgebraPullbackToPullback, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, ← pullbackGradedSymmetricAlgebraIso_inv,
    Iso.inv_hom_id]
  exact CategoryTheory.Functor.map_id _ _

end

end TauCeti.AlgebraicGeometry
