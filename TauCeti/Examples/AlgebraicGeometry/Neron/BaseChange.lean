/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.AlgebraicGeometry.Neron.BaseChange
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.EqToHom

/-!
# Examples for the smooth base change of Néron models

These are the checks of NeronModelsAndSemistableAbelianVarieties §1.10 on
`TauCeti.AlgebraicGeometry.Neron.NeronModel.baseChange`:

* **Base change along the identity.** For `S' = S`, the canonical isomorphism
  `M.model ×_S S ≅ M.model` identifies the base change of a Néron model `M` with `M`: it is
  compatible with the generic isomorphisms, up to the identification `A ×_η η ≅ A`.
* **Fibres of the base change.** For a point `s' ⟶ S'` lying over a point `s ⟶ S` through
  `t : s' ⟶ s`, the fibre of the base-changed model at `s'` is the base change along `t` of the
  fibre of the model at `s`. For an extension `R → R'` of discrete valuation rings with
  `Spec R' ⟶ Spec R` étale, this says that the special fibre of the base-changed model is the base
  change of the special fibre along the extension `κ(R) → κ(R')` of residue fields; the statement
  below needs only a local homomorphism of local rings whose `Spec` map is smooth.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Neron

namespace TauCeti.NeronBaseChangeExamples

universe u

section Identity

variable {η S : Scheme.{u}} {j : η ⟶ S} {A : Over η}

/-- Base change along `𝟙 η` and then along the composite `𝟙 η ≫ j` is base change along `j`. -/
@[reassoc]
private theorem pullbackComp_id_hom_app_comp_pullbackId (B : Over S) :
    (Over.pullbackComp (𝟙 η) j).hom.app B ≫ Over.pullbackId.hom.app ((Over.pullback j).obj B) =
      eqToHom (by simp) := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.pullbackComp, Over.pullbackId]
    simpa using (eqToHom_comp_pullback_fst _ (Category.id_comp j) _).symm
  · simp only [Over.pullbackComp, Over.pullbackId]
    simpa using (eqToHom_comp_pullback_snd _ (Category.id_comp j) _).symm

/-- The generic isomorphism of a base change along the identity, for an arbitrary `S`-scheme
`X` and isomorphism `e : X ×_S η ≅ A`. -/
private theorem pullbackId_comp_genericIso (X : Over S) (e : (Over.pullback j).obj X ≅ A) :
    (Over.pullback j).map (Over.pullbackId.hom.app X) ≫ e.hom =
      ((Over.pullbackComp j (𝟙 S)).inv.app X ≫ eqToHom (by simp) ≫
        (Over.pullbackComp (𝟙 η) j).hom.app X ≫ (Over.pullback (𝟙 η)).map e.hom) ≫
          Over.pullbackId.hom.app A := by
  simp only [Category.assoc]
  rw [Over.pullbackId.hom.naturality e.hom, Functor.id_map,
    pullbackComp_id_hom_app_comp_pullbackId_assoc, eqToHom_trans_assoc,
    Over.pullbackComp_id_inv_app_comp_eqToHom_assoc]

/-- **Base change along the identity.** The canonical isomorphism
`Over.pullbackId.app M.model : M.model ×_S S ≅ M.model` from the base change of `M` along `𝟙 S`
to `M` is compatible with the generic isomorphisms, through `Over.pullbackId.app A`. -/
example (M : NeronModel j A) :
    (Over.pullback j).map (Over.pullbackId.hom.app M.model) ≫ M.genericIso.hom =
      (M.baseChange (IsPullback.id_vert j)).genericIso.hom ≫ Over.pullbackId.hom.app A := by
  rw [NeronModel.baseChange_genericIso_hom]
  simp only [NatTrans.comp_app, eqToHom_app]
  exact pullbackId_comp_genericIso M.model M.genericIso

end Identity

section Fibre

variable {η S η' S' s s' : Scheme.{u}} {j : η ⟶ S} {g : S' ⟶ S} {j' : η' ⟶ S'} {g' : η' ⟶ η}
  {A : Over η}

/-- **Fibres of a base change.** If `i' : s' ⟶ S'` lies over `i : s ⟶ S` through `t : s' ⟶ s`,
the fibre at `i'` of the base change of `X` along `g : S' ⟶ S` is the base change along `t` of the
fibre of `X` at `i`. -/
def fibreBaseChangeIso (X : Over S) {i : s ⟶ S} {i' : s' ⟶ S'} {t : s' ⟶ s}
    (h : i' ≫ g = t ≫ i) :
    (Over.pullback i').obj ((Over.pullback g).obj X) ≅
      (Over.pullback t).obj ((Over.pullback i).obj X) :=
  (Over.pullbackComp i' g).symm.app X ≪≫ eqToIso (by simp only [h]) ≪≫
    (Over.pullbackComp t i).app X

/-- The fibre isomorphism commutes with the projections to `X`. -/
theorem fibreBaseChangeIso_hom_left_fst (X : Over S) {i : s ⟶ S} {i' : s' ⟶ S'} {t : s' ⟶ s}
    (h : i' ≫ g = t ≫ i) :
    (fibreBaseChangeIso X h).hom.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [fibreBaseChangeIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom,
    Over.comp_left, Over.eqToHom_left, Category.assoc]
  have h₁ : ((Over.pullbackComp t i).hom.app X).left ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst X.hom (t ≫ i) := by
    simp [Over.pullbackComp]
  have h₂ : ((Over.pullbackComp i' g).inv.app X).left ≫ pullback.fst X.hom (i' ≫ g) =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
    simp [Over.pullbackComp]
  rw [h₁, eqToHom_comp_pullback_fst X.hom h, h₂]

/-- **Fibres of the base change of a Néron model.** The fibre at `i'` of the base change of a
Néron model `M` along a smooth `g : S' ⟶ S` is the base change along `t` of the fibre of `M` at
`i`. -/
example [Smooth g] (sq : IsPullback j' g' g j) (M : NeronModel j A) {i : s ⟶ S} {i' : s' ⟶ S'}
    {t : s' ⟶ s} (h : i' ≫ g = t ≫ i) :
    (Over.pullback i').obj (M.baseChange sq).model ≅
      (Over.pullback t).obj ((Over.pullback i).obj M.model) :=
  fibreBaseChangeIso M.model h

end Fibre

section SpecialFibre

variable {η η' : Scheme.{u}} {R R' : Type u} [CommRing R] [CommRing R'] [IsLocalRing R]
  [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ]
  {j : η ⟶ Spec (.of R)} {j' : η' ⟶ Spec (.of R')} {g' : η' ⟶ η} {A : Over η}

/-- `Spec κ(R') ⟶ Spec R' ⟶ Spec R` is `Spec κ(R') ⟶ Spec κ(R) ⟶ Spec R`. -/
theorem specMap_residue_comp_specMap :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R')) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    IsLocalRing.ResidueField.map_comp_residue]

/-- **Special fibre of the base change.** For a local homomorphism `R → R'` of local rings with
smooth `Spec R' ⟶ Spec R` (for instance an extension of discrete valuation rings with étale `Spec`
map), the
special fibre of the base change of a Néron model `M` over `Spec R` is the base change of the
special fibre of `M` along `Spec κ(R') ⟶ Spec κ(R)`. -/
example [Smooth (Spec.map (CommRingCat.ofHom φ))]
    (sq : IsPullback j' g' (Spec.map (CommRingCat.ofHom φ)) j) (M : NeronModel j A) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R')))).obj
        (M.baseChange sq).model ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)))).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj M.model) :=
  fibreBaseChangeIso M.model (specMap_residue_comp_specMap φ)

end SpecialFibre

end TauCeti.NeronBaseChangeExamples
