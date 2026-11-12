/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivedTensor
public import TauCeti.Algebra.Homology.ModuleCat.KFlat.Resolution
import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# Independence of K-flat tensor models

A quasi-isomorphism between K-flat complexes of modules remains a quasi-isomorphism after
tensoring on either side with any complex, and therefore also under termwise left tensoring by any
module. Thus the endofunctor `CochainComplex.kFlatTensor` of the unbounded derived category sends
quasi-isomorphisms in its K-flat input to natural isomorphisms. The comparison is induced by the
specified map of models, so its identity and composition laws are those of
`CochainComplex.kFlatTensorMap`.

The arbitrary factor is resolved by a K-flat complex, and the Koszul braiding exchanges
the two factors. No boundedness, freeness or termwise flatness is required of either input.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 064L and 064M.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

/-- Tensoring on the right with a K-flat complex preserves quasi-isomorphisms. -/
instance quasiIso_tensorHom_id (A : CochainComplex (ModuleCat.{u} R) ℤ) [A.IsKFlat]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (tensorHom f (𝟙 A)) := by
  rw [HomologicalComplex.tensorHom, ← whiskerRight_eq_mapBifunctorMap]
  have : QuasiIso (A ◁ f) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (tensorHom (𝟙 A) f))
  exact quasiIso_of_arrow_mk_iso (A ◁ f) (f ▷ A)
    (Arrow.isoMk (β_ A K) (β_ A L) (BraidedCategory.braiding_naturality_right A f).symm)

/-- A quasi-isomorphism between K-flat complexes stays a quasi-isomorphism after tensoring
with an arbitrary, possibly unbounded, complex. -/
instance quasiIso_tensorHom_id_of_isKFlat
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (tensorHom f (𝟙 A)) := by
  obtain ⟨P, p, hp, hP⟩ := A.exists_quasiIso_isKFlat_moduleCat
  have : QuasiIso p := hp
  have : P.IsKFlat := hP
  have h : tensorHom (𝟙 K) p ≫ tensorHom f (𝟙 A) =
      tensorHom f (𝟙 P) ≫ tensorHom (𝟙 L) p := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  apply (quasiIso_iff_comp_left (tensorHom (𝟙 K) p) _).1
  rw [h]
  infer_instance

/-- A quasi-isomorphism between K-flat complexes of `R`-modules remains a quasi-isomorphism after
tensoring on the left with any, possibly unbounded, complex `A`. -/
instance quasiIso_id_tensorHom_of_isKFlat (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKFlat] [Q.IsKFlat]
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (tensorHom (𝟙 A) f) := by
  rw [HomologicalComplex.tensorHom, ← whiskerLeft_eq_mapBifunctorMap]
  have : QuasiIso (f ▷ A) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 A)))
  exact quasiIso_of_arrow_mk_iso (f ▷ A) (A ◁ f)
    (Arrow.isoMk (β_ P A) (β_ Q A) (BraidedCategory.braiding_naturality_left f A).symm)

/-- Tensoring a quasi-isomorphism on the left with a K-flat complex via `◁` is a
quasi-isomorphism. -/
instance quasiIso_whiskerLeft (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKFlat]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso (P ◁ f) := by
  rw [whiskerLeft_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom (𝟙 P) f))

/-- Tensoring a quasi-isomorphism on the right with a K-flat complex via `▷` is a
quasi-isomorphism. -/
instance quasiIso_whiskerRight (Q : CochainComplex (ModuleCat.{u} R) ℤ) [Q.IsKFlat]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (f ▷ Q) := by
  rw [whiskerRight_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 Q)))

/-- Whiskering a quasi-isomorphism between K-flat complexes on the right by an arbitrary complex
gives a quasi-isomorphism. -/
instance quasiIso_whiskerRight_of_isKFlat
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKFlat] [Q.IsKFlat]
    (f : P ⟶ Q) [QuasiIso f] (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (f ▷ A) := by
  rw [whiskerRight_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 A)))

/-- Whiskering a quasi-isomorphism between K-flat complexes on the left by an arbitrary complex
gives a quasi-isomorphism. -/
instance quasiIso_whiskerLeft_of_isKFlat (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKFlat] [Q.IsKFlat]
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (A ◁ f) := by
  rw [whiskerLeft_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom (𝟙 A) f))

/-- Tensoring two quasi-isomorphisms of `R`-module complexes produces a quasi-isomorphism whenever
the left factors are K-flat. -/
lemma quasiIso_tensorHom_of_isKFlat_left
    {P₁ P₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ} [P₁.IsKFlat] [P₂.IsKFlat]
    (f₁ : P₁ ⟶ P₂) (f₂ : L₁ ⟶ L₂) [QuasiIso f₁] [QuasiIso f₂] :
    QuasiIso (tensorHom f₁ f₂) := by
  have h : tensorHom f₁ f₂ = tensorHom f₁ (𝟙 L₁) ≫ tensorHom (𝟙 P₂) f₂ := by
    simp only [HomologicalComplex.tensorHom, ← mapBifunctorMap_comp,
      Category.id_comp, Category.comp_id]
  rw [h]
  infer_instance

/-- Tensoring two quasi-isomorphisms of `R`-module complexes produces a quasi-isomorphism whenever
the right factors are K-flat. -/
lemma quasiIso_tensorHom_of_isKFlat_right
    {K₁ K₂ Q₁ Q₂ : CochainComplex (ModuleCat.{u} R) ℤ} [Q₁.IsKFlat] [Q₂.IsKFlat]
    (f₁ : K₁ ⟶ K₂) (f₂ : Q₁ ⟶ Q₂) [QuasiIso f₁] [QuasiIso f₂] :
    QuasiIso (tensorHom f₁ f₂) := by
  have h : tensorHom f₁ f₂ = tensorHom f₁ (𝟙 Q₁) ≫ tensorHom (𝟙 K₂) f₂ := by
    simp only [HomologicalComplex.tensorHom, ← mapBifunctorMap_comp,
      Category.id_comp, Category.comp_id]
  rw [h]
  infer_instance

/-- Termwise left tensoring by an arbitrary `R`-module preserves quasi-isomorphisms between K-flat
complexes. -/
instance quasiIso_mapHomologicalComplex_tensorLeft_of_isKFlat (M : ModuleCat.{u} R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKFlat] [Q.IsKFlat]
    (g : P ⟶ Q) [QuasiIso g] :
    QuasiIso (((CategoryTheory.MonoidalCategory.tensorLeft M).mapHomologicalComplex
      (.up ℤ)).map g) := by
  let e := (CategoryTheory.MonoidalCategory.curriedTensor
    (ModuleCat.{u} R)).mapBifunctorSingleRowZeroNatIso M
  exact quasiIso_of_arrow_mk_iso
    (tensorHom (𝟙 ((single (ModuleCat.{u} R) (.up ℤ) 0).obj M)) g)
    (((CategoryTheory.MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).map g)
    (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality g).symm)

variable [HasDerivedCategory (ModuleCat.{u} R)]

/-- A quasi-isomorphism of K-flat models induces an invertible transformation on the entire
unbounded derived category, not just on bounded or K-flat right inputs. -/
instance isIso_kFlatTensorMap
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] : IsIso (kFlatTensorMap f) := by
  have : IsIso (whiskerRight
      ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map f)
      DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro A
    simp only [whiskerRight_app, curriedTensor_map₂CochainComplex_map_app,
      Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj]
    infer_instance
  rw [kFlatTensorMap_eq_liftNatTrans]
  exact (Localization.liftNatIso DerivedCategory.Q (quasiIso (ModuleCat.{u} R) (.up ℤ))
    _ _ K.kFlatTensor L.kFlatTensor (asIso (whiskerRight
      ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map f)
      DerivedCategory.Q))).isIso_hom

end CochainComplex
