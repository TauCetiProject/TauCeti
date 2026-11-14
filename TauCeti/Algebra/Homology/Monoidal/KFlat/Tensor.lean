/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivedTensor
public import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# Bilateral quasi-isomorphism invariance of K-flat tensor products

In an abelian braided monoidal preadditive category `C` satisfying the graded-tensor hypotheses of
`HomologicalComplex.monoidalCategory`, the Koszul braiding exchanges the two factors of the
totalized tensor product on `CochainComplex C ℤ`, so tensoring on the right with a K-flat complex
also preserves quasi-isomorphisms (`CochainComplex.quasiIso_tensorHom_id`,
`CochainComplex.quasiIso_whiskerRight`).

When in addition `(CochainComplex.kFlatLocalizerMorphism C).HasLeftResolutions` holds, every
arbitrary cochain complex admits a left resolution by a K-flat complex, so any quasi-isomorphism
between K-flat complexes remains a quasi-isomorphism after tensoring on either side with any
complex (`CochainComplex.quasiIso_tensorHom_id_of_isKFlat`,
`CochainComplex.quasiIso_id_tensorHom_of_isKFlat`), after tensoring with another quasi-isomorphism
(`CochainComplex.quasiIso_tensorHom_of_isKFlat_left`,
`CochainComplex.quasiIso_tensorHom_of_isKFlat_right`), and under termwise left or right tensoring
by any object of `C` (`CochainComplex.quasiIso_mapHomologicalComplex_tensorLeft_of_isKFlat`,
`CochainComplex.quasiIso_mapHomologicalComplex_tensorRight_of_isKFlat`). Consequently, when
`HasDerivedCategory C` also holds, any quasi-isomorphism between K-flat complexes induces a natural
isomorphism of derived tensor endofunctors `CochainComplex.kFlatTensor`
(`CochainComplex.isIso_kFlatTensorMap`).

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 064L and 064M.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

section Monoidal

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- Tensoring a quasi-isomorphism on the left with a K-flat complex via `◁` is a
quasi-isomorphism. -/
instance quasiIso_whiskerLeft (P : CochainComplex C ℤ) [P.IsKFlat]
    {A B : CochainComplex C ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso (P ◁ f) := by
  rw [whiskerLeft_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom (𝟙 P) f))

section Braided

variable [BraidedCategory C]

/-- Tensoring on the right with a K-flat complex preserves quasi-isomorphisms. -/
instance quasiIso_tensorHom_id (A : CochainComplex C ℤ) [A.IsKFlat]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (tensorHom f (𝟙 A)) := by
  rw [HomologicalComplex.tensorHom, ← whiskerRight_eq_mapBifunctorMap]
  exact quasiIso_of_arrow_mk_iso (A ◁ f) (f ▷ A)
    (Arrow.isoMk (TauCeti.koszulBraiding C A K) (TauCeti.koszulBraiding C A L)
      (by simp [TauCeti.koszulBraidingHom_naturality_right]))

/-- Tensoring a quasi-isomorphism on the right with a K-flat complex via `▷` is a
quasi-isomorphism. -/
instance quasiIso_whiskerRight (Q : CochainComplex C ℤ) [Q.IsKFlat]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (f ▷ Q) := by
  rw [whiskerRight_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 Q)))

section HasLeftResolutions

variable [(kFlatLocalizerMorphism C).HasLeftResolutions]

/-- A quasi-isomorphism between K-flat complexes stays a quasi-isomorphism after tensoring on the
right with an arbitrary, possibly unbounded, complex. -/
instance quasiIso_tensorHom_id_of_isKFlat
    {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] (A : CochainComplex C ℤ) :
    QuasiIso (tensorHom f (𝟙 A)) := by
  let res : (kFlatLocalizerMorphism C).LeftResolution A := Nonempty.some inferInstance
  let p := res.w
  have : IsKFlat ((kFlatLocalizerMorphism C).functor.obj res.X₁) := by
    rw [kFlatLocalizerMorphism_functor]; exact res.X₁.property
  have : QuasiIso p := (mem_quasiIso_iff _).1 res.hw
  have h : tensorHom (𝟙 K) p ≫ tensorHom f (𝟙 A) =
      tensorHom f (𝟙 _) ≫ tensorHom (𝟙 L) p := by
    simp only [HomologicalComplex.tensorHom, ← mapBifunctorMap_comp,
      Category.id_comp, Category.comp_id]
  apply (quasiIso_iff_comp_left (tensorHom (𝟙 K) p) _).1
  rw [h]
  infer_instance

/-- A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism after tensoring on the
left with any, possibly unbounded, complex `A`. -/
instance quasiIso_id_tensorHom_of_isKFlat (A : CochainComplex C ℤ)
    {P Q : CochainComplex C ℤ} [P.IsKFlat] [Q.IsKFlat]
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (tensorHom (𝟙 A) f) := by
  rw [HomologicalComplex.tensorHom, ← whiskerLeft_eq_mapBifunctorMap]
  have : QuasiIso (f ▷ A) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 A)))
  exact quasiIso_of_arrow_mk_iso (f ▷ A) (A ◁ f)
    (Arrow.isoMk (TauCeti.koszulBraiding C P A) (TauCeti.koszulBraiding C Q A)
      (by simp [TauCeti.koszulBraidingHom_naturality_left]))

/-- Whiskering a quasi-isomorphism between K-flat complexes on the right by an arbitrary complex
gives a quasi-isomorphism. -/
instance quasiIso_whiskerRight_of_isKFlat
    {P Q : CochainComplex C ℤ} [P.IsKFlat] [Q.IsKFlat]
    (f : P ⟶ Q) [QuasiIso f] (A : CochainComplex C ℤ) :
    QuasiIso (f ▷ A) := by
  rw [whiskerRight_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 A)))

/-- Whiskering a quasi-isomorphism between K-flat complexes on the left by an arbitrary complex
gives a quasi-isomorphism. -/
instance quasiIso_whiskerLeft_of_isKFlat (A : CochainComplex C ℤ)
    {P Q : CochainComplex C ℤ} [P.IsKFlat] [Q.IsKFlat]
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (A ◁ f) := by
  rw [whiskerLeft_eq_mapBifunctorMap]
  exact inferInstanceAs (QuasiIso (tensorHom (𝟙 A) f))

/-- Tensoring two quasi-isomorphisms of cochain complexes produces a quasi-isomorphism whenever the
left factors are K-flat. -/
lemma quasiIso_tensorHom_of_isKFlat_left
    {P₁ P₂ L₁ L₂ : CochainComplex C ℤ} [P₁.IsKFlat] [P₂.IsKFlat]
    (f₁ : P₁ ⟶ P₂) (f₂ : L₁ ⟶ L₂) [QuasiIso f₁] [QuasiIso f₂] :
    QuasiIso (tensorHom f₁ f₂) := by
  have h : tensorHom f₁ f₂ = tensorHom f₁ (𝟙 L₁) ≫ tensorHom (𝟙 P₂) f₂ := by
    simp only [HomologicalComplex.tensorHom, ← mapBifunctorMap_comp,
      Category.id_comp, Category.comp_id]
  rw [h]
  infer_instance

/-- Tensoring two quasi-isomorphisms of cochain complexes produces a quasi-isomorphism whenever the
right factors are K-flat. -/
lemma quasiIso_tensorHom_of_isKFlat_right
    {K₁ K₂ Q₁ Q₂ : CochainComplex C ℤ} [Q₁.IsKFlat] [Q₂.IsKFlat]
    (f₁ : K₁ ⟶ K₂) (f₂ : Q₁ ⟶ Q₂) [QuasiIso f₁] [QuasiIso f₂] :
    QuasiIso (tensorHom f₁ f₂) := by
  have h : tensorHom f₁ f₂ = tensorHom f₁ (𝟙 Q₁) ≫ tensorHom (𝟙 K₂) f₂ := by
    simp only [HomologicalComplex.tensorHom, ← mapBifunctorMap_comp,
      Category.id_comp, Category.comp_id]
  rw [h]
  infer_instance

/-- Termwise left tensoring by an arbitrary object of `C` preserves quasi-isomorphisms between
K-flat complexes. -/
instance quasiIso_mapHomologicalComplex_tensorLeft_of_isKFlat (M : C)
    {P Q : CochainComplex C ℤ} [P.IsKFlat] [Q.IsKFlat]
    (g : P ⟶ Q) [QuasiIso g] :
    QuasiIso (((MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).map g) := by
  let e := (MonoidalCategory.curriedTensor C).mapBifunctorSingleRowZeroNatIso M
  exact quasiIso_of_arrow_mk_iso
    (tensorHom (𝟙 ((single C (.up ℤ) 0).obj M)) g)
    (((MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).map g)
    (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality g).symm)

/-- Termwise right tensoring by an arbitrary object of `C` preserves quasi-isomorphisms between
K-flat complexes. -/
instance quasiIso_mapHomologicalComplex_tensorRight_of_isKFlat (M : C)
    {P Q : CochainComplex C ℤ} [P.IsKFlat] [Q.IsKFlat]
    (g : P ⟶ Q) [QuasiIso g] :
    QuasiIso (((MonoidalCategory.tensorRight M).mapHomologicalComplex (.up ℤ)).map g) := by
  let e := NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M) (.up ℤ)
  exact quasiIso_of_arrow_mk_iso
    (((MonoidalCategory.tensorLeft M).mapHomologicalComplex (.up ℤ)).map g)
    (((MonoidalCategory.tensorRight M).mapHomologicalComplex (.up ℤ)).map g)
    (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality g).symm)

/-- A quasi-isomorphism between K-flat complexes induces an invertible natural transformation of
their derived tensor endofunctors on the unbounded derived category. -/
instance isIso_kFlatTensorMap [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] : IsIso (kFlatTensorMap f) := by
  have : IsIso (Functor.whiskerRight
      ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.map f)
      DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro A
    simp only [whiskerRight_app, curriedTensor_map₂CochainComplex_map_app,
      Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj]
    infer_instance
  rw [kFlatTensorMap_eq_liftNatTrans]
  exact (Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    _ _ K.kFlatTensor L.kFlatTensor (asIso (Functor.whiskerRight
      ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.map f)
      DerivedCategory.Q))).isIso_hom

end HasLeftResolutions

end Braided

end Monoidal

end CochainComplex
