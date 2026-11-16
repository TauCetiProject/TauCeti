/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure
import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# Quasi-isomorphisms and tensor products of K-flat complexes

Let `C` be an abelian braided monoidal preadditive category in which `CochainComplex C ℤ` carries
Mathlib's totalized monoidal structure (`HomologicalComplex.monoidalCategory`) and the Koszul
braiding (`TauCeti.koszulBraidedCategory`).

* Tensoring on the right with a K-flat complex preserves quasi-isomorphisms
  (`CochainComplex.quasiIso_tensorHom_id`).
* The tensor product of two quasi-isomorphisms `f : K₁ ⟶ L₁` and `g : K₂ ⟶ L₂` is a
  quasi-isomorphism whenever `L₁` and `K₂` are K-flat
  (`CochainComplex.quasiIso_tensorHom_of_isKFlat_right_left`) or `K₁` and `L₂` are K-flat
  (`CochainComplex.quasiIso_tensorHom_of_isKFlat_left_right`).
* When `CochainComplex.kFlatLocalizerMorphism C` has left resolutions, a quasi-isomorphism between
  K-flat complexes remains a quasi-isomorphism after tensoring on either side with an arbitrary,
  possibly unbounded, complex (`CochainComplex.quasiIso_tensorHom_id_of_isKFlat`,
  `CochainComplex.quasiIso_id_tensorHom_of_isKFlat`), so `tensorHom f g` is also a quasi-isomorphism
  whenever both `K₁` and `L₁` are K-flat (`CochainComplex.quasiIso_tensorHom_of_isKFlat_left`) or
  both `K₂` and `L₂` are K-flat (`CochainComplex.quasiIso_tensorHom_of_isKFlat_right`).

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 064L and 064M.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C]
  [∀ X₁ X₂ : GradedObject ℤ C, GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- Tensoring on the right with a K-flat complex preserves quasi-isomorphisms. -/
instance quasiIso_tensorHom_id (A : CochainComplex C ℤ) [A.IsKFlat]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (tensorHom f (𝟙 A)) := by
  rw [HomologicalComplex.tensorHom, ← whiskerRight_eq_mapBifunctorMap]
  have : QuasiIso (A ◁ f) := by
    rw [whiskerLeft_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (tensorHom (𝟙 A) f))
  exact quasiIso_of_arrow_mk_iso (A ◁ f) (f ▷ A)
    (Arrow.isoMk (β_ A K) (β_ A L) (BraidedCategory.braiding_naturality_right A f).symm)

/-- The tensor product of two quasi-isomorphisms `f : K₁ ⟶ L₁` and `g : K₂ ⟶ L₂` is a
quasi-isomorphism whenever `L₁` and `K₂` are K-flat. -/
theorem quasiIso_tensorHom_of_isKFlat_right_left
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} [L₁.IsKFlat] [K₂.IsKFlat]
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (tensorHom f g) := by
  have hfg : tensorHom f g = tensorHom f (𝟙 K₂) ≫ tensorHom (𝟙 L₁) g := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  rw [hfg]
  infer_instance

/-- The tensor product of two quasi-isomorphisms `f : K₁ ⟶ L₁` and `g : K₂ ⟶ L₂` is a
quasi-isomorphism whenever `K₁` and `L₂` are K-flat. -/
theorem quasiIso_tensorHom_of_isKFlat_left_right
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} [K₁.IsKFlat] [L₂.IsKFlat]
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (tensorHom f g) := by
  have hfg : tensorHom f g = tensorHom (𝟙 K₁) g ≫ tensorHom f (𝟙 L₂) := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  rw [hfg]
  infer_instance

section HasLeftResolutions

variable [(kFlatLocalizerMorphism C).HasLeftResolutions]

/-- A quasi-isomorphism between K-flat complexes stays a quasi-isomorphism after tensoring on the
right with an arbitrary, possibly unbounded, complex. -/
instance quasiIso_tensorHom_id_of_isKFlat
    {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] (A : CochainComplex C ℤ) :
    QuasiIso (tensorHom f (𝟙 A)) := by
  obtain ⟨R⟩ : Nonempty ((kFlatLocalizerMorphism C).LeftResolution A) := inferInstance
  let P : CochainComplex C ℤ := R.X₁.obj
  let p : P ⟶ A := R.w
  have : QuasiIso p := (mem_quasiIso_iff p).1 R.hw
  have h : tensorHom (𝟙 K) p ≫ tensorHom f (𝟙 A) =
      tensorHom f (𝟙 P) ≫ tensorHom (𝟙 L) p := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  apply (quasiIso_iff_comp_left (tensorHom (𝟙 K) p) _).1
  rw [h]
  infer_instance

/-- A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism after tensoring on the
left with an arbitrary, possibly unbounded, complex `A`. -/
instance quasiIso_id_tensorHom_of_isKFlat (A : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (tensorHom (𝟙 A) f) := by
  rw [HomologicalComplex.tensorHom, ← whiskerLeft_eq_mapBifunctorMap]
  have : QuasiIso (f ▷ A) := by
    rw [whiskerRight_eq_mapBifunctorMap]
    exact inferInstanceAs (QuasiIso (tensorHom f (𝟙 A)))
  exact quasiIso_of_arrow_mk_iso (f ▷ A) (A ◁ f)
    (Arrow.isoMk (β_ K A) (β_ L A) (BraidedCategory.braiding_naturality_left f A).symm)

/-- The tensor product of two quasi-isomorphisms `f : K₁ ⟶ L₁` and `g : K₂ ⟶ L₂` is a
quasi-isomorphism whenever both `K₁` and `L₁` are K-flat. -/
theorem quasiIso_tensorHom_of_isKFlat_left
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} [K₁.IsKFlat] [L₁.IsKFlat]
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (tensorHom f g) := by
  have hfg : tensorHom f g = tensorHom f (𝟙 K₂) ≫ tensorHom (𝟙 L₁) g := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  rw [hfg]
  infer_instance

/-- The tensor product of two quasi-isomorphisms `f : K₁ ⟶ L₁` and `g : K₂ ⟶ L₂` is a
quasi-isomorphism whenever both `K₂` and `L₂` are K-flat. -/
theorem quasiIso_tensorHom_of_isKFlat_right
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} [K₂.IsKFlat] [L₂.IsKFlat]
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (tensorHom f g) := by
  have hfg : tensorHom f g = tensorHom (𝟙 K₁) g ≫ tensorHom f (𝟙 L₂) := by
    simp only [← mapBifunctorMap_comp, Category.id_comp, Category.comp_id]
  rw [hfg]
  infer_instance

end HasLeftResolutions

end CochainComplex
