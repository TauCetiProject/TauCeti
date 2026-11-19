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
tensoring with any complex. Thus the endofunctor `CochainComplex.kFlatTensor` of the unbounded
derived category sends quasi-isomorphisms in its K-flat input to natural isomorphisms. The
comparison is induced by the specified map of models, so its identity and composition laws
are those of `CochainComplex.kFlatTensorMap`.

The arbitrary right factor is resolved by a K-flat complex, and the Koszul braiding exchanges
the two factors. No boundedness, freeness or termwise flatness is required of either input.

## References

* [The Stacks Project][stacks], Section 15.60, Tags 064L and 064M.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex
open scoped MonoidalCategory

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]

/-- Left whiskering with a K-flat complex of modules preserves quasi-isomorphisms. -/
instance quasiIso_whiskerLeft (A : CochainComplex (ModuleCat.{u} R) ℤ) [A.IsKFlat]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (A ◁ f) := by
  rw [whiskerLeft_eq_mapBifunctorMap, ← HomologicalComplex.tensorHom]
  infer_instance

/-- Right whiskering with a K-flat complex of modules preserves quasi-isomorphisms. -/
instance quasiIso_whiskerRight (A : CochainComplex (ModuleCat.{u} R) ℤ) [A.IsKFlat]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (f ▷ A) :=
  quasiIso_of_arrow_mk_iso (A ◁ f) (f ▷ A)
    (Arrow.isoMk (β_ A K) (β_ A L) (BraidedCategory.braiding_naturality_right A f).symm)

/-- Tensoring on the right with a K-flat complex preserves quasi-isomorphisms. -/
instance quasiIso_tensorHom_id (A : CochainComplex (ModuleCat.{u} R) ℤ) [A.IsKFlat]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (tensorHom f (𝟙 A)) := by
  rw [HomologicalComplex.tensorHom, ← whiskerRight_eq_mapBifunctorMap]
  infer_instance

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

/-- Right whiskering a quasi-isomorphism between K-flat complexes of modules with an arbitrary,
possibly unbounded, complex preserves quasi-isomorphisms. -/
instance quasiIso_whiskerRight_of_isKFlat
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (f ▷ A) := by
  rw [whiskerRight_eq_mapBifunctorMap, ← HomologicalComplex.tensorHom]
  infer_instance

/-- Left whiskering a quasi-isomorphism between K-flat complexes of modules with an arbitrary,
possibly unbounded, complex preserves quasi-isomorphisms. -/
instance quasiIso_whiskerLeft_of_isKFlat
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (A ◁ f) :=
  quasiIso_of_arrow_mk_iso (f ▷ A) (A ◁ f)
    (Arrow.isoMk (β_ K A) (β_ L A) (BraidedCategory.braiding_naturality_left f A).symm)

/-- A quasi-isomorphism between K-flat complexes of modules remains a quasi-isomorphism after
tensoring on the left with an arbitrary, possibly unbounded, complex. -/
instance quasiIso_id_tensorHom_of_isKFlat
    (A : CochainComplex (ModuleCat.{u} R) ℤ)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (tensorHom (𝟙 A) f) := by
  rw [HomologicalComplex.tensorHom, ← whiskerLeft_eq_mapBifunctorMap]
  infer_instance

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
