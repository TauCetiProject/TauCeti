/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Flasque.Resolution
public import TauCeti.Topology.Sheaves.Godement

/-!
# Godement sections compute derived global sections

For sheaves of modules over a commutative ring on an arbitrary topological space, the
cohomology of the global sections of the Godement resolution is naturally isomorphic to the
native right derived functors of global sections. The comparison takes values in modules,
not just abelian groups. It is characterized by every map from the Godement resolution to an
injective resolution compatible with the augmentations, so its value does not depend on a
choice of comparison map. In degree `0` it sends the canonical map `Γ(F) ⟶ R⁰Γ(F)` to the
inclusion of global sections into the degree-zero cycles of the Godement sections complex
(`TauCeti.Topology.toRightDerivedZero_app_comp_rightDerivedΓIsoGodement_hom_app`).

The construction uses the native module-valued Godement resolution
`TauCeti.Topology.godementResolution` and the flasque-resolution comparison
`CategoryTheory.Sheaf.rightDerivedΓIsoOfIsFlasque`. The Godement terms need not be injective.
No separation, compactness or nonemptiness hypothesis on the space is needed.

## References

* The Stacks Project, Cohomology of Sheaves, Lemma 20.12.3 (tag 09SY) and
  Lemma 20.30.2 (tag 0FKT).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

/-- Native derived global sections are computed by the global sections of the Godement
resolution, naturally in the module sheaf. -/
def rightDerivedΓIsoGodement (n : ℕ) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ≅
      godementResolution (ModuleCat.{u} R) X ⋙
        (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n :=
  Sheaf.rightDerivedΓIsoOfIsFlasque _ (toGodementResolution (ModuleCat.{u} R) X)
    (isFlasque_godementResolution_obj_X (ModuleCat.{u} R) X) n

/-- The component of the Godement comparison is the flasque-resolution comparison for the
Godement augmentation. -/
@[simp]
lemma rightDerivedΓIsoGodement_app (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (rightDerivedΓIsoGodement (X := X) (R := R) n).app F =
      Sheaf.rightDerivedΓObjIsoOfIsFlasque
        ((toGodementResolution (ModuleCat.{u} R) X).app F)
        (isFlasque_godementResolution_obj_X (ModuleCat.{u} R) X F) n := by
  simp [rightDerivedΓIsoGodement]

/-- The Godement comparison is induced by any augmentation-preserving map to any injective
resolution. In particular the comparison is independent of all such choices. -/
@[reassoc]
lemma rightDerivedΓIsoGodement_hom_comp_homologyMap
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (n : ℕ)
    (I : InjectiveResolution F)
    (φ : (godementResolution (ModuleCat.{u} R) X).obj F ⟶ I.cocomplex)
    (hφ : (toGodementResolution (ModuleCat.{u} R) X).app F ≫ φ = I.ι) :
    (rightDerivedΓIsoGodement (X := X) (R := R) n).hom.app F ≫
      ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ =
      (I.isoRightDerivedObj (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)) n).hom := by
  simpa only [← Iso.app_hom, rightDerivedΓIsoGodement_app] using
    Sheaf.rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap
      ((toGodementResolution (ModuleCat.{u} R) X).app F)
      (isFlasque_godementResolution_obj_X (ModuleCat.{u} R) X F) n I φ hφ

/-- In degree `0`, the Godement comparison sends a global section of `F`, viewed in `R⁰Γ(F)`, to
the cohomology class of its image in the global sections of the first Godement sheaf. -/
@[reassoc]
lemma toRightDerivedZero_app_comp_rightDerivedΓIsoGodement_hom_app
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).toRightDerivedZero.app F ≫
        (rightDerivedΓIsoGodement (X := X) (R := R) 0).hom.app F =
      (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
        ((godementResolution (ModuleCat.{u} R) X).obj F)).liftCycles
          ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
            (CochainComplex.fromSingle₀Equiv _ F
              ((toGodementResolution (ModuleCat.{u} R) X).app F)).val) 1 (by simp)
          (Functor.map_fromSingle₀Equiv_val_comp_d
            (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
            ((toGodementResolution (ModuleCat.{u} R) X).app F)) ≫
        (((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj
          ((godementResolution (ModuleCat.{u} R) X).obj F)).homologyπ 0 := by
  rw [← Iso.app_hom, rightDerivedΓIsoGodement_app]
  exact Sheaf.toRightDerivedZero_app_comp_rightDerivedΓObjIsoOfIsFlasque_hom _ _

end TauCeti.Topology
