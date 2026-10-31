/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Projective
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Flat
public import TauCeti.Algebra.Homology.CochainComplex.ProjectiveResolution
public import TauCeti.Algebra.Homology.Monoidal.KFlat

/-!
# Flat resolutions of bounded above complexes of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. Every cochain complex `K` of sheaves of
`R`-modules which is strictly bounded above by `n` receives a quasi-isomorphism from a complex of
flat sheaves of modules, again strictly bounded above by `n`; such a complex is K-flat
(`CochainComplex.exists_quasiIso_isKFlat_sheafOfModules`). No points of the site are used.

The underlying complex of presheaves of modules of `K` has a resolution by a bounded above complex
of projective presheaves of modules (`CochainComplex.exists_quasiIso_projective`, since presheaves
of modules have enough projectives). Sheafification is exact, so it carries this resolution to a
quasi-isomorphism onto the sheafification of the underlying complex of `K`, which is `K` itself.
The modules of sections of a projective presheaf of modules are flat, so the sheafified terms are
flat sheaves of modules, and a bounded above complex of flat objects is K-flat
(`CochainComplex.isKFlat_of_boundedAbove_flat`).

These are the bounded above K-flat replacements from which derived tensor products of complexes of
sheaves of modules are computed.

## References

* The Stacks Project, Cohomology on Sites, Section 21.17, Flat resolutions.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

open TauCeti.SheafOfModules

namespace CochainComplex

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

/-- A cochain complex of sheaves of modules over a sheaf of commutative rings which is strictly
bounded above by `n` receives a quasi-isomorphism from a K-flat complex of flat sheaves of modules
which is also strictly bounded above by `n`. -/
theorem exists_quasiIso_isKFlat_sheafOfModules
    (K : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    ∃ (P : CochainComplex (SheafOfModules.{u} (ringCatSheaf R)) ℤ) (π : P ⟶ K) (_ : QuasiIso π)
      (_ : ∀ i, PreservesFiniteLimits (tensorLeft (P.X i))) (_ : P.IsKFlat), P.IsStrictlyLE n := by
  let ι := (SheafOfModules.forget (ringCatSheaf R)).mapHomologicalComplex (.up ℤ)
  let a := PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)
  have : CochainComplex.IsStrictlyLE (ι.obj K) n :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K _ n).2 inferInstance
  obtain ⟨P, π, _, hP, _⟩ := CochainComplex.exists_quasiIso_projective (ι.obj K) n
  -- resolve the underlying complex of presheaves by projectives, then sheafify;
  -- sheafifying the underlying complex of `K` recovers `K`
  let e : (a.mapHomologicalComplex (.up ℤ)).obj (ι.obj K) ≅ K :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ sheafificationIso _ (K.X i))
      (fun _ _ _ ↦ (sheafificationIso_hom_naturality (K.d _ _)).symm)
  have hflat (i : ℤ) : PreservesFiniteLimits
      (tensorLeft (((a.mapHomologicalComplex (.up ℤ)).obj P).X i)) :=
    -- the projectivity of `P.X i` is stated in `PresheafOfModules (ringCatSheaf R).obj`, whose
    -- ring presheaf is by definition `R.obj ⋙ forget₂ _ _`, so it is passed explicitly
    have (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) (PresheafOfModulesOfCommRing.obj (P.X i) X) :=
      @PresheafOfModulesOfCommRing.flat_obj_of_projective _ _ R.obj (P.X i) (hP i) X
    PresheafOfModulesOfCommRing.preservesFiniteLimits_tensorLeft_sheafification_obj_of_flat
      (R := R) (P.X i)
  have : CochainComplex.IsStrictlyLE ((a.mapHomologicalComplex (.up ℤ)).obj P) n :=
    (CochainComplex.isStrictlyLE_iff _ n).2 fun i hi ↦
      a.map_isZero (P.isZero_of_isStrictlyLE n i hi)
  have : a.Additive := a.additive_of_preserves_binary_products
  have : QuasiIso ((a.mapHomologicalComplex (.up ℤ)).map π) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology π a
  -- filtered colimits of sheaves of modules are exact, also for the small index category `ℕ`
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} (ringCatSheaf R)) :=
    AB5OfSize_of_univLE.{0, 0, u, u} _
  exact ⟨_, (a.mapHomologicalComplex (.up ℤ)).map π ≫ e.hom, inferInstance, hflat,
    CochainComplex.isKFlat_of_boundedAbove_flat _ n, inferInstance⟩

end CochainComplex
