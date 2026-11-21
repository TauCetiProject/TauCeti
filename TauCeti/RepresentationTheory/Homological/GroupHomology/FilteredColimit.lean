/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Functoriality

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import TauCeti.Algebra.Homology.ShortComplex.Colimit
import TauCeti.RepresentationTheory.Homological.GroupHomology.DirectedUnion

/-!
# Group homology of a filtered union

For a filtered diagram of groups with injective maps to a group `G` whose images cover `G`,
`Rep.isColimitGroupHomologyCocone` exhibits `Hₙ(G, A)` as the colimit of the homology of the
stages with coefficients restricted from `A`. The diagram is not required to present the stages
as literal subgroups, so the result also applies to injective stabilization maps.

The proof uses finite support for inhomogeneous chains and exactness of filtered colimits of
modules. For the directed-union formula, see K. S. Brown, *Cohomology of Groups*, and for its
application to stable general linear groups, see van der Kallen, *Homology stability for linear
groups*, §4.6.

The diagram and cocones reduce at their objects and vertices so one can use their dependent
projections directly as maps between the corresponding chain complexes and homology modules.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits groupHomology

universe u

namespace Rep

variable {k : Type u} [CommRing k] {J : Type u} [SmallCategory J] {F : J ⥤ GrpCat.{u}}

/-- The diagram of inhomogeneous chains of the stages of `c` with coefficients restricted
from `A`. Transition maps use the identity on the underlying coefficient module. -/
@[expose] def restrictedChainsDiagram {c : Cocone F} (A : Rep k c.pt) :
    J ⥤ ChainComplex (ModuleCat k) ℕ where
  obj j := inhomogeneousChains (res (c.ι.app j).hom A)
  map {i j} f := chainsMap (F.map f).hom
    (isIntertwiningMap_res_res A (f₁ := MonoidHom.id (F.obj i))
      (by simpa only [GrpCat.hom_comp, MonoidHom.comp_id] using
        congrArg GrpCat.Hom.hom (c.w f))).toRes
  map_id i := by
    rw [← chainsMap_id]
    exact chainsMap_congr (by simp) (by simp)
  map_comp f g := by
    rw [← chainsMap_comp]
    exact chainsMap_congr (by simp) (by simp)

/-- The cocone of inhomogeneous chains induced by the legs of `c` and the identity on `A`. -/
@[expose] def restrictedChainsCocone {c : Cocone F} (A : Rep k c.pt) :
    Cocone (A.restrictedChainsDiagram (c := c)) where
  pt := inhomogeneousChains A
  ι :=
    { app := fun j ↦ chainsMap (c.ι.app j).hom (𝟙 _)
      naturality := fun i j f ↦ by
        dsimp [restrictedChainsDiagram]
        rw [← chainsMap_comp]
        exact chainsMap_congr (congrArg GrpCat.Hom.hom (c.w f)) (by simp) }

/-- The vertex of the chain cocone is the inhomogeneous chain complex with coefficients `A`. -/
@[simp] theorem restrictedChainsCocone_pt {c : Cocone F} (A : Rep k c.pt) :
    A.restrictedChainsCocone.pt = inhomogeneousChains A := (rfl)

/-- The chain cocone leg at a stage is induced by the corresponding group inclusion map. -/
@[simp] theorem restrictedChainsCocone_ι_app {c : Cocone F} (A : Rep k c.pt) (j : J) :
    A.restrictedChainsCocone.ι.app j = chainsMap (c.ι.app j).hom (𝟙 _) := (rfl)

/-- The term at stage `j` is the complex for the restriction along the `j`th cocone leg. -/
@[simp] theorem restrictedChainsDiagram_obj {c : Cocone F} (A : Rep k c.pt) (j : J) :
    A.restrictedChainsDiagram.obj j = inhomogeneousChains (res (c.ι.app j).hom A) := (rfl)

/-- The transition sends an inhomogeneous chain along the corresponding group homomorphism. -/
theorem restrictedChainsDiagram_map {c : Cocone F} (A : Rep k c.pt) {i j : J} (f : i ⟶ j) :
    A.restrictedChainsDiagram.map f = chainsMap (F.map f).hom
      (isIntertwiningMap_res_res A (f₁ := MonoidHom.id (F.obj i))
        (by simpa only [GrpCat.hom_comp, MonoidHom.comp_id] using
          congrArg GrpCat.Hom.hom (c.w f))).toRes := (rfl)

/-- The group homology cocone associated to `c`, with coefficients restricted from `A`. -/
@[expose] def groupHomologyCocone {c : Cocone F} (A : Rep k c.pt) (n : ℕ) :
    Cocone (A.restrictedChainsDiagram ⋙ HomologicalComplex.homologyFunctor _ _ n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapCocone A.restrictedChainsCocone

/-- The vertex of the homology cocone is the homology of the ambient group with coefficients `A`. -/
@[simp] theorem groupHomologyCocone_pt {c : Cocone F} (A : Rep k c.pt) (n : ℕ) :
    (A.groupHomologyCocone n).pt = groupHomology A n := (rfl)

/-- The legs are the homology maps induced by the group cocone legs. -/
@[simp] theorem groupHomologyCocone_ι_app {c : Cocone F} (A : Rep k c.pt) (n : ℕ) (j : J) :
    (A.groupHomologyCocone n).ι.app j = groupHomology.map (c.ι.app j).hom (𝟙 _) n := (rfl)

variable [IsFiltered J] {c : Cocone F}

/-- An inhomogeneous chain with coefficients in `A` lifts to some stage of a filtered group
cocone whose legs jointly cover the ambient group. -/
theorem exists_restrictedChainsCocone_f_eq (A : Rep k c.pt)
    (hcover : ∀ g : c.pt, ∃ j, ∃ x : F.obj j, (c.ι.app j).hom x = g)
    {n : ℕ} (x : (inhomogeneousChains A).X n) :
    ∃ j y, (A.restrictedChainsCocone.ι.app j).f n y = x := by
  -- Lift first to the image subgroup, then along the surjection from the stage to its image.
  let S (j : J) : Subgroup c.pt := (c.ι.app j).hom.range
  have hle {i j : J} (f : i ⟶ j) : S i ≤ S j := by
    rintro g ⟨z, rfl⟩
    exact ⟨F.map f z, DFunLike.congr_fun (congrArg GrpCat.Hom.hom (c.w f)) z⟩
  have hS : Directed (· ≤ ·) S := fun i j ↦
    ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j), hle (IsFiltered.rightToMax i j)⟩
  have htop : ⨆ j, S j = ⊤ := eq_top_iff.2 fun g _ ↦ by
    obtain ⟨j, z, hz⟩ := hcover g
    exact Subgroup.mem_iSup_of_mem j ⟨z, hz⟩
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨j, y, hy⟩ := TauCeti.groupHomology.exists_chainsMap_subtype_f_eq_of_directed hS htop x
  let f := (c.ι.app j).hom
  let e := f.rangeRestrict
  have he : f.range.subtype.comp e = f := f.subtype_comp_rangeRestrict
  let φ := (isIntertwiningMap_res_res A (f₁ := MonoidHom.id (F.obj j))
    (by simpa only [MonoidHom.comp_id] using he)).toRes
  have : Epi φ := (Rep.epi_iff_surjective _).2 fun z ↦
    ⟨z, Representation.IsIntertwiningMap.toRes_hom_apply _ z⟩
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((chainsMap e φ).f n)).1
    (chainsMap_f_map_epi _ _ f.rangeRestrict_surjective _) y
  have hcomp : chainsMap e φ ≫ chainsMap f.range.subtype (𝟙 _) = chainsMap f (𝟙 _) := by
    rw [← chainsMap_comp]
    exact chainsMap_congr he (by simp [φ]; rfl)
  have h := congrArg (fun a : inhomogeneousChains (res f A) ⟶ inhomogeneousChains A ↦ a.f n z)
    hcomp
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply, hz] at h
  exact ⟨j, z, h.symm.trans hy⟩

/-- For a filtered group cocone with injective legs that jointly cover the ambient group, the
cocone of inhomogeneous chains with restricted coefficients is a colimit. -/
def isColimitRestrictedChainsCocone (A : Rep k c.pt)
    (hinj : ∀ j, Function.Injective (c.ι.app j))
    (hcover : ∀ g : c.pt, ∃ j, ∃ x : F.obj j, (c.ι.app j).hom x = g) :
    IsColimit A.restrictedChainsCocone := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  apply isColimitOfReflects (forget (ModuleCat k))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨j, y, hy⟩ := A.exists_restrictedChainsCocone_f_eq hcover (n := n) x
    exact ⟨j, y, hy.symm⟩
  · -- Since the chain legs are injective, equality from one stage needs no further transition.
    intro j x y hxy
    have hm := chainsMap_f_map_mono (c.ι.app j).hom (𝟙 (res (c.ι.app j).hom A)) (hinj j) n
    have h : x = y := (ModuleCat.mono_iff_injective _).1 hm hxy
    exact ⟨j, 𝟙 j, congrArg _ h⟩

/-- Group homology of a filtered union is the colimit of the homology of the stages with
restricted coefficients. No finite generation or triviality assumption on `A` is needed. -/
def isColimitGroupHomologyCocone (A : Rep k c.pt) (n : ℕ)
    (hinj : ∀ j, Function.Injective (c.ι.app j))
    (hcover : ∀ g : c.pt, ∃ j, ∃ x : F.obj j, (c.ι.app j).hom x = g) :
    IsColimit (A.groupHomologyCocone n) :=
  isColimitOfPreserves (HomologicalComplex.homologyFunctor _ _ n)
    (A.isColimitRestrictedChainsCocone hinj hcover)

end Rep

end
