/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology
public import TauCeti.CategoryTheory.AInfinity.Cohomology
public import TauCeti.CategoryTheory.AInfinity.Transfer

/-!
# The minimal A-infinity category on Hom cohomology

Let `𝒞` be an `A∞` category over a field `K` on a graded linear quiver `C`.  Each Hom complex of
`𝒞` is the unary complex of the sub-`A∞` algebra `TauCeti.AInfinityCategory.homAlgebra`, so it has
a homogeneous special contraction onto its cohomology with zero differential
(`TauCeti.AInfinityAlgebra.cohomologyContraction`).  Taken on every hom module at once, these give
a homogeneous special contraction `TauCeti.AInfinityCategory.cohomologyContraction` of the total
complex of morphisms of `𝒞` onto the total module of morphisms of the cohomology quiver
`TauCeti.AInfinityCategory.CohomologyQuiver`.  By construction its inclusion, projection and
homotopy preserve every hom module, so it is compatible with the hom modules.

Homological transfer of `A∞` categories (`TauCeti.AInfinityCategory.transfer`) along this
contraction gives the **minimal model** `TauCeti.AInfinityCategory.minimalModel`: an `A∞` category
on the cohomology quiver whose differential vanishes and whose composition is the composition
induced on cohomology, `[g] ∘ [f] = [g ∘ f]`.  This is the minimal structure of Kadeishvili's
theorem for `A∞` categories; the comparison `A∞` quasi-equivalence between the minimal model and
`𝒞` is not constructed in this file.  The higher operations `m₃, m₄, …` of the minimal model record
the coherence which the graded cohomology category forgets.

## Main definitions

* `TauCeti.AInfinityCategory.cohomologyContraction`: over a field, a homogeneous special
  contraction of the total complex of morphisms onto the total module of Hom cohomologies.
* `TauCeti.AInfinityCategory.minimalModel`: the transferred minimal `A∞` category on the
  cohomology quiver.

## Main results

* `TauCeti.AInfinityCategory.isHomCompatible_cohomologyContraction`: the contraction is compatible
  with the hom modules.
* `TauCeti.AInfinityCategory.isMinimal_minimalModel` and
  `TauCeti.AInfinityCategory.homDifferential_minimalModel`: the minimal model is minimal.
* `TauCeti.AInfinityCategory.comp_minimalModel_cohomologyClass`: its composition is the
  composition induced on cohomology.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 7.
* P. Seidel, *Fukaya categories and Picard--Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Section (1i).
-/

public section

namespace TauCeti

open GradedLinearQuiver

universe u v w

namespace AInfinityCategory

variable {K : Type w} [Field K] {C : Type u} [GradedLinearQuiver.{u, v, w} K C]
  (𝒞 : AInfinityCategory K C)

/-- The inclusion of the cohomology contraction: on the Hom cohomology between `X` and `Y` it is
the chosen inclusion of cycle representatives of the Hom complex between `X.obj` and `Y.obj`. -/
private noncomputable def contractionIncl : TotalHom K 𝒞.CohomologyQuiver →ₗ[K] TotalHom K C :=
  letI := Classical.decEq 𝒞.CohomologyQuiver
  DirectSum.toModule K _ _ fun p ↦
    homInclusion p.1.obj p.2.obj ∘ₗ (𝒞.homAlgebra p.1.obj p.2.obj).cohomologyContraction.incl

/-- The projection of the cohomology contraction: on the morphisms `X ⟶ Y` it is the projection of
the cohomology contraction of the Hom complex from `X` to `Y`. -/
private noncomputable def contractionProj : TotalHom K C →ₗ[K] TotalHom K 𝒞.CohomologyQuiver :=
  letI := Classical.decEq C
  DirectSum.toModule K _ _ fun p ↦
    homInclusion (R := K) (C := 𝒞.CohomologyQuiver) ⟨p.1⟩ ⟨p.2⟩ ∘ₗ
      (𝒞.homAlgebra p.1 p.2).cohomologyContraction.proj

/-- The homotopy of the cohomology contraction: on the morphisms `X ⟶ Y` it is the homotopy of the
cohomology contraction of the Hom complex from `X` to `Y`. -/
private noncomputable def contractionHomotopy : Module.End K (TotalHom K C) :=
  DirectSum.lmap fun p ↦ (𝒞.homAlgebra p.1 p.2).cohomologyContraction.homotopy

private theorem contractionIncl_homInclusion (X Y : 𝒞.CohomologyQuiver)
    (a : homModule (R := K) X Y) :
    𝒞.contractionIncl (homInclusion X Y a) =
      homInclusion X.obj Y.obj ((𝒞.homAlgebra X.obj Y.obj).cohomologyContraction.incl a) := by
  let := Classical.decEq 𝒞.CohomologyQuiver
  let := Classical.decEq C
  rw [contractionIncl, homInclusion_eq_lof, DirectSum.toModule_lof, LinearMap.comp_apply]

private theorem contractionProj_homInclusion (X Y : C) (f : homModule (R := K) X Y) :
    𝒞.contractionProj (homInclusion X Y f) =
      homInclusion (R := K) (C := 𝒞.CohomologyQuiver) ⟨X⟩ ⟨Y⟩
        ((𝒞.homAlgebra X Y).cohomologyContraction.proj f) := by
  let := Classical.decEq C
  rw [contractionProj, homInclusion_eq_lof, DirectSum.toModule_lof, LinearMap.comp_apply]

private theorem contractionHomotopy_homInclusion (X Y : C) (f : homModule (R := K) X Y) :
    𝒞.contractionHomotopy (homInclusion X Y f) =
      homInclusion X Y ((𝒞.homAlgebra X Y).cohomologyContraction.homotopy f) := by
  classical
  rw [contractionHomotopy, homInclusion_eq_lof, DirectSum.lmap_lof]

/-- **The cohomology contraction of an `A∞` category** over a field: the special contraction of
the total complex of morphisms of `𝒞`, with differential `m₁`, onto the total module of morphisms
of the cohomology quiver with zero differential, given on each hom module by the cohomology
contraction of its Hom complex. -/
noncomputable def cohomologyContraction :
    LinearSpecialContraction 𝒞.differential (0 : Module.End K (TotalHom K 𝒞.CohomologyQuiver)) where
  incl := 𝒞.contractionIncl
  proj := 𝒞.contractionProj
  homotopy := 𝒞.contractionHomotopy
  dM_comp_incl := totalHom_linearMap_ext fun X Y a ↦ by
    have h := (𝒞.homAlgebra X.obj Y.obj).cohomologyContraction.dM_incl_apply a
    rw [homAlgebra_differential_apply] at h
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero, contractionIncl_homInclusion,
      ← homInclusion_homDifferential, h]
  proj_comp_dM := totalHom_linearMap_ext fun X Y f ↦ by
    have h := (𝒞.homAlgebra X Y).cohomologyContraction.proj_dM_apply f
    rw [homAlgebra_differential_apply] at h
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero, contractionProj_homInclusion,
      ← homInclusion_homDifferential, h]
  proj_comp_incl := totalHom_linearMap_ext fun X Y a ↦ by
    simp [contractionIncl_homInclusion, contractionProj_homInclusion]
  dM_comp_homotopy_add_homotopy_comp_dM := totalHom_linearMap_ext fun X Y f ↦ by
    have h := LinearMap.congr_fun
      (𝒞.homAlgebra X Y).cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM f
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, homAlgebra_differential_apply] at h
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, contractionHomotopy_homInclusion, contractionProj_homInclusion,
      contractionIncl_homInclusion, ← homInclusion_homDifferential]
    rw [← map_add, h, map_sub]
  homotopy_comp_incl := totalHom_linearMap_ext fun X Y a ↦ by
    simp [contractionIncl_homInclusion, contractionHomotopy_homInclusion]
  proj_comp_homotopy := totalHom_linearMap_ext fun X Y f ↦ by
    simp [contractionHomotopy_homInclusion, contractionProj_homInclusion]
  homotopy_comp_homotopy := totalHom_linearMap_ext fun X Y f ↦ by
    simp [contractionHomotopy_homInclusion]

/-- The inclusion of the cohomology contraction chooses cycle representatives in the Hom complex
between the underlying objects. -/
@[simp]
theorem cohomologyContraction_incl_homInclusion (X Y : 𝒞.CohomologyQuiver)
    (a : homModule (R := K) X Y) :
    𝒞.cohomologyContraction.incl (homInclusion X Y a) =
      homInclusion X.obj Y.obj ((𝒞.homAlgebra X.obj Y.obj).cohomologyContraction.incl a) :=
  𝒞.contractionIncl_homInclusion X Y a

/-- The projection of the cohomology contraction is the projection of the cohomology contraction
of each Hom complex. -/
@[simp]
theorem cohomologyContraction_proj_homInclusion (X Y : 𝒞.CohomologyQuiver)
    (f : homModule (R := K) X.obj Y.obj) :
    𝒞.cohomologyContraction.proj (homInclusion X.obj Y.obj f) =
      homInclusion X Y ((𝒞.homAlgebra X.obj Y.obj).cohomologyContraction.proj f) :=
  𝒞.contractionProj_homInclusion X.obj Y.obj f

/-- The homotopy of the cohomology contraction is the homotopy of the cohomology contraction of
each Hom complex. -/
@[simp]
theorem cohomologyContraction_homotopy_homInclusion (X Y : C) (f : homModule (R := K) X Y) :
    𝒞.cohomologyContraction.homotopy (homInclusion X Y f) =
      homInclusion X Y ((𝒞.homAlgebra X Y).cohomologyContraction.homotopy f) :=
  𝒞.contractionHomotopy_homInclusion X Y f

/-- The homotopy of the cohomology contraction has degree minus one. -/
theorem isHomogeneous_cohomologyContraction_homotopy :
    LinearMap.IsHomogeneous 𝒞.cohomologyContraction.homotopy 𝒞.grading.piece
      𝒞.grading.piece (-1) := by
  rw [LinearMap.isHomogeneous_def, 𝒞.grading_eq]
  intro p x hx
  refine totalGrading_piece_induction
    (P := fun x ↦ 𝒞.cohomologyContraction.homotopy x ∈ (totalGrading K C).piece (p + -1))
    (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun X Y f hf ↦ ?_) hx
  have h := (𝒞.homAlgebra X Y).isHomogeneous_cohomologyContraction_homotopy
  rw [homAlgebra_grading] at h
  rw [cohomologyContraction_homotopy_homInclusion, homInclusion_mem_totalGrading_piece_iff]
  exact h.map_mem hf

/-- The inclusion of the cohomology contraction has degree zero. -/
theorem isHomogeneous_cohomologyContraction_incl :
    LinearMap.IsHomogeneous 𝒞.cohomologyContraction.incl
      (totalGrading K 𝒞.CohomologyQuiver).piece 𝒞.grading.piece 0 := by
  rw [LinearMap.isHomogeneous_def, 𝒞.grading_eq]
  intro p x hx
  refine totalGrading_piece_induction
    (P := fun x ↦ 𝒞.cohomologyContraction.incl x ∈ (totalGrading K C).piece (p + 0))
    (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun X Y a ha ↦ ?_) hx
  have h := (𝒞.homAlgebra X.obj Y.obj).isHomogeneous_cohomologyContraction_incl
  rw [homAlgebra_grading] at h
  rw [cohomologyContraction_incl_homInclusion, homInclusion_mem_totalGrading_piece_iff]
  exact h.map_mem ha

/-- The projection of the cohomology contraction has degree zero. -/
theorem isHomogeneous_cohomologyContraction_proj :
    LinearMap.IsHomogeneous 𝒞.cohomologyContraction.proj 𝒞.grading.piece
      (totalGrading K 𝒞.CohomologyQuiver).piece 0 := by
  rw [LinearMap.isHomogeneous_def, 𝒞.grading_eq]
  intro p x hx
  refine totalGrading_piece_induction
    (P := fun x ↦
      𝒞.cohomologyContraction.proj x ∈ (totalGrading K 𝒞.CohomologyQuiver).piece (p + 0))
    (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    (fun X Y f hf ↦ ?_) hx
  have h := (𝒞.homAlgebra X Y).isHomogeneous_cohomologyContraction_proj
  rw [homAlgebra_grading] at h
  rw [cohomologyContraction_proj_homInclusion (X := ⟨X⟩) (Y := ⟨Y⟩),
    homInclusion_mem_totalGrading_piece_iff]
  exact h.map_mem hf

/-- **The cohomology contraction is compatible with the hom modules**, along the identification of
the objects of the cohomology quiver with those of `C`. -/
theorem isHomCompatible_cohomologyContraction :
    𝒞.cohomologyContraction.IsHomCompatible 𝒞.cohomologyQuiverEquiv where
  incl_homInclusion_mem X Y a := by
    rw [cohomologyContraction_incl_homInclusion, cohomologyQuiverEquiv_apply,
      cohomologyQuiverEquiv_apply]
    exact LinearMap.mem_range_self _ _
  proj_homInclusion_mem U V f := by
    rw [cohomologyContraction_proj_homInclusion (X := ⟨U⟩) (Y := ⟨V⟩),
      cohomologyQuiverEquiv_symm_apply, cohomologyQuiverEquiv_symm_apply]
    exact LinearMap.mem_range_self _ _
  homotopy_homInclusion_mem U V f := by
    rw [cohomologyContraction_homotopy_homInclusion]
    exact LinearMap.mem_range_self _ _

/-! ### The minimal model -/

/-- The **minimal model** of an `A∞` category over a field: the `A∞` category on the quiver of Hom
cohomologies transferred along the cohomology contraction.  Its differential vanishes
(`homDifferential_minimalModel`), its composition is the composition induced on cohomology
(`comp_minimalModel_cohomologyClass`), and its higher operations are the transferred ones. -/
noncomputable def minimalModel : AInfinityCategory K 𝒞.CohomologyQuiver :=
  𝒞.transfer 𝒞.cohomologyQuiverEquiv 𝒞.cohomologyContraction
    𝒞.isHomogeneous_cohomologyContraction_homotopy 𝒞.isHomogeneous_cohomologyContraction_incl
    𝒞.isHomogeneous_cohomologyContraction_proj 𝒞.isHomCompatible_cohomologyContraction

/-- The total algebra of morphisms of the minimal model is the `A∞` algebra transferred from the
total algebra of morphisms of `𝒞` along the cohomology contraction. -/
theorem minimalModel_toAInfinityAlgebra :
    𝒞.minimalModel.toAInfinityAlgebra =
      𝒞.toAInfinityAlgebra.transfer 𝒞.cohomologyContraction
        𝒞.isHomogeneous_cohomologyContraction_homotopy 𝒞.isHomogeneous_cohomologyContraction_incl
        𝒞.isHomogeneous_cohomologyContraction_proj :=
  transfer_toAInfinityAlgebra ..

/-- The differential of the minimal model vanishes. -/
@[simp]
theorem homDifferential_minimalModel (X Y : 𝒞.CohomologyQuiver) :
    𝒞.minimalModel.homDifferential X Y = 0 := by
  ext a
  apply homInclusion_injective X Y
  rw [minimalModel, homInclusion_homDifferential_transfer, LinearMap.zero_apply,
    LinearMap.zero_apply, map_zero]

/-- **The minimal model is minimal**: the unary operation of its total algebra vanishes. -/
theorem isMinimal_minimalModel : 𝒞.minimalModel.IsMinimal := by
  rw [minimalModel_toAInfinityAlgebra]
  exact AInfinityAlgebra.isMinimal_transfer _ _ _ _ _ rfl

/-- **The composition of the minimal model is the composition induced on cohomology**:
`[g] ∘ [f] = [g ∘ f]` for closed morphisms `g` and `f`. -/
theorem comp_minimalModel_cohomologyClass {X Y Z : 𝒞.CohomologyQuiver}
    {g : homModule (R := K) Y.obj Z.obj} {f : homModule (R := K) X.obj Y.obj}
    (hg : g ∈ (𝒞.homAlgebra Y.obj Z.obj).cycles) (hf : f ∈ (𝒞.homAlgebra X.obj Y.obj).cycles) :
    𝒞.minimalModel.comp X Y Z ((𝒞.homAlgebra Y.obj Z.obj).cohomologyClass hg)
        ((𝒞.homAlgebra X.obj Y.obj).cohomologyClass hf) =
      (𝒞.homAlgebra X.obj Z.obj).cohomologyClass (𝒞.comp_mem_homAlgebra_cycles hg hf) := by
  apply homInclusion_injective X Z
  have hg' := (𝒞.homAlgebra Y.obj Z.obj).cohomologyContraction_incl_mem_cycles
    ((𝒞.homAlgebra Y.obj Z.obj).cohomologyClass hg)
  have hf' := (𝒞.homAlgebra X.obj Y.obj).cohomologyContraction_incl_mem_cycles
    ((𝒞.homAlgebra X.obj Y.obj).cohomologyClass hf)
  rw [minimalModel, homInclusion_comp_transfer, cohomologyContraction_incl_homInclusion,
    cohomologyContraction_incl_homInclusion, ← homInclusion_comp,
    cohomologyContraction_proj_homInclusion,
    AInfinityAlgebra.cohomologyContraction_proj_of_mem_cycles _
      (𝒞.comp_mem_homAlgebra_cycles hg' hf')]
  congr 1
  exact 𝒞.cohomologyClass_comp_congr hg' hf' hg hf
    (AInfinityAlgebra.cohomologyClass_cohomologyContraction_incl ..)
    (AInfinityAlgebra.cohomologyClass_cohomologyContraction_incl ..)

end AInfinityCategory

end TauCeti
