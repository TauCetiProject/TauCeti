/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.LinearAlgebra.Graded.Splitting

/-!
# The minimal A-infinity model on cohomology

Over a field, the unary complex of an `A∞` algebra contracts onto its cohomology.  The
construction chooses homogeneous representatives of cohomology classes and homogeneous
degree-minus-one preimages of boundaries.  If `s` is the latter section, then
`q = 1 - s m₁` projects onto cycles.  The projection to cohomology is the class of `q x`, and
the contracting homotopy applies `s` to the boundary

`q x - i [q x]`.

These formulas give a special contraction with homogeneous inclusion, projection, and homotopy.
Applying homological transfer produces the minimal `A∞` structure on cohomology and a
quasi-isomorphism to the original algebra.  Its binary operation is the product already induced
on cohomology, so this is Kadeishvili's existence theorem with the multiplication pinned rather
than merely an abstract minimal structure.

## Main definitions

* `TauCeti.AInfinityAlgebra.cohomologyContraction`: a homogeneous special contraction of the
  unary complex onto cohomology with zero differential.
* `TauCeti.AInfinityAlgebra.minimalModel`: the transferred `A∞` structure on cohomology.
* `TauCeti.AInfinityAlgebra.minimalModelInclusion`: the extending quasi-isomorphism from the
  minimal model to the original algebra.

## Main results

* `TauCeti.AInfinityAlgebra.isMinimal_minimalModel`: the transferred structure is minimal.
* `TauCeti.AInfinityAlgebra.minimalModel_m_two`: its binary operation is the cohomology product.
* `TauCeti.AInfinityAlgebra.isQuasiIso_minimalModelInclusion`: the extending morphism is a
  quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.cohomologyMap_minimalModelInclusion_cohomologyEquiv`: the extending
  morphism induces the identity on cohomology.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

open DirectSum

namespace TauCeti.AInfinityAlgebra

universe uK uA

variable {K : Type uK} {A : Type uA} [Field K] [AddCommGroup A] [Module K A]
  (𝒜 : AInfinityAlgebra K A)

private theorem isHomogeneous_differential :
    LinearMap.IsHomogeneous 𝒜.differential 𝒜.grading.piece 𝒜.grading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.differential_mem_piece hx

private theorem isHomogeneous_boundaries :
    SetLike.IsHomogeneous 𝒜.grading.piece 𝒜.boundaries := by
  rw [boundaries_def]
  exact 𝒜.isHomogeneous_differential.isHomogeneous_range

private noncomputable def boundariesGrading : InternalGrading K 𝒜.boundaries :=
  𝒜.grading.submodule 𝒜.boundaries 𝒜.isHomogeneous_boundaries

private def toBoundaries : A →ₗ[K] 𝒜.boundaries :=
  𝒜.differential.codRestrict 𝒜.boundaries fun x ↦ 𝒜.differential_mem_boundaries x

private theorem isHomogeneous_toBoundaries :
    LinearMap.IsHomogeneous 𝒜.toBoundaries 𝒜.grading.piece
      𝒜.boundariesGrading.piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  exact (𝒜.grading.mem_submodule_piece 𝒜.boundaries
    𝒜.isHomogeneous_boundaries).2 (𝒜.differential_mem_piece hx)

/-- A cycle has zero boundary. -/
private theorem toBoundaries_eq_zero_of_mem_cycles {x : A} (hx : x ∈ 𝒜.cycles) :
    𝒜.toBoundaries x = 0 := by
  apply Subtype.ext
  rw [toBoundaries, LinearMap.codRestrict_apply, ZeroMemClass.coe_zero]
  rwa [cycles_def, LinearMap.mem_ker] at hx

private theorem toBoundaries_surjective : Function.Surjective 𝒜.toBoundaries := by
  rintro ⟨y, hy⟩
  rw [boundaries_def, LinearMap.mem_range] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

private noncomputable def boundaryPreimage : 𝒜.boundaries →ₗ[K] A :=
  Classical.choose (𝒜.isHomogeneous_toBoundaries.exists_rightInverse
    𝒜.toBoundaries_surjective)

private theorem toBoundaries_comp_boundaryPreimage :
    𝒜.toBoundaries ∘ₗ 𝒜.boundaryPreimage = LinearMap.id :=
  (Classical.choose_spec (𝒜.isHomogeneous_toBoundaries.exists_rightInverse
    𝒜.toBoundaries_surjective)).1

private theorem isHomogeneous_boundaryPreimage :
    LinearMap.IsHomogeneous 𝒜.boundaryPreimage 𝒜.boundariesGrading.piece
      𝒜.grading.piece (-1) :=
  (Classical.choose_spec (𝒜.isHomogeneous_toBoundaries.exists_rightInverse
    𝒜.toBoundaries_surjective)).2

private theorem differential_boundaryPreimage (b : 𝒜.boundaries) :
    𝒜.differential (𝒜.boundaryPreimage b) = b := by
  have h := LinearMap.congr_fun 𝒜.toBoundaries_comp_boundaryPreimage b
  exact congrArg Subtype.val h

private def classMap : 𝒜.cycles →ₗ[K] 𝒜.Cohomology :=
  𝒜.boundariesInCycles.mkQ

private theorem isHomogeneous_classMap :
    LinearMap.IsHomogeneous 𝒜.classMap 𝒜.cyclesGrading.piece
      𝒜.cohomologyGrading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  rw [add_zero]
  have heq : 𝒜.cohomologyClass z.2 = 𝒜.classMap z := by
    rw [𝒜.cohomologyClass_eq_mk]
    unfold classMap
    congr 1
  exact 𝒜.mem_cohomologyGrading_piece_iff.2
    ⟨z, z.2, 𝒜.mem_cyclesGrading_piece.mp hz, heq⟩

private theorem classMap_surjective : Function.Surjective 𝒜.classMap := by
  exact Submodule.mkQ_surjective 𝒜.boundariesInCycles

private noncomputable def cycleRepresentative : 𝒜.Cohomology →ₗ[K] 𝒜.cycles :=
  Classical.choose (𝒜.isHomogeneous_classMap.exists_rightInverse
    𝒜.classMap_surjective)

private theorem cohomologyClass_comp_cycleRepresentative :
    𝒜.classMap ∘ₗ 𝒜.cycleRepresentative = LinearMap.id :=
  (Classical.choose_spec
    (𝒜.isHomogeneous_classMap.exists_rightInverse 𝒜.classMap_surjective)).1

private theorem isHomogeneous_cycleRepresentative :
    LinearMap.IsHomogeneous 𝒜.cycleRepresentative 𝒜.cohomologyGrading.piece
      𝒜.cyclesGrading.piece 0 :=
  (Classical.choose_spec
    (𝒜.isHomogeneous_classMap.exists_rightInverse 𝒜.classMap_surjective)).2

private theorem classMap_apply (z : 𝒜.cycles) :
    𝒜.classMap z = 𝒜.cohomologyClass z.2 := by
  unfold classMap
  rw [𝒜.cohomologyClass_eq_mk]
  congr 1

private theorem cohomologyClass_cycleRepresentative (x : 𝒜.Cohomology) :
    𝒜.classMap (𝒜.cycleRepresentative x) = x := by
  exact LinearMap.congr_fun 𝒜.cohomologyClass_comp_cycleRepresentative x

private noncomputable def contractionIncl : 𝒜.Cohomology →ₗ[K] A :=
  𝒜.cycles.subtype ∘ₗ 𝒜.cycleRepresentative

private noncomputable def cycleProjectionAmbient : Module.End K A :=
  LinearMap.id - 𝒜.boundaryPreimage ∘ₗ 𝒜.toBoundaries

private theorem cycleProjectionAmbient_apply (x : A) :
    𝒜.cycleProjectionAmbient x = x - 𝒜.boundaryPreimage (𝒜.toBoundaries x) :=
  rfl

private theorem cycleProjectionAmbient_mem_cycles (x : A) :
    𝒜.cycleProjectionAmbient x ∈ 𝒜.cycles := by
  rw [cycles_def, LinearMap.mem_ker, cycleProjectionAmbient_apply, map_sub,
    𝒜.differential_boundaryPreimage]
  -- Expose the codomain-subtype coercion left by `differential_boundaryPreimage`.
  change 𝒜.differential x - 𝒜.differential x = 0
  exact sub_self _

private noncomputable def cycleProjection : A →ₗ[K] 𝒜.cycles :=
  𝒜.cycleProjectionAmbient.codRestrict 𝒜.cycles
    𝒜.cycleProjectionAmbient_mem_cycles

private theorem coe_cycleProjection (x : A) :
    (𝒜.cycleProjection x : A) =
      x - 𝒜.boundaryPreimage (𝒜.toBoundaries x) :=
  rfl

private theorem isHomogeneous_cycleProjection :
    LinearMap.IsHomogeneous 𝒜.cycleProjection 𝒜.grading.piece
      𝒜.cyclesGrading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero, 𝒜.mem_cyclesGrading_piece, coe_cycleProjection]
  exact Submodule.sub_mem _ hx <|
    by simpa only [add_assoc, add_neg_cancel, add_zero] using
      𝒜.isHomogeneous_boundaryPreimage.map_mem
        (𝒜.isHomogeneous_toBoundaries.map_mem hx)

private noncomputable def contractionProj : A →ₗ[K] 𝒜.Cohomology :=
  𝒜.classMap ∘ₗ 𝒜.cycleProjection

private theorem contractionProj_apply (x : A) :
    𝒜.contractionProj x = 𝒜.classMap (𝒜.cycleProjection x) :=
  rfl

private theorem contractionProj_incl (x : 𝒜.Cohomology) :
    𝒜.contractionProj (𝒜.contractionIncl x) = x := by
  rw [contractionProj_apply]
  have hd := 𝒜.toBoundaries_eq_zero_of_mem_cycles (x := 𝒜.contractionIncl x)
    (𝒜.cycleRepresentative x).2
  apply Eq.trans _ (𝒜.cohomologyClass_cycleRepresentative x)
  congr 1
  apply Subtype.ext
  rw [coe_cycleProjection, hd, map_zero, sub_zero]
  rfl

private theorem cycleProjection_incl (x : 𝒜.Cohomology) :
    𝒜.cycleProjection (𝒜.contractionIncl x) = 𝒜.cycleRepresentative x := by
  apply Subtype.ext
  rw [coe_cycleProjection, 𝒜.toBoundaries_eq_zero_of_mem_cycles (x := 𝒜.contractionIncl x)
    (𝒜.cycleRepresentative x).2, map_zero, sub_zero]
  rfl

private theorem contractionProj_differential (x : A) :
    𝒜.contractionProj (𝒜.differential x) = 0 := by
  rw [contractionProj_apply]
  rw [classMap_apply]
  apply (𝒜.cohomologyClass_eq_zero_iff _).2
  rw [coe_cycleProjection]
  have hdd : 𝒜.toBoundaries (𝒜.differential x) = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun 𝒜.differential_comp_self_eq_zero x
  rw [hdd, map_zero, sub_zero]
  exact 𝒜.differential_mem_boundaries x

private noncomputable def boundaryResidual : A →ₗ[K] 𝒜.boundaries :=
  (𝒜.cycles.subtype ∘ₗ 𝒜.cycleProjection -
      𝒜.contractionIncl ∘ₗ 𝒜.contractionProj).codRestrict 𝒜.boundaries fun x ↦ by
    apply (𝒜.cohomologyClass_eq_iff (𝒜.cycleProjection x).2
      (𝒜.cycleRepresentative (𝒜.contractionProj x)).2).1
    rw [← classMap_apply, ← classMap_apply, 𝒜.cohomologyClass_cycleRepresentative,
      contractionProj_apply]

private theorem coe_boundaryResidual (x : A) :
    (𝒜.boundaryResidual x : A) =
      𝒜.cycleProjection x - 𝒜.contractionIncl (𝒜.contractionProj x) :=
  rfl

private noncomputable def contractionHomotopy : Module.End K A :=
  𝒜.boundaryPreimage ∘ₗ 𝒜.boundaryResidual

private theorem differential_contractionHomotopy (x : A) :
    𝒜.differential (𝒜.contractionHomotopy x) =
      𝒜.cycleProjection x - 𝒜.contractionIncl (𝒜.contractionProj x) := by
  rw [contractionHomotopy, LinearMap.comp_apply, differential_boundaryPreimage,
    coe_boundaryResidual]

private theorem boundaryResidual_differential (x : A) :
    𝒜.boundaryResidual (𝒜.differential x) = 𝒜.toBoundaries x := by
  apply Subtype.ext
  rw [coe_boundaryResidual, contractionProj_differential, map_zero, sub_zero, coe_cycleProjection]
  have hdd : 𝒜.toBoundaries (𝒜.differential x) = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun 𝒜.differential_comp_self_eq_zero x
  rw [hdd, map_zero, sub_zero]
  rfl

private theorem contractionHomotopy_differential (x : A) :
    𝒜.contractionHomotopy (𝒜.differential x) =
      𝒜.boundaryPreimage (𝒜.toBoundaries x) := by
  rw [contractionHomotopy, LinearMap.comp_apply, boundaryResidual_differential]

private theorem cycleProjection_boundaryPreimage (b : 𝒜.boundaries) :
    𝒜.cycleProjection (𝒜.boundaryPreimage b) = 0 := by
  apply Subtype.ext
  rw [coe_cycleProjection]
  have h := LinearMap.congr_fun 𝒜.toBoundaries_comp_boundaryPreimage b
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h, sub_self]
  rfl

private theorem contractionProj_boundaryPreimage (b : 𝒜.boundaries) :
    𝒜.contractionProj (𝒜.boundaryPreimage b) = 0 := by
  rw [contractionProj_apply, cycleProjection_boundaryPreimage, map_zero]

private theorem boundaryResidual_incl (x : 𝒜.Cohomology) :
    𝒜.boundaryResidual (𝒜.contractionIncl x) = 0 := by
  apply Subtype.ext
  rw [coe_boundaryResidual, contractionProj_incl, cycleProjection_incl]
  -- Expose both occurrences of the cycle representative in the ambient space.
  change (𝒜.cycleRepresentative x : A) - 𝒜.cycleRepresentative x = 0
  exact sub_self _

private theorem boundaryResidual_boundaryPreimage (b : 𝒜.boundaries) :
    𝒜.boundaryResidual (𝒜.boundaryPreimage b) = 0 := by
  apply Subtype.ext
  rw [coe_boundaryResidual, cycleProjection_boundaryPreimage,
    contractionProj_boundaryPreimage, map_zero, sub_zero]
  rfl

private theorem contractionHomotopy_boundaryPreimage (b : 𝒜.boundaries) :
    𝒜.contractionHomotopy (𝒜.boundaryPreimage b) = 0 := by
  rw [contractionHomotopy, LinearMap.comp_apply, boundaryResidual_boundaryPreimage, map_zero]

/-- Over a field, the unary complex of an `A∞` algebra admits a homogeneous special
contraction onto its cohomology with zero differential. -/
noncomputable def cohomologyContraction :
    LinearSpecialContraction 𝒜.differential (0 : Module.End K 𝒜.Cohomology) where
  incl := 𝒜.contractionIncl
  proj := 𝒜.contractionProj
  homotopy := 𝒜.contractionHomotopy
  dM_comp_incl := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    rw [LinearMap.zero_apply, map_zero]
    rw [contractionIncl, LinearMap.comp_apply]
    -- Expose the inclusion through cycles so its cycle equation is the goal.
    change 𝒜.differential (𝒜.cycleRepresentative x : A) = 0
    have h := 𝒜.mem_cycles.mp (𝒜.cycleRepresentative x).2
    rwa [← differential_apply] at h
  proj_comp_dM := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, contractionProj_differential, LinearMap.comp_apply,
      LinearMap.zero_apply]
  proj_comp_incl := by
    apply LinearMap.ext
    intro x
    exact 𝒜.contractionProj_incl x
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      differential_contractionHomotopy, contractionHomotopy_differential,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, coe_cycleProjection]
    abel
  homotopy_comp_incl := by
    apply LinearMap.ext
    intro x
    -- Expose the structure projections as the private maps whose interaction was proved above.
    change 𝒜.contractionHomotopy (𝒜.contractionIncl x) = 0
    rw [contractionHomotopy, LinearMap.comp_apply,
      boundaryResidual_incl, map_zero]
  proj_comp_homotopy := by
    apply LinearMap.ext
    intro x
    -- Expose the structure projections as the private maps whose interaction was proved above.
    change 𝒜.contractionProj (𝒜.contractionHomotopy x) = 0
    rw [contractionHomotopy, LinearMap.comp_apply,
      contractionProj_boundaryPreimage]
  homotopy_comp_homotopy := by
    apply LinearMap.ext
    intro x
    -- Expose the structure projections as the private maps whose interaction was proved above.
    change 𝒜.contractionHomotopy (𝒜.contractionHomotopy x) = 0
    have hi : 𝒜.contractionHomotopy x =
        𝒜.boundaryPreimage (𝒜.boundaryResidual x) := rfl
    rw [hi, contractionHomotopy_boundaryPreimage]

/-- The inclusion of the cohomology contraction is a cycle. -/
theorem cohomologyContraction_incl_mem_cycles (x : 𝒜.Cohomology) :
    𝒜.cohomologyContraction.incl x ∈ 𝒜.cycles := by
  -- Expose the contraction inclusion as the chosen cycle representative.
  change (𝒜.cycleRepresentative x : A) ∈ 𝒜.cycles
  exact (𝒜.cycleRepresentative x).2

/-- The inclusion of the cohomology contraction chooses a representative of the given class. -/
@[simp]
theorem cohomologyClass_cohomologyContraction_incl (x : 𝒜.Cohomology) :
    𝒜.cohomologyClass (𝒜.cohomologyContraction_incl_mem_cycles x) = x := by
  calc
    _ = 𝒜.classMap (𝒜.cycleRepresentative x) := by
      symm
      apply 𝒜.classMap_apply
    _ = x := 𝒜.cohomologyClass_cycleRepresentative x

/-- The inclusion of the cohomology contraction has degree zero. -/
theorem isHomogeneous_cohomologyContraction_incl :
    LinearMap.IsHomogeneous 𝒜.cohomologyContraction.incl 𝒜.cohomologyGrading.piece
      𝒜.grading.piece 0 := by
  -- Expose the contraction field as the private inclusion to use its construction.
  change LinearMap.IsHomogeneous 𝒜.contractionIncl 𝒜.cohomologyGrading.piece
    𝒜.grading.piece 0
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero, contractionIncl, LinearMap.comp_apply]
  exact 𝒜.mem_cyclesGrading_piece.mp <| by
    simpa only [add_zero] using 𝒜.isHomogeneous_cycleRepresentative.map_mem hx

/-- The projection of the cohomology contraction has degree zero. -/
theorem isHomogeneous_cohomologyContraction_proj :
    LinearMap.IsHomogeneous 𝒜.cohomologyContraction.proj 𝒜.grading.piece
      𝒜.cohomologyGrading.piece 0 := by
  -- Expose the contraction field as the private projection to use its construction.
  change LinearMap.IsHomogeneous 𝒜.contractionProj 𝒜.grading.piece
    𝒜.cohomologyGrading.piece 0
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero, contractionProj, LinearMap.comp_apply]
  simpa only [add_zero] using 𝒜.isHomogeneous_classMap.map_mem
    (𝒜.isHomogeneous_cycleProjection.map_mem hx)

/-- The homotopy of the cohomology contraction has degree minus one. -/
theorem isHomogeneous_cohomologyContraction_homotopy :
    LinearMap.IsHomogeneous 𝒜.cohomologyContraction.homotopy 𝒜.grading.piece
      𝒜.grading.piece (-1) := by
  -- Expose the contraction field as the private homotopy to use its construction.
  change LinearMap.IsHomogeneous 𝒜.contractionHomotopy 𝒜.grading.piece
    𝒜.grading.piece (-1)
  rw [LinearMap.isHomogeneous_def]
  intro p x hx
  exact 𝒜.isHomogeneous_boundaryPreimage.map_mem <| by
    rw [boundariesGrading, 𝒜.grading.mem_submodule_piece 𝒜.boundaries
      𝒜.isHomogeneous_boundaries]
    rw [coe_boundaryResidual]
    exact Submodule.sub_mem _ (𝒜.mem_cyclesGrading_piece.mp <| by
      simpa only [add_zero] using 𝒜.isHomogeneous_cycleProjection.map_mem hx) <|
      by simpa only [cohomologyContraction, add_zero] using
        𝒜.isHomogeneous_cohomologyContraction_incl.map_mem
          (𝒜.isHomogeneous_cohomologyContraction_proj.map_mem hx)

/-- The minimal `A∞` model on cohomology obtained by homogeneous transfer. -/
noncomputable def minimalModel : AInfinityAlgebra K 𝒜.Cohomology :=
  𝒜.transfer 𝒜.cohomologyContraction 𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl 𝒜.isHomogeneous_cohomologyContraction_proj

/-- The grading of the minimal model is the quotient grading on cohomology. -/
@[simp]
theorem minimalModel_grading : 𝒜.minimalModel.grading = 𝒜.cohomologyGrading := by
  rw [minimalModel, transfer_grading]

/-- The transferred model on cohomology is minimal. -/
theorem isMinimal_minimalModel : 𝒜.minimalModel.IsMinimal :=
  𝒜.isMinimal_transfer 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj rfl

/-- The differential of the minimal model vanishes. -/
@[simp]
theorem minimalModel_differential : 𝒜.minimalModel.differential = 0 :=
  (𝒜.minimalModel.isMinimal_def).mp 𝒜.isMinimal_minimalModel

/-- The binary operation of the minimal model is the product induced on cohomology. -/
@[simp]
theorem minimalModel_m_two (x y : 𝒜.Cohomology) :
    𝒜.minimalModel.m 2 ![x, y] = x * y := by
  rw [minimalModel, mul_transfer]
  -- Expose the contraction fields as their private maps to compute the transferred product.
  change 𝒜.contractionProj
      (𝒜.mul (𝒜.contractionIncl x) (𝒜.contractionIncl y)) = x * y
  rw [contractionProj_apply]
  -- Expose the inclusion through the chosen cycle representatives.
  change 𝒜.classMap (𝒜.cycleProjection
      (𝒜.mul (𝒜.cycleRepresentative x) (𝒜.cycleRepresentative y))) = x * y
  rw [classMap_apply]
  have hz : 𝒜.mul (𝒜.cycleRepresentative x) (𝒜.cycleRepresentative y) ∈
      𝒜.cycles := by
    simpa only [mul_apply] using 𝒜.m_two_mem_cycles
      (𝒜.cycleRepresentative x).2 (𝒜.cycleRepresentative y).2
  have hq : 𝒜.cycleProjection
      (𝒜.mul (𝒜.cycleRepresentative x) (𝒜.cycleRepresentative y)) =
      ⟨𝒜.mul (𝒜.cycleRepresentative x) (𝒜.cycleRepresentative y), hz⟩ := by
    apply Subtype.ext
    rw [coe_cycleProjection, 𝒜.toBoundaries_eq_zero_of_mem_cycles hz, map_zero, sub_zero]
  rw [hq]
  calc
    𝒜.cohomologyClass hz = 𝒜.cohomologyMul
        (𝒜.cohomologyClass (𝒜.cycleRepresentative x).2)
        (𝒜.cohomologyClass (𝒜.cycleRepresentative y).2) :=
      by simpa only [mul_apply] using
        (𝒜.cohomologyMul_cohomologyClass
          (𝒜.cycleRepresentative x).2 (𝒜.cycleRepresentative y).2).symm
    _ = x * y := by
      rw [← 𝒜.cohomology_mul_eq_cohomologyMul, ← classMap_apply,
        𝒜.cohomologyClass_cycleRepresentative, ← classMap_apply,
        𝒜.cohomologyClass_cycleRepresentative]

/-- The `A∞` morphism from the minimal model on cohomology to the original algebra, extending
the chosen cycle representatives. -/
noncomputable def minimalModelInclusion : AInfinityHom 𝒜.minimalModel 𝒜 :=
  𝒜.transferInclusion 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

/-- The linear part of the minimal-model quasi-isomorphism is the chosen inclusion of cohomology
representatives. -/
@[simp]
theorem linearPart_minimalModelInclusion :
    𝒜.minimalModelInclusion.linearPart = 𝒜.cohomologyContraction.incl := by
  unfold minimalModelInclusion minimalModel
  rw [linearPart_transferInclusion]

/-- The morphism from the minimal model to the original algebra induces the identity on
cohomology, once the minimal model is identified with its own cohomology. -/
theorem cohomologyMap_minimalModelInclusion_cohomologyEquiv (x : 𝒜.Cohomology) :
    𝒜.minimalModelInclusion.cohomologyMap (𝒜.isMinimal_minimalModel.cohomologyEquiv x) = x := by
  simp

/-- The morphism from the minimal model to the original algebra is a quasi-isomorphism. -/
theorem isQuasiIso_minimalModelInclusion : 𝒜.minimalModelInclusion.IsQuasiIso :=
  𝒜.isQuasiIso_transferInclusion 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

end TauCeti.AInfinityAlgebra
