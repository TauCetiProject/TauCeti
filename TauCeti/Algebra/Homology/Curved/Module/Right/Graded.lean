/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Shift
public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.CategoryTheory.DG.Preadditive

/-!
# Forgetting the differential of curved right modules

The underlying graded right module is an object of the existing graded module category over
the opposite algebra. Forgetting the differential of a closed map gives a faithful additive
linear functor which reflects isomorphisms. Cohomological shift by `n` corresponds to grading
shift by `-n`, since both
replace the degree-`p` piece by the degree-`(p + n)` piece.

This functor detects the graded splittings used in the Frobenius exact structure on curved
right modules. A graded splitting need not commute with the differentials.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Category.GradedModuleCat.Abelian`: the reflection
  of isomorphisms proof adapts the corresponding forgetful-functor proof.
-/

public section

open CategoryTheory

namespace TauCeti.CurvedDGRightModuleCat

universe uR uA uM u

section Objects

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The underlying graded right module, viewed as a graded module over the opposite algebra. -/
@[expose, implicit_reducible]
noncomputable def gradedObject (M : CurvedDGRightModuleCat.{uR, uA, uM} h) :
    GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece where
  carrier := M
  grading := InternalGrading.ofDecomposition M.grading
  gradedSMul := by
    simpa only [InternalGrading.ofDecomposition_piece] using M.gradedSMul

/-- Forgetting the differential preserves the homogeneous pieces. -/
@[simp]
theorem gradedObject_piece (M : CurvedDGRightModuleCat.{uR, uA, uM} h) (p : ℤ) :
    (gradedObject M).grading.piece p = M.grading p :=
  congrFun (InternalGrading.ofDecomposition_piece M.grading) p

end Objects

-- The closed category keeps the original module objects.
attribute [local implicit_reducible] ForgetEnrichment EnrichedFunctor.ofDGMap

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- Forget the differential of a curved module and the closedness of a degree-zero map. -/
@[expose, implicit_reducible]
noncomputable def forgetDifferential :
    ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h) ⥤
      GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece where
  obj M := gradedObject (ForgetEnrichment.to _ M)
  map f := GradedModuleCat.ofHom (closedHom f)
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      simp only [gradedObject_piece, add_zero] at hx ⊢
      exact closedHom_mem f hx)
  map_id M := GradedModuleCat.hom_ext (closedHom_id _)
  map_comp f g := GradedModuleCat.hom_ext (closedHom_comp f g)

/-- The graded forgetful functor takes a curved module to its underlying graded right module. -/
@[simp]
theorem forgetDifferential_obj_of (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (forgetDifferential (h := h)).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      gradedObject M :=
  (rfl)

/-- The graded forgetful functor acts by the underlying right-linear map. -/
@[simp]
theorem forgetDifferential_map_hom {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    ((forgetDifferential (h := h)).map f).hom = closedHom f :=
  (rfl)

instance : (forgetDifferential (h := h)).Faithful where
  map_injective hfg := closedHom_injective (congrArg GradedModuleCat.Hom.hom hfg)

instance : (forgetDifferential (h := h)).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    let e : (ForgetEnrichment.to _ M : CurvedDGRightModuleCat.{u, u, u} h) ≃ₗ[Aᵐᵒᵖ]
        (ForgetEnrichment.to _ N : CurvedDGRightModuleCat.{u, u, u} h) :=
      ((GradedModuleCat.toModuleCat).mapIso
      (asIso ((forgetDifferential (h := h)).map f))).toLinearEquiv
    have heMap : e.toLinearMap = closedHom f := by
      dsimp only [e]
      rw [Iso.toLinearMap_toLinearEquiv]
      rfl
    have he : LinearMap.IsHomogeneous e.toLinearMap
        (InternalGrading.ofDecomposition (ForgetEnrichment.to _ M).grading).piece
        (InternalGrading.ofDecomposition (ForgetEnrichment.to _ N).grading).piece 0 := by
      rw [heMap]
      apply LinearMap.isHomogeneous_def.mpr
      intro p x hx
      simp only [InternalGrading.ofDecomposition_piece, add_zero] at hx ⊢
      exact closedHom_mem f hx
    have hd : ∀ x, (ForgetEnrichment.to _ N).differential (e x) =
        e ((ForgetEnrichment.to _ M).differential x) := by
      change ∀ x, (ForgetEnrichment.to _ N).differential (e.toLinearMap x) =
        e.toLinearMap ((ForgetEnrichment.to _ M).differential x)
      rw [heMap]
      exact differential_closedHom f
    let i := closedIsoOf e (fun p x ↦ by
      constructor
      · intro hx
        have hx' : x ∈
            (InternalGrading.ofDecomposition (ForgetEnrichment.to _ M).grading).piece p := by
          simpa only [InternalGrading.ofDecomposition_piece] using hx
        simpa only [InternalGrading.ofDecomposition_piece, add_zero, LinearEquiv.coe_coe]
          using he.map_mem hx'
      · intro hx
        have hx' : e x ∈
            (InternalGrading.ofDecomposition (ForgetEnrichment.to _ N).grading).piece p := by
          simpa only [InternalGrading.ofDecomposition_piece] using hx
        simpa only [InternalGrading.ofDecomposition_piece, add_zero, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply] using
          (LinearMap.IsHomogeneous.linearEquiv_symm he).map_mem hx') hd
    have hi : i.hom = f := by
      apply closedHom_injective
      dsimp only [i]
      rw [closedHom_closedIsoOf_hom]
      exact heMap
    rw [← hi]
    infer_instance

instance : (forgetDifferential (h := h)).Additive where
  map_add {M N f g} := by
    apply GradedModuleCat.hom_ext
    change closedHom (f + g) = closedHom f + closedHom g
    simp only [closedHom_eq]
    rw [dgClosedHom_add R f g, map_add]
    rfl

instance : (forgetDifferential (h := h)).Linear R where
  map_smul {M N} f r := by
    apply GradedModuleCat.hom_ext
    change closedHom (r • f) = r • closedHom f
    simp only [closedHom_eq]
    rw [dgClosedHom_smul R r f, map_smul]
    rfl

/-- After forgetting the differential, cohomological shift by `n` is grading shift by `-n`. -/
noncomputable def closedShiftFunctorCompForgetDifferentialIso (n : ℤ) :
    closedShiftFunctor (h := h) n ⋙ forgetDifferential ≅
      forgetDifferential ⋙ GradedModuleCat.shiftFunctor (-n) :=
  NatIso.ofComponents (fun M ↦
    GradedModuleCat.isoMk
      (LinearEquiv.refl Aᵐᵒᵖ (ForgetEnrichment.to _ M : CurvedDGRightModuleCat.{u, u, u} h))
      fun p x ↦ by
      change x ∈ (gradedObject ((ForgetEnrichment.to _ M).shift n)).grading.piece p ↔
        x ∈ ((gradedObject (ForgetEnrichment.to _ M)).shiftObj (-n)).grading.piece p
      rw [gradedObject_piece, shift_grading, GradedModuleCat.mem_shiftObj_piece_iff,
        gradedObject_piece, sub_neg_eq_add])
    (fun f ↦ by
      apply GradedModuleCat.hom_ext
      change LinearMap.id.comp (closedHom ((closedShiftFunctor n).map f)) =
        (closedHom f).comp LinearMap.id
      rw [LinearMap.id_comp, LinearMap.comp_id]
      exact closedHom_closedShiftFunctor_map n f)

/-- The shift comparison acts by the identity on underlying right modules. -/
@[simp]
theorem closedShiftFunctorCompForgetDifferentialIso_hom_app_hom (n : ℤ)
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    ((closedShiftFunctorCompForgetDifferentialIso (h := h) n).hom.app M).hom = LinearMap.id :=
  (rfl)

end TauCeti.CurvedDGRightModuleCat
