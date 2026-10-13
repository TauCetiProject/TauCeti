/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Shift
public import TauCeti.Algebra.Category.GradedModuleCat.Basic

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
noncomputable def toGradedModuleCat (M : CurvedDGRightModuleCat.{uR, uA, uM} h) :
    GradedModuleCat.{uM} (InternalGrading.ofDecomposition 𝒜).opposite.piece where
  carrier := M
  grading := InternalGrading.ofDecomposition M.grading
  gradedSMul := by
    simpa only [InternalGrading.ofDecomposition_piece] using M.gradedSMul

/-- Forgetting the differential preserves the homogeneous pieces. -/
@[simp]
theorem toGradedModuleCat_piece (M : CurvedDGRightModuleCat.{uR, uA, uM} h) (p : ℤ) :
    (toGradedModuleCat M).grading.piece p = M.grading p :=
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
  obj M := toGradedModuleCat (ForgetEnrichment.to _ M)
  map f := GradedModuleCat.ofHom (closedHom f)
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      simp only [toGradedModuleCat_piece, add_zero] at hx ⊢
      exact closedHom_mem f hx)
  map_id M := GradedModuleCat.hom_ext (closedHom_id _)
  map_comp f g := GradedModuleCat.hom_ext (closedHom_comp f g)

/-- The graded forgetful functor takes a curved module to its underlying graded right module. -/
@[simp]
theorem forgetDifferential_obj_of (M : CurvedDGRightModuleCat.{u, u, u} h) :
    (forgetDifferential (h := h)).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) =
      toGradedModuleCat M :=
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

/-- A graded isomorphism commuting with the differentials lifts to the closed category. -/
noncomputable def closedIsoOfGradedIso {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (g : toGradedModuleCat M ≅ toGradedModuleCat N)
    (hd : ∀ x, N.differential (g.hom.hom x) = g.hom.hom (M.differential x)) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ≅
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N := by
  let e : M ≃ₗ[Aᵐᵒᵖ] N :=
    ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g).toLinearEquiv
  have he (x : M) : e x = g.hom.hom x :=
    (Iso.toLinearEquiv_apply ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g) x).trans
      ((congrArg (fun f ↦ f x) (GradedModuleCat.toModuleCat_map g.hom)).trans
        (ModuleCat.ofHom_apply g.hom.hom x))
  have heInv (x : N) : e.symm x = g.inv.hom x :=
    (congrArg (fun e : N ≃ₗ[Aᵐᵒᵖ] M ↦ e x)
      (Iso.toLinearEquiv_symm ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g))).trans
      ((Iso.toLinearEquiv_apply ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g).symm x).trans
        ((congrArg (fun f ↦ f x) (GradedModuleCat.toModuleCat_map g.inv)).trans
          (ModuleCat.ofHom_apply g.inv.hom x)))
  refine closedIsoOf e (fun p x ↦ ?_) (fun x ↦ ?_)
  · constructor
    · intro hx
      rw [he]
      simpa only [toGradedModuleCat_piece, add_zero] using
        g.hom.isHomogeneous.map_mem (by simpa only [toGradedModuleCat_piece] using hx)
    · intro hx
      have hxN : e x ∈ (toGradedModuleCat N).grading.piece p := by
        rw [toGradedModuleCat_piece]
        exact hx
      have hx' : e.symm (e x) ∈ M.grading (p + 0) := by
        rw [heInv]
        simpa only [toGradedModuleCat_piece] using g.inv.isHomogeneous.map_mem hxN
      simpa only [e.symm_apply_apply, add_zero] using hx'
  · rw [he, he]
    exact hd x

/-- The lifted graded isomorphism retains its forward underlying linear map. -/
@[simp]
theorem closedHom_closedIsoOfGradedIso_hom {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (g : toGradedModuleCat M ≅ toGradedModuleCat N)
    (hd : ∀ x, N.differential (g.hom.hom x) = g.hom.hom (M.differential x)) :
    closedHom (closedIsoOfGradedIso g hd).hom = g.hom.hom := by
  dsimp only [closedIsoOfGradedIso]
  refine (closedHom_closedIsoOf_hom _ _ _).trans ?_
  exact (Iso.toLinearMap_toLinearEquiv
    ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g)).trans
    ((congrArg ModuleCat.Hom.hom (GradedModuleCat.toModuleCat_map g.hom)).trans
      (ModuleCat.hom_ofHom g.hom.hom))

/-- The lifted graded isomorphism retains its inverse underlying linear map. -/
@[simp]
theorem closedHom_closedIsoOfGradedIso_inv {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (g : toGradedModuleCat M ≅ toGradedModuleCat N)
    (hd : ∀ x, N.differential (g.hom.hom x) = g.hom.hom (M.differential x)) :
    closedHom (closedIsoOfGradedIso g hd).inv = g.inv.hom := by
  dsimp only [closedIsoOfGradedIso]
  refine (closedHom_closedIsoOf_inv _ _ _).trans ?_
  exact (congrArg LinearEquiv.toLinearMap
    (Iso.toLinearEquiv_symm ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g))).trans
    ((Iso.toLinearMap_toLinearEquiv
      ((GradedModuleCat.toModuleCat (𝒜 := _)).mapIso g).symm).trans
      ((congrArg ModuleCat.Hom.hom (GradedModuleCat.toModuleCat_map g.inv)).trans
        (ModuleCat.hom_ofHom g.inv.hom)))

instance : (forgetDifferential (h := h)).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    let g := asIso ((forgetDifferential (h := h)).map f)
    let i := closedIsoOfGradedIso g (differential_closedHom f)
    have hi : i.hom = f := by
      apply closedHom_injective
      simp only [i, closedHom_closedIsoOfGradedIso_hom, g, asIso_hom,
        forgetDifferential_map_hom]
    rw [← hi]
    infer_instance

instance : (forgetDifferential (h := h)).Additive where
  map_add {_ _ f g} := GradedModuleCat.hom_ext (closedHom_add f g)

instance : (forgetDifferential (h := h)).Linear R where
  map_smul {_ _} f r := GradedModuleCat.hom_ext (closedHom_smul r f)

/-- After forgetting the differential, cohomological shift by `n` is grading shift by `-n`. -/
noncomputable def closedShiftFunctorCompForgetDifferentialIso (n : ℤ) :
    closedShiftFunctor (h := h) n ⋙ forgetDifferential ≅
      forgetDifferential ⋙ GradedModuleCat.shiftFunctor (-n) :=
  NatIso.ofComponents (fun M ↦
    GradedModuleCat.isoMk
      (LinearEquiv.refl Aᵐᵒᵖ (ForgetEnrichment.to _ M : CurvedDGRightModuleCat.{u, u, u} h))
      fun p x ↦ by
      -- The functor and shift wrap the same carrier; exposing their grading fields lets
      -- the two public membership formulas compare the actual shifted pieces.
      change x ∈ (toGradedModuleCat ((ForgetEnrichment.to _ M).shift n)).grading.piece p ↔
        x ∈ ((toGradedModuleCat (ForgetEnrichment.to _ M)).shiftObj (-n)).grading.piece p
      rw [toGradedModuleCat_piece, shift_grading, GradedModuleCat.mem_shiftObj_piece_iff,
        toGradedModuleCat_piece, sub_neg_eq_add])
    (fun f ↦ by
      apply GradedModuleCat.hom_ext
      rw [GradedModuleCat.hom_comp, GradedModuleCat.hom_comp]
      simp [closedHom_closedShiftFunctor_map])

/-- The shift comparison acts by the identity on underlying right modules. -/
@[simp]
theorem closedShiftFunctorCompForgetDifferentialIso_hom_app_hom (n : ℤ)
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    ((closedShiftFunctorCompForgetDifferentialIso (h := h) n).hom.app M).hom = LinearMap.id := by
  simp [closedShiftFunctorCompForgetDifferentialIso]

/-- The inverse shift comparison acts by the identity on underlying right modules. -/
@[simp]
theorem closedShiftFunctorCompForgetDifferentialIso_inv_app_hom (n : ℤ)
    (M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :
    ((closedShiftFunctorCompForgetDifferentialIso (h := h) n).inv.app M).hom = LinearMap.id := by
  ext x
  simp [closedShiftFunctorCompForgetDifferentialIso, LinearEquiv.refl]

end TauCeti.CurvedDGRightModuleCat
