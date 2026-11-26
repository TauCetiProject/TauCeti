/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveBundle.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange

/-!
# Projectivity of a projective bundle over affine opens

Over an affine open `U` of the base, the restriction of `P(E)` is
`Proj (Sym Γ(E, U))` over `Spec Γ(S, U)`. The identification uses
`TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraSectionsEquiv` and
`CategoryTheory.CommMon.isPullback_relativeProjCover_fromSpec`.
`CategoryTheory.Over.isoMk` packages the identification over the coefficient spectrum.
For a quasi-coherent module of finite type, its sections over `U` form a finite module, so
the restriction is projective by `AlgebraicGeometry.Scheme.isProjectiveOver_proj` and
`AlgebraicGeometry.Scheme.IsProjectiveOver.of_isClosedImmersion`. In particular, the restriction
admits a closed immersion into projective space with finitely many coordinates over `Γ(S, U)`.

## References

* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
* [The Stacks Project, Definition 29.44.1](https://stacks.math.columbia.edu/tag/01W8)
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle

open _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (F : QuasicoherentSheaf S)
variable {U : S.Opens} (hU : IsAffineOpen U)

/-- Over an affine open `U` of the base, the restriction of `P(E)` is isomorphic over
`Spec Γ(S, U)` to the projective spectrum of the symmetric algebra of the sections of `E` on `U`. -/
def affineOpenIso :
    Over.mk (pullback.fst hU.fromSpec (projection S F.obj)) ≅
      Over.mk (TauCeti.SymmetricAlgebra.projToSpec Γ(S, U)
        ((Scheme.Modules.sectionsFunctor U).obj F.obj)) := by
  let M := (Scheme.Modules.sectionsFunctor U).obj F.obj
  let A := ((gradedSymmetricAlgebra S).obj F).obj
  let grades := TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(S, U) M
  let chartGrades := A.gradedSectionsGrading U
  let e := gradedSymmetricAlgebraSectionsEquiv F hU
  let f : grades →+*ᵍ chartGrades :=
    { __ := e.toRingHom
      map_mem := fun {n a} ha ↦
        (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F hU n a).mpr ha }
  let g : chartGrades →+*ᵍ grades :=
    { __ := e.symm.toRingHom
      map_mem := fun {n a} ha ↦
        (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F hU n (e.symm a)).mp
          ((e.apply_symm_apply a).symm ▸ ha) }
  let chartIso := Proj.mapIso f g e.apply_symm_apply e.symm_apply_apply
  let h := A.isPullback_relativeProjCover_fromSpec ⟨U, hU⟩
  refine Over.isoMk (h.isoPullback.symm ≪≫ chartIso) ?_
  have hr (r : Γ(S, U)) :
      f.gradedZeroRingHom (algebraMap Γ(S, U) (grades 0) r) =
        algebraMap Γ(S, U) (chartGrades 0) r := by
    apply Subtype.ext
    rw [GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
      SetLike.GradeZero.coe_algebraMap]
    exact e.commutes r
  have hmap : chartIso.hom ≫ Proj.toSpecCoeff grades = Proj.toSpecCoeff chartGrades :=
    (congrArg (· ≫ Proj.toSpecCoeff grades)
      (Proj.mapIso_hom f g e.apply_symm_apply e.symm_apply_apply)).trans
        (Proj.map_toSpecCoeff grades f _ hr)
  calc
    _ = (h.isoPullback.inv ≫ chartIso.hom) ≫ Proj.toSpecCoeff grades :=
      congrArg (_ ≫ ·) (Proj.toSpecCoeff_homogeneousSubmodule Γ(S, U) M).symm
    _ = h.isoPullback.inv ≫ Proj.toSpecCoeff chartGrades :=
      (Category.assoc _ _ _).trans (congrArg (h.isoPullback.inv ≫ ·) hmap)
    _ = _ := h.isoPullback_inv_fst

/-- The restriction of `P(E)` to an affine open `U` is projective over its coefficient ring when
`Γ(E, U)` is finite. This holds on every affine open if `E` is of finite type, by
`Scheme.Modules.finite_sections_of_isAffineOpen`. See Stacks, Section 27.21 and
Definition 29.44.1. -/
theorem isProjectiveOver_affineOpen
    [Module.Finite Γ(S, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj)] :
    let : (pullback hU.fromSpec (projection S F.obj)).Over (Spec (.of Γ(S, U))) :=
      ⟨pullback.fst hU.fromSpec (projection S F.obj)⟩
    (pullback hU.fromSpec (projection S F.obj)).IsProjectiveOver Γ(S, U) := by
  let : (pullback hU.fromSpec (projection S F.obj)).Over (Spec (.of Γ(S, U))) :=
    ⟨pullback.fst hU.fromSpec (projection S F.obj)⟩
  let e : pullback hU.fromSpec (projection S F.obj) ≅
      Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(S, U)
        ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :=
    (Over.forget _).mapIso (affineOpenIso F hU)
  have : e.hom.IsOver (Spec (.of Γ(S, U))) := ⟨Over.w (affineOpenIso F hU).hom⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion Γ(S, U) e.hom

end TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle
