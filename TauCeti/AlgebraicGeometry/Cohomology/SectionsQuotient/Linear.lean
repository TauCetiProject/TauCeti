/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The linear two-open computation of first cohomology

For a cover `X = U ∪ V`, the Mayer–Vietoris boundary from sections on `U ∩ V` to
`H¹(X, M)` is linear over global functions. If first cohomology vanishes on both
members, it identifies `H¹(X, M)` with the module cokernel of the difference of
restrictions from the two members. No acyclicity on the overlap is needed.

This upgrades the additive computation in `SectionsQuotient.Basic` to a linear one,
so it can be used for dimensions and extension of scalars. For quasi-coherent coefficients,
affine acyclicity supplies the hypotheses on any two affine opens of a locally Noetherian
scheme. The quotient uses the sign `s| - t|` of the Mayer–Vietoris sequence.

The construction reuses `mayerVietorisSectionClass`, its kernel calculation and
surjectivity, and Mathlib's linear first isomorphism theorem. It does not assert a comparison of
Čech complexes or flat base change.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 4.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules TauCeti.CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)

/-- The difference of restrictions from two opens, linear over global functions. -/
def mayerVietorisSectionsDifferenceLinear :
    (Γ(M, U) × Γ(M, V)) →ₗ[Γ(X, ⊤)] Γ(M, U ⊓ V) :=
  (Scheme.Modules.sectionsRestrictionLinear M (homOfLE inf_le_left)).comp
      (LinearMap.fst _ _ _) -
    (Scheme.Modules.sectionsRestrictionLinear M (homOfLE inf_le_right)).comp
      (LinearMap.snd _ _ _)

@[simp]
lemma mayerVietorisSectionsDifferenceLinear_apply (s : Γ(M, U)) (t : Γ(M, V)) :
    mayerVietorisSectionsDifferenceLinear M U V (s, t) =
      mayerVietorisSectionsDifference M U V (s, t) := by
  simp only [mayerVietorisSectionsDifferenceLinear, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    Scheme.Modules.sectionsRestrictionLinear_apply, mayerVietorisSectionsDifference_apply]
  rfl

private def terminalUnion (hUV : U ⊔ V = ⊤) : IsTerminal (U ⊔ V) := by
  rw [hUV]
  exact isTerminalTop

variable (hUV : U ⊔ V = ⊤)

private def boundaryAddHom : Γ(M, U ⊓ V) →+ Cohomology M 1 :=
  ((CategoryTheory.Sheaf.cohomologyPresheafObjIsoH
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1
      (terminalUnion U V hUV)).addCommGroupIsoToAddEquiv.toAddMonoidHom).comp
    (mayerVietorisSectionClass (Opens.mayerVietorisSquare U V)
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M))

private lemma boundaryAddHom_naturality {N : X.Modules} (f : M ⟶ N)
    (s : Γ(M, U ⊓ V)) :
    (cohomologyFunctor X 1).map f (boundaryAddHom M U V hUV s) =
      boundaryAddHom N U V hUV (f.app (U ⊓ V) s) := by
  let F := (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f
  have h := ConcreteCategory.congr_hom
    ((CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ 1
      (terminalUnion U V hUV)).hom.naturality F)
    (mayerVietorisSectionClass (Opens.mayerVietorisSquare U V)
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) s)
  have hn := mayerVietorisSectionClass_naturality (Opens.mayerVietorisSquare U V)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) F s
  have he := congrArg (CategoryTheory.Sheaf.cohomologyPresheafObjIsoH
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj N) 1
      (terminalUnion U V hUV)).hom hn
  -- The evaluation and composite functors compute to the named coefficient maps.
  -- `convert!` reduces their category wrappers without unfolding the Ext construction.
  convert! h.symm.trans he using 1

/-- The Mayer–Vietoris connecting class of a section on the overlap, linear over global
functions. Its sign is fixed by the existing Mayer–Vietoris boundary. -/
def mayerVietorisBoundaryLinear : Γ(M, U ⊓ V) →ₗ[Γ(X, ⊤)] Cohomology M 1 where
  __ := boundaryAddHom M U V hUV
  map_smul' r s := by
    -- The inherited additive-hom fields compute through their coercion to functions.
    change boundaryAddHom M U V hUV (r • s) = r • boundaryAddHom M U V hUV s
    rw [Scheme.Modules.cohomology_smul]
    have h := boundaryAddHom_naturality M U V hUV (M.globalSectionsSmul r) s
    simp only [Scheme.Modules.globalSectionsSmul_app, Scheme.Modules.smul_apply] at h
    rw [Scheme.Modules.sectionsGlobal_smul]
    convert! h.symm using 1

/-- The linear boundary is the site-level connecting class followed by the terminal-object
comparison with cohomology of the whole scheme. -/
lemma mayerVietorisBoundaryLinear_apply (s : Γ(M, U ⊓ V)) :
    mayerVietorisBoundaryLinear M U V hUV s =
      (CategoryTheory.Sheaf.cohomologyPresheafObjIsoH
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1 (T := U ⊔ V)
          (by rw [hUV]; exact isTerminalTop)).hom
        (mayerVietorisSectionClass (Opens.mayerVietorisSquare U V)
          ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) s) :=
  (rfl)

/-- The boundary is natural in the coefficient module. -/
lemma mayerVietorisBoundaryLinear_naturality {N : X.Modules} (f : M ⟶ N)
    (s : Γ(M, U ⊓ V)) :
    Scheme.Modules.cohomologyMapLinear f 1 (mayerVietorisBoundaryLinear M U V hUV s) =
      mayerVietorisBoundaryLinear N U V hUV (f.app (U ⊓ V) s) := by
  rw [Scheme.Modules.cohomologyMapLinear_apply,
    mayerVietorisBoundaryLinear_apply, mayerVietorisBoundaryLinear_apply]
  exact boundaryAddHom_naturality M U V hUV f s

/-- The kernel of the boundary consists exactly of differences of restricted sections. -/
lemma ker_mayerVietorisBoundaryLinear :
    LinearMap.ker (mayerVietorisBoundaryLinear M U V hUV) =
      LinearMap.range (mayerVietorisSectionsDifferenceLinear M U V) := by
  ext s
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  rw [mayerVietorisBoundaryLinear_apply]
  let e := (CategoryTheory.Sheaf.cohomologyPresheafObjIsoH
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1
      (terminalUnion U V hUV)).addCommGroupIsoToAddEquiv
  have h := (e.map_eq_zero_iff).trans (mayerVietorisSectionClass_eq_zero_iff
    (Opens.mayerVietorisSquare U V)
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) s)
  -- Categorical maps and additive equivalences have the same underlying function.
  convert! h using 1
  simp only [Prod.exists, mayerVietorisSectionsDifferenceLinear_apply,
    mayerVietorisSectionsDifference_apply]
  rfl

variable (hU : Subsingleton (cohomologyOn M 1 U))
  (hV : Subsingleton (cohomologyOn M 1 V))

include hU hV in
/-- When first cohomology vanishes on both covering members, the boundary is surjective. -/
lemma mayerVietorisBoundaryLinear_surjective :
    Function.Surjective (mayerVietorisBoundaryLinear M U V hUV) :=
  ((CategoryTheory.Sheaf.cohomologyPresheafObjIsoH
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) 1
      (terminalUnion U V hUV)).addCommGroupIsoToAddEquiv.surjective).comp
    (mayerVietorisSectionClass_surjective (Opens.mayerVietorisSquare U V)
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) hU hV)

/-- First cohomology of a two-open cover with acyclic members is the module cokernel of
restriction differences. Only vanishing in degree one on each member is required. -/
def sectionsQuotientLinearEquivCohomologyOne :
    (Γ(M, U ⊓ V) ⧸ LinearMap.range (mayerVietorisSectionsDifferenceLinear M U V)) ≃ₗ[Γ(X, ⊤)]
      Cohomology M 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_mayerVietorisBoundaryLinear M U V hUV).symm).trans
    ((mayerVietorisBoundaryLinear M U V hUV).quotKerEquivOfSurjective
      (mayerVietorisBoundaryLinear_surjective M U V hUV hU hV))

/-- The quotient comparison sends a represented section to its connecting class. -/
@[simp]
lemma sectionsQuotientLinearEquivCohomologyOne_mk (s : Γ(M, U ⊓ V)) :
    sectionsQuotientLinearEquivCohomologyOne M U V hUV hU hV (Submodule.Quotient.mk s) =
      mayerVietorisBoundaryLinear M U V hUV s := by
  simp [sectionsQuotientLinearEquivCohomologyOne]

/-- The inverse comparison returns the quotient class of an overlap section from its boundary. -/
@[simp]
lemma sectionsQuotientLinearEquivCohomologyOne_symm_boundary (s : Γ(M, U ⊓ V)) :
    (sectionsQuotientLinearEquivCohomologyOne M U V hUV hU hV).symm
        (mayerVietorisBoundaryLinear M U V hUV s) = Submodule.Quotient.mk s := by
  apply (sectionsQuotientLinearEquivCohomologyOne M U V hUV hU hV).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (sectionsQuotientLinearEquivCohomologyOne_mk M U V hUV hU hV s).symm

end TauCeti.AlgebraicGeometry
