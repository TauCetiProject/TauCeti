/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.CategoryTheory.Sites.SheafCohomology.SectionsQuotient

/-!
# The two-open Čech description of first cohomology

For a sheaf of modules `M` and a cover `X = U ∪ V` with vanishing `H¹(U, M)` and
`H¹(V, M)`, this file identifies `H¹(X, M)` additively with

`Γ(M, U ∩ V) / {s|_{U ∩ V} - t|_{U ∩ V} : s ∈ Γ(M, U), t ∈ Γ(M, V)}`.

The equivalence is induced by the Mayer–Vietoris connecting map. The coefficients
need not be quasi-coherent, and no vanishing on the overlap is required. Thus the
same computation applies whenever acyclicity of the two members is available.
This is a two-member comparison in degree one, not the general Čech comparison
for arbitrary affine covers.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, §4.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules) (U V : Opens X)

/-- The Čech coboundary for two open subsets, with sign `s| - t|`. -/
def cechDifference : (Γ(M, U) × Γ(M, V)) →+ Γ(M, U ⊓ V) :=
  mayerVietorisSectionsDifference (Opens.mayerVietorisSquare U V)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)

@[simp]
lemma cechDifference_apply (s : Γ(M, U)) (t : Γ(M, V)) :
    cechDifference M U V (s, t) =
      M.val.map (CategoryTheory.homOfLE inf_le_left).op s -
        M.val.map (CategoryTheory.homOfLE inf_le_right).op t :=
  mayerVietorisSectionsDifference_apply
    (Opens.mayerVietorisSquare U V) ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) s t

/-- The two-open Čech comparison in degree one: if the members cover the scheme and
have vanishing first cohomology, the quotient of overlap sections by coboundaries is
first cohomology of the scheme. -/
def sectionsQuotientEquivCohomologyOne (hUV : U ⊔ V = ⊤)
    (hU : Subsingleton (cohomologyOn M 1 U)) (hV : Subsingleton (cohomologyOn M 1 V)) :
    (Γ(M, U ⊓ V) ⧸ (cechDifference M U V).range) ≃+ Cohomology M 1 :=
  (mayerVietorisSectionsQuotientEquiv
    (Opens.mayerVietorisSquare U V) ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    hU hV).trans <|
      (eqToIso (congrArg (cohomologyOn M 1) hUV)).addCommGroupIsoToAddEquiv.trans
        (cohomologyOnTopIso M 1).addCommGroupIsoToAddEquiv

/-- The Čech comparison sends an overlap section to its Mayer–Vietoris connecting class,
transported from the union to the whole scheme. -/
@[simp]
lemma sectionsQuotientEquivCohomologyOne_mk (hUV : U ⊔ V = ⊤)
    (hU : Subsingleton (cohomologyOn M 1 U)) (hV : Subsingleton (cohomologyOn M 1 V))
    (s : Γ(M, U ⊓ V)) :
    sectionsQuotientEquivCohomologyOne M U V hUV hU hV (QuotientAddGroup.mk s) =
      (cohomologyOnTopIso M 1).hom
        ((eqToIso (congrArg (cohomologyOn M 1) hUV)).hom
          (mayerVietorisSectionClass
            (Opens.mayerVietorisSquare U V)
            ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) s)) := by
  exact congrArg
    (fun x ↦ (cohomologyOnTopIso M 1).hom ((eqToIso (congrArg (cohomologyOn M 1) hUV)).hom x))
    (mayerVietorisSectionsQuotientEquiv_mk
      (Opens.mayerVietorisSquare U V) ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      hU hV s)

end TauCeti.AlgebraicGeometry
