/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.CategoryTheory.Sites.SheafCohomology.SectionsQuotient

/-!
# First cohomology as a quotient of sections on a two-open cover

For a sheaf of modules `M` and a cover `X = U ∪ V` with vanishing `H¹(U, M)` and
`H¹(V, M)`, this file identifies `H¹(X, M)` additively with

`Γ(M, U ∩ V) / {s|_{U ∩ V} - t|_{U ∩ V} : s ∈ Γ(M, U), t ∈ Γ(M, V)}`.

The equivalence is induced by the Mayer–Vietoris connecting map. The coefficients
need not be quasi-coherent, and no vanishing on the overlap is required. Thus the
same computation applies whenever acyclicity of the two members is available.
This computes first cohomology directly from the Mayer–Vietoris sequence; it does
not identify a Čech complex with derived cohomology.

Use `TauCeti.AlgebraicGeometry.sectionsQuotientEquivCohomologyOne M U V hUV hU hV`
for the comparison, where `hUV` states that the opens cover and `hU`, `hV` state
vanishing of first cohomology on the two opens.

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

/-- The difference of restrictions to the overlap of two open subsets, with sign `s| - t|`
matching the Mayer–Vietoris sequence. This is the negative of the standard Čech differential. -/
def mayerVietorisSectionsDifference : (Γ(M, U) × Γ(M, V)) →+ Γ(M, U ⊓ V) :=
  TauCeti.CategoryTheory.mayerVietorisSectionsDifference (Opens.mayerVietorisSquare U V)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)

@[simp]
lemma mayerVietorisSectionsDifference_apply (s : Γ(M, U)) (t : Γ(M, V)) :
    mayerVietorisSectionsDifference M U V (s, t) =
      M.val.map (CategoryTheory.homOfLE inf_le_left).op s -
        M.val.map (CategoryTheory.homOfLE inf_le_right).op t :=
  TauCeti.CategoryTheory.mayerVietorisSectionsDifference_apply
    (Opens.mayerVietorisSquare U V) ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) s t

/-- The two-open quotient description in degree one: if the members cover the scheme and
have vanishing first cohomology, the quotient of overlap sections by coboundaries is
first cohomology of the scheme. -/
def sectionsQuotientEquivCohomologyOne (hUV : U ⊔ V = ⊤)
    (hU : Subsingleton (cohomologyOn M 1 U)) (hV : Subsingleton (cohomologyOn M 1 V)) :
    (Γ(M, U ⊓ V) ⧸ (mayerVietorisSectionsDifference M U V).range) ≃+ Cohomology M 1 :=
  (mayerVietorisSectionsQuotientEquiv
    (Opens.mayerVietorisSquare U V) ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    hU hV).trans <|
      (eqToIso (congrArg (cohomologyOn M 1) hUV)).addCommGroupIsoToAddEquiv.trans
        (cohomologyOnTopIso M 1).addCommGroupIsoToAddEquiv

/-- The quotient comparison sends an overlap section to its Mayer–Vietoris connecting class,
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
