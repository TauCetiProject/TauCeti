/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Leray.Basic
import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Leray comparison in degree one

For an open cover, vanishing of `H¹(Uᵢ,F)` on the individual members suffices to compare
Čech `H¹` with sheaf `H¹`. Acyclicity of finite intersections in positive degrees is not needed.

Embed `F` into an injective sheaf `I` with quotient `Q`. The Čech sequence is left exact in every
degree, and the map `Č⁰(I) → Č⁰(Q)` is onto by the memberwise vanishing. Its complex cokernel `R`
therefore embeds into `Č(Q)` and agrees in degree zero. Consequently `H⁰(R) ≅ H⁰(Q)`, and the
long exact sequence for `0 → Č(F) → Č(I) → R → 0` identifies both degree-one groups as the
cokernel of the same global-sections map.

## Main results

* `homologyCechComplexIsoHOne`: the comparison assuming memberwise `H¹` vanishing.
* `homologyCechComplexIsoH_one_eq_homologyCechComplexIsoHOne`: agreement with all-degree Leray.
* `homologyMap_comp_homologyCechComplexIsoHOne_hom`: naturality in the coefficient sheaf.
* `homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom`: refinement compatibility.
* `isIso_homologyMap_cechComplexMap_one`: refinement maps between such covers are isomorphisms.

The existing `cechComplexHomologyMap_eq` makes these maps independent of the refinement morphism.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, degree-one Leray comparison.
-/

public section
noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- **Degree-one Leray comparison.** Vanishing of `H¹(Uᵢ,F)` on the members of an open
cover suffices for `H¹(U,F) ≅ H¹(X,F)`; no acyclicity of intersections is assumed. -/
def homologyCechComplexIsoHOne (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F 1) :=
  CategoryTheory.homologyCechComplexIsoHOne U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF

/-- With the all-degree Leray hypotheses, the degree-one comparison agrees with the
existing all-degree comparison. The memberwise vanishing witness may be chosen independently. -/
lemma homologyCechComplexIsoH_one_eq_homologyCechComplexIsoHOne
    (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (hF₁ : ∀ i, Subsingleton (F.H' 1 (U i))) :
    homologyCechComplexIsoH U hU F hF 1 = homologyCechComplexIsoHOne U hU F hF₁ := by
  rw [homologyCechComplexIsoH_def U hU F hF (fun _ a k ↦
    CompleteLattice.finite_product_of_forall_finset_inf
      (p := fun W ↦ Subsingleton (F.H' (k + 1) W)) U (fun t ht ↦ hF t ht k) a)]
  exact CategoryTheory.homologyCechComplexIsoH_one U isTerminalTop
    ((Opens.coversTop_iff X U).2 hU) F _ hF₁

section Naturality

variable {κ : Type u} (V : κ → Opens X)
  {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- Degree-one Leray comparison is natural in the coefficient sheaf. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoHOne_hom
    (hU : ⨆ i, U i = ⊤) (f : F ⟶ G)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (U i))) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1 ≫
        (homologyCechComplexIsoHOne U hU G hG).hom =
      (homologyCechComplexIsoHOne U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f 1) :=
  CategoryTheory.homologyMap_comp_homologyCechComplexIsoHOne_hom U isTerminalTop
    ((Opens.coversTop_iff X U).2 hU) f hF hG

/-- Degree-one Leray comparison commutes with the actual map induced by a cover refinement. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫
        (homologyCechComplexIsoHOne U hU F hFU).hom =
      (homologyCechComplexIsoHOne V hV F hFV).hom :=
  CategoryTheory.homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom U isTerminalTop V
    ((Opens.coversTop_iff X U).2 hU) ((Opens.coversTop_iff X V).2 hV) F hFU hFV φ

/-- A refinement between memberwise `H¹`-acyclic covers induces an isomorphism on `H¹`. -/
theorem isIso_homologyMap_cechComplexMap_one
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    IsIso (HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1) :=
  CategoryTheory.isIso_homologyMap_cechComplexMap_one U V
    ((Opens.coversTop_iff X U).2 hU) ((Opens.coversTop_iff X V).2 hV) F hFU hFV φ

end Naturality

end TauCeti.Topology
