/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Leray
public import TauCeti.Topology.Sheaves.Cech.Basic

import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Leray's theorem: Čech cohomology of a Leray cover computes sheaf cohomology

Let `F` be a sheaf of abelian groups on a topological space `X` and let `U` be an open cover of
`X` such that `F` has no cohomology in positive degrees on any nonempty finite intersection of
members of `U` (a *Leray cover* for `F`). Then the Čech cohomology `Hⁿ(U, F)`, the cohomology of
the Čech complex `Č(U, F)`, is isomorphic to the sheaf cohomology `Hⁿ(X, F)` in every degree,
naturally in `F`. In particular the comparison commutes with every endomorphism of `F`, so it
respects any module structure on both sides that is induced by an action of a ring on `F`.

This is Leray's acyclicity theorem for a covering of a site
(`TauCeti.CategoryTheory.homologyCechComplexIsoH`), applied to the site of opens of `X`: the cover
generates a covering sieve of `⊤`
(`TauCeti.Topology.ofArrows_mem_grothendieckTopology_of_iSup_eq_top`), and the finite products
of opens are their intersections.

## Main results

* `TauCeti.Topology.homologyCechComplexIsoH`: for a Leray cover `U` of `X`,
  `Hⁿ(U, F) ≅ Hⁿ(X, F)` for every `n`;
* `TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom`: this isomorphism is natural
  in `F`;
* `TauCeti.Topology.homologyCechComplexIsoH_zero`: in degree `0` it is the identification of both
  groups with the global sections.
* `TauCeti.Topology.δ_comp_homologyCechComplexIsoH_one_hom`: in degree `1` the comparison
  intertwines the connecting maps of the Čech and sheaf injective cokernel sequences.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.11, and the proof of Theorem III.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} {U : ι → Opens X}

/-- The Leray condition on nonempty finite intersections implies it on finite products. -/
private lemma isLerayProd_of_finset {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ) : Subsingleton (F.H' (k + 1) (∏ᶜ fun j ↦ U (a j))) :=
  -- the product of the members `U (a j)` is their intersection
  CompleteLattice.finite_product_of_forall_finset_inf (p := fun W ↦ Subsingleton (F.H' (k + 1) W))
    U (fun s hs ↦ hF s hs k) a

variable (U) (hU : ⨆ i, U i = ⊤)

include hU

/-- **Leray's theorem.** Let `U` be a family of opens covering a topological space `X`, and let `F`
be a sheaf of abelian groups on `X` with no cohomology in positive degrees on any nonempty finite
intersection of members of `U`. Then the Čech cohomology `Hⁿ(U, F)`, the cohomology of the Čech
complex of `F` for `U`, is isomorphic to the sheaf cohomology `Hⁿ(X, F)`, for every `n`, naturally
in `F` (`TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom`). -/
def homologyCechComplexIsoH (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U))) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology n ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F n) :=
  CategoryTheory.homologyCechComplexIsoH U isTerminalTop
    (ofArrows_mem_grothendieckTopology_of_iSup_eq_top U hU) F (isLerayProd_of_finset hF) n

/-- In degree `0`, the comparison of Leray's theorem is the identification of both groups with
the global sections. -/
@[simp]
lemma homologyCechComplexIsoH_zero (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U))) :
    homologyCechComplexIsoH U hU F hF 0 = homologyZeroCechIso U hU F := by
  rw [homologyCechComplexIsoH, homologyZeroCechIso_def, CategoryTheory.homologyCechComplexIsoH_zero]

/-- In degree one, the all-degree Leray comparison intertwines the connecting maps of
the Čech and sheaf injective cokernel sequences. The short exactness witness may be any one. -/
@[reassoc]
lemma δ_comp_homologyCechComplexIsoH_one_hom
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (hS : (cechInjectiveCokernelSequence U F).ShortExact) :
    hS.δ 0 1 rfl ≫ (homologyCechComplexIsoH U hU F hF 1).hom =
      (homologyZeroCechIso U hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) := by
  rw [homologyZeroCechIso_def]
  exact CategoryTheory.δ_comp_homologyCechComplexIsoH_one_hom U isTerminalTop _ F _ hS

/-- **Naturality of Leray's theorem.** The comparison `Hⁿ(U, F) ≅ Hⁿ(X, F)` commutes with the maps
induced by a morphism `F ⟶ G` of sheaves which both satisfy the hypotheses of Leray's theorem. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoH_hom
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (hG : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (G.H' (k + 1) (s.inf U)))
    (f : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n ≫
        (homologyCechComplexIsoH U hU G hG n).hom =
      (homologyCechComplexIsoH U hU F hF n).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f n) :=
  CategoryTheory.homologyMap_comp_homologyCechComplexIsoH_hom U isTerminalTop _ _ _ f n

end TauCeti.Topology
