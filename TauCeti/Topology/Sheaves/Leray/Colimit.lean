/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Leray.One
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

/-!
# Vanishing of degree one Čech cohomology from vanishing sheaf cohomology

Let `F` be a sheaf of `R`-modules on a topological space `X` whose underlying sheaf of abelian
groups has `H¹(X, F) = 0`. By the degree one Leray comparison
(`TauCeti.Topology.homologyCechComplexIsoHOne`), every open cover whose members have
vanishing `H¹` has vanishing first Čech cohomology, computed with module coefficients. If every
open cover of `X` is refined by such a cover, every class of the cover-colimit Čech
cohomology `TauCeti.Topology.cechCohomology` dies on a refinement, so the degree one Čech cohomology
of `F` vanishes.

Under the refinement hypothesis, this is the converse of
`CategoryTheory.Sheaf.subsingleton_H'_one_of_isZero_cechCohomology_moduleCat`. A typical use is
a compact Riemann surface, where coordinate discs have vanishing `H¹` for the structure sheaf, and
`H¹(X, 𝒪) = 0` can be read off from the Čech cohomology of one cover by such discs.

## Main results

* `CategoryTheory.Sheaf.isZero_homology_one_cechComplex_of_subsingleton_H`: a cover
  whose members have vanishing `H¹` has vanishing first Čech cohomology when `H¹(X, F) = 0`.
* `CategoryTheory.Sheaf.isZero_cechCohomology_one_of_subsingleton_H`: if every open cover is
  refined by such a cover and `H¹(X, F) = 0`, the degree one Čech cohomology of `F`
  vanishes.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 12.8 (Leray's theorem).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.CategoryTheory TauCeti.Topology

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- **Leray covers have the cohomology of the sheaf.** Let `F` be a sheaf of modules whose
underlying sheaf of abelian groups has `H¹(X, F) = 0`. An open cover whose members `U i`
have `H¹(U i, F) = 0` has vanishing first Čech cohomology, with module coefficients. -/
theorem isZero_homology_one_cechComplex_of_subsingleton_H {ι : Type u}
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hF : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i)))
    (h : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1)) :
    IsZero (((cechComplexFunctor U).obj F.obj).homology 1) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let FAb := (sheafCompose (Opens.grothendieckTopology X) G).obj F
  have hFAb : FAb.obj = F.obj ⋙ G := rfl
  have hAb : IsZero (((cechComplexFunctor U).obj FAb.obj).homology 1) :=
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Sheaf.H FAb 1))).of_iso
      (homologyCechComplexIsoHOne U hU FAb hF)
  rw [hFAb] at hAb
  -- forgetting the module structure commutes with forming the Čech complex and its homology
  have hG : IsZero (G.obj (((cechComplexFunctor U).obj F.obj).homology 1)) :=
    hAb.of_iso (((((cechComplexFunctor U).obj F.obj).sc 1).mapHomologyIso G).symm ≪≫
      HomologicalComplex.homologyMapIso ((cechComplexFunctorMapIso U G).app F.obj) 1)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hG.eq_of_src _ _

/-- **Vanishing of Čech `H¹` from vanishing sheaf `H¹`.** Let `F` be a sheaf of modules whose
underlying sheaf of abelian groups has `H¹(X, F) = 0`. If every open cover of `X` is refined by an
open cover whose members `W i` have `H¹(W i, F) = 0`, then the degree one Čech cohomology of
`F`, the colimit over all open covers, vanishes. -/
theorem isZero_cechCohomology_one_of_subsingleton_H
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    (h : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1)) :
    IsZero ((cechCohomology X (ModuleCat.{u} R) 1).obj F.obj) := by
  refine (IsZero.iff_id_eq_zero _).2 (cechCohomology_obj_hom_ext fun V ↦ ?_)
  obtain ⟨ι, W, hW, hWV, hWa⟩ := hF V.opens V.isOpenCover
  choose k hk using hWV
  let φ : FormalCoproduct.mk ι W ⟶ V.toFormalCoproduct := ⟨k, fun i ↦ homOfLE (hk i)⟩
  have hz := isZero_homology_one_cechComplex_of_subsingleton_H F W hW hWa h
  -- the structure map at `V` factors through the vanishing Čech cohomology of `W`
  rw [Category.comp_id, comp_zero, ← toCechCohomology_opens,
    ← cechComplexHomologyMap_comp_toCechCohomology (ModuleCat.{u} R) 1 φ V.isOpenCover
      (IsOpenCover.mk hW), NatTrans.comp_app, cechComplexHomologyMap_app]
  exact (congrArg (· ≫ _) (hz.eq_of_tgt _ 0)).trans zero_comp

end CategoryTheory.Sheaf
