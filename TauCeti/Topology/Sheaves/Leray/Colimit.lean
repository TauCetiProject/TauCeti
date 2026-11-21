/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Topology.Sheaves.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Cohomology.Instances
public import TauCeti.Topology.Sheaves.Leray.One
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

/-!
# Degree one Čech cohomology from finite Leray covers

Let `F` be a sheaf of `R`-modules on a topological space `X`. By the degree one Leray comparison
(`TauCeti.Topology.homologyCechComplexIsoHOne`), an open cover whose members have vanishing `H¹`
computes the sheaf cohomology `H¹(X, F)` of the underlying sheaf of abelian groups, and a
refinement between two such covers induces an isomorphism on first Čech cohomology
(`TauCeti.Topology.isIso_homologyMap_cechComplexMap_one`). In particular, if `H¹(X, F) = 0` and
every open cover of `X` is refined by such a cover, every class of the cover-colimit Čech
cohomology `TauCeti.Topology.cechCohomology` dies on a refinement, so the degree one Čech
cohomology of `F` vanishes.

Suppose now that every open cover of `X` is refined by such a finite cover. Then every finite such
cover `U` also computes the degree one cover-colimit Čech cohomology
`TauCeti.Topology.cechCohomology` of `F`: the structure map `TauCeti.Topology.toCechCohomology`
from `H¹(Č(U, F))` is an isomorphism, since the Čech cohomology is constant along the cofinal
system of such covers (`TauCeti.Topology.isIso_toCechCohomology_app_of_forall_isIso`). This holds
for sheaves of modules and for sheaves of abelian groups.

Under the refinement hypothesis, the vanishing above is the converse of
`CategoryTheory.Sheaf.subsingleton_H'_one_of_isZero_cechCohomology_moduleCat`. A typical use is
a compact Riemann surface, where coordinate discs have vanishing `H¹` for the structure sheaf, and
`H¹(X, 𝒪)` can be computed from the Čech cohomology of one finite cover by such discs.

## Main definitions

* `CategoryTheory.Sheaf.homologyCechComplexIsoCechCohomologyOne`: the isomorphism between the Čech
  `H¹` of a finite cover whose members have vanishing `H¹` and the degree one Čech cohomology, for
  a sheaf of modules; `CategoryTheory.Sheaf.homologyCechComplexIsoCechCohomologyOneAddCommGrpCat`
  is the version for a sheaf of abelian groups.

## Main results

* `CategoryTheory.Sheaf.isZero_homology_one_cechComplex_of_subsingleton_H`: a cover
  whose members have vanishing `H¹` has vanishing first Čech cohomology when `H¹(X, F) = 0`.
* `CategoryTheory.Sheaf.isZero_cechCohomology_one_of_subsingleton_H`: if every open cover is
  refined by such a cover and `H¹(X, F) = 0`, the degree one Čech cohomology of `F`
  vanishes.
* `CategoryTheory.Sheaf.isIso_homologyMap_cechComplexMap_one_of_subsingleton_H'`: with module
  coefficients, a refinement between covers whose members have vanishing `H¹` induces an
  isomorphism on degree one Čech cohomology.
* `CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'` and
  `CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'_addCommGrpCat`: if every
  open cover is refined by such a finite cover, every such cover computes the degree one Čech
  cohomology, for sheaves of modules and of abelian groups.
* `CategoryTheory.Sheaf.finite_cechCohomology_one_iff_finite_homology_cechComplex` and
  `CategoryTheory.Sheaf.finrank_cechCohomology_one_eq_finrank_homology_cechComplex`: the degree one
  Čech cohomology is finitely generated exactly when the Čech `H¹` of such a cover is, with the
  same rank.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 12.8 (Leray's theorem).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.CategoryTheory TauCeti.Topology

universe u

namespace CategoryTheory.Sheaf

section ModuleCat

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
  exact (isZero_homology_cechComplex_comp_iff U G F.obj 1).1 hAb

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

/-! ### Finite Leray covers compute degree one Čech cohomology -/

/-- **Refinements between Leray covers, with module coefficients.** For a sheaf of modules
`F`, a refinement between covers whose members have vanishing `H¹` induces an isomorphism on
degree one Čech cohomology. -/
theorem isIso_homologyMap_cechComplexMap_one_of_subsingleton_H' {ι κ : Type u}
    {U : ι → Opens X} {V : κ → Opens X} (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i)))
    (hFV : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    IsIso (HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have : IsIso (HomologicalComplex.homologyMap (cechComplexMap (F.obj ⋙ G) φ) 1) :=
    isIso_homologyMap_cechComplexMap_one U V hU hV ((sheafCompose _ G).obj F) hFU hFV φ
  -- `G` conjugates the map to the one for the underlying sheaf of abelian groups
  have : IsIso (G.map (HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1)) := by
    rw [(Iso.eq_comp_inv _).2
      (cechComplexFunctorMapHomologyIso_hom_comp_homologyMap_cechComplexMap U G F.obj φ 1)]
    infer_instance
  exact isIso_of_reflects_iso _ G

/-- **A finite Leray cover computes degree one Čech cohomology.** Let `F` be a sheaf of modules
such that every open cover of `X` is refined by a finite open cover whose members `W i` have
`H¹(W i, F) = 0`. Then for every finite open cover `U` whose members have `H¹(U i, F) = 0`, the
map from `H¹(Č(U, F))` to the degree one Čech cohomology of `F` is an isomorphism. -/
theorem isIso_toCechCohomology_one_of_subsingleton_H'
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    IsIso ((toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj) :=
  isIso_toCechCohomology_app_of_forall_isIso _ 1 F.obj
    (fun W ↦ Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 W)) hF
    (fun V W hV hW φ ↦ isIso_homologyMap_cechComplexMap_one_of_subsingleton_H' F
      W.isOpenCover.iSup_eq_top V.isOpenCover.iSup_eq_top hW hV φ) U (IsOpenCover.mk hU) hFU

/-- **The Čech `H¹` of a finite Leray cover.** If every open cover of `X` is refined by a finite
open cover whose members have vanishing `H¹` for `F`, then every finite open cover `U` whose
members have vanishing `H¹` computes the degree one Čech cohomology of `F`: `H¹(Č(U, F))` is
isomorphic to it through the structure map. -/
def homologyCechComplexIsoCechCohomologyOne
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      (cechCohomology X (ModuleCat.{u} R) 1).obj F.obj :=
  @asIso _ _ _ _ ((toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj)
    (isIso_toCechCohomology_one_of_subsingleton_H' F hF U hU hFU)

/-- The forward map of `homologyCechComplexIsoCechCohomologyOne` is the structure map of `U`. -/
theorem homologyCechComplexIsoCechCohomologyOne_hom
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    (homologyCechComplexIsoCechCohomologyOne F hF U hU hFU).hom =
      (toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj :=
  (rfl)

/-- **The inverse of `homologyCechComplexIsoCechCohomologyOne` on a coarser cover.** For an open
cover `V` refined by `U` through `φ`, the structure map of `V` followed by the inverse of
`homologyCechComplexIsoCechCohomologyOne` is the map `H¹(Č(V, F)) ⟶ H¹(Č(U, F))` induced by
`φ`. -/
@[reassoc]
theorem toCechCohomology_app_comp_homologyCechComplexIsoCechCohomologyOne_inv
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i)))
    {κ : Type u} {V : κ → Opens X} (hV : IsOpenCover V)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (toCechCohomology (ModuleCat.{u} R) 1 V hV).app F.obj ≫
        (homologyCechComplexIsoCechCohomologyOne F hF U hU hFU).inv =
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 :=
  -- the source of `(toCechCohomology _ 1 V hV).app F.obj` is the homology of the Čech complex only
  -- after unfolding, so the steps are combined as terms
  (Iso.comp_inv_eq _).2 <| (homologyMap_cechComplexMap_comp_toCechCohomology_app _ 1 φ hV
    (IsOpenCover.mk hU) F.obj).symm.trans
      (_ ≫= (homologyCechComplexIsoCechCohomologyOne_hom F hF U hU hFU).symm)

/-- **Finiteness of degree one Čech cohomology on a finite Leray cover.** If every open cover of `X`
is refined by a finite open cover whose members have vanishing `H¹` for `F`, then for every finite
open cover `U` whose members have vanishing `H¹`, the degree one Čech cohomology of `F` is a
finitely generated module exactly when the Čech `H¹` of `U` is. -/
theorem finite_cechCohomology_one_iff_finite_homology_cechComplex
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    Module.Finite R ((cechCohomology X (ModuleCat.{u} R) 1).obj F.obj) ↔
      Module.Finite R (((cechComplexFunctor U).obj F.obj).homology 1) :=
  (Module.Finite.equiv_iff
    (homologyCechComplexIsoCechCohomologyOne F hF U hU hFU).toLinearEquiv).symm

/-- **Rank of degree one Čech cohomology on a finite Leray cover.** If every open cover of `X` is
refined by a finite open cover whose members have vanishing `H¹` for `F`, then for every finite
open cover `U` whose members have vanishing `H¹`, the degree one Čech cohomology of `F` has the
rank of the Čech `H¹` of `U`. -/
theorem finrank_cechCohomology_one_eq_finrank_homology_cechComplex
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    Module.finrank R ((cechCohomology X (ModuleCat.{u} R) 1).obj F.obj) =
      Module.finrank R (((cechComplexFunctor U).obj F.obj).homology 1) :=
  (homologyCechComplexIsoCechCohomologyOne F hF U hU hFU).toLinearEquiv.finrank_eq.symm

end ModuleCat

section AddCommGrpCat

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- **A finite Leray cover computes degree one Čech cohomology, for sheaves of abelian groups.**
If every open cover of `X` is refined by a finite open cover whose members `W i` have
`H¹(W i, F) = 0`, then for every finite open cover `U` whose members have `H¹(U i, F) = 0`, the
map from `H¹(Č(U, F))` to the degree one Čech cohomology of `F` is an isomorphism. -/
theorem isIso_toCechCohomology_one_of_subsingleton_H'_addCommGrpCat
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (F.H' 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) :
    IsIso ((toCechCohomology AddCommGrpCat.{u} 1 U (IsOpenCover.mk hU)).app F.obj) :=
  isIso_toCechCohomology_app_of_forall_isIso _ 1 F.obj (fun W ↦ Subsingleton (F.H' 1 W)) hF
    (fun V W hV hW φ ↦ isIso_homologyMap_cechComplexMap_one _ _ W.isOpenCover.iSup_eq_top
      V.isOpenCover.iSup_eq_top F hW hV φ) U (IsOpenCover.mk hU) hFU

/-- **The Čech `H¹` of a finite Leray cover, for sheaves of abelian groups.** Under the
hypotheses of `isIso_toCechCohomology_one_of_subsingleton_H'_addCommGrpCat`, `H¹(Č(U, F))` is
isomorphic to the degree one Čech cohomology of `F` through the structure map. -/
def homologyCechComplexIsoCechCohomologyOneAddCommGrpCat
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (F.H' 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      (cechCohomology X AddCommGrpCat.{u} 1).obj F.obj :=
  @asIso _ _ _ _ ((toCechCohomology AddCommGrpCat.{u} 1 U (IsOpenCover.mk hU)).app F.obj)
    (isIso_toCechCohomology_one_of_subsingleton_H'_addCommGrpCat F hF U hU hFU)

/-- The forward map of `homologyCechComplexIsoCechCohomologyOneAddCommGrpCat` is the structure map
of `U`. -/
theorem homologyCechComplexIsoCechCohomologyOneAddCommGrpCat_hom
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (F.H' 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (homologyCechComplexIsoCechCohomologyOneAddCommGrpCat F hF U hU hFU).hom =
      (toCechCohomology AddCommGrpCat.{u} 1 U (IsOpenCover.mk hU)).app F.obj :=
  (rfl)

/-- **The inverse of `homologyCechComplexIsoCechCohomologyOneAddCommGrpCat` on a coarser cover.**
For an open cover `V` refined by `U` through `φ`, the structure map of `V` followed by the inverse
of `homologyCechComplexIsoCechCohomologyOneAddCommGrpCat` is the map `H¹(Č(V, F)) ⟶ H¹(Č(U, F))`
induced by `φ`. -/
@[reassoc]
theorem toCechCohomology_app_comp_homologyCechComplexIsoCechCohomologyOneAddCommGrpCat_inv
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (F.H' 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i)))
    {κ : Type u} {V : κ → Opens X} (hV : IsOpenCover V)
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    (toCechCohomology AddCommGrpCat.{u} 1 V hV).app F.obj ≫
        (homologyCechComplexIsoCechCohomologyOneAddCommGrpCat F hF U hU hFU).inv =
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 :=
  -- as for `toCechCohomology_app_comp_homologyCechComplexIsoCechCohomologyOne_inv`, the steps are
  -- combined as terms
  (Iso.comp_inv_eq _).2 <| (homologyMap_cechComplexMap_comp_toCechCohomology_app _ 1 φ hV
    (IsOpenCover.mk hU) F.obj).symm.trans
      (_ ≫= (homologyCechComplexIsoCechCohomologyOneAddCommGrpCat_hom F hF U hU hFU).symm)

end AddCommGrpCat

end CategoryTheory.Sheaf
