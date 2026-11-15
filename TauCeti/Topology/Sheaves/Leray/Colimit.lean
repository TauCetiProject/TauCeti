/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Topology.Sheaves.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Leray.One
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.Finiteness.Basic
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

/-!
# Degree one Čech cohomology from finite Leray covers

Let `F` be a sheaf of `R`-modules on a topological space `X`. By the degree one Leray comparison
(`TauCeti.Topology.homologyCechComplexIsoHOne`), a finite open cover whose members have vanishing
`H¹` computes the sheaf cohomology `H¹(X, F)` of the underlying sheaf of abelian groups, and a
refinement between two such covers induces an isomorphism on first Čech cohomology
(`TauCeti.Topology.isIso_homologyMap_cechComplexMap_one`).

Suppose that every open cover of `X` is refined by such a finite cover. Then every such cover `U`
also computes the degree one cover-colimit Čech cohomology `TauCeti.Topology.cechCohomology` of `F`:
the structure map `TauCeti.Topology.toCechCohomology` from `H¹(Č(U, F))` is an isomorphism. Its
inverse sends the class of a cocycle on an open cover `V` to its image on a common refinement `W`
of `U` and `V` of the same kind, pulled back to `U`; any two such `W` have a common refinement of
the same kind, so the result does not depend on `W`. In particular, if `H¹(X, F) = 0` then the
degree one Čech cohomology of `F` vanishes.

Under the refinement hypothesis, this vanishing is the converse of
`CategoryTheory.Sheaf.subsingleton_H'_one_of_isZero_cechCohomology_moduleCat`. A typical use is
a compact Riemann surface, where coordinate discs have vanishing `H¹` for the structure sheaf, and
`H¹(X, 𝒪)` can be computed from the Čech cohomology of one finite cover by such discs.

## Main definitions

* `CategoryTheory.Sheaf.cechCohomologyOneIsoOfLeray`: the isomorphism between the Čech `H¹` of a
  finite cover whose members have vanishing `H¹` and the degree one Čech cohomology.

## Main results

* `CategoryTheory.Sheaf.isZero_homology_one_cechComplex_of_subsingleton_H`: a finite cover
  whose members have vanishing `H¹` has vanishing first Čech cohomology when `H¹(X, F) = 0`.
* `CategoryTheory.Sheaf.isZero_cechCohomology_one_of_subsingleton_H`: if every open cover is
  refined by such a finite cover and `H¹(X, F) = 0`, the degree one Čech cohomology of `F`
  vanishes.
* `CategoryTheory.Sheaf.isIso_homologyMap_cechComplexMap_one_of_subsingleton_H'`: with module
  coefficients, a refinement between finite covers whose members have vanishing `H¹` induces an
  isomorphism on degree one Čech cohomology.
* `CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'`: if every open cover is
  refined by such a finite cover, every such cover computes the degree one Čech cohomology.
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

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

/-- **Leray covers have the cohomology of the sheaf.** Let `F` be a sheaf of modules whose
underlying sheaf of abelian groups has `H¹(X, F) = 0`. A finite open cover whose members `U i`
have `H¹(U i, F) = 0` has vanishing first Čech cohomology, with module coefficients. -/
theorem isZero_homology_one_cechComplex_of_subsingleton_H {ι : Type u} [Finite ι]
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
underlying sheaf of abelian groups has `H¹(X, F) = 0`. If every open cover of `X` is refined by a
finite open cover whose members `W i` have `H¹(W i, F) = 0`, then the degree one Čech cohomology of
`F`, the colimit over all open covers, vanishes. -/
theorem isZero_cechCohomology_one_of_subsingleton_H
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    (h : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1)) :
    IsZero ((cechCohomology X (ModuleCat.{u} R) 1).obj F.obj) := by
  refine (IsZero.iff_id_eq_zero _).2 (cechCohomology_obj_hom_ext fun V ↦ ?_)
  obtain ⟨ι, _, W, hW, hWV, hWa⟩ := hF V.opens V.isOpenCover
  choose k hk using hWV
  let φ : FormalCoproduct.mk ι W ⟶ V.toFormalCoproduct := ⟨k, fun i ↦ homOfLE (hk i)⟩
  have hz := isZero_homology_one_cechComplex_of_subsingleton_H F W hW hWa h
  -- the structure map at `V` factors through the vanishing Čech cohomology of `W`
  rw [Category.comp_id, comp_zero, ← toCechCohomology_opens,
    ← cechComplexHomologyMap_comp_toCechCohomology (ModuleCat.{u} R) 1 φ V.isOpenCover
      (IsOpenCover.mk hW), NatTrans.comp_app, cechComplexHomologyMap_app]
  exact (congrArg (· ≫ _) (hz.eq_of_tgt _ 0)).trans zero_comp

/-! ### Finite Leray covers compute degree one Čech cohomology -/

/-- **Refinements between finite Leray covers, with module coefficients.** For a sheaf of modules
`F`, a refinement between finite covers whose members have vanishing `H¹` induces an isomorphism on
degree one Čech cohomology. -/
theorem isIso_homologyMap_cechComplexMap_one_of_subsingleton_H' {ι κ : Type u} [Finite ι]
    [Finite κ] {U : ι → Opens X} {V : κ → Opens X} (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
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

section Inverse

variable {F} {ι : Type u} [Finite ι] {U : ι → Opens X}

/-- Restrictions of the maps on degree one Čech cohomology induced by refinements compose. -/
private lemma homologyMap_cechComplexMap_comp {ι₁ ι₂ ι₃ : Type u} {U₁ : ι₁ → Opens X}
    {U₂ : ι₂ → Opens X} {U₃ : ι₃ → Opens X} (φ : FormalCoproduct.mk _ U₁ ⟶ FormalCoproduct.mk _ U₂)
    (ψ : FormalCoproduct.mk _ U₂ ⟶ FormalCoproduct.mk _ U₃) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj (φ ≫ ψ)) 1 =
      HomologicalComplex.homologyMap (cechComplexMap F.obj ψ) 1 ≫
        HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 := by
  rw [cechComplexMap_comp, HomologicalComplex.homologyMap_comp]

variable (F U) in
/-- A refinement of a family `V` and of the cover `U` by a finite cover whose members have
vanishing `H¹`. -/
private structure LerayRefinement {κ : Type u} (V : κ → Opens X) where
  /-- The index type of the refining cover. -/
  ν : Type u
  [finite : Finite ν]
  /-- The refining cover. -/
  W : ν → Opens X
  iSup_eq_top : ⨆ i, W i = ⊤
  subsingleton : ∀ i, Subsingleton (Sheaf.H'
    ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i))
  /-- The refinement of `V`. -/
  toV : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V
  /-- The refinement of `U`. -/
  toU : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U

attribute [instance] LerayRefinement.finite

/-- Any two open covers have a common refinement by a finite cover whose members have vanishing
`H¹`, provided every open cover has a refinement of that kind. -/
private lemma exists_common_refinement
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {κ₁ κ₂ : Type u} {V₁ : κ₁ → Opens X} {V₂ : κ₂ → Opens X} (hV₁ : IsOpenCover V₁)
    (hV₂ : IsOpenCover V₂) :
    ∃ (ν : Type u) (_ : Finite ν) (W : ν → Opens X), ⨆ i, W i = ⊤ ∧
      (∀ i, Subsingleton (Sheaf.H'
        ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i))) ∧
      Nonempty (FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ₁ V₁) ∧
      Nonempty (FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ₂ V₂) := by
  have hV : IsOpenCover fun p : κ₁ × κ₂ ↦ V₁ p.1 ⊓ V₂ p.2 := by
    refine IsOpenCover.mk (eq_top_iff.2 fun x _ ↦ ?_)
    obtain ⟨i, hi⟩ := hV₁.exists_mem x
    obtain ⟨j, hj⟩ := hV₂.exists_mem x
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  obtain ⟨ν, hν, W, hW, hWV, hFW⟩ := hF _ hV
  choose k hk using hWV
  exact ⟨ν, hν, W, hW, hFW, ⟨⟨fun i ↦ (k i).1, fun i ↦ homOfLE ((hk i).trans inf_le_left)⟩⟩,
    ⟨⟨fun i ↦ (k i).2, fun i ↦ homOfLE ((hk i).trans inf_le_right)⟩⟩⟩

variable (hU : ⨆ i, U i = ⊤)
  (hFU : ∀ i, Subsingleton (Sheaf.H'
    ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i)))

namespace LerayRefinement

variable {κ : Type u} {V : κ → Opens X}

include hU hFU in
private lemma isIso_toU (L : LerayRefinement F U V) :
    IsIso (HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1) :=
  isIso_homologyMap_cechComplexMap_one_of_subsingleton_H' F L.iSup_eq_top hU L.subsingleton hFU
    L.toU

/-- The map `H¹(Č(V, F)) ⟶ H¹(Č(U, F))` through a common refinement. -/
private def leg (L : LerayRefinement F U V) :
    ((cechComplexFunctor V).obj F.obj).homology 1 ⟶ ((cechComplexFunctor U).obj F.obj).homology 1 :=
  haveI := L.isIso_toU hU hFU
  HomologicalComplex.homologyMap (cechComplexMap F.obj L.toV) 1 ≫
    inv (HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1)

@[reassoc]
private lemma leg_comp_homologyMap (L : LerayRefinement F U V) :
    L.leg hU hFU ≫ HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1 =
      HomologicalComplex.homologyMap (cechComplexMap F.obj L.toV) 1 := by
  have := L.isIso_toU hU hFU
  simp [leg]

/-- Followed by the structure map of `U`, the map through a common refinement is the structure map
of `V`. -/
private lemma leg_comp_toCechCohomology (L : LerayRefinement F U V) (hV : IsOpenCover V) :
    L.leg hU hFU ≫ (toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj =
      (toCechCohomology (ModuleCat.{u} R) 1 V hV).app F.obj := by
  have hW := IsOpenCover.mk L.iSup_eq_top
  -- the source of `(toCechCohomology _ 1 L.W hW).app F.obj` is the homology of the Čech complex
  -- only after unfolding `Functor.comp_obj`, so `rw` cannot match the composites and the steps are
  -- combined as terms
  exact (L.leg hU hFU ≫= (homologyMap_cechComplexMap_comp_toCechCohomology_app _ 1 L.toU
    (IsOpenCover.mk hU) hW F.obj).symm).trans <| (Category.assoc _ _ _).symm.trans <|
      (L.leg_comp_homologyMap hU hFU =≫ _).trans <|
        homologyMap_cechComplexMap_comp_toCechCohomology_app _ 1 L.toV hV hW F.obj

/-- Precompose the refinement of `V` with a refinement `V ⟶ V'`. -/
private def comp {κ' : Type u} {V' : κ' → Opens X} (L : LerayRefinement F U V)
    (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk κ' V') : LerayRefinement F U V' where
  ν := L.ν
  W := L.W
  iSup_eq_top := L.iSup_eq_top
  subsingleton := L.subsingleton
  toV := L.toV ≫ φ
  toU := L.toU

private lemma leg_comp {κ' : Type u} {V' : κ' → Opens X} (L : LerayRefinement F U V)
    (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk κ' V') :
    (L.comp φ).leg hU hFU =
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫ L.leg hU hFU := by
  have := L.isIso_toU hU hFU
  simp only [leg, comp, homologyMap_cechComplexMap_comp, Category.assoc]

include hU hFU in
/-- The map through a common refinement does not depend on the refinement. -/
private lemma leg_eq
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    (L L' : LerayRefinement F U V) : L.leg hU hFU = L'.leg hU hFU := by
  obtain ⟨ν, _, W, hW, hFW, ⟨c⟩, ⟨c'⟩⟩ := exists_common_refinement hF
    (IsOpenCover.mk L.iSup_eq_top) (IsOpenCover.mk L'.iSup_eq_top)
  have := isIso_homologyMap_cechComplexMap_one_of_subsingleton_H' F hW L.iSup_eq_top hFW
    L.subsingleton c
  have := L.isIso_toU hU hFU
  rw [← cancel_mono (HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1 ≫
    HomologicalComplex.homologyMap (cechComplexMap F.obj c) 1), ← Category.assoc,
    leg_comp_homologyMap]
  conv_rhs => rw [← homologyMap_cechComplexMap_comp,
    (cechComplexMapHomotopy F.obj (c ≫ L.toU) (c' ≫ L'.toU)).homologyMap_eq 1,
    homologyMap_cechComplexMap_comp, ← Category.assoc, leg_comp_homologyMap]
  rw [← homologyMap_cechComplexMap_comp, ← homologyMap_cechComplexMap_comp]
  exact (cechComplexMapHomotopy F.obj _ _).homologyMap_eq 1

/-- For a refinement of `U` itself, the map through it is the identity. -/
private lemma leg_self (L : LerayRefinement F U U) : L.leg hU hFU = 𝟙 _ := by
  have := L.isIso_toU hU hFU
  rw [← cancel_mono (HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1),
    leg_comp_homologyMap, Category.id_comp]
  exact (cechComplexMapHomotopy F.obj _ _).homologyMap_eq 1

end LerayRefinement

variable (F U)

omit [Finite ι] in
include hU in
/-- A refinement of an open cover `V` and of `U` by a finite cover whose members have vanishing
`H¹`. -/
private lemma nonempty_lerayRefinement
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {κ : Type u} {V : κ → Opens X} (hV : IsOpenCover V) :
    Nonempty (LerayRefinement F U V) := by
  obtain ⟨ν, _, W, hW, hFW, ⟨a⟩, ⟨b⟩⟩ := exists_common_refinement hF hV (IsOpenCover.mk hU)
  exact ⟨⟨ν, W, hW, hFW, a, b⟩⟩

end Inverse

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
    IsIso ((toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj) := by
  let L : ∀ V : PointOpenCover X, LerayRefinement F U V.opens := fun V ↦
    (nonempty_lerayRefinement F U hU hF V.isOpenCover).some
  let f : ∀ V : PointOpenCover X, ((cechComplexFunctor V.opens).obj F.obj).homology 1 ⟶
      ((cechComplexFunctor U).obj F.obj).homology 1 := fun V ↦ (L V).leg hU hFU
  have hf : ∀ ⦃i j : PointOpenCover X⦄, i ≤ j → ∀ φ : j.toFormalCoproduct ⟶ i.toFormalCoproduct,
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫ f j = f i := fun _ j _ φ ↦ by
    rw [← LerayRefinement.leg_comp]
    exact LerayRefinement.leg_eq hU hFU hF _ _
  let s : (cechCohomology X (ModuleCat.{u} R) 1).obj F.obj ⟶
      ((cechComplexFunctor U).obj F.obj).homology 1 :=
    cechCohomologyDesc PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 1 f hf
  -- the sources of the components of `toCechCohomology` and `cechCohomologyι` are the homology of
  -- the Čech complex only after unfolding, so `rw` cannot match the composites below and the steps
  -- are combined as terms
  refine ⟨s, ?_, cechCohomology_obj_hom_ext fun V ↦ ?_⟩
  · obtain ⟨V₀, ⟨θ⟩⟩ := PointOpenCover.exists_refinement U (IsOpenCover.mk hU)
    have hθ := (homologyMap_cechComplexMap_comp_toCechCohomology_app _ 1 θ (IsOpenCover.mk hU)
      V₀.isOpenCover F.obj).symm.trans
        (_ ≫= NatTrans.congr_app (toCechCohomology_opens _ 1 V₀) F.obj)
    refine (hθ =≫ s).trans <| (Category.assoc _ _ _).trans <|
      (_ ≫= cechCohomologyι_app_cechCohomologyDesc PointOpenCover.toFormalCoproduct
        (fun _ _ h ↦ h) 1 f hf V₀).trans ?_
    exact (LerayRefinement.leg_comp hU hFU (L V₀) θ).symm.trans <| LerayRefinement.leg_self hU hFU _
  · refine ((Category.assoc _ _ _).symm.trans (cechCohomologyι_app_cechCohomologyDesc
      PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 1 f hf V =≫ _)).trans ?_
    exact ((L V).leg_comp_toCechCohomology hU hFU V.isOpenCover).trans <|
      (NatTrans.congr_app (toCechCohomology_opens _ 1 V) F.obj).trans (Category.comp_id _).symm

/-- **The Čech `H¹` of a finite Leray cover.** If every open cover of `X` is refined by a finite
open cover whose members have vanishing `H¹` for `F`, then every finite open cover `U` whose
members have vanishing `H¹` computes the degree one Čech cohomology of `F`: `H¹(Č(U, F))` is
isomorphic to it through the structure map. -/
def cechCohomologyOneIsoOfLeray
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

/-- The forward map of `cechCohomologyOneIsoOfLeray` is the structure map of `U`. -/
theorem cechCohomologyOneIsoOfLeray_hom
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    (cechCohomologyOneIsoOfLeray F hF U hU hFU).hom =
      (toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj :=
  (rfl)

/-- **The inverse of `cechCohomologyOneIsoOfLeray` on a coarser cover.** For an open cover `V`
refined by `U` through `φ`, the structure map of `V` followed by the inverse of
`cechCohomologyOneIsoOfLeray` is the map `H¹(Č(V, F)) ⟶ H¹(Č(U, F))` induced by `φ`. -/
@[reassoc]
theorem toCechCohomology_app_comp_cechCohomologyOneIsoOfLeray_inv
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
        (cechCohomologyOneIsoOfLeray F hF U hU hFU).inv =
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 :=
  -- the source of `(toCechCohomology _ 1 V hV).app F.obj` is the homology of the Čech complex only
  -- after unfolding, so the steps are combined as terms
  (Iso.comp_inv_eq _).2 <| (homologyMap_cechComplexMap_comp_toCechCohomology_app _ 1 φ hV
    (IsOpenCover.mk hU) F.obj).symm.trans
      (_ ≫= (cechCohomologyOneIsoOfLeray_hom F hF U hU hFU).symm)

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
  (Module.Finite.equiv_iff (cechCohomologyOneIsoOfLeray F hF U hU hFU).toLinearEquiv).symm

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
  (cechCohomologyOneIsoOfLeray F hF U hU hFU).toLinearEquiv.finrank_eq.symm

end CategoryTheory.Sheaf
