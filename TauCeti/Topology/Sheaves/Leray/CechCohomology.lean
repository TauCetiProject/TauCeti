/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Topology.Sheaves.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Leray.One
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients

/-!
# A finite Leray cover computes degree one Čech cohomology

Let `F` be a sheaf of `R`-modules on a topological space `X` such that every open cover of `X` is
refined by a finite open cover whose members `W i` have `H¹(W i, F) = 0`. Then every finite open
cover `U` of `X` whose members have `H¹(U i, F) = 0` computes the degree one Čech cohomology of
`F`, the colimit over all open covers: the structure map
`TauCeti.Topology.toCechCohomology` from `H¹(Č(U, F))` is an isomorphism
(`CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'`). Unlike
`CategoryTheory.Sheaf.isZero_cechCohomology_one_of_subsingleton_H`, no vanishing of `H¹(X, F)` is
assumed.

The proof constructs the inverse. Every open cover `V` and the cover `U` have a common refinement
`W` by a finite cover of the same kind, and the refinement map `H¹(Č(U, F)) ⟶ H¹(Č(W, F))` is an
isomorphism by the degree one Leray comparison
(`TauCeti.Topology.isIso_homologyMap_cechComplexMap_one`). The inverse sends the class of a cocycle
on `V` to its image on `W`, pulled back to `U`; any two such `W` have a common refinement of the
same kind, so the result does not depend on `W`.

## Main definitions

* `CategoryTheory.Sheaf.forget₂HomologyCechComplexIso`: forgetting the module structure commutes
  with the Čech cohomology of a family of opens.
* `CategoryTheory.Sheaf.cechCohomologyOneIsoOfLeray`: the isomorphism between the Čech `H¹` of a
  finite Leray cover and the degree one Čech cohomology.

## Main results

* `CategoryTheory.Sheaf.isZero_homology_cechComplex_iff`: the Čech cohomology of a presheaf of
  modules vanishes exactly when that of the underlying presheaf of abelian groups does.
* `CategoryTheory.Sheaf.isIso_homologyMap_cechComplexMap_one_of_subsingleton_H'`: for a sheaf of
  modules, a refinement between finite covers whose members have vanishing `H¹` induces an
  isomorphism on degree one Čech cohomology.
* `CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'`: a finite cover whose
  members have vanishing `H¹` computes the degree one Čech cohomology.
* `CategoryTheory.Sheaf.finiteDimensional_cechCohomology_one_iff` and
  `CategoryTheory.Sheaf.finrank_cechCohomology_one`: over a field, the degree one Čech cohomology is
  finite-dimensional exactly when that of the cover is, with the same dimension.

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

/-- Forgetting the module structure commutes with the Čech cohomology of a family of opens. -/
def forget₂HomologyCechComplexIso (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) {ι : Type u}
    (U : ι → Opens X) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (((cechComplexFunctor U).obj P).homology n) ≅
      ((cechComplexFunctor U).obj (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).homology n :=
  ((((cechComplexFunctor U).obj P).sc n).mapHomologyIso _).symm ≪≫
    HomologicalComplex.homologyMapIso
      ((cechComplexFunctorMapIso U (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).app P) n

/-- The Čech cohomology of a presheaf of modules vanishes if and only if that of the underlying
presheaf of abelian groups does. -/
theorem isZero_homology_cechComplex_iff (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) {ι : Type u}
    (U : ι → Opens X) (n : ℕ) :
    IsZero (((cechComplexFunctor U).obj P).homology n) ↔
      IsZero (((cechComplexFunctor U).obj
        (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).homology n) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  rw [← (forget₂HomologyCechComplexIso P U n).isZero_iff]
  refine ⟨G.map_isZero, fun h ↦ (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)⟩
  rw [G.map_id, G.map_zero]
  exact h.eq_of_src _ _

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
  let FAb := (sheafCompose (Opens.grothendieckTopology X) G).obj F
  have hAb : IsIso (HomologicalComplex.homologyMap (cechComplexMap (F.obj ⋙ G) φ) 1) :=
    isIso_homologyMap_cechComplexMap_one U V hU hV FAb hFU hFV φ
  -- transport along the identification of the Čech complexes of `F.obj ⋙ G` with the images
  -- under `G` of those of `F.obj`
  have h₁ := congrArg (HomologicalComplex.homologyMap · 1)
    (cechComplexFunctorMapIso_hom_app_comp_cechComplexMap U G F.obj φ)
  simp only [HomologicalComplex.homologyMap_comp] at h₁
  have h₂ : IsIso (HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex _).map (cechComplexMap F.obj φ)) 1) := by
    have : IsIso (HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex _).map (cechComplexMap F.obj φ)) 1 ≫
          HomologicalComplex.homologyMap ((cechComplexFunctorMapIso U G).hom.app F.obj) 1) := by
      rw [h₁]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (HomologicalComplex.homologyMap ((cechComplexFunctorMapIso U G).hom.app F.obj) 1)
  have h₃ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ 1).map (cechComplexMap F.obj φ)) G
  have h₄ : IsIso (G.map (HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1)) := by
    have : IsIso (ShortComplex.homologyMap (G.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor _ _ 1).map (cechComplexMap F.obj φ))) ≫
          (ShortComplex.mapHomologyIso _ G).hom) := by
      have : IsIso (ShortComplex.homologyMap (G.mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor _ _ 1).map (cechComplexMap F.obj φ)))) := h₂
      infer_instance
    rw [h₃] at this
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (ShortComplex.mapHomologyIso _ G).hom _ _ this
  exact isIso_of_reflects_iso _ G

/-! ### The inverse of the structure map -/

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

/-- Two refinements induce the same map on degree one Čech cohomology. -/
private lemma homologyMap_cechComplexMap_eq {ι₁ ι₂ : Type u} {U₁ : ι₁ → Opens X}
    {U₂ : ι₂ → Opens X} (φ ψ : FormalCoproduct.mk _ U₁ ⟶ FormalCoproduct.mk _ U₂) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 =
      HomologicalComplex.homologyMap (cechComplexMap F.obj ψ) 1 := by
  have h := NatTrans.congr_app (cechComplexHomologyMap_eq (ModuleCat.{u} R) 1 φ ψ) F.obj
  rw [cechComplexHomologyMap_app, cechComplexHomologyMap_app] at h
  exact h

/-- The component at `F` of the map induced by a refinement, followed by a natural
transformation. -/
private lemma app_cechComplexHomologyMap_comp {ι₁ ι₂ : Type u} {U₁ : ι₁ → Opens X}
    {U₂ : ι₂ → Opens X} (φ : FormalCoproduct.mk _ U₁ ⟶ FormalCoproduct.mk _ U₂)
    {G : ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R}
    (g : cechComplexFunctor U₁ ⋙ HomologicalComplex.homologyFunctor _ _ 1 ⟶ G) :
    (cechComplexHomologyMap (ModuleCat.{u} R) 1 φ ≫ g).app F.obj =
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫ g.app F.obj := by
  rw [NatTrans.comp_app, cechComplexHomologyMap_app]
  rfl

variable (F U) in
/-- A refinement of a family `A` and of the cover `U` by a finite cover whose members have
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

/-- Any two finite covers whose members have vanishing `H¹` have a common refinement of the same
kind, provided every open cover has a refinement of that kind. -/
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

private lemma leg_comp_homologyMap (L : LerayRefinement F U V) :
    L.leg hU hFU ≫ HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1 =
      HomologicalComplex.homologyMap (cechComplexMap F.obj L.toV) 1 := by
  have := L.isIso_toU hU hFU
  simp [leg]

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
    homologyMap_cechComplexMap_eq (c ≫ L.toU) (c' ≫ L'.toU), homologyMap_cechComplexMap_comp,
    ← Category.assoc, leg_comp_homologyMap]
  rw [← homologyMap_cechComplexMap_comp, ← homologyMap_cechComplexMap_comp]
  exact homologyMap_cechComplexMap_eq _ _

/-- For a refinement of `U` itself, the map through it is the identity. -/
private lemma leg_self (L : LerayRefinement F U U) : L.leg hU hFU = 𝟙 _ := by
  have := L.isIso_toU hU hFU
  rw [← cancel_mono (HomologicalComplex.homologyMap (cechComplexMap F.obj L.toU) 1),
    leg_comp_homologyMap, Category.id_comp]
  exact homologyMap_cechComplexMap_eq _ _

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
  obtain ⟨V₀, ⟨θ⟩⟩ := PointOpenCover.exists_refinement U (IsOpenCover.mk hU)
  have ht : (toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj =
      HomologicalComplex.homologyMap (cechComplexMap F.obj θ) 1 ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 1 V₀).app F.obj :=
    (NatTrans.congr_app (toCechCohomology_eq _ 1 U _ V₀ θ) F.obj).trans
      (app_cechComplexHomologyMap_comp θ _)
  refine ⟨s, ?_, ?_⟩
  · refine (congrArg (· ≫ s) ht).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (cechCohomologyι_app_cechCohomologyDesc PointOpenCover.toFormalCoproduct
        (fun _ _ h ↦ h) 1 f hf V₀)).trans ?_
    exact (LerayRefinement.leg_comp hU hFU (L V₀) θ).symm.trans <| LerayRefinement.leg_self hU hFU _
  · refine cechCohomology_obj_hom_ext fun V ↦ ?_
    have hL := (L V).isIso_toU hU hFU
    have hW : HomologicalComplex.homologyMap (cechComplexMap F.obj (L V).toU) 1 ≫
        (toCechCohomology (ModuleCat.{u} R) 1 _ (IsOpenCover.mk (L V).iSup_eq_top)).app F.obj =
          (toCechCohomology (ModuleCat.{u} R) 1 U (IsOpenCover.mk hU)).app F.obj :=
      (app_cechComplexHomologyMap_comp _ _).symm.trans
        (NatTrans.congr_app (cechComplexHomologyMap_comp_toCechCohomology (ModuleCat.{u} R) 1
          (L V).toU (IsOpenCover.mk hU) (IsOpenCover.mk (L V).iSup_eq_top)) F.obj)
    have hV : HomologicalComplex.homologyMap (cechComplexMap F.obj (L V).toV) 1 ≫
        (toCechCohomology (ModuleCat.{u} R) 1 _ (IsOpenCover.mk (L V).iSup_eq_top)).app F.obj =
          (toCechCohomology (ModuleCat.{u} R) 1 V.opens V.isOpenCover).app F.obj :=
      (app_cechComplexHomologyMap_comp _ _).symm.trans
        (NatTrans.congr_app (cechComplexHomologyMap_comp_toCechCohomology (ModuleCat.{u} R) 1
          (L V).toV V.isOpenCover (IsOpenCover.mk (L V).iSup_eq_top)) F.obj)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (cechCohomologyι_app_cechCohomologyDesc PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 1
        f hf V))).trans (Eq.trans ?_ (Category.comp_id _).symm)
    change (L V).leg hU hFU ≫ _ = _
    rw [LerayRefinement.leg]
    refine (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      ((congrArg (_ ≫ ·) hW.symm).trans (@IsIso.inv_hom_id_assoc _ _ _ _ _ hL _ _))).trans ?_
    exact hV.trans (NatTrans.congr_app (toCechCohomology_opens _ 1 V) F.obj)

/-- **The Čech `H¹` of a finite Leray cover.** If every open cover of `X` is refined by a finite
open cover whose members have vanishing `H¹` for `F`, then every such cover `U` computes the degree
one Čech cohomology of `F`: `H¹(Č(U, F))` is isomorphic to it through the structure map. -/
@[expose]
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

@[simp]
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
  rfl

section Field

variable {K : Type u} [Field K] (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} K))

/-- Over a field, the degree one Čech cohomology is finite-dimensional exactly when the Čech `H¹`
of a finite Leray cover is. -/
theorem finiteDimensional_cechCohomology_one_iff
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    FiniteDimensional K ((cechCohomology X (ModuleCat.{u} K) 1).obj F.obj) ↔
      FiniteDimensional K (((cechComplexFunctor U).obj F.obj).homology 1) :=
  let e := (cechCohomologyOneIsoOfLeray F hF U hU hFU).toLinearEquiv
  ⟨fun _ ↦ e.symm.finiteDimensional, fun _ ↦ e.finiteDimensional⟩

/-- Over a field, the degree one Čech cohomology has the dimension of the Čech `H¹` of a finite
Leray cover. -/
theorem finrank_cechCohomology_one
    (hF : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ι : Type u) (_ : Finite ι) (W : ι → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, Subsingleton (Sheaf.H'
          ((sheafCompose _ (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).obj F) 1 (W i)))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).obj F) 1 (U i))) :
    Module.finrank K ((cechCohomology X (ModuleCat.{u} K) 1).obj F.obj) =
      Module.finrank K (((cechComplexFunctor U).obj F.obj).homology 1) :=
  (cechCohomologyOneIsoOfLeray F hF U hU hFU).toLinearEquiv.finrank_eq.symm

end Field

end CategoryTheory.Sheaf
