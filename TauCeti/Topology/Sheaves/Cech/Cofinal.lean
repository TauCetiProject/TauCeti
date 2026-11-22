/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# Čech cohomology from arbitrary small covers, and finite covers of compact spaces

The Čech cohomology `TauCeti.Topology.cechCohomology X A n` of presheaves on a topological space
`X` is the colimit over the point-neighborhood covers of `X`. Every `u`-small open cover `U` of
`X` is refined by a point-neighborhood cover, so it has a canonical map `toCechCohomology A n U hU`
from its Čech cohomology to `TauCeti.Topology.cechCohomology X A n`, natural in the presheaf and
with respect to refinements, and independent of the chosen refinement.

On a compact space, the finite indexed covers `TauCeti.Topology.FiniteOpenCover X` form another
cofinal system of covers. The colimit of the Čech cohomologies over them is canonically isomorphic
to the Čech cohomology (`finiteCechCohomologyIso`), compatibly with the maps from every small open
cover. No separation axiom is assumed.

## Main definitions

* `TauCeti.Topology.toCechCohomology A n U hU`: the map to the Čech cohomology from the Čech
  cohomology of a `u`-small open cover `U`.
* `TauCeti.Topology.finiteCechCohomologyIso X A n`: on a compact space, the isomorphism between
  the colimit over finite indexed covers and the Čech cohomology.

## Main results

* `TauCeti.Topology.cechComplexHomologyMap_comp_toCechCohomology`: `toCechCohomology` is natural
  with respect to refinements of open covers, and
  `TauCeti.Topology.homologyMap_cechComplexMap_comp_toCechCohomology_app` is its component at a
  presheaf.
* `TauCeti.Topology.isIso_toCechCohomology_app_of_forall_isIso`: if every open cover is refined by
  a finite cover of a given kind, and refinements between such covers induce isomorphisms on Čech
  cohomology, then every such cover computes the Čech cohomology.
* `TauCeti.Topology.isIso_toCechCohomology_app_zero`: for a sheaf, `toCechCohomology` is an
  isomorphism in degree `0` for every cover.
* `TauCeti.Topology.toCechCohomology_comp_finiteCechCohomologyIso_inv`: the inverse of
  `finiteCechCohomologyIso` on the image of the Čech cohomology of a small open cover.

## References

* The Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY).
* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4.
* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, arXiv:1309.2370v6, Appendix A: Definition A.4.3 and
  Lemma A.4.4, for Čech cohomology as a colimit over covers and the cofinality of finite covers
  of compact spaces.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe v' u u'

namespace TauCeti.Topology

variable {X : TopCat.{u}} (A : Type u') [Category.{v'} A] [Preadditive A] [HasProducts.{u} A]
  [CategoryWithHomology A] [HasColimitsOfShape (PointOpenCover X) A] (n : ℕ)

/-- The map from the Čech cohomology `Hⁿ(Č(U, P))` of a `u`-small open cover `U` of `X` to the
Čech cohomology of `P` on `X`, natural in the presheaf `P`: the map induced by a refinement of `U`
by a point-neighborhood cover, followed by the structure map of the colimit. It depends on neither
choice (`TauCeti.CategoryTheory.toCechCohomology_eq`). -/
def toCechCohomology {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    cechComplexFunctor U ⋙ HomologicalComplex.homologyFunctor A _ n ⟶
      cechCohomology X A n :=
  TauCeti.CategoryTheory.toCechCohomology A _ _ n (FormalCoproduct.mk ι U)
    (PointOpenCover.exists_refinement U hU)

/-- `toCechCohomology` is the map `TauCeti.CategoryTheory.toCechCohomology` to the colimit over
the point-neighborhood cover system. -/
theorem toCechCohomology_def {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U) :
    toCechCohomology A n U hU =
      TauCeti.CategoryTheory.toCechCohomology A PointOpenCover.toFormalCoproduct
        (fun _ _ h ↦ h) n (FormalCoproduct.mk ι U) (PointOpenCover.exists_refinement U hU) :=
  (rfl)

/-- For a point-neighborhood cover, `toCechCohomology` is the structure map of the colimit. -/
@[simp]
theorem toCechCohomology_opens (V : PointOpenCover X) :
    toCechCohomology A n V.opens V.isOpenCover =
      TauCeti.CategoryTheory.cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n V :=
  TauCeti.CategoryTheory.toCechCohomology_self A _ _ n V _

/-- Compute the structure map of any small cover using any point-neighborhood cover
refining it, independently of the refinement chosen in its definition. -/
theorem toCechCohomology_eq {ι : Type u} (U : ι → Opens X) (hU : IsOpenCover U)
    (V : PointOpenCover X) (φ : V.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    toCechCohomology A n U hU =
      TauCeti.CategoryTheory.cechComplexHomologyMap A n φ ≫
        TauCeti.CategoryTheory.cechCohomologyι PointOpenCover.toFormalCoproduct
          (fun _ _ h ↦ h) n V :=
  TauCeti.CategoryTheory.toCechCohomology_eq A _ _ n _ V φ

/-- **`toCechCohomology` is natural with respect to refinements.** If the open cover `V` refines
the open cover `U` through `φ`, the map from the Čech cohomology of `U` to the Čech cohomology on
`X` factors through the map induced by `φ`. -/
@[reassoc]
theorem cechComplexHomologyMap_comp_toCechCohomology {ι κ : Type u} {U : ι → Opens X}
    {V : κ → Opens X} (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (hU : IsOpenCover U)
    (hV : IsOpenCover V) :
    TauCeti.CategoryTheory.cechComplexHomologyMap A n φ ≫ toCechCohomology A n V hV =
      toCechCohomology A n U hU :=
  TauCeti.CategoryTheory.cechComplexHomologyMap_comp_toCechCohomology A _ _ n φ _

/-- The component at a presheaf `P` of `cechComplexHomologyMap_comp_toCechCohomology`: the map on
Čech cohomology induced by a refinement `φ` of the open cover `U` by the open cover `V`, followed
by the structure map of `V`, is the structure map of `U`. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_toCechCohomology_app {ι κ : Type u} {U : ι → Opens X}
    {V : κ → Opens X} (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U) (hU : IsOpenCover U)
    (hV : IsOpenCover V) (P : (Opens X)ᵒᵖ ⥤ A) :
    HomologicalComplex.homologyMap (TauCeti.CategoryTheory.cechComplexMap P φ) n ≫
        (toCechCohomology A n V hV).app P =
      (toCechCohomology A n U hU).app P :=
  TauCeti.CategoryTheory.homologyMap_cechComplexMap_comp_toCechCohomology_app A _ _ n φ _ P

/-- **Covers computing Čech cohomology.** Let `L` be a property of opens such that every open
cover of `X` is refined by a finite open cover whose members have `L`, and every refinement
between two finite open covers whose members have `L` induces an isomorphism on the degree `n`
Čech cohomology of `P`. Then for every finite open cover `U` whose members have `L`, the map from
`Hⁿ(Č(U, P))` to the Čech cohomology of `P` is an isomorphism. -/
theorem isIso_toCechCohomology_app_of_forall_isIso [HasColimitsOfSize.{u, u} A]
    (P : (Opens X)ᵒᵖ ⥤ A) (L : Opens X → Prop)
    (hL : ∀ {κ : Type u} (V : κ → Opens X), IsOpenCover V →
      ∃ (ν : Type u) (_ : Finite ν) (W : ν → Opens X), ⨆ i, W i = ⊤ ∧ (∀ i, ∃ k, W i ≤ V k) ∧
        ∀ i, L (W i))
    (hiso : ∀ V W : FiniteOpenCover X, (∀ i, L (V.opens i)) → (∀ i, L (W.opens i)) →
      ∀ φ : W.toFormalCoproduct ⟶ V.toFormalCoproduct,
        IsIso (HomologicalComplex.homologyMap (TauCeti.CategoryTheory.cechComplexMap P φ) n))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : IsOpenCover U) (hLU : ∀ i, L (U i)) :
    IsIso ((toCechCohomology A n U hU).app P) := by
  -- the finite covers whose members have `L` form a directed system, cofinal with the
  -- point-neighborhood covers, along which the Čech cohomology of `P` is constant
  let J := {W : FiniteOpenCover X // ∀ i, L (W.opens i)}
  have hJ {κ : Type u} (V : κ → Opens X) (hV : IsOpenCover V) :
      ∃ T : J, Nonempty (T.val.toFormalCoproduct ⟶ FormalCoproduct.mk κ V) := by
    obtain ⟨ν, _, W, hW, hWV, hLW⟩ := hL V hV
    obtain ⟨T, ⟨e⟩⟩ := FiniteOpenCover.exists_iso W (IsOpenCover.mk hW)
    choose k hk using hWV
    exact ⟨⟨T, fun i ↦ by rw [FiniteOpenCover.opens_eq_of_iso e i]; exact hLW _⟩,
      ⟨e.hom ≫ ⟨k, fun i ↦ homOfLE (hk i)⟩⟩⟩
  have : IsDirectedOrder J := ⟨fun a b ↦ by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.val b.val
    obtain ⟨T, ⟨ψ⟩⟩ := hJ c.opens c.isOpenCover
    exact ⟨T, ⟨ψ ≫ hac.some⟩, ⟨ψ ≫ hbc.some⟩⟩⟩
  obtain ⟨U₀, ⟨e⟩⟩ := FiniteOpenCover.exists_iso U hU
  let j₀ : J := ⟨U₀, fun i ↦ by rw [FiniteOpenCover.opens_eq_of_iso e i]; exact hLU _⟩
  let E : J → FormalCoproduct.{u} (Opens X) := fun W ↦ W.val.toFormalCoproduct
  have hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i) := fun _ _ h ↦ h
  have h₁ (W : J) : ∃ V : PointOpenCover X, Nonempty (V.toFormalCoproduct ⟶ E W) :=
    PointOpenCover.exists_refinement W.val.opens W.val.isOpenCover
  have h₂ (V : PointOpenCover X) : ∃ W : J, Nonempty (E W ⟶ V.toFormalCoproduct) :=
    hJ V.opens V.isOpenCover
  have : IsIso ((TauCeti.CategoryTheory.cechCohomologyι E hE n j₀).app P) :=
    TauCeti.CategoryTheory.isIso_cechCohomologyι_app A E hE n P j₀ fun W _ φ ↦
      hiso _ _ j₀.property W.property φ
  have : IsIso (TauCeti.CategoryTheory.cechComplexHomologyMap A n e.hom) :=
    ⟨TauCeti.CategoryTheory.cechComplexHomologyMap A n e.inv, by
      rw [← TauCeti.CategoryTheory.cechComplexHomologyMap_comp, e.inv_hom_id,
        TauCeti.CategoryTheory.cechComplexHomologyMap_id], by
      rw [← TauCeti.CategoryTheory.cechComplexHomologyMap_comp, e.hom_inv_id,
        TauCeti.CategoryTheory.cechComplexHomologyMap_id]⟩
  let c := TauCeti.CategoryTheory.cechCohomologyIso A E hE PointOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) n h₁ h₂
  have hfac : TauCeti.CategoryTheory.cechComplexHomologyMap A n e.hom ≫
      TauCeti.CategoryTheory.cechCohomologyι E hE n j₀ ≫ c.hom = toCechCohomology A n U hU := by
    rw [TauCeti.CategoryTheory.cechCohomologyIso_hom]
    -- the source of `cechCohomologyι E hE n j₀` is that of the structure map of `U₀` only after
    -- unfolding the diagram, so the steps are combined as terms
    exact (_ ≫= TauCeti.CategoryTheory.cechCohomologyι_comp_cechCohomologyComparison A E hE _ _ n
      h₁ j₀).trans
        (TauCeti.CategoryTheory.cechComplexHomologyMap_comp_toCechCohomology A _ _ n e.hom (h₁ j₀))
  rw [← hfac]
  exact IsIso.comp_isIso'
    (inferInstance : IsIso ((TauCeti.CategoryTheory.cechComplexHomologyMap A n e.hom).app P))
    (IsIso.comp_isIso'
      (inferInstance : IsIso ((TauCeti.CategoryTheory.cechCohomologyι E hE n j₀).app P))
      (inferInstance : IsIso (c.hom.app P)))

/-- **Every cover computes degree `0` Čech cohomology of a sheaf.** For a sheaf `F` and any
`u`-small open cover `U`, the map `H⁰(Č(U, F)) ⟶ H⁰(X, F)` to the cover-colimit Čech cohomology is
an isomorphism: both sides are the global sections of `F`. -/
theorem isIso_toCechCohomology_app_zero [HasZeroObject A] {ι : Type u} (U : ι → Opens X)
    (hU : IsOpenCover U) (F : Sheaf (Opens.grothendieckTopology X) A) :
    IsIso ((toCechCohomology A 0 U hU).app F.obj) := by
  obtain ⟨V, ⟨ψ⟩⟩ := PointOpenCover.exists_refinement U hU
  have := quasiIsoAt_cechAugmentation_zero_of_iSup_eq_top U hU.iSup_eq_top F
  have e := NatTrans.congr_app (toCechCohomology_eq A 0 U hU V ψ) F.obj
  -- the composite is one of natural transformations between functors whose source is a wrapped
  -- homology functor, which `rw` does not see through
  erw [NatTrans.comp_app] at e
  -- through the augmentation, `toCechCohomology` is the identification with global sections
  let f := (HomologicalComplex.singleObjHomologySelfIso _ 0 _).inv ≫
    HomologicalComplex.homologyMap (TauCeti.CategoryTheory.cechAugmentation U isTerminalTop F.obj) 0
  have h : f ≫ (toCechCohomology A 0 U hU).app F.obj = (cechCohomologyZeroIso F).hom := by
    rw [cechCohomologyZeroIso_hom F V, e, TauCeti.CategoryTheory.cechComplexHomologyMap_app,
      Category.assoc, ← HomologicalComplex.homologyMap_comp_assoc,
      TauCeti.CategoryTheory.cechAugmentation_comp_cechComplexMap]
  have : IsIso (f ≫ (toCechCohomology A 0 U hU).app F.obj) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left f _

variable (X) [CompactSpace X] [HasColimitsOfShape (FiniteOpenCover X) A]

/-- **Finite covers compute Čech cohomology on a compact space.** On a compact space, the colimit
of the Čech cohomologies over the finite indexed covers is canonically isomorphic to the Čech
cohomology, naturally in the presheaf. No separation axiom is assumed. -/
def finiteCechCohomologyIso :
    TauCeti.CategoryTheory.cechCohomology A (FiniteOpenCover.toFormalCoproduct (X := X))
        (fun _ _ h ↦ h) n ≅ cechCohomology X A n :=
  TauCeti.CategoryTheory.cechCohomologyIso A _ _ _ _ n
    (fun W ↦ PointOpenCover.exists_refinement W.opens W.isOpenCover)
    (fun V ↦ FiniteOpenCover.exists_refinement V.opens V.isOpenCover)

/-- The isomorphism `finiteCechCohomologyIso` sends the structure map at a finite cover to the map
`toCechCohomology` of that cover. -/
@[reassoc (attr := simp)]
theorem cechCohomologyι_comp_finiteCechCohomologyIso_hom (W : FiniteOpenCover X) :
    TauCeti.CategoryTheory.cechCohomologyι FiniteOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n W ≫
        (finiteCechCohomologyIso X A n).hom =
      toCechCohomology A n W.opens W.isOpenCover := by
  rw [finiteCechCohomologyIso, TauCeti.CategoryTheory.cechCohomologyIso_hom]
  exact TauCeti.CategoryTheory.cechCohomologyι_comp_cechCohomologyComparison A _ _ _ _ n _ W

/-- The inverse of `finiteCechCohomologyIso` sends the image of the Čech cohomology of any
`u`-small open cover to the map induced by a refinement by a finite indexed cover, followed by the
structure map at that finite cover. -/
@[reassoc]
theorem toCechCohomology_comp_finiteCechCohomologyIso_inv {ι : Type u} (U : ι → Opens X)
    (hU : IsOpenCover U) (W : FiniteOpenCover X)
    (φ : W.toFormalCoproduct ⟶ FormalCoproduct.mk ι U) :
    toCechCohomology A n U hU ≫ (finiteCechCohomologyIso X A n).inv =
      TauCeti.CategoryTheory.cechComplexHomologyMap A n φ ≫
        TauCeti.CategoryTheory.cechCohomologyι FiniteOpenCover.toFormalCoproduct
          (fun _ _ h ↦ h) n W := by
  rw [finiteCechCohomologyIso, TauCeti.CategoryTheory.cechCohomologyIso_inv]
  exact (TauCeti.CategoryTheory.toCechCohomology_comp_cechCohomologyComparison A _ _ _ _ n _ _
    _).trans (TauCeti.CategoryTheory.toCechCohomology_eq A _ _ n _ W φ)

end TauCeti.Topology
