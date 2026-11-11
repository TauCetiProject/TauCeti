/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Cech.Pullback

/-!
# Pullback and open restriction on Čech cohomology

For a continuous map `f : X ⟶ Y` and a presheaf morphism `P ⟶ f_* Q`, the fixed-cover
pullbacks induce a map from the Čech cohomology of `P` on `Y` to that of `Q` on `X`.
The target uses its own point-neighborhood cover system, not the inverse images of a
cofinal system on `Y` (which need not be cofinal on `X`). The map is characterized on
every small open cover and is natural in the coefficient morphism.

When `f` is inducing and surjective, for instance a homeomorphism, every open cover of `X` is the
inverse image of an open cover of `Y`. So if moreover the coefficient morphism is an isomorphism,
the pullback is an epimorphism (`TopCat.Hom.epi_cechCohomologyPullback`): Čech cohomology, and its
vanishing, transports along homeomorphisms.

Specializing to the inclusion of an open subspace gives restriction on Čech cohomology.
These constructions require no separation, compactness, or sheaf condition.

The fixed-cover maps are `TopCat.Hom.cechComplexPullback`, and the passage to the
colimit follows the Stacks Project, Cohomology of Sheaves, §20.15 (tag 09UY).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.CategoryTheory TauCeti.Topology

universe u v w

variable {A : Type v} [Category.{w} A] [Preadditive A] [HasProducts.{u} A]
  [CategoryWithHomology A] {X Y : TopCat.{u}}
  [HasColimitsOfShape (PointOpenCover X) A] [HasColimitsOfShape (PointOpenCover Y) A]

namespace TopCat.Hom

variable (f : X ⟶ Y) (n : ℕ) {P : Y.Presheaf A} {Q : X.Presheaf A}
  (α : P ⟶ (TopCat.Presheaf.pushforward A f).obj Q)

private def cechPullbackLeg {ι : Type u} (U : ι → Opens Y) (hU : IsOpenCover U) :
    ((cechComplexFunctor U).obj P).homology n ⟶
      (TauCeti.Topology.cechCohomology X A n).obj Q :=
  HomologicalComplex.homologyMap (cechComplexPullback f U α) n ≫
    (TauCeti.Topology.toCechCohomology A n (fun i ↦ (Opens.map f).obj (U i))
      (hU.comap f.hom)).app Q

omit [HasColimitsOfShape (PointOpenCover Y) A] in
private lemma cechPullbackLeg_refinement {ι κ : Type u} {U : ι → Opens Y}
    {V : κ → Opens Y} (φ : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (hU : IsOpenCover U) (hV : IsOpenCover V) :
    HomologicalComplex.homologyMap (cechComplexMap P φ) n ≫ cechPullbackLeg f n α V hV =
      cechPullbackLeg f n α U hU := by
  -- The cover proof uses `Opens.comap`, whereas the complex uses `Opens.map`.
  -- Their agreement requires semireducible unfolding during rewriting.
  erw [cechPullbackLeg, ← HomologicalComplex.homologyMap_comp_assoc,
    cechComplexMap_comp_cechComplexPullback, HomologicalComplex.homologyMap_comp_assoc]
  have h := congrArg (fun t ↦ t.app Q)
    (TauCeti.Topology.cechComplexHomologyMap_comp_toCechCohomology A n
      (⟨φ.f, fun i ↦ (Opens.map f).map (φ.φ i)⟩ :
        FormalCoproduct.mk κ (fun i ↦ (Opens.map f).obj (V i)) ⟶
          FormalCoproduct.mk ι (fun i ↦ (Opens.map f).obj (U i)))
      (hU.comap f.hom) (hV.comap f.hom))
  simp only [NatTrans.comp_app, cechComplexHomologyMap_app] at h
  exact congrArg (HomologicalComplex.homologyMap (cechComplexPullback f U α) n ≫ ·) h

/-- Pull back Čech cohomology along a continuous map and a coefficient morphism `P ⟶ f_* Q`.
On any small cover this is the fixed-cover pullback followed by the structure map on `X`. -/
def cechCohomologyPullback :
    (TauCeti.Topology.cechCohomology Y A n).obj P ⟶
      (TauCeti.Topology.cechCohomology X A n).obj Q :=
  colimit.desc _
    { pt := (TauCeti.Topology.cechCohomology X A n).obj Q
      ι :=
        { app U := cechPullbackLeg f n α U.opens U.isOpenCover
          naturality := fun U V g ↦ by
            rw [Functor.flip_obj_map,
              cechCohomologyDiagram_map A PointOpenCover.toFormalCoproduct
                (fun _ _ h ↦ h) n g (leOfHom g).some, cechComplexHomologyMap_app]
            exact (cechPullbackLeg_refinement f n α (leOfHom g).some
              U.isOpenCover V.isOpenCover).trans (Category.comp_id _).symm } }

private lemma cechCohomologyι_app_comp_cechCohomologyPullback (U : PointOpenCover Y) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) n U).app P ≫
        cechCohomologyPullback f n α = cechPullbackLeg f n α U.opens U.isOpenCover :=
  by
    rw [cechCohomologyι_app, cechCohomologyPullback]
    exact colimit.ι_desc _ _

/-- Pullback commutes with the structure map of every small open cover, including covers
which are not point-neighborhood covers. This characterizes the pullback uniquely. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_app_comp_cechCohomologyPullback {ι : Type u}
    (U : ι → Opens Y) (hU : IsOpenCover U) :
    (TauCeti.Topology.toCechCohomology A n U hU).app P ≫ cechCohomologyPullback f n α =
      HomologicalComplex.homologyMap (cechComplexPullback f U α) n ≫
        (TauCeti.Topology.toCechCohomology A n (fun i ↦ (Opens.map f).obj (U i))
          (hU.comap f.hom)).app Q := by
  obtain ⟨V, ⟨φ⟩⟩ := PointOpenCover.exists_refinement U hU
  -- The diagram's value is a wrapped fixed-cover homology functor.
  erw [TauCeti.Topology.toCechCohomology_eq A n U hU V φ,
    NatTrans.comp_app, Category.assoc, cechCohomologyι_app_comp_cechCohomologyPullback,
    cechComplexHomologyMap_app]
  exact cechPullbackLeg_refinement f n α φ hU V.isOpenCover

/-- A commutative square of coefficient morphisms induces a commutative square on
cover-colimit Čech cohomology. -/
@[reassoc]
theorem cechCohomologyPullback_naturality {P' : Y.Presheaf A} {Q' : X.Presheaf A}
    (α' : P' ⟶ (TopCat.Presheaf.pushforward A f).obj Q') (β : P ⟶ P') (γ : Q ⟶ Q')
    (h : β ≫ α' = α ≫ (TopCat.Presheaf.pushforward A f).map γ) :
    (TauCeti.Topology.cechCohomology Y A n).map β ≫ cechCohomologyPullback f n α' =
      cechCohomologyPullback f n α ≫ (TauCeti.Topology.cechCohomology X A n).map γ := by
  apply cechCohomology_obj_hom_ext
  intro U
  rw [← toCechCohomology_opens A n U]
  -- Unfold the diagram's value when matching the fixed-cover structure maps.
  erw [← (TauCeti.Topology.toCechCohomology A n U.opens U.isOpenCover).naturality_assoc,
    toCechCohomology_app_comp_cechCohomologyPullback,
    toCechCohomology_app_comp_cechCohomologyPullback_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, cechComplexPullback_naturality f _ α α' β γ h,
    HomologicalComplex.homologyMap_comp_assoc]
  exact (congrArg (HomologicalComplex.homologyMap (cechComplexPullback f U.opens α) n ≫ ·)
    ((TauCeti.Topology.toCechCohomology A n (fun i ↦ (Opens.map f).obj (U.opens i))
      (U.isOpenCover.comap f.hom)).naturality γ)).trans (Category.assoc _ _ _).symm

/-- **Pullback along an inducing surjection is onto.** If `f` is inducing and surjective, for
instance a homeomorphism, and the coefficient morphism `P ⟶ f_* Q` is an isomorphism, then the
pullback map on Čech cohomology is an epimorphism. In particular the Čech cohomology of `Q` on `X`
vanishes as soon as that of `P` on `Y` does. -/
theorem epi_cechCohomologyPullback [IsIso α] (hf : Topology.IsInducing f)
    (hs : Function.Surjective f) : Epi (cechCohomologyPullback f n α) := by
  constructor
  intro Z g₁ g₂ hg
  refine cechCohomology_obj_hom_ext fun V ↦ ?_
  rw [← toCechCohomology_opens A n V]
  -- every member of `V` is the inverse image of an open subset of `Y`
  choose U hU using fun i ↦ hf.isOpen_iff.1 (V.opens i).isOpen
  let U' (i : X) : Opens Y := ⟨U i, (hU i).1⟩
  have hU' : IsOpenCover U' := .of_sets (fun i ↦ (hU i).1) <| Set.eq_univ_of_forall fun y ↦ by
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨i, hi⟩ := V.isOpenCover.exists_mem x
    exact Set.mem_iUnion.2 ⟨i, ((hU i).2.symm ▸ hi : x ∈ f ⁻¹' U i)⟩
  let φ : FormalCoproduct.mk X (fun i ↦ (Opens.map f).obj (U' i)) ⟶ V.toFormalCoproduct :=
    ⟨id, fun i ↦ homOfLE (Opens.ext (hU i).2).le⟩
  -- the cover proof produced by `IsOpenCover.comap` is stated for `Opens.comap`
  have hV' : IsOpenCover fun i ↦ (Opens.map f).obj (U' i) := hU'.comap f.hom
  have e₁ : HomologicalComplex.homologyMap (cechComplexPullback f U' α) n ≫
      (TauCeti.Topology.toCechCohomology A n _ hV').app Q =
      (TauCeti.Topology.toCechCohomology A n U' hU').app P ≫ cechCohomologyPullback f n α :=
    (toCechCohomology_app_comp_cechCohomologyPullback f n α U' hU').symm
  have e₂ : (TauCeti.Topology.toCechCohomology A n V.opens V.isOpenCover).app Q =
      (cechComplexHomologyMap A n φ).app Q ≫ (TauCeti.Topology.toCechCohomology A n _ hV').app Q :=
    (NatTrans.congr_app
      (cechComplexHomologyMap_comp_toCechCohomology A n φ V.isOpenCover hV') Q).symm
  have key : (TauCeti.Topology.toCechCohomology A n _ hV').app Q ≫ g₁ =
      (TauCeti.Topology.toCechCohomology A n _ hV').app Q ≫ g₂ := by
    -- the source of `toCechCohomology` is a wrapped homology object, so the steps are terms
    refine (cancel_epi (HomologicalComplex.homologyMap (cechComplexPullback f U' α) n)).1 ?_
    exact (Category.assoc _ _ _).symm.trans <| (e₁ =≫ g₁).trans <| (Category.assoc _ _ _).trans <|
      (_ ≫= hg).trans <| (Category.assoc _ _ _).symm.trans <| (e₁ =≫ g₂).symm.trans <|
        Category.assoc _ _ _
  exact (e₂ =≫ g₁).trans <| (Category.assoc _ _ _).trans <| (_ ≫= key).trans <|
    (Category.assoc _ _ _).symm.trans (e₂ =≫ g₂).symm

end TopCat.Hom

namespace TopologicalSpace.Opens

variable (W : Opens X) (n : ℕ) (P : X.Presheaf A)
  [HasColimitsOfShape (PointOpenCover ((Opens.toTopCat X).obj W)) A]

/-- Restriction on Čech cohomology to an open subspace, using the subspace's own
point-neighborhood covers. The restricted presheaf evaluates on ambient open subsets. -/
def cechCohomologyRestrict :
    (TauCeti.Topology.cechCohomology X A n).obj P ⟶
      (TauCeti.Topology.cechCohomology ((Opens.toTopCat X).obj W) A n).obj
        (W.isOpenEmbedding.isOpenMap.functor.op ⋙ P) :=
  TopCat.Hom.cechCohomologyPullback W.inclusion' n
    (Functor.whiskerRight (NatTrans.op W.isOpenEmbedding.isOpenMap.adjunction.counit) P)

/-- Restriction on cover-colimit cohomology agrees with fixed-cover restriction along
every small cover. In particular it is independent of refinement functions. -/
@[reassoc (attr := simp)]
theorem toCechCohomology_app_comp_cechCohomologyRestrict {ι : Type u}
    (U : ι → Opens X) (hU : IsOpenCover U) :
    (TauCeti.Topology.toCechCohomology A n U hU).app P ≫ cechCohomologyRestrict W n P =
      HomologicalComplex.homologyMap (cechComplexRestrict W U P) n ≫
        (TauCeti.Topology.toCechCohomology A n (fun i ↦ (Opens.map W.inclusion').obj (U i))
          (hU.comap W.inclusion'.hom)).app
          (W.isOpenEmbedding.isOpenMap.functor.op ⋙ P) :=
  by
    rw [cechCohomologyRestrict, cechComplexRestrict_eq]
    exact TopCat.Hom.toCechCohomology_app_comp_cechCohomologyPullback
      W.inclusion' n _ U hU

/-- Open restriction commutes with every morphism of coefficient presheaves. -/
@[reassoc]
theorem cechCohomologyRestrict_naturality {Q : X.Presheaf A} (β : P ⟶ Q) :
    (TauCeti.Topology.cechCohomology X A n).map β ≫ cechCohomologyRestrict W n Q =
      cechCohomologyRestrict W n P ≫
        (TauCeti.Topology.cechCohomology ((Opens.toTopCat X).obj W) A n).map
          (Functor.whiskerLeft W.isOpenEmbedding.isOpenMap.functor.op β) := by
  rw [cechCohomologyRestrict, cechCohomologyRestrict]
  apply TopCat.Hom.cechCohomologyPullback_naturality
  ext V
  exact (β.naturality
    (W.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op).symm

end TopologicalSpace.Opens
