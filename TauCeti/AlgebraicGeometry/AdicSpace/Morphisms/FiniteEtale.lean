/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyStronglySheafy
public import TauCeti.RingTheory.Huber.Pair.Finite

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale
import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete

/-!
# Finite étale morphisms of analytic adic spaces

A morphism `f : Y ⟶ X` of adic spaces is *finite étale* (`TauCeti.AdicSpace.IsFiniteEtale`) when
every point of `X` has an open neighbourhood `V`, isomorphic to the adic spectrum `Spa(A, A⁺)` of a
complete Hausdorff Tate Huber pair `(A, A⁺)`, whose inverse image `f⁻¹(V)` in `Y` is isomorphic to
`Spa(B, B⁺)` for a sheafy Huber pair `(B, B⁺)` such that over `V` the morphism `f` is induced by a
finite étale morphism of Huber pairs `(A, A⁺) → (B, B⁺)`
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale`: `B` is finite étale over `A` with its natural
`A`-module topology and `B⁺` is the integral closure of the image of `A⁺`). Neither noetherianness
nor strong sheafiness of the base is assumed in the definition.

Because a finite étale algebra over a complete Hausdorff Tate ring is finite projective and carries
its module topology, `B` is automatically complete, Hausdorff, and Tate
(`TauCeti.IsNaturallyComplete.of_projective`, `TauCeti.Huber.IsTateRing.of_isModuleTopology`). Thus
both the target `X` and the source `Y` of a finite étale morphism are automatically analytic adic
spaces (`IsFiniteEtale.isAnalytic_target`, `IsFiniteEtale.isAnalytic_source`). Conversely, the
identity of an adic space `X`, any isomorphism onto `X`, and any morphism from an empty adic space
into `X` are finite étale precisely when `X` is analytic.

For complete Hausdorff Tate `(A, A⁺)` and sheafy `(B, B⁺)`, a finite étale morphism of Huber pairs
induces a finite étale morphism of affinoid adic spaces, both for explicit compatible pairs of
definition (`IsFiniteEtale.comapOfPresentation`) and for canonical pair spectra
(`IsFiniteEtale.spa`). Finite étale morphisms are invariant under isomorphisms, descend along open
covers of the target (`IsFiniteEtale.of_iSup_eq_top`), sit inside Huber's finiteness hierarchy
(`locallyOfFiniteType`, `quasiCompact`, `isWeaklyFiniteType`), carry locally noetherian analytic
structure from target to source (`isLocallyNoetherianAnalytic_source`), and have clopen image on
underlying topological spaces (`isClopen_range`).

## Main definitions

* `TauCeti.AdicSpace.IsFiniteEtale`: finite étale morphisms of analytic adic spaces.

## Main results

* `TauCeti.AdicSpace.isOpenImmersion_of_isEmpty`: every morphism of adic spaces out of an empty
  adic space is an open immersion.
* `TauCeti.AdicSpace.IsFiniteEtale.exists_complete_tate_chart`: upgrades each local witness `(B, T)`
  of a finite étale morphism to a complete Hausdorff Tate Huber pair.
* `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target` and
  `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_source`: target and source of a finite étale morphism
  are analytic.
* `TauCeti.AdicSpace.IsFiniteEtale.respectsIso`: invariance under source and target isomorphisms.
* `TauCeti.AdicSpace.IsFiniteEtale.comapOfPresentation` and
  `TauCeti.AdicSpace.IsFiniteEtale.spa`: affinoid constructors from `Pair.Hom.IsFiniteEtale`.
* `TauCeti.AdicSpace.IsFiniteEtale.of_iSup_eq_top`: descent along open covers of the target.
* `TauCeti.AdicSpace.IsFiniteEtale.id`, `TauCeti.AdicSpace.isFiniteEtale_id_iff`,
  `TauCeti.AdicSpace.IsFiniteEtale.of_isIso`, `TauCeti.AdicSpace.isFiniteEtale_of_isIso_iff`,
  `TauCeti.AdicSpace.IsFiniteEtale.of_isEmpty`, and
  `TauCeti.AdicSpace.isFiniteEtale_of_isEmpty_iff`: identities, isomorphisms, and empty covers over
  analytic targets.
* `TauCeti.AdicSpace.IsFiniteEtale.locallyOfFiniteType`,
  `TauCeti.AdicSpace.IsFiniteEtale.quasiCompact`,
  `TauCeti.AdicSpace.IsFiniteEtale.isWeaklyFiniteType`, and
  `TauCeti.AdicSpace.IsFiniteEtale.isLocallyNoetherianAnalytic_source`: finiteness hierarchy and
  ascent of locally noetherian analytic structure.
* `TauCeti.AdicSpace.IsFiniteEtale.isClopen_range` and
  `TauCeti.AdicSpace.IsFiniteEtale.surjective_of_nonempty_of_isPreconnected`: clopenness of the
  image and surjectivity onto preconnected bases.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §6, Definition 6.2(i).
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of Mathematics
  E30 (1996), §1.6.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber PreAdicSpace ValuationSpectrum

universe u

namespace AdicSpace

variable {X Y Z : AdicSpace.{u}}

/-! ### Morphisms out of empty adic spaces -/

/-- **Every morphism of adic spaces out of an empty adic space is an open immersion.** Because both
source and target structure presheaves are sheaves, their sections over the empty open are terminal,
so the comparison map over the empty image is an isomorphism. -/
theorem isOpenImmersion_of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] :
    PreAdicSpace.IsOpenImmersion f.hom := by
  have hopen : IsOpenEmbedding f.hom.base := Topology.IsOpenEmbedding.of_isEmpty f.hom.base
  refine ⟨hopen, fun U ↦ ?_⟩
  have hmapU : (Opens.map f.hom.toHom.base).obj (hopen.functor.obj U) = ⊥ :=
    Subsingleton.elim _ ⊥
  have himgU : hopen.functor.obj U = ⊥ := by
    ext x
    exact ⟨fun ⟨y, _, _⟩ ↦ IsEmpty.false y, False.elim⟩
  let sY : TopCat.Sheaf CompleteSeparatedTopCommRingCat.{u} Y.obj.toPresheafedSpace :=
    ⟨Y.obj.toPresheafedSpace.presheaf, (isAdic_iff.mp Y.property).1⟩
  let sX : TopCat.Sheaf CompleteSeparatedTopCommRingCat.{u} X.obj.toPresheafedSpace :=
    ⟨X.obj.toPresheafedSpace.presheaf, (isAdic_iff.mp X.property).1⟩
  have hTY' := sY.isTerminalOfEqEmpty hmapU
  have hTX := sX.isTerminalOfEqEmpty himgU
  exact ⟨hTX.from _, hTX.hom_ext _ _, hTY'.hom_ext _ _⟩

/-! ### Definition and chart upgrades -/

/-- **Finite étale morphisms of analytic adic spaces** (Kedlaya–Liu I, Definition 8.2.16; Scholze,
Definition 7.1): a morphism `f : Y ⟶ X` in `AdicSpace` is *finite étale* when every point `x` of `X`
has an open neighbourhood `V`, isomorphic to `Spa(A, A⁺)` for a complete Hausdorff Tate Huber pair
`(A, A⁺)`, whose full preimage `f⁻¹(V)` is isomorphic to `Spa(B, B⁺)` for a sheafy Huber pair
`(B, B⁺)` such that over `V` the morphism `f` is induced by a finite étale morphism of Huber pairs
`φ : (A, A⁺) → (B, B⁺)`. -/
def IsFiniteEtale : MorphismProperty AdicSpace.{u} := fun Y X f ↦
  ∀ x : X.obj, ∃ (V : Opens X.obj) (_ : x ∈ V)
    (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
    (_ : IsHuberRing B) (T : Pair B) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
    (eV : X.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
    Y.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫
        eV.inv ≫ X.obj.ofRestrict _

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFiniteEtale`. -/
theorem isFiniteEtale_iff (f : Y ⟶ X) :
    IsFiniteEtale f ↔
      ∀ x : X.obj, ∃ (V : Opens X.obj) (_ : x ∈ V)
        (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
        (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
        (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
        (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsTopologicalRing B)
        (_ : IsHuberRing B) (T : Pair B) (P' : PairOfDefinition B)
        (hP' : P'.ringOfDefinition ≤ T.plus)
        (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
          (presentationLimitPresheaf P' T.plus))
        (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
        (eV : X.obj.restrict V.isOpenEmbedding ≅
          presentationLimitPreAdicSpace P S.plus
            S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
        (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
          presentationLimitPreAdicSpace P' T.plus
            T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
        Y.obj.ofRestrict _ ≫ f.hom =
          eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫
            eV.inv ≫ X.obj.ofRestrict _ :=
  (Iff.rfl)

/-- **Automatic completeness and Tate structure of the source chart.** In each local witness of a
finite étale morphism `f : Y ⟶ X`, the finite étale `A`-algebra `B` carries a compatible uniform
group structure making it a complete Hausdorff Tate ring (`IsNaturallyComplete.of_projective`,
`IsTateRing.of_isModuleTopology`). -/
theorem IsFiniteEtale.exists_complete_tate_chart {f : Y ⟶ X} (hf : IsFiniteEtale f) (x : X.obj) :
    ∃ (V : Opens X.obj) (_ : x ∈ V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsTateRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsTateRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (φ : Pair.Hom S T) (_ : φ.IsFiniteEtale)
      (eV : X.obj.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
      (eU : Y.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
      Y.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫
          eV.inv ≫ X.obj.ofRestrict _ := by
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hsheaf, φ, hφ,
    eV, eU, hfac⟩ := hf x
  let _ : Algebra A B := φ.toRingHom.toAlgebra
  have _ : Module.Finite A B := hφ.finite
  have _ : Algebra.Etale A B := hφ.etale
  have _ : IsModuleTopology A B := hφ.isModuleTopology
  have _ : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have _ : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have _ : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _⟩ := isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := A) (M := B))
  have _ : IsTateRing B := IsTateRing.of_isModuleTopology (A := A) (B := B)
  exact ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', hsheaf, φ, hφ,
    eV, eU, hfac⟩

/-- **The target of a finite étale morphism is analytic.** -/
theorem IsFiniteEtale.isAnalytic_target {f : Y ⟶ X} (hf : IsFiniteEtale f) : X.IsAnalytic := by
  refine isAnalytic_iff.mpr fun x ↦ ?_
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, _, _, _, _, _, _, _, _, _, _, _, eV, _, _⟩ :=
    hf x
  exact ⟨V, (mem_propOpens_iff _).mpr ((isTateAffinoid_iff _).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, S, P, hP, ⟨eV⟩⟩), hx⟩

/-- **The source of a finite étale morphism is analytic.** -/
theorem IsFiniteEtale.isAnalytic_source {f : Y ⟶ X} (hf : IsFiniteEtale f) : Y.IsAnalytic := by
  refine isAnalytic_iff.mpr fun y ↦ ?_
  obtain ⟨V, hx, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP', _, _, _,
    _, eU, _⟩ := hf.exists_complete_tate_chart (f.hom.base y)
  exact ⟨(Opens.map f.hom.base).obj V, (mem_propOpens_iff _).mpr ((isTateAffinoid_iff _).mpr
    ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, T, P', hP', ⟨eU⟩⟩), hx⟩

/-! ### Invariance under isomorphism and affinoid constructors -/

private theorem IsFiniteEtale.iso_hom_comp (e : Z ≅ Y) {f : Y ⟶ X}
    (hf : IsFiniteEtale f) : IsFiniteEtale (e.hom ≫ f) := by
  intro x
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hsheaf, φ, hφ,
    eV, eU, hfac⟩ := hf x
  let e' : Z.obj ≅ Y.obj := (ObjectProperty.ι isAdic).mapIso e
  have hhom : (e.hom ≫ f).hom = e'.hom ≫ f.hom := by
    simp [e']
  have key := Opens.map_inv_obj_map_hom_obj (forgetToTop.mapIso e') ((Opens.map f.hom.base).obj V)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range
      ((Opens.map e'.inv.base).obj ((Opens.map (e.hom ≫ f).hom.base).obj V)).inclusion' =
      Set.range ((Opens.map f.hom.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion', hhom, comp_base, Opens.map_comp_obj]
    exact congrArg SetLike.coe key
  refine ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', hsheaf, φ, hφ, eV,
    restrictIso e' _ ≪≫
      restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  have lhs : Z.obj.ofRestrict ((Opens.map (e.hom ≫ f).hom.base).obj V).isOpenEmbedding ≫
      (e.hom ≫ f).hom =
      (Z.obj.ofRestrict ((Opens.map (e.hom ≫ f).hom.base).obj V).isOpenEmbedding ≫ e'.hom) ≫
        f.hom := by
    simp [e']
  rw [lhs, ← restrictIso_hom_ofRestrict, Category.assoc,
    ← restrictIsoOfRangeEq_hom_ofRestrict Y.obj (Opens.isOpenEmbedding _)
      (Opens.isOpenEmbedding _) hr, Category.assoc, hfac]
  simp

private theorem IsFiniteEtale.comp_iso_hom (e : X ≅ Z) {f : Y ⟶ X}
    (hf : IsFiniteEtale f) : IsFiniteEtale (f ≫ e.hom) := by
  intro z
  let e' : X.obj ≅ Z.obj := (ObjectProperty.ι isAdic).mapIso e
  have hhom : (f ≫ e.hom).hom = f.hom ≫ e'.hom := by
    simp [e']
  obtain ⟨V, hx, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hsheaf, φ, hφ,
    eV, eU, hfac⟩ := hf (e'.inv.base z)
  have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e') V
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range
      ((Opens.map (f ≫ e.hom).hom.base).obj ((Opens.map e'.inv.base).obj V)).inclusion' =
      Set.range ((Opens.map f.hom.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion', hhom, comp_base, Opens.map_comp_obj]
    exact congrArg (fun U ↦ ((Opens.map f.hom.base).obj U : Set Y.obj)) key
  refine ⟨(Opens.map e'.inv.base).obj V, hx, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', hsheaf, φ, hφ,
    (restrictIso e' V).symm ≪≫ eV,
    restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  have lhs : Y.obj.ofRestrict
      ((Opens.map (f ≫ e.hom).hom.base).obj ((Opens.map e'.inv.base).obj V)).isOpenEmbedding ≫
      (f ≫ e.hom).hom =
      (Y.obj.ofRestrict
        ((Opens.map (f ≫ e.hom).hom.base).obj ((Opens.map e'.inv.base).obj V)).isOpenEmbedding ≫
        f.hom) ≫ e'.hom := by
    simp [e']
  rw [lhs, ← restrictIsoOfRangeEq_hom_ofRestrict Y.obj (Opens.isOpenEmbedding _)
      (Opens.isOpenEmbedding _) hr, Category.assoc, Category.assoc, reassoc_of% hfac]
  simp

/-- Being finite étale is invariant under isomorphisms of the source and of the target. -/
instance IsFiniteEtale.respectsIso : MorphismProperty.RespectsIso (@IsFiniteEtale.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ hf.iso_hom_comp e)
    (fun e _ hf ↦ hf.comp_iso_hom e)

/-- **Affinoid finite étale morphisms for explicit presentations.** Let `(A, A⁺)` be a complete
Hausdorff Tate Huber pair and `(B, B⁺)` a Huber pair, with compatible pairs of definition whose
structure presheaves are sheaves. If `φ : (A, A⁺) → (B, B⁺)` is finite étale, then the induced
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace` is finite étale. -/
theorem IsFiniteEtale.comapOfPresentation {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (AdicSpace.comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  refine fun _ ↦ ⟨⊤, trivial, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hS, B, inferInstance, inferInstance,
    inferInstance, inferInstance, T, P', hT, hsheafT, φ, hφ, restrictTopIso _,
    restrictIsoOfRangeEq _ _ (Opens.isOpenEmbedding ⊤) ?_ ≪≫ restrictTopIso _, ?_⟩
  · rw [Opens.map_top]
  · rw [← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id, Iso.trans_hom, restrictTopIso_hom,
      Category.assoc, ← comapOfPresentation_hom S P hS hsheafS T P' hT hsheafT φ,
      restrictIsoOfRangeEq_hom_ofRestrict_assoc]

/-- **`Spa(φ)` is finite étale for a finite étale morphism of sheafy Huber pairs** over a complete
Hausdorff Tate ring (`AdicSpace.comapOfPair`). -/
theorem IsFiniteEtale.spa {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hpres := IsFiniteEtale.comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP'
    (hT.isSheaf P' hP') φ hφ
  have hfac : comapOfPair hS hT φ = (ofPairIsoOfPresentation T hT P' hP').hom ≫
      AdicSpace.comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ ≫
      (ofPairIsoOfPresentation S hS P hP).inv := by
    rw [comapOfPresentation_ofPairIsoOfPresentation_inv, Iso.hom_inv_id_assoc]
  rw [hfac]
  exact (hpres.comp_iso_hom (ofPairIsoOfPresentation S hS P hP).symm).iso_hom_comp
    (ofPairIsoOfPresentation T hT P' hP')

/-! ### Target-cover descent, identities, isomorphisms, and empty covers -/

/-- **Finite étale morphisms descend along any open cover of the target.** -/
theorem IsFiniteEtale.of_iSup_eq_top {f : Y ⟶ X} {ι : Type*} (V : ι → Opens X.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, IsFiniteEtale
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)) :
        (⟨Y.obj.restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding,
          isAdic_restrict _ Y.property⟩ : AdicSpace.{u}) ⟶
        ⟨X.obj.restrict (V i).isOpenEmbedding, isAdic_restrict _ X.property⟩)) :
    IsFiniteEtale f := by
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.symm ▸ Set.mem_univ x : x ∈ iSup V)
  obtain ⟨W, hx, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, T, P', hP', hs, φ, hφ,
    eW, eU, hfac⟩ := hf i ⟨x, hi⟩
  let V' : Opens X.obj := (V i).isOpenEmbedding.isOpenMap.functor.obj W
  let U := (Opens.map f.hom.base).obj (V i)
  let U' := (Opens.map (f.hom.restrictPreimage (V i)).base).obj W
  have hr : Set.range ((Y.obj.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      Y.obj.ofRestrict U.isOpenEmbedding).base =
      Set.range (Y.obj.ofRestrict ((Opens.map f.hom.base).obj V').isOpenEmbedding).base := by
    ext y
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      have hzW : (⟨f.hom.base z.1, z.2⟩ : X.obj.restrict (V i).isOpenEmbedding) ∈ W := by
        rw [← Hom.restrictPreimage_base_apply]
        exact Opens.mem_map.mp hz
      exact ⟨⟨z.1, ⟨⟨f.hom.base z.1, z.2⟩, hzW, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨y, z, hz, hzy⟩, rfl⟩
      have hyV : f.hom.base y ∈ V i := hzy ▸ z.2
      let y' : Y.obj.restrict U.isOpenEmbedding := ⟨y, Opens.mem_map.mpr hyV⟩
      refine ⟨⟨y', ?_⟩, rfl⟩
      have heq : (f.hom.restrictPreimage (V i)).base y' = z :=
        (f.hom.restrictPreimage_base_apply (V i) y').trans (Subtype.ext hzy.symm)
      exact Opens.mem_map.mpr (heq.symm ▸ hz)
  let e := IsOpenImmersion.isoOfRangeEq
    ((Y.obj.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      Y.obj.ofRestrict U.isOpenEmbedding)
    (Y.obj.ofRestrict ((Opens.map f.hom.base).obj V').isOpenEmbedding) hr
  refine ⟨V', ⟨⟨x, hi⟩, hx, rfl⟩, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, T, P', hP', hs, φ, hφ,
    (restrictRestrictIso X.obj (V i).isOpenEmbedding W).symm ≪≫ eW, e.symm ≪≫ eU, ?_⟩
  have hsource := congrArg (fun g ↦ g ≫ f.hom)
    (IsOpenImmersion.isoOfRangeEq_inv_comp _ _ hr)
  have hsquare := congrArg (fun g ↦ g ≫ X.obj.ofRestrict (V i).isOpenEmbedding) hfac
  have htarget := congrArg
    (fun g ↦ eU.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hs φ ≫ eW.inv ≫ g)
    (restrictRestrictIso_hom_ofRestrict X.obj (V i).isOpenEmbedding W)
  simp only [Category.assoc] at hsource htarget
  simp only [ObjectProperty.homMk_hom, Category.assoc, Hom.restrictPreimage_ofRestrict] at hsquare
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
    hsource.symm.trans (congrArg (fun g ↦ e.inv ≫ g) (hsquare.trans htarget.symm))

/-- **The identity of an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.id {X : AdicSpace.{u}} (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) := by
  intro x
  obtain ⟨V, hV, hx⟩ := isAnalytic_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      ((ObjectProperty.prop_iff_of_iso PreAdicSpace.isSheafy eV).mp
        (isSheafy_restrict _ (isAdic_iff.mp X.property).1))
  refine ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, A, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP, hsheaf, Pair.Hom.id S, Pair.Hom.isFiniteEtale_id S, eV,
    restrictIsoOfRangeEq X.obj _ V.isOpenEmbedding
      (by rw [Opens.set_range_inclusion', Opens.set_range_inclusion']; rfl) ≪≫ eV, ?_⟩
  rw [presentationLimitPreAdicSpacePairComap_id, Category.id_comp, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, restrictIsoOfRangeEq_hom_ofRestrict]
  exact Category.comp_id _

/-- **The identity of an adic space `X` is finite étale if and only if `X` is analytic.** -/
theorem isFiniteEtale_id_iff {X : AdicSpace.{u}} : IsFiniteEtale (𝟙 X) ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.id⟩

/-- **An isomorphism onto an analytic adic space is finite étale.** -/
theorem IsFiniteEtale.of_isIso (f : Y ⟶ X) [IsIso f] (hX : X.IsAnalytic) : IsFiniteEtale f := by
  have h : f = (asIso f).hom ≫ 𝟙 X := (Category.comp_id f).symm
  rw [h]
  exact (IsFiniteEtale.id hX).iso_hom_comp (asIso f)

/-- **An isomorphism in `AdicSpace` is finite étale if and only if its target is analytic.** -/
theorem isFiniteEtale_of_isIso_iff (f : Y ⟶ X) [IsIso f] : IsFiniteEtale f ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.of_isIso f⟩

/-- The zero ring `PUnit` is finite étale with its module topology over any Huber pair `S`. -/
private theorem isFiniteEtale_punit {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (S : Pair A) :
    (Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}).IsFiniteEtale := by
  have _ : IsLocalization.Away (0 : A) PUnit.{u + 1} :=
    { map_units := fun _ ↦ isUnit_of_subsingleton _
      surj := fun _ ↦ ⟨(0, 1), Subsingleton.elim _ _⟩
      exists_of_eq := fun {_ _} _ ↦ ⟨⟨0, 1, pow_one 0⟩, by simp⟩ }
  have _ : Algebra.Etale A PUnit.{u + 1} := Algebra.Etale.of_isLocalizationAway (0 : A)
  have _ : Module.Finite A PUnit.{u + 1} :=
    Module.Finite.of_surjective (Algebra.ofId A PUnit.{u + 1}).toLinearMap
      fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  have _ : IsModuleTopology A PUnit.{u + 1} := ⟨Subsingleton.elim _ _⟩
  exact Pair.finiteAlgebra.isFiniteEtale_algebraHom S PUnit.{u + 1}

/-- **Every morphism from an empty adic space into an analytic adic space is finite étale** (the
empty cover of degree `0`, modelled over each Tate affinoid chart by the zero `A`-algebra). -/
theorem IsFiniteEtale.of_isEmpty (f : Y ⟶ X) [IsEmpty Y.obj] (hX : X.IsAnalytic) :
    IsFiniteEtale f := by
  intro x
  obtain ⟨V, hV, hx⟩ := isAnalytic_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have _ : IsModuleTopology A PUnit.{u + 1} := ⟨Subsingleton.elim _ _⟩
  have _ : Module.Finite A PUnit.{u + 1} :=
    Module.Finite.of_surjective (Algebra.ofId A PUnit.{u + 1}).toLinearMap
      fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  let T : Pair PUnit.{u + 1} := S.finiteAlgebra PUnit.{u + 1}
  let P' : PairOfDefinition PUnit.{u + 1} :=
    { ringOfDefinition := ⊤
      isOpen_ringOfDefinition := isOpen_discrete _
      idealOfDefinition := ⊥
      fg_idealOfDefinition := Submodule.fg_bot
      isAdic_idealOfDefinition := is_bot_adic_iff.mpr inferInstance }
  have hP' : P'.ringOfDefinition ≤ T.plus := fun y _ ↦ by
    rw [Subsingleton.elim y 0]
    exact T.plus.zero_mem
  have hpu : IsPseudoUniformizer (0 : PUnit.{u + 1}) :=
    isPseudoUniformizer_iff.mpr ⟨Subsingleton.elim (0 : PUnit.{u + 1}) 1 ▸ isUnit_one, .zero⟩
  let _ : IsTateRing PUnit.{u + 1} := ⟨⟨0, hpu⟩⟩
  have _ : IsStronglyNoetherian PUnit.{u + 1} := IsNoetherianType.isStronglyNoetherian
  have hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(ValuationSpectrum.spa T.plus))
      (presentationLimitPresheaf P' T.plus) :=
    isSheaf_presentationLimitPresheaf_of_isStronglyNoetherian P' hP'
      T.isRingOfIntegralElements.isPowerBounded_of_mem
  let φ : Pair.Hom S T := Pair.finiteAlgebra.algebraHom S PUnit.{u + 1}
  let Z : AdicSpace.{u} := ofPresentation T P' hP' hsheaf
  have _ : IsEmpty Z.obj := by
    have hspa : ValuationSpectrum.spa T.plus = ∅ :=
      (spa_eq_empty_iff_subsingleton _ T.isRingOfIntegralElements).mpr inferInstance
    exact Set.isEmpty_coe_sort.mpr hspa
  let U := (Opens.map f.hom.base).obj V
  let YV : AdicSpace.{u} := ⟨Y.obj.restrict U.isOpenEmbedding, isAdic_restrict _ Y.property⟩
  have _ : IsEmpty YV.obj :=
    ⟨fun z ↦ IsEmpty.false (Y.obj.ofRestrict U.isOpenEmbedding |>.base z)⟩
  let g₁ : YV ⟶ X := ObjectProperty.homMk (Y.obj.ofRestrict U.isOpenEmbedding ≫ f.hom)
  let g₂ : Z ⟶ X := ObjectProperty.homMk
    (presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫ eV.inv ≫
      X.obj.ofRestrict V.isOpenEmbedding)
  have _ : PreAdicSpace.IsOpenImmersion g₁.hom := isOpenImmersion_of_isEmpty g₁
  have _ : PreAdicSpace.IsOpenImmersion g₂.hom := isOpenImmersion_of_isEmpty g₂
  have hrange : Set.range g₁.hom.base = Set.range g₂.hom.base := by
    rw [Set.range_eq_empty, Set.range_eq_empty]
  let eU := IsOpenImmersion.isoOfRangeEq g₁.hom g₂.hom hrange
  refine ⟨V, hx, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, PUnit.{u + 1}, inferInstance, inferInstance,
    inferInstance, inferInstance, T, P', hP', hsheaf, φ, isFiniteEtale_punit S, eV, eU, ?_⟩
  exact (IsOpenImmersion.isoOfRangeEq_hom_comp g₁.hom g₂.hom hrange).symm

/-- **A morphism from an empty adic space into `X` is finite étale if and only if `X` is
analytic.** -/
theorem isFiniteEtale_of_isEmpty_iff (f : Y ⟶ X) [IsEmpty Y.obj] :
    IsFiniteEtale f ↔ X.IsAnalytic :=
  ⟨IsFiniteEtale.isAnalytic_target, IsFiniteEtale.of_isEmpty f⟩

/-! ### Finiteness hierarchy and topological properties -/

/-- **A finite étale morphism is locally of finite type** (`Pair.Hom.IsFiniteEtale.isFinite`). -/
theorem IsFiniteEtale.locallyOfFiniteType {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    PreAdicSpace.LocallyOfFiniteType f.hom := by
  choose V hx A iCA uA gA tA cA h2A tateA S P hP B iCB uB gB tB cB h2B tateB T P' hP'
    hsheaf φ hφ eV eU hfac using hf.exists_complete_tate_chart
  have hcov : iSup V = ⊤ := eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩
  refine PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top_restrictPreimage V hcov fun x ↦ ?_
  have hfin : (φ x).IsTopologicallyFiniteType := (hφ x).isFinite.isTopologicallyFiniteType
  have hmodel : PreAdicSpace.LocallyOfFiniteType
      (presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x) (hsheaf x) (φ x)) := by
    rw [presentationLimitPreAdicSpacePairComap_def]
    exact locallyOfFiniteType_presentationLimitPreAdicSpaceComap (P x) (P' x) (hP x) (hP' x)
      (hsheaf x) (φ x) hfin
  have hres : f.hom.restrictPreimage (V x) =
      (eU x).hom ≫ presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x)
        (hsheaf x) (φ x) ≫ (eV x).inv := by
    rw [← cancel_mono (X.obj.ofRestrict (V x).isOpenEmbedding), Hom.restrictPreimage_ofRestrict,
      hfac x, Category.assoc, Category.assoc]
  rw [hres, MorphismProperty.cancel_left_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}]
  exact (MorphismProperty.cancel_right_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}
    _ _).mpr hmodel

/-- **A finite étale morphism is quasi-compact.** Over each base chart `V ≅ Spa(A, A⁺)`, the
chart morphism is spectral because `A` is Tate; open affinoid subspaces subordinated to the charts
form a topological basis of `X` whose members are quasi-compact and pull back to quasi-compact
subsets of `Y`. -/
theorem IsFiniteEtale.quasiCompact {f : Y ⟶ X} (hf : IsFiniteEtale f) : QuasiCompact f := by
  choose V hx A iCA uA _ tA _ _ tateA S P hP B iCB tB rB hB T P' hP'
    hsheaf φ _ eV eU hfac using hf
  have hspec (x : X.obj) :
      IsSpectralMap ((Set.mapsTo_preimage f.hom.base (V x : Set X.obj)).restrict
        f.hom.base _ _) := by
    have hfac' := congrArg (fun k ↦ ConcreteCategory.hom (forgetToTop.map k)) (hfac x)
    simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
    have hg : IsSpectralMap
        (presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x) (hsheaf x)
          (φ x)).base := by
      have h := (φ x).isSpectralMap_spaComap fun J hJ ↦
        IsTateRing.isOpen_map_of_isOpen (φ x).toRingHom hJ
      rw [Pair.Hom.spaComap_def] at h
      rw [presentationLimitPreAdicSpacePairComap_def, presentationLimitPreAdicSpaceComap_toHom,
        presentationLimitPresheafedSpaceComap_base]
      exact h
    have heq : (Set.mapsTo_preimage f.hom.base (V x : Set X.obj)).restrict f.hom.base _ _ =
        TopCat.homeoOfIso (forgetToTop.mapIso (eV x).symm) ∘
          (presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x) (hsheaf x)
            (φ x)).base ∘ TopCat.homeoOfIso (forgetToTop.mapIso (eU x)) :=
      funext fun y ↦ Subtype.ext (congrArg (fun k ↦ k y) hfac')
    rw [heq]
    exact (TopCat.homeoOfIso (forgetToTop.mapIso (eV x).symm)).isProperMap.isSpectralMap.comp
      (hg.comp (TopCat.homeoOfIso (forgetToTop.mapIso (eU x))).isProperMap.isSpectralMap)
  have hB : Opens.IsBasis {W : Opens X.obj | W ∈ X.obj.affinoidOpens ∧ ∃ x : X.obj, W ≤ V x} := by
    refine Opens.isBasis_iff_nbhd.mpr fun {U z} hzU ↦ ?_
    have hzUV : z ∈ U ⊓ V z := ⟨hzU, hx z⟩
    obtain ⟨W, hW, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp
      (isBasis_affinoidOpens X.property.isLocallyAffinoid)) hzUV
    exact ⟨W, ⟨hW, z, hWle.trans inf_le_right⟩, hzW, hWle.trans inf_le_left⟩
  refine (quasiCompact_iff_isSpectralMap f).mpr
    (isSpectralMap_of_isTopologicalBasis hB f.hom.base.hom.continuous ?_)
  rintro _ ⟨W, ⟨hW, x, hWV⟩, rfl⟩
  have hcomp := ((Set.mapsTo_preimage f.hom.base (V x : Set X.obj)).isSpectralMap_restrict_iff
    f.hom.base.hom.continuous.continuousOn (V x).isOpen).mp (hspec x)
    (W : Set X.obj) hWV W.isOpen (isCompact_of_mem_affinoidOpens hW)
  rwa [Set.inter_eq_right.mpr (Set.preimage_mono hWV)] at hcomp

/-- **A finite étale morphism is of weakly finite type.** -/
theorem IsFiniteEtale.isWeaklyFiniteType {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    IsWeaklyFiniteType f :=
  (isWeaklyFiniteType_iff f).mpr ⟨hf.locallyOfFiniteType.locallyOfWeaklyFiniteType, hf.quasiCompact⟩

/-- **Locally noetherian analytic structure ascends along finite étale morphisms.** -/
theorem IsFiniteEtale.isLocallyNoetherianAnalytic_source {f : Y ⟶ X} (hf : IsFiniteEtale f)
    (hX : X.IsLocallyNoetherianAnalytic) : Y.IsLocallyNoetherianAnalytic :=
  isLocallyNoetherianAnalytic_iff.mpr
    ⟨hX.isLocallyNoetherian.of_locallyOfFiniteType hf.locallyOfFiniteType, hf.isAnalytic_source⟩

/-- **The image of a finite étale morphism of adic spaces is clopen.** Locally on `X`, the image is
that of `Pair.Hom.spaComap` for a finite étale morphism over a Tate ring, which is clopen by
`Pair.Hom.IsFiniteEtale.isClopen_range_spaComap`. -/
theorem IsFiniteEtale.isClopen_range {f : Y ⟶ X} (hf : IsFiniteEtale f) :
    IsClopen (Set.range f.hom.base) := by
  choose V hx A iCA uA _ tA _ _ tateA S P hP B iCB tB rB hB T P' hP'
    hsheaf φ hφ eV eU hfac using hf
  have hlocal (x : X.obj) :
      IsClopen ((Subtype.val : V x → X.obj) ⁻¹' Set.range f.hom.base) := by
    let g := presentationLimitPreAdicSpacePairComap (P x) (P' x) (hP x) (hP' x) (hsheaf x) (φ x)
    let hU_homeo := TopCat.homeoOfIso (forgetToTop.mapIso (eU x))
    let hV_homeo := TopCat.homeoOfIso (forgetToTop.mapIso (eV x))
    have hfac' := congrArg (fun k ↦ ConcreteCategory.hom (forgetToTop.map k)) (hfac x)
    simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
    have hpre : (Subtype.val : V x → X.obj) ⁻¹' Set.range f.hom.base =
        hV_homeo ⁻¹' Set.range (φ x).spaComap := by
      ext v
      constructor
      · rintro ⟨y, hy⟩
        have hyU : y ∈ (Opens.map f.hom.base).obj (V x) := by
          change f.hom.base y ∈ V x
          rw [hy]
          exact v.2
        let u : forgetToTop.obj
            (Y.obj.restrict ((Opens.map f.hom.base).obj (V x)).isOpenEmbedding) := ⟨y, hyU⟩
        refine ⟨hU_homeo u, ?_⟩
        have hv' : (v : forgetToTop.obj (X.obj.restrict (V x).isOpenEmbedding)) =
            hV_homeo.symm (g.base (hU_homeo u)) :=
          Subtype.ext (hy.symm.trans (congrArg (fun k ↦ k u) hfac'))
        exact (presentationLimitPreAdicSpacePairComap_base_apply
          (P x) (P' x) (hP x) (hP' x) (hsheaf x) (φ x) (hU_homeo u)).symm.trans
          ((hV_homeo.apply_symm_apply _).symm.trans (congrArg hV_homeo hv'.symm))
      · rintro ⟨z, hz⟩
        let u := hU_homeo.symm z
        refine ⟨u.1, ?_⟩
        have hgz : g.base (hU_homeo u) = hV_homeo v :=
          (presentationLimitPreAdicSpacePairComap_base_apply
            (P x) (P' x) (hP x) (hP' x) (hsheaf x) (φ x) (hU_homeo u)).trans
            ((congrArg (φ x).spaComap (hU_homeo.apply_symm_apply z)).trans hz)
        exact (congrArg (fun k ↦ k u) hfac').trans
          (congrArg Subtype.val ((congrArg hV_homeo.symm hgz).trans (hV_homeo.symm_apply_apply v)))
    rw [hpre]
    exact (hφ x).isClopen_range_spaComap.preimage hV_homeo.continuous
  refine ⟨isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x hx_not ↦ ?_),
    isOpen_iff_forall_mem_open.mpr fun x hx_mem ↦ ?_⟩
  · refine ⟨Subtype.val '' ((Subtype.val : V x → X.obj) ⁻¹' (Set.range f.hom.base)ᶜ),
      ?_, (V x).isOpen.isOpenMap_subtype_val _ (hlocal x).1.isOpen_compl,
      ⟨⟨x, hx x⟩, hx_not, rfl⟩⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hv
  · refine ⟨Subtype.val '' ((Subtype.val : V x → X.obj) ⁻¹' Set.range f.hom.base),
      ?_, (V x).isOpen.isOpenMap_subtype_val _ (hlocal x).2, ⟨⟨x, hx x⟩, hx_mem, rfl⟩⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hv

/-- **A finite étale morphism from a nonempty source into a preconnected target is surjective.** -/
theorem IsFiniteEtale.surjective_of_nonempty_of_isPreconnected {f : Y ⟶ X} (hf : IsFiniteEtale f)
    [Nonempty Y.obj] [PreconnectedSpace X.obj] : Function.Surjective f.hom.base := by
  have hrange := hf.isClopen_range.eq_univ (Set.range_nonempty f.hom.base)
  exact Set.range_eq_univ.mp hrange

end AdicSpace

end TauCeti
