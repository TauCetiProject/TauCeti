/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Finite.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyTate
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.FiniteAlgebra
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteEtale

/-!
# Finite étale morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *finite étale* (Kedlaya–Liu, Definition 8.2.16) if every
point of `Y` has an open neighbourhood `V` such that `V ≅ Spa(A, A⁺)` for a complete Hausdorff Tate
Huber pair and `f⁻¹(V) ≅ Spa(B, B⁺)` for a complete Hausdorff Huber pair, under which `f`
restricted to `f⁻¹(V) → V` is the morphism induced by a finite étale morphism of Huber pairs
`φ : (A, A⁺) → (B, B⁺)` (`TauCeti.Huber.Pair.Hom.IsFiniteEtale`): `B` is a finite étale
`A`-algebra with its natural topology and `B⁺` is the integral closure of the image of `A⁺`.

This is the notion of finite étale morphism for analytic adic spaces that need not be locally
noetherian, where Huber's infinitesimal definition is not available. The condition is local on the
target, and no particular cover is fixed. The plus ring is part of the condition: for a finite étale
`A`-algebra `B` the pair `(B, B°)` is in general not the one attached to `B`. The Tate charts force
both spaces to be analytic. Sheafiness is not automatic: the definition asks that `Spa(B, B⁺)` be an
adic space, and that `Spa(A, A⁺)` be one follows from its being an open subspace of `Y`.

A finite étale morphism of Huber pairs over a complete Hausdorff Tate ring is finite
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`), so finite étale morphisms of adic spaces are
finite in Huber's sense (`TauCeti.AdicSpace.IsFinite`), hence quasi-compact
(`TauCeti.AdicSpace.IsFinite.quasiCompact`) and of weakly finite type
(`TauCeti.AdicSpace.IsFinite.isWeaklyFiniteType`). The fibres of `Spa(B, B⁺) → Spa(A, A⁺)` have
at most as many points as the local rank of `B`
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.finite_fibre`), so finite étale morphisms have finite
fibres.

## Main definitions

* `TauCeti.AdicSpace.IsFiniteEtale`: finite étale morphisms of adic spaces.

## Main results

* `TauCeti.AdicSpace.isFiniteEtale_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a finite étale morphism of complete Hausdorff Huber pairs
  over a Tate ring, both of whose spectra are adic spaces, is finite étale.
* `TauCeti.AdicSpace.IsFiniteEtale.isFinite`: finite étale morphisms are finite.
* `TauCeti.AdicSpace.IsFiniteEtale.finite_preimage_singleton`: finite étale morphisms have finite
  fibres.
* `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_source`,
  `TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target`: the source and the target of a finite étale
  morphism are analytic.
* `TauCeti.AdicSpace.IsFiniteEtale.of_iSup_eq_top`: being finite étale descends along open covers
  of the target.
* `TauCeti.AdicSpace.IsFiniteEtale.respectsIso`: being finite étale is invariant under isomorphisms
  of the source and of the target.
* `TauCeti.AdicSpace.isFiniteEtale_id` and `TauCeti.AdicSpace.isFiniteEtale_of_isIso`: the
  identity of an analytic adic space, and every isomorphism onto one, are finite étale.

## Implementation notes

`IsFiniteEtale` is the target-local property `TauCeti.AdicSpace.targetLocally` attached to the
finite étale morphisms of Huber pairs `(A, A⁺) → (B, B⁺)` with `A` a Tate ring, the same shape as
`TauCeti.AdicSpace.IsFinite` (`Morphisms/Finite/Basic.lean`). Descent along open covers, the
affinoid case, isomorphism invariance and the identity are specializations of the general results
for `targetLocally`, and `IsFiniteEtale.isFinite` is its monotonicity in the property of Huber
pairs.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1(ii).
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Annals of Mathematics
  Studies 207 (2020), Lecture 7, Definition 7.5.1(1).
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Finite étale morphisms** (Kedlaya–Liu, Definition 8.2.16): a morphism `f : X ⟶ Y` of adic
spaces is *finite étale* when every point `y` of `Y` has an open neighbourhood `V` together with a
complete Hausdorff Tate Huber pair `(A, A⁺)`, a complete Hausdorff Huber pair `(B, B⁺)` such that
`Spa(B, B⁺)` has a sheaf as structure presheaf, a finite étale morphism `φ : (A, A⁺) → (B, B⁺)` of
Huber pairs, and isomorphisms identifying `Y` restricted to `V` with `Spa(A, A⁺)` and `X` restricted
to `f⁻¹(V)` with `Spa(B, B⁺)`, under which `f` becomes the morphism induced by `φ`. -/
def IsFiniteEtale {X Y : AdicSpace.{u}} (f : X ⟶ Y) : Prop :=
  targetLocally (@fun A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ↦ IsTateRing A ∧ φ.IsFiniteEtale) f

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFiniteEtale`: being finite étale is the target-local
property attached to finite étale morphisms of Huber pairs over Tate rings. -/
theorem isFiniteEtale_iff (f : X ⟶ Y) : IsFiniteEtale f ↔
    targetLocally (@fun A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ↦ IsTateRing A ∧ φ.IsFiniteEtale) f :=
  Iff.rfl

/-! ### Finite étale morphisms are finite, with finite fibres -/

/-- **Finite étale morphisms are finite**: over a complete Hausdorff Tate ring, a finite étale
morphism of Huber pairs is finite (`TauCeti.Huber.Pair.Hom.IsFiniteEtale.isFinite`). -/
theorem IsFiniteEtale.isFinite {f : X ⟶ Y} (hf : IsFiniteEtale f) : IsFinite f :=
  (isFinite_iff f).mpr <|
    targetLocally_mono (fun _ ⟨_, hφ⟩ ↦ hφ.isFinite) ((isFiniteEtale_iff f).mp hf)

/-- **The fibres of a finite étale morphism are finite.** Over a neighbourhood `V` supplied by the
definition, the morphism is, up to homeomorphisms, the map `Spa(B, B⁺) → Spa(A, A⁺)` induced by a
finite étale morphism of Huber pairs, whose fibres are finite
(`TauCeti.Huber.Pair.Hom.IsFiniteEtale.finite_fibre`). -/
theorem IsFiniteEtale.finite_preimage_singleton {f : X ⟶ Y} (hf : IsFiniteEtale f) (y : Y.obj) :
    (f.hom.base ⁻¹' {y}).Finite := by
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, ⟨_, hφ⟩,
    hsheaf, eV, eU, hfac⟩ := (targetLocally_iff f).mp ((isFiniteEtale_iff f).mp hf) y
  let g := presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf
  let eU' := TopCat.homeoOfIso (forgetToTop.mapIso eU)
  let eV' := TopCat.homeoOfIso (forgetToTop.mapIso eV)
  -- on points, `Spa(φ)` is `φ.spaComap`, whose fibres are finite
  have hg : ⇑(ConcreteCategory.hom g.base) = φ.spaComap := funext fun w ↦ Subtype.ext <|
    (presentationLimitPreAdicSpaceComap_base_val _ _ _ _ _ _ _ _ w).trans (φ.spaComap_val w).symm
  have hfin : (⇑(ConcreteCategory.hom g.base) ⁻¹' {eV' ⟨y, hy⟩}).Finite :=
    hg ▸ (hφ.finite_fibre _).1
  -- the defining square, on points
  have hfac' := congrArg (fun h ↦ ConcreteCategory.hom (forgetToTop.map h)) hfac
  simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
  -- the fibre of `f` over `y` is the image of the fibre of `Spa(φ)` over the point of `y`
  refine (hfin.image fun w ↦ (eU'.symm w).val).subset fun x hx ↦ ?_
  have hxV : f.hom.base x ∈ V := (Set.mem_singleton_iff.mp hx).symm ▸ hy
  have h := congrArg (fun h ↦ h ⟨x, hxV⟩) hfac'
  exact ⟨eU' ⟨x, hxV⟩, eV'.symm_apply_eq.mp (Subtype.ext (h.symm.trans hx)),
    congrArg Subtype.val (eU'.symm_apply_apply _)⟩

/-! ### Finite étale morphisms have analytic source and target -/

/-- **The target of a finite étale morphism is analytic**: the neighbourhoods supplied by the
definition are open Tate affinoid subspaces. -/
theorem IsFiniteEtale.isAnalytic_target {f : X ⟶ Y} (hf : IsFiniteEtale f) : Y.IsAnalytic :=
  isAnalytic_iff.mpr fun y ↦ by
    obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hA, -⟩,
      _, eV, _⟩ := (targetLocally_iff f).mp ((isFiniteEtale_iff f).mp hf) y
    exact ⟨V, (mem_propOpens_iff _).mpr <| (isTateAffinoid_iff _).mpr ⟨A, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA, S, P, hP,
      ⟨eV⟩⟩, hy⟩

/-- **The source of a finite étale morphism is analytic**: the preimages of the neighbourhoods
supplied by the definition are open Tate affinoid subspaces, a finite algebra over a Tate ring being
Tate. -/
theorem IsFiniteEtale.isAnalytic_source {f : X ⟶ Y} (hf : IsFiniteEtale f) : X.IsAnalytic :=
  isAnalytic_iff.mpr fun x ↦ by
    obtain ⟨V, hy, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP', φ, ⟨_, -⟩,
      _, _, eU, _⟩ := (targetLocally_iff f).mp ((isFiniteEtale_iff f).mp hf) (f.hom.base x)
    have : IsTateRing B := IsTateRing.of_continuous (φ := φ.toRingHom) φ.continuous_toRingHom
    exact ⟨(Opens.map f.hom.base).obj V, (mem_propOpens_iff _).mpr <| (isTateAffinoid_iff _).mpr
      ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, T, P', hP', ⟨eU⟩⟩, hy⟩

/-! ### Descent along open covers of the target -/

/-- **Being finite étale descends along open covers of the target**: if `Y` is covered by opens
`V i` over which the restrictions `f⁻¹(V i) → V i` of `f` are finite étale, then `f` is finite
étale. A neighbourhood supplied by a restriction is an open of `V i`, hence an open of `Y`, with the
same preimage in `X`. -/
theorem IsFiniteEtale.of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (V : ι → Opens Y.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, IsFiniteEtale
      (X := ⟨_, isAdic_restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding X.property⟩)
      (Y := ⟨_, isAdic_restrict (V i).isOpenEmbedding Y.property⟩)
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)))) :
    IsFiniteEtale f :=
  targetLocally_of_iSup_eq_top V hV hf

/-! ### Affinoid morphisms, identities and isomorphisms -/

/-- **Affinoid morphisms**: for a finite étale morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`
between complete Hausdorff pairs, with `A` a Tate ring and both adic spectra adic spaces, the
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is finite étale, witnessed over the whole of
`Spa(A, A⁺)`. -/
theorem isFiniteEtale_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsTateRing A] {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (P : PairOfDefinition A) (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : φ.IsFiniteEtale) :
    IsFiniteEtale (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) :=
  targetLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf hA φ ⟨inferInstance, hφ⟩

/-- **Being finite étale is invariant under isomorphisms** of the source and of the target. -/
instance IsFiniteEtale.respectsIso : MorphismProperty.RespectsIso @IsFiniteEtale.{u} :=
  targetLocally_respectsIso

/-- **The identity of an analytic adic space is finite étale**: every point has an open Tate
affinoid neighbourhood `Spa(A, A⁺)`, over which the identity is the morphism induced by the
identity of `(A, A⁺)`, a finite étale morphism of Huber pairs. Analyticity is necessary, since the
target of a finite étale morphism is analytic
(`TauCeti.AdicSpace.IsFiniteEtale.isAnalytic_target`). -/
theorem isFiniteEtale_id (hX : X.IsAnalytic) : IsFiniteEtale (𝟙 X) :=
  targetLocally_id fun y ↦ by
    obtain ⟨V, hV, hyV⟩ := isAnalytic_iff.mp hX y
    obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, eV⟩ :=
      (isTateAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
    exact ⟨V, hyV, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, S, P, hP, ⟨inferInstance, Pair.Hom.isFiniteEtale_id S⟩, eV⟩

/-- **Isomorphisms onto analytic adic spaces are finite étale.** -/
theorem isFiniteEtale_of_isIso (f : X ⟶ Y) [IsIso f] (hY : Y.IsAnalytic) : IsFiniteEtale f := by
  simpa using MorphismProperty.RespectsIso.precomp @IsFiniteEtale.{u} f (𝟙 Y)
    (isFiniteEtale_id hY)

end AdicSpace

end TauCeti
