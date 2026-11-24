/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.TargetLocally
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.WeaklyFiniteType
public import TauCeti.RingTheory.Huber.Pair.Finite.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete.Basic

/-!
# Finite morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *finite* (Huber 1996, (1.4.4)) if every point of `Y` has
an open neighbourhood `V` such that `V ≅ Spa(A, A⁺)` and `f⁻¹(V) ≅ Spa(B, B⁺)` for complete
Hausdorff Huber pairs, under which `f` restricted to `f⁻¹(V) → V` is the morphism induced by a
finite morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` (`TauCeti.Huber.Pair.Hom.IsFinite`):
`φ` is topologically of finite type and the ring maps `A → B` and `A⁺ → B⁺` are integral.

Unlike the chart-local finiteness conditions (`TauCeti.PreAdicSpace.chartLocally`), which are
local on the source, finiteness is local on the target: the whole preimage of `V` is required to be
affinoid, and finiteness descends along open covers of the target. That the preimage of every open
affinoid of `Y` is then affinoid and finite over it needs hypotheses on `Y`: Huber's standing class
(1.1.1) (`TauCeti.Huber.IsHuberStandard`), or strongly noetherian complete Tate affinoids
(Zavyalov, Theorem B.2.18). This is why, on general adic spaces, `IsFinite` is defined locally on
the target.

Over each such `V` a finite morphism is in particular the morphism induced by a morphism of Huber
pairs topologically of finite type, so finite morphisms are locally of finite type. The preimage of
a quasi-compact open subset of `V` is quasi-compact, since a morphism of Huber pairs topologically
of finite type is adic and rational subsets pull back to rational subsets; hence finite morphisms
are quasi-compact, and so of weakly finite type. The identity of every adic space is finite, as
every point has an open affinoid neighbourhood with a complete model, and finiteness is invariant
under isomorphisms of the source and of the target; so isomorphisms are finite
(`CategoryTheory.MorphismProperty.of_isIso`).

## Main definitions

* `TauCeti.AdicSpace.IsFinite`: finite morphisms of adic spaces.

## Main results

* `TauCeti.AdicSpace.isFinite_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a finite morphism of complete Hausdorff Huber pairs is
  finite.
* `TauCeti.AdicSpace.IsFinite.chartLocally`: a finite morphism is chart-locally induced by finite
  morphisms of Huber pairs.
* `TauCeti.AdicSpace.IsFinite.locallyOfFiniteType`: finite morphisms are locally of finite type.
* `TauCeti.AdicSpace.IsFinite.quasiCompact`: finite morphisms are quasi-compact.
* `TauCeti.AdicSpace.IsFinite.isWeaklyFiniteType`: finite morphisms are of weakly finite type.
* `TauCeti.AdicSpace.IsFinite.of_iSup_eq_top`: finiteness descends along open covers of the
  target.
* `TauCeti.AdicSpace.IsFinite.containsIdentities`, `TauCeti.AdicSpace.IsFinite.respectsIso`:
  identities are finite, and finiteness is invariant under isomorphisms of the source and of the
  target.

## Implementation notes

`IsFinite` is the target-local property `TauCeti.AdicSpace.targetLocally` attached to finite
morphisms of Huber pairs, so its descent along open covers (`IsFinite.of_iSup_eq_top`), the affinoid
case, the isomorphism invariance and the finiteness of identities are specializations of the
general results for `targetLocally` (`Morphisms/TargetLocally.lean`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.4, (1.4.2) and (1.4.4).
* B. Zavyalov, *Quotients of admissible formal schemes and adic spaces by finite groups*,
  Appendix B.2, Definition B.2.12 and Theorem B.2.18.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Finite morphisms** (Huber 1996, (1.4.4)): a morphism `f : X ⟶ Y` of adic spaces is *finite*
when every point `y` of `Y` has an open neighbourhood `V` together with complete Hausdorff Huber
pairs `(A, A⁺)` and `(B, B⁺)`, `Spa(B, B⁺)` having a sheaf as structure presheaf, a finite
morphism `φ : (A, A⁺) → (B, B⁺)` of Huber pairs, and isomorphisms identifying `Y` restricted to
`V` with `Spa(A, A⁺)` and `X` restricted to `f⁻¹(V)` with `Spa(B, B⁺)`, under which `f` becomes the
morphism induced by `φ`. -/
def IsFinite {X Y : AdicSpace.{u}} (f : X ⟶ Y) : Prop :=
  targetLocally (fun φ ↦ φ.IsFinite) f

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsFinite`: finiteness is the target-local property
attached to finite morphisms of Huber pairs. -/
theorem isFinite_iff (f : X ⟶ Y) : IsFinite f ↔ targetLocally (fun φ ↦ φ.IsFinite) f :=
  Iff.rfl

/-! ### Finite morphisms are of weakly finite type -/

/-- **A finite morphism is chart-locally finite**: every point `x` of the source lies in the
preimage `f⁻¹(V)` of a neighbourhood `V` of `f x` supplied by the definition, and these form a
chart of `f` at `x`. -/
theorem IsFinite.chartLocally {f : X ⟶ Y} (hf : IsFinite f) :
    PreAdicSpace.chartLocally (fun φ ↦ φ.IsFinite) f.hom := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨V, hV, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ :=
    (targetLocally_iff f).mp ((isFinite_iff f).mp hf) (f.hom.base x)
  exact ⟨(Opens.map f.hom.base).obj V, hV, V, le_rfl, A, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eU, eV,
    hfac⟩

/-- **Finite morphisms are locally of finite type**: a finite morphism of Huber pairs is
topologically of finite type. -/
theorem IsFinite.locallyOfFiniteType {f : X ⟶ Y} (hf : IsFinite f) :
    LocallyOfFiniteType f :=
  (locallyOfFiniteType_iff_chartLocally f).mpr <|
    chartLocally_mono (fun _ hφ ↦ hφ.isTopologicallyFiniteType) hf.chartLocally

/-- Over each neighbourhood `V` supplied by the definition, the preimage under a finite morphism
of a quasi-compact open subset of `V` is quasi-compact: over `V` the morphism is, up to
isomorphisms, the morphism induced by a finite morphism of Huber pairs, whose map of adic spectra
is spectral. -/
private theorem IsFinite.exists_isCompact_preimage {f : X ⟶ Y} (hf : IsFinite f) (y : Y.obj) :
    ∃ V : Opens Y.obj, y ∈ V ∧ ∀ W : Opens Y.obj, W ≤ V → IsCompact (W : Set Y.obj) →
      IsCompact (f.hom.base ⁻¹' W) := by
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ :=
    (targetLocally_iff f).mp ((isFinite_iff f).mp hf) y
  refine ⟨V, hy, fun W hWV hW ↦ ?_⟩
  -- the morphism induced by `φ` has spectral underlying map, `φ` being adic
  have hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ObjectProperty.prop_of_iso PreAdicSpace.isAdic eV (isAdic_restrict _ Y.property)
  have hc := (quasiCompact_iff_isSpectralMap _).mp
    (quasiCompact_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf hA φ fun _ hJ ↦
      hφ.isTopologicallyFiniteType.isTopologicallyFiniteType_toRingHom.isAdicHom.isOpen_map hJ)
  rw [ObjectProperty.homMk_hom] at hc
  -- the defining square, on underlying spaces
  have hfac' := congrArg (fun g ↦ ConcreteCategory.hom (forgetToTop.map g)) hfac
  simp only [Functor.map_comp, TopCat.hom_comp] at hfac'
  -- over `V`, `f` is a spectral map up to the homeomorphisms `eU` and `eV`
  have hg := (TopCat.homeoOfIso (forgetToTop.mapIso eV.symm)).isProperMap.isSpectralMap.comp
    (hc.comp (TopCat.homeoOfIso (forgetToTop.mapIso eU)).isProperMap.isSpectralMap)
  -- `W` is a quasi-compact open subset of `V`, and `f⁻¹(W) ⊆ f⁻¹(V)` is the image of its
  -- preimage in `f⁻¹(V)`, which is the preimage under the spectral map above
  have hWc : IsCompact (V.inclusion' ⁻¹' (W : Set Y.obj)) :=
    (V.isOpenEmbedding.isInducing.isCompact_preimage_iff
      (by rw [Opens.set_range_inclusion']; exact hWV)).mpr hW
  have hpre : ((Opens.map f.hom.base).obj V).inclusion' ⁻¹' (f.hom.base ⁻¹' W) =
      (⇑(TopCat.homeoOfIso (forgetToTop.mapIso eV.symm)) ∘
        ⇑(presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf).base ∘
        ⇑(TopCat.homeoOfIso (forgetToTop.mapIso eU))) ⁻¹' (V.inclusion' ⁻¹' W) := by
    ext x
    exact iff_of_eq (congrArg (· ∈ (W : Set Y.obj)) (congrArg (fun g ↦ g x) hfac'))
  rw [← Set.image_preimage_eq_of_subset (f := ((Opens.map f.hom.base).obj V).inclusion')
    (s := f.hom.base ⁻¹' W) (by rw [Opens.set_range_inclusion']; exact fun x hx ↦ hWV hx), hpre]
  exact (hg.isCompact_preimage_of_isOpen (W.isOpen.preimage V.inclusion'.hom.continuous)
    hWc).image ((Opens.map f.hom.base).obj V).inclusion'.hom.continuous

/-- **Finite morphisms are quasi-compact**: the quasi-compact opens lying in a neighbourhood
supplied by the definition form a basis of the target, and their preimages are quasi-compact. -/
theorem IsFinite.quasiCompact {f : X ⟶ Y} (hf : IsFinite f) : QuasiCompact f := by
  choose V hV hpre using hf.exists_isCompact_preimage
  refine (quasiCompact_iff_isSpectralMap f).mpr <| isSpectralMap_of_isTopologicalBasis
    (B := {W | ∃ (W' : Opens Y.obj) (y : Y.obj), (W' : Set Y.obj) = W ∧ W' ≤ V y ∧ IsCompact W})
    (isTopologicalBasis_of_isOpen_of_nhds ?_ fun y u hy hu ↦ ?_) f.hom.base.hom.continuous ?_
  · rintro _ ⟨W, -, rfl, -⟩
    exact W.isOpen
  · obtain ⟨W, hWa, hyW, hWu⟩ := Opens.isBasis_iff_nbhd.mp
      (isBasis_affinoidOpens Y.property.isLocallyAffinoid) (U := ⟨u, hu⟩ ⊓ V y) ⟨hy, hV y⟩
    exact ⟨W, ⟨W, y, rfl, hWu.trans inf_le_right, isCompact_of_mem_affinoidOpens hWa⟩, hyW,
      hWu.trans inf_le_left⟩
  · rintro _ ⟨W, y, rfl, hWV, hW⟩
    exact hpre y W hWV hW

/-- **Finite morphisms are of weakly finite type**: they are locally of finite type and
quasi-compact. -/
theorem IsFinite.isWeaklyFiniteType {f : X ⟶ Y} (hf : IsFinite f) : IsWeaklyFiniteType f :=
  (isWeaklyFiniteType_iff f).mpr
    ⟨hf.locallyOfFiniteType.locallyOfWeaklyFiniteType, hf.quasiCompact⟩

/-! ### Descent along open covers of the target -/

/-- **Finiteness descends along open covers of the target**: if `Y` is covered by opens `V i`
over which the restrictions `f⁻¹(V i) → V i` of `f` are finite, then `f` is finite. A
neighbourhood supplied by a restriction is an open of `V i`, hence an open of `Y`, with the same
preimage in `X`. -/
theorem IsFinite.of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (V : ι → Opens Y.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, IsFinite
      (X := ⟨_, isAdic_restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding X.property⟩)
      (Y := ⟨_, isAdic_restrict (V i).isOpenEmbedding Y.property⟩)
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)))) :
    IsFinite f :=
  targetLocally_of_iSup_eq_top V hV hf

/-! ### Affinoid morphisms, identities and isomorphisms -/

/-- **Affinoid morphisms**: for a finite morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` between
complete Hausdorff pairs whose adic spectra are adic spaces, the morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)`
induced by `φ` is finite, witnessed over the whole of `Spa(A, A⁺)`. -/
theorem isFinite_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (P : PairOfDefinition A) (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : φ.IsFinite) :
    IsFinite (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) :=
  targetLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf hA φ hφ

/-- **Being finite is invariant under isomorphisms** of the source and of the target. -/
instance IsFinite.respectsIso : MorphismProperty.RespectsIso @IsFinite.{u} :=
  targetLocally_respectsIso

/-- **Identities are finite**: every point of an adic space has an open affinoid neighbourhood
with a complete model `Spa(A, A⁺)`, over which the identity is the morphism induced by the identity
of `(A, A⁺)`, a finite morphism of Huber pairs. So isomorphisms are finite
(`CategoryTheory.MorphismProperty.of_isIso`). -/
instance IsFinite.containsIdentities : MorphismProperty.ContainsIdentities @IsFinite.{u} where
  id_mem X := targetLocally_id fun y ↦ by
    obtain ⟨V, hV, hyV⟩ := X.property.isLocallyAffinoid y
    obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, eV⟩ :=
      (isAffinoid_iff_exists_complete _).mp ((mem_propOpens_iff _).mp hV)
    exact ⟨V, hyV, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, S, P, hP, Pair.Hom.isFinite_id S, eV⟩

end AdicSpace

end TauCeti
