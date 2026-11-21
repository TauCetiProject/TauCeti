/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NoetherianSpace
public import TauCeti.AlgebraicGeometry.FiniteEtale.FullyFaithful
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Properties
import TauCeti.AlgebraicGeometry.FiniteEtale.Spreading
import TauCeti.Topology.Sober

/-!
# Extending finite étale covers across points where purity holds

Let `X` be a scheme with Noetherian underlying topological space and `U ⊆ X` an open subscheme.
If purity holds for the local ring `𝒪_{X, x}` at every point `x ∉ U`, then every finite étale
cover of `U` extends to a finite étale cover of `X` (Stacks, Lemma 58.21.6, Tag 0EY7).

The proof takes a maximal open subscheme `U₀ ⊇ U` to which a given finite étale cover `Y` over `U`
extends. If `U₀ ≠ ⊤`, let `x` be the generic point of an irreducible component of `X \ U₀`. Then
every strict generalization of `x` lies in `U₀`, so the preimage of `U₀` in `Spec 𝒪_{X, x}` is
the punctured spectrum of `𝒪_{X, x}`
(`AlgebraicGeometry.Scheme.preimage_fromSpecStalk_eq_puncturedSpectrum`).
Purity at `x` extends the pullback of the cover across the closed point of `Spec 𝒪_{X, x}`, and
spreading out (`TauCeti.FiniteEtaleScheme.exists_spread_of_iso_fromSpecStalk`) yields an extension
to a strictly larger open subscheme `U₀ ⊔ W`, contradicting maximality of `U₀`.

Combining this essential surjectivity with full faithfulness for complements of depth at least two
(`TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepthStalk`) shows that restriction of
finite étale covers to `U` is an equivalence of categories when `X` is locally Noetherian with
Noetherian underlying topological space and every point outside `U` has depth at least two and
satisfies purity.

## Main results

* `AlgebraicGeometry.Scheme.preimage_fromSpecStalk_eq_puncturedSpectrum`: if `x ∉ U` and every
  strict generalization of `x` lies in `U`, then `X.fromSpecStalk x ⁻¹ᵁ U` is the punctured
  spectrum of `𝒪_{X, x}`.
* `TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds`: over a Noetherian topological
  space, local purity outside an open `U` implies that restriction of finite étale covers to `U` is
  essentially surjective (Stacks, Lemma 58.21.6, Tag 0EY7).
* `TauCeti.FiniteEtaleScheme.isEquivalence_pullback_ι_of_purityHolds`: over a locally Noetherian
  scheme with Noetherian underlying topological space, depth at least two and local purity outside
  an open `U` imply that restriction of finite étale covers to `U` is an equivalence of categories.

## References

* [The Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7)
-/

public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- If `x ∉ U` and every strict generalization of `x` lies in `U`, then the preimage of `U` under
`X.fromSpecStalk x : Spec 𝒪_{X, x} ⟶ X` is the punctured spectrum of `𝒪_{X, x}`. -/
theorem preimage_fromSpecStalk_eq_puncturedSpectrum {X : Scheme.{u}} (U : X.Opens) {x : X}
    (hx : x ∉ U) (hgen : ∀ y : X, y ⤳ x → y ≠ x → y ∈ U) :
    X.fromSpecStalk x ⁻¹ᵁ U = TauCeti.IsLocalRing.puncturedSpectrum (X.presheaf.stalk x) := by
  ext p
  refine Iff.trans ?_
    (TauCeti.IsLocalRing.mem_puncturedSpectrum_iff (X.presheaf.stalk x) p).symm
  change X.fromSpecStalk x p ∈ U ↔ p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)
  constructor
  · intro hp heq
    rw [heq, Scheme.fromSpecStalk_closedPoint] at hp
    exact hx hp
  · intro hp
    have hspec : X.fromSpecStalk x p ⤳ x := by
      have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    refine hgen (X.fromSpecStalk x p) hspec fun heq ↦ hp ?_
    exact (X.fromSpecStalk x).isEmbedding.injective
      (heq.trans Scheme.fromSpecStalk_closedPoint.symm)

end AlgebraicGeometry.Scheme

namespace TauCeti.FiniteEtaleScheme

/-- **Extension of finite étale covers across points where purity holds.** Let `X` be a scheme
whose underlying topological space is Noetherian and `U ⊆ X` an open subscheme. If purity holds
for the local ring `𝒪_{X, x}` at every point `x ∉ U`, then every finite étale cover of `U` extends
to a finite étale cover of `X`. -/
@[stacks 0EY7]
theorem essSurj_pullback_ι_of_purityHolds {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (h : ∀ x : X, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x)) :
    (pullback U.ι).EssSurj := by
  constructor
  intro Y
  let S : Set X.Opens :=
    { V | ∃ hUV : U ≤ V, ∃ YV : FiniteEtaleScheme V.toScheme,
      Nonempty ((pullback (X.homOfLE hUV)).obj YV ≅ Y) }
  have hUS : U ∈ S := by
    refine ⟨le_rfl, Y, ⟨?_⟩⟩
    exact eqToIso (congrArg (fun g ↦ (pullback g).obj Y) (X.homOfLE_rfl U)) ≪≫
      pullbackId.app Y
  obtain ⟨U₀, ⟨hUU₀, YU₀, ⟨eU₀⟩⟩, hmax⟩ := wellFounded_gt.has_min S ⟨U, hUS⟩
  have hU₀_top : U₀ = ⊤ := by
    by_contra hne
    let Z : Set X := (U₀ : Set X)ᶜ
    have hZ_closed : IsClosed Z := U₀.isOpen.isClosed_compl
    have hZ_ne : Z.Nonempty := by
      by_contra hempty
      apply hne
      ext z
      simp only [Opens.coe_top, Set.mem_univ, iff_true]
      by_contra hz
      exact hempty ⟨z, hz⟩
    obtain ⟨z, hz⟩ := hZ_ne
    obtain ⟨⟨x, hxU₀⟩, hx_gen, -⟩ := hZ_closed.exists_genericPoint_specializes hz
    have : QuasiSober Z := hZ_closed.isClosedEmbedding_subtypeVal.quasiSober
    have hgen : ∀ y : X, y ⤳ x → y ≠ x → y ∈ U₀ := by
      intro y hyx hyne
      by_contra hyU₀
      have hspec : (⟨y, hyU₀⟩ : Z) ⤳ ⟨x, hxU₀⟩ :=
        Topology.IsInducing.subtypeVal.specializes_iff.mp hyx
      exact hyne (congrArg Subtype.val ((TauCeti.mem_genericPoints_iff.mp hx_gen) _ hspec))
    have heq : X.fromSpecStalk x ⁻¹ᵁ U₀ =
        IsLocalRing.puncturedSpectrum (X.presheaf.stalk x) :=
      X.preimage_fromSpecStalk_eq_puncturedSpectrum U₀ hxU₀ hgen
    let j := (Spec (X.presheaf.stalk x)).isoOfEq heq
    let Yp : FiniteEtaleScheme (IsLocalRing.puncturedSpectrum (X.presheaf.stalk x)).toScheme :=
      (pullback j.inv).obj ((pullback (X.fromSpecStalk x ∣_ U₀)).obj YU₀)
    obtain ⟨Yx, ⟨ex⟩⟩ :=
      (IsLocalRing.purityHolds_iff _).mp (h x fun hxU ↦ hxU₀ (hUU₀ hxU)) Yp
    let e : (pullback (X.fromSpecStalk x ∣_ U₀)).obj YU₀ ≅
        (pullback (X.fromSpecStalk x ⁻¹ᵁ U₀).ι).obj Yx :=
      (pullbackId.app _).symm ≪≫
        eqToIso (congrArg (fun g ↦ (pullback g).obj _) j.hom_inv_id.symm) ≪≫
        (pullbackComp j.hom j.inv).app _ ≪≫
        (pullback j.hom).mapIso ex.symm ≪≫
        (pullbackComp j.hom (IsLocalRing.puncturedSpectrum _).ι).symm.app Yx ≪≫
        eqToIso (congrArg (fun g ↦ (pullback g).obj Yx) (Scheme.isoOfEq_hom_ι _ heq))
    have : NoetherianSpace U₀.toScheme := U₀.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact U₀.ι := ⟨fun V _ _ ↦ NoetherianSpace.isCompact (U₀.ι ⁻¹' V)⟩
    obtain ⟨W, _, hxW, Y', ⟨e'⟩, -⟩ := exists_spread_of_iso_fromSpecStalk U₀ x YU₀ Yx e
    have hmem : U₀ ⊔ W ∈ S := by
      refine ⟨hUU₀.trans le_sup_left, Y', ⟨?_⟩⟩
      refine eqToIso (congrArg (fun g ↦ (pullback g).obj Y')
          (X.homOfLE_homOfLE hUU₀ le_sup_left).symm) ≪≫
        (pullbackComp (X.homOfLE hUU₀) (X.homOfLE le_sup_left)).app Y' ≪≫
        (pullback (X.homOfLE hUU₀)).mapIso e' ≪≫ eU₀
    have hlt : U₀ < U₀ ⊔ W :=
      lt_of_le_of_ne le_sup_left fun heq' ↦ hxU₀ (heq'.symm ▸ Opens.mem_sup.mpr (Or.inr hxW))
    exact hmax (U₀ ⊔ W) hmem hlt
  subst hU₀_top
  refine ⟨(pullback X.topIso.inv).obj YU₀, ⟨?_⟩⟩
  have hUι : U.ι ≫ X.topIso.inv = X.homOfLE hUU₀ := by
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      X.topIso_hom, Scheme.homOfLE_ι]
  exact (pullbackComp U.ι X.topIso.inv).symm.app YU₀ ≪≫
    eqToIso (congrArg (fun g ↦ (pullback g).obj YU₀) hUι) ≪≫ eU₀

/-- **Equivalence of finite étale covers across points of depth at least two where purity holds.**
Let `X` be a locally Noetherian scheme with Noetherian underlying topological space and `U ⊆ X` an
open subscheme. If at every point `x ∉ U` the local ring `𝒪_{X, x}` has depth at least two and
satisfies purity, then restriction of finite étale covers from `X` to `U` is an equivalence of
categories. -/
@[stacks 0EY7 "equivalence"]
theorem isEquivalence_pullback_ι_of_purityHolds {X : Scheme.{u}} [IsLocallyNoetherian X]
    [NoetherianSpace X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      2 ≤ _root_.IsLocalRing.depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))
    (hpurity : ∀ x : X, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x)) :
    (pullback U.ι).IsEquivalence :=
  have hff := fullyFaithfulPullbackιOfTwoLeDepthStalk U hdepth
  { faithful := hff.faithful
    full := hff.full
    essSurj := essSurj_pullback_ι_of_purityHolds U hpurity }

end TauCeti.FiniteEtaleScheme
