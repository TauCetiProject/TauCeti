/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pushout
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Base
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Pair

/-!
# Completed pushout of rational localisation Huber pairs

Let `A → B` and `A → C` be adic homomorphisms of Huber rings, `(A, A⁺)`, `(B, B⁺)` and
`(C, C⁺)` Huber pairs, and `(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` their completed tensor product.
Combining the fixed-base comparison `toRationalLocalization` / `ofRationalLocalization` (from
`Rational.Pair`) with base-localisation invariance `toBaseLocalization` / `ofBaseLocalization`
(from `Rational.Base`), this file proves that `(D⟨T''/(inl(s) · inr(s'))⟩, D_W⁺)` is a
`TauCeti.Huber.IsCompletedPushout` over any compatible rational localisation
`(A⟨T₀/s₀⟩, A_0⁺)`.

## Main results

* `TauCeti.Huber.Pair.completedTensor.isCompletedPushout_rationalLocalizationPair`: the localised
  completed tensor pair is a `TauCeti.Huber.IsCompletedPushout` over `(A⟨T₀/s₀⟩, A_0⁺)`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51,
  §7.5 and §8.1.
-/

public section

open UniformSpace
open scoped Pointwise

open TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withLoc " P:term:max T:term:max s:term:max S:term:max hden:term:max
    " in " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    $t)

open TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withLocHuber " P:term:max T:term:max s:term:max S:term:max hden:term:max
    " in " t:term : term =>
  `(withLoc $P $T $s $S $hden in
    letI := isHuberRing_completion_locTopology $P $T $s $S $hden
    $t)

open TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withRationalTensor " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    P':term:max T':term:max s':term:max S':term:max hden':term:max
    Q:term:max S'':term:max hden'':term:max " in " t:term : term =>
  `(withLoc $P $T $s $S $hden in withLoc $P' $T' $s' $S' $hden' in
    letI : Algebra $A (Completion $S) :=
      ((toCompletionLoc $P $T $s $S $hden).comp (algebraMap $A $B)).toAlgebra
    letI : Algebra $A (Completion $S') :=
      ((toCompletionLoc $P' $T' $s' $S' $hden').comp (algebraMap $A $C)).toAlgebra
    haveI : IsAdicHom (algebraMap $A (Completion $S)) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc $P $T $s $S $hden)
        (inferInstanceAs (IsAdicHom (algebraMap $A $B)))
    haveI : IsAdicHom (algebraMap $A (Completion $S')) :=
      IsAdicHom.comp (isAdicHom_toCompletionLoc $P' $T' $s' $S' $hden')
        (inferInstanceAs (IsAdicHom (algebraMap $A $C)))
    withLoc $Q _ _ $S'' $hden'' in
    $t)

open TauCeti.Huber TauCeti.Huber.PairOfDefinition in
local macro "withRationalTensorHuber " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    P':term:max T':term:max s':term:max S':term:max hden':term:max
    Q:term:max S'':term:max hden'':term:max " in " t:term : term =>
  `(withRationalTensor $A $B $C $P $T $s $S $hden $P' $T' $s' $S' $hden' $Q $S'' $hden'' in
    letI := isHuberRing_completion_locTopology $P $T $s $S $hden
    letI := isHuberRing_completion_locTopology $P' $T' $s' $S' $hden'
    letI := isHuberRing_completion_locTopology $Q _ _ $S'' $hden''
    $t)

namespace TauCeti.Huber.Pair.completedTensor

open CompletedTensor PairOfDefinition

section Pushout

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing A] [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]

/-- **The localised completed tensor pair is a completed pushout of the localised factor pairs.**
Given morphisms `f₀ : (A⟨T₀/s₀⟩, A_0⁺) → (B⟨T/s⟩, B_U⁺)` and
`g₀ : (A⟨T₀/s₀⟩, A_0⁺) → (C⟨T'/s'⟩, C_V⁺)` compatible with `A → B` and `A → C`, `(D⟨T''/s''⟩, D_W⁺)`
forms a `TauCeti.Huber.IsCompletedPushout` square with `f₀` and `g₀`. -/
theorem isCompletedPushout_rationalLocalizationPair
    (P₀ : PairOfDefinition A) (UA : Pair A) (hP₀ : P₀.ringOfDefinition ≤ UA.plus)
    (T₀ : Finset A) (s₀ : A) (S₀ : Type u) [CommRing S₀] [Algebra A S₀]
    [IsLocalization.Away s₀ S₀] (hden₀ : HasDenominatorPower P₀ T₀ s₀ S₀)
    (P : PairOfDefinition B) (UB : Pair B) (hP : P.ringOfDefinition ≤ UB.plus)
    (T : Finset B) (s : B) (S : Type u) [CommRing S] [Algebra B S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (P' : PairOfDefinition C) (UC : Pair C) (hP' : P'.ringOfDefinition ≤ UC.plus)
    (T' : Finset C) (s' : C) (S' : Type u) [CommRing S'] [Algebra C S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
    (Q : PairOfDefinition (CompletedTensor A B C))
    (hQ : Q.ringOfDefinition ≤ (UB.completedTensor A UC).plus) (S'' : Type u) [CommRing S'']
    [Algebra (CompletedTensor A B C) S'']
    [IsLocalization.Away (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'']
    (hden'' : HasDenominatorPower Q
      (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
        insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) : Finset _)
      (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'') :
    withLocHuber P₀ T₀ s₀ S₀ hden₀ in
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    ∀ (f₀ : Hom (rationalLocalizationPair P₀ UA hP₀ T₀ s₀ S₀ hden₀)
          (rationalLocalizationPair P UB hP T s S hden))
      (g₀ : Hom (rationalLocalizationPair P₀ UA hP₀ T₀ s₀ S₀ hden₀)
          (rationalLocalizationPair P' UC hP' T' s' S' hden'))
      (hf₀ : f₀.toRingHom.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) =
        (toCompletionLoc P T s S hden).comp (algebraMap A B))
      (hg₀ : g₀.toRingHom.comp (toCompletionLoc P₀ T₀ s₀ S₀ hden₀) =
        (toCompletionLoc P' T' s' S' hden').comp (algebraMap A C)),
      let _ : Algebra (Completion S₀) (Completion S) := f₀.toRingHom.toAlgebra
      let _ : Algebra (Completion S₀) (Completion S') := g₀.toRingHom.toAlgebra
      let _ : IsAdicHom (algebraMap (Completion S₀) (Completion S)) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ f₀.continuous_toRingHom
          (hf₀.symm ▸ IsAdicHom.comp (isAdicHom_toCompletionLoc P T s S hden)
            (inferInstanceAs (IsAdicHom (algebraMap A B))))
      let _ : IsAdicHom (algebraMap (Completion S₀) (Completion S')) :=
        isAdicHom_of_comp_toCompletionLoc P₀ T₀ s₀ S₀ hden₀ g₀.continuous_toRingHom
          (hg₀.symm ▸ IsAdicHom.comp (isAdicHom_toCompletionLoc P' T' s' S' hden')
            (inferInstanceAs (IsAdicHom (algebraMap A C))))
      let fwd := (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden''
          hP hP' hQ).comp
        (toBaseLocalization P₀ T₀ s₀ S₀ hden₀
          (rationalLocalizationPair P UB hP T s S hden)
          (rationalLocalizationPair P' UC hP' T' s' S' hden')
          f₀.toRingHom g₀.toRingHom f₀.continuous_toRingHom g₀.continuous_toRingHom hf₀ hg₀)
      IsCompletedPushout f₀ g₀
        (fwd.comp (inl (Completion S₀) _ _)) (fwd.comp (inr (Completion S₀) _ _)) :=
  withLocHuber P₀ T₀ s₀ S₀ hden₀ in
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    intro f₀ g₀ hf₀ hg₀ _ _ _ _ fwd
    let inv := (ofBaseLocalization P₀ T₀ s₀ S₀ hden₀
        (rationalLocalizationPair P UB hP T s S hden)
        (rationalLocalizationPair P' UC hP' T' s' S' hden')
        f₀.toRingHom g₀.toRingHom f₀.continuous_toRingHom g₀.continuous_toRingHom hf₀ hg₀).comp
      (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ)
    have hinv_fwd : inv.comp fwd = Hom.id _ := by
      dsimp only [fwd, inv]
      rw [Hom.comp_assoc, ← Hom.comp_assoc (ofRationalLocalization ..),
        ofRationalLocalization_comp_toRationalLocalization, Hom.id_comp,
        ofBaseLocalization_comp_toBaseLocalization]
    have hfwd_inv : fwd.comp inv = Hom.id _ := by
      dsimp only [fwd, inv]
      rw [Hom.comp_assoc, ← Hom.comp_assoc (toBaseLocalization ..),
        toBaseLocalization_comp_ofBaseLocalization, Hom.id_comp,
        toRationalLocalization_comp_ofRationalLocalization]
    have hpush := isCompletedPushout f₀ g₀ (RingHom.algebraMap_toAlgebra f₀.toRingHom)
      (RingHom.algebraMap_toAlgebra g₀.toRingHom)
    refine ⟨by rw [Hom.comp_assoc, hpush.condition, ← Hom.comp_assoc],
      fun D _ _ _ _ _ _ _ V a b hab ↦ ?_⟩
    obtain ⟨h₀, ⟨hh₀l, hh₀r⟩, hh₀uniq⟩ := hpush.existsUnique_desc D V a b hab
    refine ⟨h₀.comp inv,
      ⟨by rw [Hom.comp_assoc, ← Hom.comp_assoc inv fwd, hinv_fwd, Hom.id_comp, hh₀l],
        by rw [Hom.comp_assoc, ← Hom.comp_assoc inv fwd, hinv_fwd, Hom.id_comp, hh₀r]⟩,
      fun k ⟨hkl, hkr⟩ ↦ ?_⟩
    have hk : k.comp fwd = h₀ :=
      hh₀uniq (k.comp fwd) ⟨by rwa [Hom.comp_assoc], by rwa [Hom.comp_assoc]⟩
    calc k = k.comp (fwd.comp inv) := by rw [hfwd_inv, Hom.comp_id]
      _ = (k.comp fwd).comp inv := (Hom.comp_assoc k fwd inv).symm
      _ = h₀.comp inv := by rw [hk]

end Pushout

end TauCeti.Huber.Pair.completedTensor
