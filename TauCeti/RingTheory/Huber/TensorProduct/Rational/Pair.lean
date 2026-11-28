/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
public import TauCeti.RingTheory.Huber.TensorProduct.Pair
public import TauCeti.RingTheory.Huber.TensorProduct.Rational.Basic
import TauCeti.RingTheory.Subring.Basic

/-!
# Completed tensor products of rational localisation Huber pairs

Let `A → B` and `A → C` be adic homomorphisms of Huber rings, `(B, B⁺)` and `(C, C⁺)` Huber pairs,
`(D, D⁺) = (B, B⁺) ⊗̂_A (C, C⁺)` their completed tensor product, and `p_B`, `p_C` the maps on
`Spa` induced by `inl` and `inr`. For rational subsets `U = R(T/s) ⊆ Spa(B, B⁺)` and
`V = R(T'/s') ⊆ Spa(C, C⁺)`, write `W = p_B⁻¹(R(T/s)) ∩ p_C⁻¹(R(T'/s'))` and `D_W⁺` for the
rational-localisation plus ring of `D⟨T''/(inl(s) · inr(s'))⟩`
(`(rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus`).

This file upgrades the topological ring equivalence
`TauCeti.Huber.CompletedTensor.completionLocEquiv` (from `Rational.Basic`) between
`B⟨T/s⟩ ⊗̂_A C⟨T'/s'⟩` and `D⟨T''/(inl(s) · inr(s'))⟩` to Huber pairs without completeness,
Hausdorffness, Tate or sheafiness hypotheses: it identifies the
completed tensor plus ring with `D_W⁺` and constructs inverse Huber-pair morphisms
`toRationalLocalization` and `ofRationalLocalization`.

## Main definitions

* `TauCeti.Huber.Pair.completedTensor.toRationalLocalization`,
  `TauCeti.Huber.Pair.completedTensor.ofRationalLocalization`: mutually inverse morphisms of Huber
  pairs between `(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` and `(D⟨T''/s''⟩, D_W⁺)`.

## Main results

* `TauCeti.Huber.Pair.completedTensor.map_plus_completionLocEquiv`: `completionLocEquiv` carries
  the completed tensor plus ring onto
  `(rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus`, the plus ring
  `D_W⁺` of `D⟨T''/(inl(s) · inr(s'))⟩`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, after Definition 2.4.12.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51,
  §7.5 and §8.1.
-/

public section

open TensorProduct UniformSpace TauCeti.Localization
open scoped Pointwise

namespace TauCeti.Huber.Pair.completedTensor

open CompletedTensor PairOfDefinition

local macro "withLocHuber " P:term:max T:term:max s:term:max S:term:max hden:term:max
    " in " t:term : term =>
  `(letI := locUniformSpace $P $T $s $S $hden
    letI := isUniformAddGroup_locUniformSpace $P $T $s $S $hden
    letI := isTopologicalRing_locUniformSpace $P $T $s $S $hden
    letI := PairOfDefinition.isHuberRing_completion_locTopology $P $T $s $S $hden
    $t)

local macro "withRationalTensorHuber " A:term:max B:term:max C:term:max
    P:term:max T:term:max s:term:max S:term:max hden:term:max
    P':term:max T':term:max s':term:max S':term:max hden':term:max
    Q:term:max S'':term:max hden'':term:max " in " t:term : term =>
  `(withLocHuber $P $T $s $S $hden in withLocHuber $P' $T' $s' $S' $hden' in
    letI : Algebra $A (UniformSpace.Completion $S) :=
      ((PairOfDefinition.toCompletionLoc $P $T $s $S $hden).comp (algebraMap $A $B)).toAlgebra
    letI : Algebra $A (UniformSpace.Completion $S') :=
      ((PairOfDefinition.toCompletionLoc $P' $T' $s' $S' $hden').comp (algebraMap $A $C)).toAlgebra
    haveI : IsAdicHom (algebraMap $A (UniformSpace.Completion $S)) :=
      IsAdicHom.comp (PairOfDefinition.isAdicHom_toCompletionLoc $P $T $s $S $hden)
        (inferInstanceAs (IsAdicHom (algebraMap $A $B)))
    haveI : IsAdicHom (algebraMap $A (UniformSpace.Completion $S')) :=
      IsAdicHom.comp (PairOfDefinition.isAdicHom_toCompletionLoc $P' $T' $s' $S' $hden')
        (inferInstanceAs (IsAdicHom (algebraMap $A $C)))
    withLocHuber $Q _ _ $S'' $hden'' in
    $t)

section FixedBase

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsHuberRing B] [IsHuberRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)] [DecidableEq (CompletedTensor A B C)]
  (P : PairOfDefinition B) (UB : Pair B) (T : Finset B) (s : B) (S : Type*) [CommRing S]
  [Algebra B S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition C) (UC : Pair C) (T' : Finset C) (s' : C) (S' : Type*) [CommRing S']
  [Algebra C S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (Q : PairOfDefinition (CompletedTensor A B C)) (S'' : Type*) [CommRing S'']
  [Algebra (CompletedTensor A B C) S'']
  [IsLocalization.Away (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'']
  (hden'' : HasDenominatorPower Q
    (insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)) : Finset _)
    (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') S'')

section RationalLocalizationPair

variable (hP : P.ringOfDefinition ≤ UB.plus) (hP' : P'.ringOfDefinition ≤ UC.plus)
  (hQ : Q.ringOfDefinition ≤ (UB.completedTensor A UC).plus)

private theorem factor_rationalLocalizationPair_plus_le_comap
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
    (PR : PairOfDefinition R) (UR : Pair R) (hPR : PR.ringOfDefinition ≤ UR.plus)
    (TR : Finset R) (sR : R) (SR : Type*) [CommRing SR] [Algebra R SR]
    [IsLocalization.Away sR SR] (hdenR : HasDenominatorPower PR TR sR SR) :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    letI := locUniformSpace PR TR sR SR hdenR
    letI := isUniformAddGroup_locUniformSpace PR TR sR SR hdenR
    letI := isTopologicalRing_locUniformSpace PR TR sR SR hdenR
    letI := isHuberRing_completion_locTopology PR TR sR SR hdenR
    ∀ (ι : Completion SR →+* CompletedTensor A (Completion S) (Completion S')),
      Continuous ι → ∀ (ι₀ : R →+* CompletedTensor A B C),
        (∀ r ∈ UR.plus, ι₀ r ∈ (UB.completedTensor A UC).plus) →
        (∀ r,
          completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
              (ι (toCompletionLoc PR TR sR SR hdenR r)) =
            toCompletionLoc Q _ _ S'' hden'' (ι₀ r)) →
        (∀ t ∈ TR, ∃ x ∈
          insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
            insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C)),
          completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
              (ι ((divBy t sR : SR) : Completion SR)) =
            ((divBy x (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') : S'') :
              Completion S'')) →
        (rationalLocalizationPair PR UR hPR TR sR SR hdenR).plus ≤
          (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus.comap
            ((completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom.comp ι) :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    let _ := locUniformSpace PR TR sR SR hdenR
    have _ := isUniformAddGroup_locUniformSpace PR TR sR SR hdenR
    have _ := isTopologicalRing_locUniformSpace PR TR sR SR hdenR
    have _ := isHuberRing_completion_locTopology PR TR sR SR hdenR
    intro ι hι ι₀ hι₀_plus hloc hdiv
    let O_W := rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden''
    have _ := O_W.isRingOfIntegralElements.isIntegrallyClosedIn
    have hcl : IsClosed (O_W.plus : Set (Completion S'')) :=
      O_W.plus.toAddSubgroup.isClosed_of_isOpen O_W.isRingOfIntegralElements.isOpen
    rw [rationalLocalizationPair_plus]
    refine completedPlusSubring_le_comap PR UR.plus TR sR SR hdenR hcl
      ((continuous_completionLocEquiv ..).comp hι) (fun r hr ↦ ?_) (fun t ht ↦ ?_)
    · rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hloc r,
        rationalLocalizationPair_plus]
      exact toCompletionLoc_mem_completedPlusSubring Q _ _ _ S'' hden'' (hι₀_plus r hr)
    · obtain ⟨x, hx, hxeq⟩ := hdiv t ht
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hxeq,
        rationalLocalizationPair_plus]
      exact divBy_mem_completedPlusSubring Q _ _ _ S'' hden'' hx

private theorem completionLocEquiv_plus_le :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus ≤
      (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus.comap
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    let e := completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
    let O_W := rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden''
    have _ := O_W.isRingOfIntegralElements.isIntegrallyClosedIn
    have hcl : IsClosed (O_W.plus : Set (Completion S'')) :=
      O_W.plus.toAddSubgroup.isClosed_of_isOpen O_W.isRingOfIntegralElements.isOpen
    refine (rationalLocalizationPair P UB hP T s S hden).completedTensor_plus_le_comap
      (rationalLocalizationPair P' UC hP' T' s' S' hden')
      hcl (f := e.toRingHom) (continuous_completionLocEquiv ..) ?_ ?_
    · exact factor_rationalLocalizationPair_plus_le_comap P UB T s S hden P' UC T' s' S' hden'
        Q S'' hden'' hQ P UB hP T s S hden
        (CompletedTensor.inl A (Completion S) (Completion S')) (CompletedTensor.continuous_inl ..)
        (CompletedTensor.inl A B C) (fun _ hb ↦ UB.inl_mem_completedTensor_plus UC hb)
        (fun b ↦ by simp only [toCompletionLoc_apply, completionLocEquiv_inl_toCompletionLoc])
        fun t ht ↦ ⟨_, Finset.mul_mem_mul (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht))
          (Finset.mem_insert_self _ _), by simp only [completionLocEquiv_inl_divBy]⟩
    · exact factor_rationalLocalizationPair_plus_le_comap P UB T s S hden P' UC T' s' S' hden'
        Q S'' hden'' hQ P' UC hP' T' s' S' hden'
        (CompletedTensor.inr A (Completion S) (Completion S')) (CompletedTensor.continuous_inr ..)
        (CompletedTensor.inr A B C) (fun _ hc ↦ UB.inr_mem_completedTensor_plus UC hc)
        (fun c ↦ by simp only [toCompletionLoc_apply, completionLocEquiv_inr_toCompletionLoc])
        fun t' ht' ↦ ⟨_, Finset.mul_mem_mul (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht')),
          by simp only [completionLocEquiv_inr_divBy]⟩

omit [IsHuberRing B] [IsHuberRing C] in
private theorem exists_mul_toCompletionLoc_of_mem_insert
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
    (PR : PairOfDefinition R) (UR : Pair R) (hPR : PR.ringOfDefinition ≤ UR.plus)
    (TR : Finset R) (sR : R) (SR : Type*) [CommRing SR] [Algebra R SR]
    [IsLocalization.Away sR SR] (hdenR : HasDenominatorPower PR TR sR SR)
    (ι₀ : R →+* CompletedTensor A B C) :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    letI := locUniformSpace PR TR sR SR hdenR
    letI := isUniformAddGroup_locUniformSpace PR TR sR SR hdenR
    letI := isTopologicalRing_locUniformSpace PR TR sR SR hdenR
    letI := isHuberRing_completion_locTopology PR TR sR SR hdenR
    ∀ (ι : Completion SR →+* CompletedTensor A (Completion S) (Completion S')),
      (∀ r,
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
            (toCompletionLoc Q _ _ S'' hden'' (ι₀ r)) =
          ι (toCompletionLoc PR TR sR SR hdenR r)) →
      ∀ {x : CompletedTensor A B C}, x ∈ insert (ι₀ sR) (TR.image ι₀) →
        ∃ y ∈ (rationalLocalizationPair PR UR hPR TR sR SR hdenR).plus,
          (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
              (toCompletionLoc Q _ _ S'' hden'' x) =
            ι y * (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
              (toCompletionLoc Q _ _ S'' hden'' (ι₀ sR)) :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    let _ := locUniformSpace PR TR sR SR hdenR
    have _ := isUniformAddGroup_locUniformSpace PR TR sR SR hdenR
    have _ := isTopologicalRing_locUniformSpace PR TR sR SR hdenR
    have _ := isHuberRing_completion_locTopology PR TR sR SR hdenR
    intro ι hι_symm x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨1, (rationalLocalizationPair PR UR hPR TR sR SR hdenR).plus.one_mem, by simp⟩
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨((divBy t sR : SR) : Completion SR), ?_, ?_⟩
    · rw [rationalLocalizationPair_plus]
      exact divBy_mem_completedPlusSubring PR UR.plus TR sR SR hdenR ht
    · rw [hι_symm, hι_symm, map_divBy_mul_toCompletionLoc PR TR sR SR hdenR t ι]

private theorem completionLocEquiv_symm_divBy_mem {x : CompletedTensor A B C}
    (hx : x ∈ insert (CompletedTensor.inl A B C s) (T.image (CompletedTensor.inl A B C)) *
      insert (CompletedTensor.inr A B C s') (T'.image (CompletedTensor.inr A B C))) :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
        ((divBy x (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') : S'') :
          Completion S'') ∈
      ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    let O_U := rationalLocalizationPair P UB hP T s S hden
    let O_V := rationalLocalizationPair P' UC hP' T' s' S' hden'
    set e := completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hx
    obtain ⟨y, hy, hay⟩ := exists_mul_toCompletionLoc_of_mem_insert
      P T s S hden P' T' s' S' hden' Q S'' hden'' P UB hP T s S hden
      (CompletedTensor.inl A B C) (CompletedTensor.inl A (Completion S) (Completion S'))
      (fun r ↦ by simp only [toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inl]) ha
    obtain ⟨z, hz, hbz⟩ := exists_mul_toCompletionLoc_of_mem_insert
      P T s S hden P' T' s' S' hden' Q S'' hden'' P' UC hP' T' s' S' hden'
      (CompletedTensor.inr A B C) (CompletedTensor.inr A (Completion S) (Completion S'))
      (fun r ↦ by simp only [toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inr]) hb
    have heq : e.symm ((divBy (a * b)
        (CompletedTensor.inl A B C s * CompletedTensor.inr A B C s') : S'') : Completion S'') =
        CompletedTensor.inl A (Completion S) (Completion S') y *
          CompletedTensor.inr A (Completion S) (Completion S') z := by
      rw [map_divBy_eq_iff Q _ _ S'' hden'' (a * b) e.symm, map_mul, map_mul, map_mul, map_mul,
        hay, hbz]
      ring
    rw [heq]
    exact mul_mem (O_U.inl_mem_completedTensor_plus (A := A) O_V hy)
      (O_U.inr_mem_completedTensor_plus (A := A) O_V hz)

private theorem factor_symm_toCompletionLoc_mem_plus
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]
    (PR : PairOfDefinition R) (UR : Pair R) (hPR : PR.ringOfDefinition ≤ UR.plus)
    (TR : Finset R) (sR : R) (SR : Type*) [CommRing SR] [Algebra R SR]
    [IsLocalization.Away sR SR] (hdenR : HasDenominatorPower PR TR sR SR)
    (ι₀ : R →+* CompletedTensor A B C) :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    letI := locUniformSpace PR TR sR SR hdenR
    letI := isUniformAddGroup_locUniformSpace PR TR sR SR hdenR
    letI := isTopologicalRing_locUniformSpace PR TR sR SR hdenR
    letI := isHuberRing_completion_locTopology PR TR sR SR hdenR
    ∀ (ι : Completion SR →+* CompletedTensor A (Completion S) (Completion S')),
      (∀ r,
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm
            (toCompletionLoc Q _ _ S'' hden'' (ι₀ r)) =
          ι (toCompletionLoc PR TR sR SR hdenR r)) →
      (∀ y ∈ (rationalLocalizationPair PR UR hPR TR sR SR hdenR).plus,
        ι y ∈ ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
          (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus) →
      ∀ {r : R}, r ∈ UR.plus →
        ((completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom.comp
          (toCompletionLoc Q _ _ S'' hden'')) (ι₀ r) ∈
          ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
            (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    let _ := locUniformSpace PR TR sR SR hdenR
    have _ := isUniformAddGroup_locUniformSpace PR TR sR SR hdenR
    have _ := isTopologicalRing_locUniformSpace PR TR sR SR hdenR
    have _ := isHuberRing_completion_locTopology PR TR sR SR hdenR
    intro ι hι_symm hι_plus r hr
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hι_symm]
    exact hι_plus _ (by
      rw [rationalLocalizationPair_plus]
      exact toCompletionLoc_mem_completedPlusSubring PR UR.plus TR sR SR hdenR hr)

private theorem completionLocEquiv_symm_plus_le :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus ≤
      ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus.comap
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    rw [rationalLocalizationPair_plus]
    let O_U := rationalLocalizationPair P UB hP T s S hden
    let O_V := rationalLocalizationPair P' UC hP' T' s' S' hden'
    let W := O_U.completedTensor A O_V
    have _ := W.isRingOfIntegralElements.isIntegrallyClosedIn
    have hcl := W.plus.toAddSubgroup.isClosed_of_isOpen W.isRingOfIntegralElements.isOpen
    let e := completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden''
    refine completedPlusSubring_le_comap Q (UB.completedTensor A UC).plus _ _ S'' hden'' hcl
      (φ := e.symm.toRingHom) (continuous_completionLocEquiv_symm ..) (fun d hd ↦ ?_)
      fun _ hx ↦ completionLocEquiv_symm_divBy_mem (hx := hx) ..
    refine UB.completedTensor_plus_le_comap UC hcl
      (f := e.symm.toRingHom.comp (toCompletionLoc Q _ _ S'' hden''))
      ((continuous_completionLocEquiv_symm ..).comp (continuous_toCompletionLoc Q _ _ S'' hden''))
      (fun b hb ↦ factor_symm_toCompletionLoc_mem_plus P UB T s S hden P' UC T' s' S' hden' Q S''
        hden'' hP hP' P UB hP T s S hden (CompletedTensor.inl A B C)
        (CompletedTensor.inl A (Completion S) (Completion S'))
        (fun _ ↦ by simp only [toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inl])
        (fun _ hy ↦ O_U.inl_mem_completedTensor_plus (A := A) O_V hy) hb)
      (fun c hc ↦ factor_symm_toCompletionLoc_mem_plus P UB T s S hden P' UC T' s' S' hden' Q S''
        hden'' hP hP' P' UC hP' T' s' S' hden' (CompletedTensor.inr A B C)
        (CompletedTensor.inr A (Completion S) (Completion S'))
        (fun _ ↦ by simp only [toCompletionLoc_apply, completionLocEquiv_symm_toCompletionLoc_inr])
        (fun _ hy ↦ O_U.inr_mem_completedTensor_plus (A := A) O_V hy) hc)
      hd

/-- **`completionLocEquiv` maps the plus ring of `(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` onto the
plus ring of `D⟨T''/s''⟩`.** -/
theorem map_plus_completionLocEquiv :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus.map
        (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom) =
      (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    Subring.map_equiv_eq_of_le_comap _ (completionLocEquiv_plus_le ..)
      (completionLocEquiv_symm_plus_le ..)

/-- Membership in the plus ring of `(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` is tested in the plus
ring of `D⟨T''/s''⟩` via `completionLocEquiv`. -/
theorem mem_completedTensor_plus_iff_completionLocEquiv :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    ∀ x : CompletedTensor A (Completion S) (Completion S'),
      x ∈ ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
          (rationalLocalizationPair P' UC hP' T' s' S' hden')).plus ↔
        completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'' x ∈
          (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'').plus :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in fun x ↦ by
    rw [← map_plus_completionLocEquiv P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ,
      RingEquiv.toRingHom_eq_coe, Subring.mem_map_equiv, RingEquiv.symm_apply_apply]

/-- The forward rational-localisation comparison
`(B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺) → (D⟨T''/s''⟩, D_W⁺)` as a morphism of Huber pairs. -/
noncomputable def toRationalLocalization :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    Hom ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden'))
      (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'') :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
  { toRingHom := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom
    continuous_toRingHom := continuous_completionLocEquiv ..
    map_mem_plus := fun _ hx ↦ (mem_completedTensor_plus_iff_completionLocEquiv ..).mp hx }

/-- The inverse rational-localisation comparison
`(D⟨T''/s''⟩, D_W⁺) → (B⟨T/s⟩, B_U⁺) ⊗̂_A (C⟨T'/s'⟩, C_V⁺)` as a morphism of Huber pairs. -/
noncomputable def ofRationalLocalization :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    Hom (rationalLocalizationPair Q (UB.completedTensor A UC) hQ _ _ S'' hden'')
      ((rationalLocalizationPair P UB hP T s S hden).completedTensor A
        (rationalLocalizationPair P' UC hP' T' s' S' hden')) :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
  { toRingHom := (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom
    continuous_toRingHom := continuous_completionLocEquiv_symm ..
    map_mem_plus := fun _ hy ↦
      (mem_completedTensor_plus_iff_completionLocEquiv P UB T s S hden P' UC T' s' S' hden'
        Q S'' hden'' hP hP' hQ _).mpr (by simpa using hy) }

/-- The underlying ring homomorphism of `toRationalLocalization`. -/
@[simp] theorem toRingHom_toRationalLocalization :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).toRingHom =
      (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').toRingHom := (rfl)

/-- The underlying ring homomorphism of `ofRationalLocalization`. -/
@[simp] theorem toRingHom_ofRationalLocalization :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).toRingHom =
      (completionLocEquiv P T s S hden P' T' s' S' hden' Q S'' hden'').symm.toRingHom := (rfl)

/-- `ofRationalLocalization` is a left inverse to `toRationalLocalization`. -/
@[simp] theorem ofRationalLocalization_comp_toRationalLocalization :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).comp
        (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ) =
      Hom.id _ :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    ext x; simp

/-- `toRationalLocalization` is a left inverse to `ofRationalLocalization`. -/
@[simp] theorem toRationalLocalization_comp_ofRationalLocalization :
    withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in
    (toRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ).comp
        (ofRationalLocalization P UB T s S hden P' UC T' s' S' hden' Q S'' hden'' hP hP' hQ) =
      Hom.id _ :=
  withRationalTensorHuber A B C P T s S hden P' T' s' S' hden' Q S'' hden'' in by
    ext x; simp

end RationalLocalizationPair

end FixedBase

end TauCeti.Huber.Pair.completedTensor
