/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedAway
public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

import TauCeti.RingTheory.AdicCompletion.AlgHom
import TauCeti.RingTheory.AdicCompletion.UniformCompletion
import TauCeti.RingTheory.Huber.Completion.Noetherian
import TauCeti.RingTheory.Huber.LocalizationTopology.Adic
import TauCeti.RingTheory.Ideal.Maps

/-!
# The completed localisation as a rational localisation

Let `A` be an adic ring of finite ideal type and `f ∈ A`. Two constructions attach a complete
ring to the basic open set `D(f)`. The theory of formal schemes uses the completed localisation
`A_{f}` (`TauCeti.AdicRing.CompletedAway`), the adic completion of `A_f` along the extension of
an ideal of definition (EGA I, Ch. 0, 7.6.1–7.6.2). Huber's theory uses the coordinate ring
`A⟨1/f⟩` of the rational subset `R(1/f)`: the uniform completion of `A_f` for Wedhorn's
localisation topology (`TauCeti.Huber.PairOfDefinition.locTopology`), computed with the pair of
definition `(A, I)` for a finitely generated ideal of definition `I`, with numerator `1` and
denominator `f`.

This file identifies the two by a homeomorphic ring isomorphism intertwining the structure maps
from `A`, for every finitely generated ideal of definition `I`. The localisation topology is the
`I A_f`-adic topology (`TauCeti.Huber.PairOfDefinition.isAdic_locTopology_adic_one`), so `A⟨1/f⟩`
is the `I A_f`-adic completion of `A_f` (`IsAdic.completionEquivAdicCompletion`). The comparison
composes this with the change of ideal of definition `TauCeti.AdicRing.CompletedAway.idealEquiv`
and the transport of adic completions along `Localization.Away f ≃ₐ[A] A_f`
(`AdicCompletion.congrₐ`). It is bicontinuous because both directions carry an ideal of
definition into the radical of the other one. The comparison
lets results about Huber's rational localisations be applied to the completed localisations,
which are the rings of sections of the formal spectrum over basic open sets.

## Main definitions

* `TauCeti.AdicRing.CompletedAway.completionLocEquiv`: the ring isomorphism
  `A_{f} ≃+* A⟨1/f⟩`.

## Main results

* `TauCeti.AdicRing.CompletedAway.completionLocEquiv_algebraMap`: it sends the image of `a ∈ A`
  in `A_{f}` to its image `toCompletionLoc a` in `A⟨1/f⟩`.
* `TauCeti.AdicRing.CompletedAway.completionLocEquiv_symm_coe`: its inverse restricted to `A_f`
  is the canonical map `A_f → A_{f}`.
* `TauCeti.AdicRing.CompletedAway.isHomeomorph_completionLocEquiv`: it is a homeomorphism.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.6
  (7.6.1, 7.6.2 and 7.6.6).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.51.
-/

public section

open Topology UniformSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

namespace TauCeti.AdicRing.CompletedAway

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  {f : A} {I : Ideal A} (hI : IsAdic I) (hfg : I.FG) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away f S] (hden : HasDenominatorPower (adic I hI hfg) {1} f S)

omit [IsAdicRing A] in
/-- The localisation topology on `A_f`, through its uniform structure, is the adic topology of
`I A_f`. -/
private theorem isAdic_locUniformSpace :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    IsAdic (I.map (algebraMap A S)) := by
  have h := isAdic_locTopology_adic_one hI hfg f S hden
  rwa [← locUniformSpace_toTopologicalSpace] at h

/-- The **completed localisation is the rational localisation** `A⟨1/f⟩`: for an adic ring `A`
of finite ideal type and a finitely generated ideal of definition `I`, the completed localisation
`A_{f}` is isomorphic to the uniform completion of `A_f` for the localisation topology of the pair
of definition `(A, I)` with numerator `1` and denominator `f`. -/
noncomputable def completionLocEquiv :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    CompletedAway A f ≃+* Completion S :=
  letI := locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  ((idealEquiv f I hI hfg).trans (AdicCompletion.congrₐ _ <| Ideal.map_map_algebraMap
      (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) S) I)).toRingEquiv.trans
    (IsAdic.completionEquivAdicCompletion (isAdic_locUniformSpace hI hfg S hden) (hfg.map _)).symm

/-- The comparison sends the image of `a ∈ A` in the completed localisation to its image in
`A⟨1/f⟩`. -/
@[simp]
theorem completionLocEquiv_algebraMap (a : A) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    completionLocEquiv hI hfg S hden (algebraMap A (CompletedAway A f) a) =
      toCompletionLoc (adic I hI hfg) {1} f S hden a := by
  simp [completionLocEquiv, IsScalarTower.algebraMap_apply A S (AdicCompletion _ S)]

/-- The inverse comparison is the canonical map `A_f → A_{f}` on the image of `A_f`. -/
@[simp]
theorem completionLocEquiv_symm_coe (x : S) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    (completionLocEquiv hI hfg S hden).symm x =
      IsLocalization.Away.lift f (isUnit_algebraMap_self A f) x := by
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) S
  have h : (algebraMap (Localization.Away f) (CompletedAway A f)).comp (e.symm : S →+* _) =
      IsLocalization.Away.lift f (isUnit_algebraMap_self A f) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) <| RingHom.ext fun a ↦ by
      simp [e, ← IsScalarTower.algebraMap_apply]
  simp only [completionLocEquiv, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
    IsAdic.completionEquivAdicCompletion_coe, AlgEquiv.toRingEquiv_symm,
    AlgEquiv.coe_toRingEquiv, AlgEquiv.symm_trans_apply]
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply,
    AdicCompletion.congrₐ_symm_of]
  exact (idealEquiv_symm_algebraMap_away f I hI hfg _).trans (DFunLike.congr_fun h x)

/-- The inverse comparison sends the image of `a ∈ A` in `A⟨1/f⟩` to its image in the completed
localisation. Use it with `rw`: `simp` first rewrites `toCompletionLoc` by `toCompletionLoc_apply`,
so the left-hand side is not in simp normal form. -/
theorem completionLocEquiv_symm_toCompletionLoc (a : A) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    (completionLocEquiv hI hfg S hden).symm (toCompletionLoc (adic I hI hfg) {1} f S hden a) =
      algebraMap A (CompletedAway A f) a := by
  rw [RingEquiv.symm_apply_eq, completionLocEquiv_algebraMap]

/-- The comparison `A_{f} ≃+* A⟨1/f⟩` is a homeomorphism. -/
theorem isHomeomorph_completionLocEquiv :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    IsHomeomorph (completionLocEquiv hI hfg S hden) := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  let φ := completionLocEquiv hI hfg S hden
  let g : A →+* Completion S := Completion.coeRingHom.comp (algebraMap A S)
  have hφ : (φ : CompletedAway A f →+* Completion S).comp (algebraMap A _) = g :=
    RingHom.ext fun a ↦ (completionLocEquiv_algebraMap hI hfg S hden a).trans
      (toCompletionLoc_apply _ _ _ _ _ a)
  have hφsymm : (φ.symm : Completion S →+* CompletedAway A f).comp g = algebraMap A _ :=
    RingHom.ext fun a ↦ (congrArg φ.symm (toCompletionLoc_apply _ _ _ _ _ a).symm).trans
      (completionLocEquiv_symm_toCompletionLoc hI hfg S hden a)
  have hJ := (isAdic_locUniformSpace hI hfg S hden).map_coeRingHom (hfg.map _)
  -- Each direction carries an ideal of definition into the radical of the other one.
  refine (Homeomorph.mk φ.toEquiv ?_ ?_).isHomeomorph
  · refine (isAdic A f).continuous_of_map_le_radical hJ ((IsAdicRing.ideal_spec A).1.map _)
      (f := (φ : CompletedAway A f →+* Completion S)) ?_
    rw [Ideal.map_map, Ideal.map_map, hφ]
    exact (Ideal.map_mono ((IsAdicRing.ideal_spec A).2.1.le_radical hI)).trans
      (Ideal.map_radical_le _)
  · refine hJ.continuous_of_map_le_radical (isAdic A f) ((hfg.map _).map _)
      (f := (φ.symm : Completion S →+* CompletedAway A f)) ?_
    rw [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hφsymm]
    exact (Ideal.map_mono (hI.le_radical (IsAdicRing.ideal_spec A).2.1)).trans
      (Ideal.map_radical_le _)

end TauCeti.AdicRing.CompletedAway
