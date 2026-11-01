/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedAway
public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

import TauCeti.RingTheory.Huber.Completion.Noetherian
import TauCeti.RingTheory.Huber.LocalizationTopology.Adic

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
is complete, Hausdorff and linearly topologised, and the universal properties of `A_{f}` and of
the uniform completion give continuous ring homomorphisms in both directions. The comparison
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

omit [IsAdicRing A] in
/-- The uniform completion `A⟨1/f⟩` is linearly topologised, being adic for the extension of
`I`. -/
private theorem isLinearTopology_completion :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    IsLinearTopology (Completion S) (Completion S) := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  exact ((isAdic_locUniformSpace hI hfg S hden).map_coeRingHom
    (hfg.map _)).isLinearTopology

/-- The localisation map `A_f → A_{f}` is continuous for the localisation topology. -/
private theorem continuous_awayLift :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    Continuous
      (IsLocalization.Away.lift f (isUnit_algebraMap_self A f) : S →+* CompletedAway A f) := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  refine (isAdic_locUniformSpace hI hfg S hden).continuous_of_map_le_radical
    (isAdic A f) (hfg.map _) ?_
  rw [Ideal.map_map, IsLocalization.Away.lift_comp (S := S)]
  exact (Ideal.map_mono (hI.le_radical (IsAdicRing.ideal_spec A).2.1)).trans
    (Ideal.map_radical_le _)

/-- The continuous ring homomorphism `A_{f} → A⟨1/f⟩` given by the universal property of the
completed localisation. -/
private noncomputable def toCompletion :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    CompletedAway A f →+* Completion S :=
  letI := locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isLinearTopology_completion hI hfg S hden
  lift (toCompletionLoc (adic I hI hfg) {1} f S hden)
    (continuous_toCompletionLoc (adic I hI hfg) {1} f S hden)
    (by
      rw [toCompletionLoc_apply]
      exact (IsLocalization.Away.algebraMap_isUnit (S := S) f).map
        (Completion.coeRingHom : S →+* Completion S))

/-- The continuous ring homomorphism `A⟨1/f⟩ → A_{f}` extending the localisation map. -/
private noncomputable def ofCompletion :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    Completion S →+* CompletedAway A f :=
  letI := locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  Completion.extensionHom _ (continuous_awayLift hI hfg S hden)

private theorem continuous_toCompletion :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    Continuous (toCompletion hI hfg S hden) := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isLinearTopology_completion hI hfg S hden
  exact continuous_lift (B := Completion S) _ _ _

private theorem continuous_ofCompletion :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    Continuous (ofCompletion hI hfg S hden) := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  exact Completion.continuous_extension

private theorem toCompletion_algebraMap (a : A) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    toCompletion hI hfg S hden (algebraMap A (CompletedAway A f) a) =
      toCompletionLoc (adic I hI hfg) {1} f S hden a := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isLinearTopology_completion hI hfg S hden
  exact lift_algebraMap (B := Completion S) _ _ _ a

private theorem ofCompletion_coe (x : S) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    ofCompletion hI hfg S hden x = IsLocalization.Away.lift f (isUnit_algebraMap_self A f) x := by
  let _ := locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
  have _ := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
  exact Completion.extensionHom_coe (β := CompletedAway A f) _
    (continuous_awayLift hI hfg S hden) x

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
  RingEquiv.ofRingHom (toCompletion hI hfg S hden) (ofCompletion hI hfg S hden)
    (completion_locTopology_ringHom_ext_of_continuous (adic I hI hfg) {1} f S hden _ _
      ((continuous_toCompletion hI hfg S hden).comp (continuous_ofCompletion hI hfg S hden))
      continuous_id <| RingHom.ext fun a ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, toCompletionLoc_apply, ofCompletion_coe,
          IsLocalization.Away.lift_eq, toCompletion_algebraMap, RingHom.comp_apply,
          RingHom.id_apply])
    (ringHom_ext A f ((continuous_ofCompletion hI hfg S hden).comp
      (continuous_toCompletion hI hfg S hden)) continuous_id <| RingHom.ext fun a ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, toCompletion_algebraMap, toCompletionLoc_apply,
          ofCompletion_coe, IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.id_apply])

/-- The comparison sends the image of `a ∈ A` in the completed localisation to its image in
`A⟨1/f⟩`. -/
@[simp]
theorem completionLocEquiv_algebraMap (a : A) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    completionLocEquiv hI hfg S hden (algebraMap A (CompletedAway A f) a) =
      toCompletionLoc (adic I hI hfg) {1} f S hden a :=
  toCompletion_algebraMap hI hfg S hden a

/-- The inverse comparison is the canonical map `A_f → A_{f}` on the image of `A_f`. -/
@[simp]
theorem completionLocEquiv_symm_coe (x : S) :
    letI := locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isUniformAddGroup_locUniformSpace (adic I hI hfg) {1} f S hden
    letI := isTopologicalRing_locUniformSpace (adic I hI hfg) {1} f S hden
    (completionLocEquiv hI hfg S hden).symm x =
      IsLocalization.Away.lift f (isUnit_algebraMap_self A f) x :=
  ofCompletion_coe hI hfg S hden x

/-- The inverse comparison sends the image of `a ∈ A` in `A⟨1/f⟩` to its image in the completed
localisation. -/
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
  -- `completionLocEquiv` is `RingEquiv.ofRingHom toCompletion ofCompletion`, whose forward and
  -- inverse functions are these two maps by definition.
  exact (Homeomorph.mk (completionLocEquiv hI hfg S hden).toEquiv
    (continuous_toCompletion hI hfg S hden) (continuous_ofCompletion hI hfg S hden)).isHomeomorph

end TauCeti.AdicRing.CompletedAway
