/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianCech.Topology

/-!
# Continuity of the rational-localization Čech complex

The augmentation and differentials of the algebraic Čech complex are continuous for the natural
module topologies over the uncompleted rational localizations. Consequently they extend to the
separated completions of this topologised algebraic complex. These give the maps of Huber's
analytic Čech complex for `M = B`; for finite `M` over a ring with a noetherian ring of definition,
identifying the completed terms with Huber's terms requires a comparison not proved here.
No finiteness, completeness or noetherian hypothesis is needed for continuity.

The topology on a face depends on its cardinality: deleting a vertex changes both the denominator
and the numerator family. The restriction is continuous because multiplying the old numerators
by the deleted vertex gives numerators for the larger face. The module restriction then follows
by extending scalars on `TauCeti.cechLocalizationRestriction` using Mathlib’s
`LinearMap.extendScalarsOfIsLocalization`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, the complexes (*) and (**) in the proof of Theorem 2.5, Case I.
-/

public section

open Filter Topology LocalizedModule

namespace TauCeti.Huber.NoetherianCech

variable {B : Type*} [CommRing B] {ι : Type*} (f : ι → B)

private noncomputable def eraseRingHom [DecidableEq ι] (S : Finset ι) (a : S) :
    Localization.Away (∏ i ∈ S.erase a.1, f i) →+* Localization.Away (∏ i ∈ S, f i) :=
  IsLocalization.Away.lift _ (IsLocalization.Away.isUnit_of_dvd _
    ⟨f a.1, (Finset.prod_erase_mul S f a.2).symm⟩)

variable [TopologicalSpace B] [IsTopologicalRing B] (P : PairOfDefinition B)
  (hf : Ideal.span (Set.range f) = ⊤)

private theorem continuous_eraseRingHom [DecidableEq ι] (p : ℕ) (S : Finset ι) (a : S) :
    @Continuous _ _ (faceTopology f P hf p (S.erase a.1)) (faceTopology f P hf (p + 1) S)
      (eraseRingHom f S a) := by
  rw [faceTopology_eq_locTopology, faceTopology_eq_locTopology, eraseRingHom]
  exact P.continuous_awayLift_locTopology _ _ _ (hasDenominatorPower f P hf p (S.erase a.1))
    _ _ _ (hasDenominatorPower f P hf (p + 1) S) (f a.1) ((Finset.prod_erase_mul S f a.2).symm)
    fun _ ht ↦ mul_mem_numerators f ht a.1

variable (M : Type*) [AddCommGroup M] [Module B M]

/-- Restriction from a face with one vertex deleted is continuous for the natural topologies of
uncompleted rational localizations. -/
theorem continuous_cechLocalizationRestriction_erase [DecidableEq ι] (p : ℕ) (S : Finset ι)
    (a : S) :
    @Continuous _ _ (faceModuleTopology f P M hf p (S.erase a.1))
      (faceModuleTopology f P M hf (p + 1) S)
      (cechLocalizationRestriction M f (S.erase_subset a.1)) := by
  let R := Localization.Away (∏ i ∈ S.erase a.1, f i)
  let T := Localization.Away (∏ i ∈ S, f i)
  let N := LocalizedModule (.powers (∏ i ∈ S, f i)) M
  let _ := faceTopology f P hf p (S.erase a.1)
  let _ := faceTopology f P hf (p + 1) S
  let _ := faceModuleTopology f P M hf p (S.erase a.1)
  let _ := faceModuleTopology f P M hf (p + 1) S
  have := isModuleTopology_faceModuleTopology f P M hf p (S.erase a.1)
  have := isModuleTopology_faceModuleTopology f P M hf (p + 1) S
  have := IsModuleTopology.isTopologicalAddGroup T N
  have := IsModuleTopology.toContinuousSMul T N
  let φ : R →+* T := eraseRingHom f S a
  let _ : Module R N := Module.compHom N φ
  have : IsScalarTower B R N :=
      IsScalarTower.of_algebraMap_smul (R := B) (A := R) (M := N) fun b x ↦ by
    -- The restricted action is defined by the localization homomorphism.
    change φ (algebraMap B R b) • x = b • x
    simp only [φ, eraseRingHom, IsLocalization.Away.lift_eq]
    exact IsScalarTower.algebraMap_smul T b x
  have : ContinuousSMul R N := ⟨((continuous_eraseRingHom f P hf p S a).comp
    continuous_fst).smul continuous_snd⟩
  exact IsModuleTopology.continuous_of_linearMap
    ((cechLocalizationRestriction M f (S.erase_subset a.1)).extendScalarsOfIsLocalization
      (.powers (∏ i ∈ S.erase a.1, f i)) R)

/-- The augmentation of the rational-localization Čech complex is continuous. -/
theorem continuous_cechLocalizationAugmentation [TopologicalSpace M] [IsModuleTopology B M] :
    @Continuous _ _ _ (termTopology f P M hf 0) (cechLocalizationAugmentation M f) := by
  let _ := termTopology f P M hf 0
  rw [termTopology_eq_pi]
  refine @continuous_pi M {S : Finset ι // S.card = 0 + 1}
    (fun S ↦ LocalizedModule (.powers (∏ i ∈ S.1, f i)) M) _
    (fun S ↦ faceModuleTopology f P M hf 0 S.1) (cechLocalizationAugmentation M f) ?_
  intro S
  let _ := faceTopology f P hf 0 S.1
  let _ := faceModuleTopology f P M hf 0 S.1
  have := isModuleTopology_faceModuleTopology f P M hf 0 S.1
  have := isTopologicalAddGroup_faceModuleTopology f P M hf 0 S.1
  have := continuousSMul_faceModuleTopology f P M hf 0 S.1
  simp_rw [cechLocalizationAugmentation_apply]
  exact IsModuleTopology.continuous_of_linearMap (mkLinearMap _ M)

/-- Every differential of the rational-localization Čech complex is continuous. -/
theorem continuous_cechLocalizationDifferential [LinearOrder ι] (p : ℕ) :
    @Continuous _ _ (termTopology f P M hf p) (termTopology f P M hf (p + 1))
      (cechLocalizationDifferential M f p) := by
  let _ := termTopology f P M hf p
  let _ := termTopology f P M hf (p + 1)
  rw [termTopology_eq_pi f P M hf (p + 1)]
  refine @continuous_pi (cechLocalizationTerm M f p) {S : Finset ι // S.card = p + 1 + 1}
    (fun S ↦ LocalizedModule (.powers (∏ i ∈ S.1, f i)) M) (termTopology f P M hf p)
    (fun S ↦ faceModuleTopology f P M hf (p + 1) S.1) (cechLocalizationDifferential M f p) ?_
  intro S
  let _ := faceModuleTopology f P M hf (p + 1) S.1
  have := isTopologicalAddGroup_faceModuleTopology f P M hf (p + 1) S.1
  have := continuousSMul_faceModuleTopology f P M hf (p + 1) S.1
  simp_rw [cechLocalizationDifferential_apply]
  apply continuous_finsetSum
  intro a _
  let _ := faceModuleTopology f P M hf p (S.1.erase a.1)
  have hres := continuous_cechLocalizationRestriction_erase f P hf M p S.1 a
  have hproj : @Continuous _ _ (termTopology f P M hf p)
      (faceModuleTopology f P M hf p (S.1.erase a.1))
      (fun x : cechLocalizationTerm M f p ↦
        x ⟨S.1.erase a.1, by rw [Finset.card_erase_of_mem a.2, S.2]; rfl⟩) := by
    rw [termTopology_eq_pi]
    exact @continuous_apply {S : Finset ι // S.card = p + 1}
      (fun S ↦ LocalizedModule (.powers (∏ i ∈ S.1, f i)) M)
      (fun S ↦ faceModuleTopology f P M hf p S.1) _
  exact (hres.comp hproj).const_smul (((-1) ^ (S.1.filter (· < a.1)).card) : B)

end TauCeti.Huber.NoetherianCech
