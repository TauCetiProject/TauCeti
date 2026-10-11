/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Augmentation
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Basic
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# The augmentation relation for permutation classes

For a nonempty finite `G`-set `X`, the permutation class is the sum of the augmentation
subrepresentation's class and the trivial line's class. This holds over any commutative ring,
including when the augmentation sequence does not split. It allows composition-factor
calculations for permutation representations without using characters in positive characteristic.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.1.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable (k G X : Type u) [CommRing k] [Monoid G] [MulAction G X] [Finite X] [Nonempty X]

/-- The permutation class is the augmentation class plus the trivial class, even when the
augmentation sequence does not split. -/
theorem permK0_eq_augmentation_add_trivial :
    letI : Module.Finite k[G] (augmentationSubrepresentation k G X).toRepresentation.asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    permK0 k G X =
      ExactK0.of (FGModuleCat.of k[G]
        (augmentationSubrepresentation k G X).toRepresentation.asModule) +
      ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  let S := (permutationAugmentationSequence k G X).map (Rep.toModuleMonoidAlgebra (k := k) (G := G))
  have hS : S.ShortExact := by
    have h := permutationAugmentationSequence_shortExact k G X
    let := h.mono_f
    let := h.epi_g
    exact h.map _
  let : Module.Finite k[G] (augmentationSubrepresentation k G X).toRepresentation.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  let : Module.Finite k[G] (Representation.trivial k G k).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  have h₁ : (ModuleCat.isFG k[G]) S.X₁ := by
    simp only [S, permutationAugmentationSequence_def]
    -- `ModuleCat.isFG` is defined by carrier finiteness; spell out the predicate after
    -- rewriting the bundled endpoint so its dependent module instance stays synchronized.
    change Module.Finite k[G] (augmentationSubrepresentation k G X).toRepresentation.asModule
    infer_instance
  have h₃ : (ModuleCat.isFG k[G]) S.X₃ := by
    simp only [S, permutationAugmentationSequence_def]
    -- As above, expose the carrier-finiteness predicate only after rewriting the endpoint.
    change Module.Finite k[G] (Representation.trivial k G k).asModule
    infer_instance
  apply (finiteModulesExactK0Equiv k[G]).injective
  simp only [map_add, permK0_def, finiteModulesExactK0Equiv_of]
  have h := ExactK0.of_conflation_fullSubcategory (isExtensionClosed_finiteModules k[G])
    (by simpa only [ExactStructure.abelian_conflation] using hS)
    h₁ h₃
  simp only [S, permutationAugmentationSequence_def] at h
  -- The object formula of the representation-to-module functor identifies the three classes.
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    Rep.toModuleMonoidAlgebra, Rep.of_ρ] using h

end TauCeti
