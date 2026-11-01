/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.TensorProduct.Pushout
import Mathlib.Topology.Instances.Int

/-!
# Checks for completed pushouts of Huber pairs

The identity and zero-factor squares have the completed universal property. In contrast,
the fold square for the diagonal into a product does not: identity and coordinate swap agree
on the base but differ on the product. The latter check uses complete, nonzero discrete rings.
-/

namespace TauCeti.Huber.CompletedPushoutChecks

universe u

variable {A B C : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- *isCompletedPushout_identity*: pushing out along an identity returns the other factor. -/
example (g : Pair.Hom S U) :
    IsCompletedPushout (Pair.Hom.id S) g g (Pair.Hom.id U) where
  condition := by simp
  existsUnique_desc D _ _ _ _ _ _ _ V a b hab := by
    refine ⟨b, ⟨by simpa using hab.symm, by simp⟩, ?_⟩
    rintro χ ⟨-, hχ⟩
    simpa using hχ

/-- *isCompletedPushout_zero_factor*: a zero factor forces every target of a cocone to be zero. -/
example [Subsingleton C] (f : Pair.Hom S T) (g : Pair.Hom S U) (i : Pair.Hom T U) :
    IsCompletedPushout f g i (Pair.Hom.id U) where
  condition := by ext; exact Subsingleton.elim _ _
  existsUnique_desc D _ _ _ _ _ _ _ V a b _ := by
    have := b.toRingHom.codomain_trivial
    refine ⟨b, ⟨?_, by simp⟩, ?_⟩
    · ext; exact Subsingleton.elim _ _
    rintro χ ⟨-, hχ⟩
    simpa using hχ

/-- *isCompletedPushout_fold*: identity and swap give distinct extensions of the diagonal. -/
example : ∃ f : Pair.Hom (Pair.discrete ℤ) (Pair.discrete (ℤ × ℤ)),
    ¬ IsCompletedPushout f f
      (Pair.Hom.id (Pair.discrete (ℤ × ℤ))) (Pair.Hom.id (Pair.discrete (ℤ × ℤ))) := by
  let diagonal : Pair.Hom (Pair.discrete ℤ) (Pair.discrete (ℤ × ℤ)) :=
    { toRingHom := (RingHom.id ℤ).prod (RingHom.id ℤ)
      continuous_toRingHom := continuous_of_discreteTopology
      map_mem_plus _ _ := by simp }
  let swap : Pair.Hom (Pair.discrete (ℤ × ℤ)) (Pair.discrete (ℤ × ℤ)) :=
    { toRingHom := (RingEquiv.prodComm : (ℤ × ℤ) ≃+* (ℤ × ℤ)).toRingHom
      continuous_toRingHom := continuous_of_discreteTopology
      map_mem_plus _ _ := by simp }
  refine ⟨diagonal, ?_⟩
  intro h
  have hdiag : (Pair.Hom.id _).comp diagonal = swap.comp diagonal := by
    apply Pair.Hom.ext
    ext x <;> simp [diagonal, swap]
  obtain ⟨χ, hχ, -⟩ := h.existsUnique_desc (ℤ × ℤ) (Pair.discrete (ℤ × ℤ))
    (Pair.Hom.id _) swap hdiag
  have heq : Pair.Hom.id (Pair.discrete (ℤ × ℤ)) = swap := by
    simpa using hχ.1.symm.trans hχ.2
  have hval := RingHom.congr_fun (congrArg Pair.Hom.toRingHom heq) (0, 1)
  have : (0 : ℤ) = 1 := by simpa [swap] using congrArg Prod.fst hval
  exact zero_ne_one this

end TauCeti.Huber.CompletedPushoutChecks
