/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.Kaehler.Basic

/-!
# Examples of continuous differentials

The degenerate cases of `Ωᶜ[B⁄A]`: the continuous differentials of a complete Hausdorff Huber
ring over itself vanish, and the derivation `d` kills the image of the base ring. The comparison
with Mathlib's Kähler differentials sends `d` to `d`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, (1.6.2).
-/

open TauCeti.Huber

section Self

variable (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A] [IsHuberRing A]

-- `Ωᶜ[A⁄A] = 0`: the identity is surjective.
example :
    haveI : IsAdicHom (algebraMap A A) := IsAdicHom.id
    Subsingleton (ContinuousKaehlerDifferential A A) :=
  haveI : IsAdicHom (algebraMap A A) := IsAdicHom.id
  ContinuousKaehlerDifferential.subsingleton_of_surjective Function.surjective_id

end Self

section Generic

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]

-- `d` is an `A`-derivation, so it kills the image of `A`.
example (a : A) : ContinuousKaehlerDifferential.D A B (algebraMap A B a) = 0 :=
  (ContinuousKaehlerDifferential.D A B).map_algebraMap a

-- The Leibniz rule for `d`, with `B` acting through either coprojection.
example (b c : B) :
    ContinuousKaehlerDifferential.D A B (b * c) =
      CompletedTensor.inr A B B b • ContinuousKaehlerDifferential.D A B c +
        CompletedTensor.inl A B B c • ContinuousKaehlerDifferential.D A B b := by
  simp [Derivation.leibniz]

-- The comparison with Kähler differentials is compatible with the two derivations.
example (b : B) :
    ContinuousKaehlerDifferential.fromKaehler A B (KaehlerDifferential.D A B b) =
      ContinuousKaehlerDifferential.D A B b := by
  simp

-- Elements of the completed diagonal ideal act by zero on `Ωᶜ[B⁄A]`.
example (x : CompletedTensor A B B) (hx : x ∈ ContinuousKaehlerDifferential.ideal A B)
    (ω : ContinuousKaehlerDifferential A B) : x • ω = 0 := by
  rw [ContinuousKaehlerDifferential.smul_eq_mulRingHom_smul,
    ContinuousKaehlerDifferential.mem_ideal_iff.mp hx, zero_smul]

end Generic
