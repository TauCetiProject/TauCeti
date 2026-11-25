/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Morphisms of power-bounded Huber pairs out of Tate rings

A continuous ring homomorphism `φ : A → B` out of a Tate ring carries power-bounded elements to
power-bounded elements (`TauCeti.Huber.IsPowerBounded.map_of_isTateRing`), so it is a morphism
`(A, A°) → (B, B°)` of the Huber pairs `TauCeti.Huber.Pair.powerBounded`.

## Main definitions

* `TauCeti.Huber.Pair.powerBoundedHom`: a continuous ring homomorphism out of a Tate ring, as a
  morphism of the Huber pairs of power-bounded elements.
-/

public section

namespace TauCeti.Huber.Pair

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]

/-- A continuous ring homomorphism `φ : A → B` out of a Tate ring preserves power-boundedness, so
it is a morphism `(A, A°) → (B, B°)` of the Huber pairs of power-bounded elements. -/
noncomputable def powerBoundedHom (φ : A →+* B) (hφ : Continuous φ) :
    (powerBounded A).Hom (powerBounded B) where
  toRingHom := φ
  continuous_toRingHom := hφ
  map_mem_plus _ ha := by
    rw [powerBounded_plus] at ha ⊢
    exact mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp ha).map_of_isTateRing
      hφ.continuousAt

/-- The underlying ring homomorphism of `powerBoundedHom φ hφ` is `φ`. -/
@[simp]
theorem Hom.toRingHom_powerBoundedHom (φ : A →+* B) (hφ : Continuous φ) :
    (powerBoundedHom φ hφ).toRingHom = φ := (rfl)

end TauCeti.Huber.Pair
