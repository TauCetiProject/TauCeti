/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.RepresentationTheory.Smooth.CoeffTwist

/-!
# Examples for twists of smooth representations by ring automorphisms

Complex conjugation `σ ∈ Aut(ℂ)` twists a complex representation `V` to `V^σ`, on which `z ∈ ℂ`
acts as `conj z`: the vector `i • v` of `V^σ` is `-i • v` in `V`. The twist is an autoequivalence
of the smooth category, it preserves admissibility and irreducibility, and twisting twice by
complex conjugation is twisting by the identity, which is the identity functor.
-/

public section

open CategoryTheory Representation

namespace TauCeti

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

/-- On the twist by complex conjugation, `i` acts as `-i`. -/
example (v : V) :
    Complex.I • CoeffTwist.of Complex.conjAe.toRingEquiv V v =
      CoeffTwist.of Complex.conjAe.toRingEquiv V (-Complex.I • v) := by
  have h : Complex.conjAe.toRingEquiv.symm Complex.I = -Complex.I :=
    Complex.conjAe.toRingEquiv.symm_apply_eq.2 (by simp)
  rw [CoeffTwist.smul_of, h]

/-- The twist by complex conjugation is an autoequivalence of the smooth category. -/
example : (SmoothRep.coeffTwist.{0} (G := G) Complex.conjAe.toRingEquiv).IsEquivalence :=
  inferInstance

/-- Twisting by complex conjugation preserves admissibility. -/
example (ρ : Representation ℂ G V) [IsAdmissible ρ] :
    IsAdmissible (ρ.coeffTwist Complex.conjAe.toRingEquiv) :=
  inferInstance

/-- Twisting by complex conjugation preserves irreducibility. -/
example (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    IsIrreducible (ρ.coeffTwist Complex.conjAe.toRingEquiv) :=
  isIrreducible_coeffTwist_iff.2 ‹_›

/-- Twisting twice by complex conjugation is twisting by the identity. -/
example : (Complex.conjAe.toRingEquiv.trans Complex.conjAe.toRingEquiv) = RingEquiv.refl ℂ := by
  ext z
  simp

/-- Twisting by the identity is the identity functor. -/
noncomputable example :
    SmoothRep.coeffTwist.{0} (G := G) (RingEquiv.refl ℂ) ≅ 𝟭 (SmoothRep.{0} ℂ G) :=
  SmoothRep.coeffTwistReflIso

end TauCeti
