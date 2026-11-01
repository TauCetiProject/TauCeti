/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Torsor.Trivial
import Mathlib.Data.ZMod.Basic

/-!
# Tests for trivial finite étale torsors

The regular split torsor is tested in arbitrary characteristic and over the zero ring.
Its three-cycle Galois-map computation distinguishes right translation from its inverse.
-/

namespace TauCeti.Algebra

open TensorProduct

attribute [local instance] rightRegularMulSemiringAction

/-- *test_field_split*: the split algebra is a torsor over any field, including its nonzero
finite étale formulation. -/
example (G K : Type*) [Group G] [Finite G] [Field K] :
    IsFiniteEtaleTorsor G K (G → K) ∧ Nontrivial (G → K) ∧ Module.Finite K (G → K) ∧
      Algebra.Etale K (G → K) ∧
      Function.Bijective (MulSemiringAction.tensorToPi K (G → K) G) :=
  ⟨inferInstance, (IsFiniteEtaleTorsor.iff_field K).mp inferInstance⟩

/-- *test_field_char_divides*: the split two-sheeted cover is a torsor in characteristic two. -/
example : IsFiniteEtaleTorsor (Multiplicative (ZMod 2)) (ZMod 2)
    (Multiplicative (ZMod 2) → ZMod 2) := inferInstance

/-- *test_zero_ring*: the regular split torsor also exists over the zero ring. -/
example (G : Type*) [Group G] [Finite G] :
    IsFiniteEtaleTorsor G (ZMod 1) (G → ZMod 1) := inferInstance

/-- *test_trivial_group*: right translation by the one-element group does not move functions. -/
example (A : Type*) [CommRing A] (f : Unit → A) (g : Unit) : g • f = f := by
  ext x
  simp

/-- The regular split torsor has constant rank equal to its group order. -/
example (G A : Type*) [Group G] [Finite G] [CommRing A] (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (G → A) p = Nat.card G :=
  IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := G) p

/-- *galois_convention_three*: at group coordinate one, `δ₀ ⊗ δ₁` gives `δ₀` on the
regular three-cycle torsor. -/
example : MulSemiringAction.tensorToPi ℚ (Multiplicative (ZMod 3) → ℚ)
    (Multiplicative (ZMod 3))
    (Pi.single (Multiplicative.ofAdd 0) 1 ⊗ₜ[ℚ] Pi.single (Multiplicative.ofAdd 1) 1)
    (Multiplicative.ofAdd 1) = Pi.single (Multiplicative.ofAdd 0) 1 := by
  ext x
  by_cases hx : x = 1
  · subst x
    simp
  · simp [hx]

/-- The inverse-translation convention would put the support at coordinate two instead;
with right translation the actual value there is zero. -/
example : MulSemiringAction.tensorToPi ℚ (Multiplicative (ZMod 3) → ℚ)
    (Multiplicative (ZMod 3))
    (Pi.single (Multiplicative.ofAdd 0) 1 ⊗ₜ[ℚ] Pi.single (Multiplicative.ofAdd 1) 1)
    (Multiplicative.ofAdd 2) = 0 := by
  ext x
  by_cases hx : x = 1
  · subst x
    have h : Multiplicative.ofAdd (2 : ZMod 3) ≠ Multiplicative.ofAdd 1 := by decide
    simp [h]
  · simp [Pi.single_apply, hx]

end TauCeti.Algebra
