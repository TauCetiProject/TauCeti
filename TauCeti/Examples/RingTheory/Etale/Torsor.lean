/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Torsor.Trivial
import Mathlib.Data.ZMod.Basic

/-!
# Tests for finite étale torsors

A finite Galois extension is a torsor under its Galois group, and a field with a faithful action
of a finite group is a torsor over its fixed field. Over the zero ring the zero algebra is a
torsor under every finite group, which then does not act faithfully. Over a field the zero
algebra has a bijective Galois map but is not a torsor, because it is not faithfully flat.

The regular split torsor is tested in arbitrary characteristic and over the zero ring.
Its three-cycle Galois-map computation distinguishes right translation from its inverse.
-/

namespace TauCeti.Algebra

/-- *test_isGalois*: a finite Galois extension is a torsor under its Galois group, which is then
a Galois group in Mathlib's sense. -/
example (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    IsFiniteEtaleTorsor Gal(L/K) K L ∧ IsGaloisGroup Gal(L/K) K L :=
  ⟨inferInstance, inferInstance⟩

/-- The rank of a finite Galois extension, computed as a torsor, is its degree. -/
example (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (p : PrimeSpectrum K) : Module.rankAtStalk (R := K) L p = Module.finrank K L := by
  rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Gal(L/K)),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/-- Artin's theorem as a torsor: a field with a faithful action of a finite group is a torsor over
its fixed field. -/
example (G L : Type*) [Group G] [Finite G] [Field L] [MulSemiringAction G L] [FaithfulSMul G L] :
    IsFiniteEtaleTorsor G (FixedPoints.subfield G L) L :=
  IsFiniteEtaleTorsor.iff_isGaloisGroup.mpr inferInstance

/-- *test_zero_ring*: over the zero ring the zero algebra is a torsor under every finite group,
and a nontrivial group does not act faithfully on it. -/
example (G A B : Type*) [Group G] [Finite G] [Nontrivial G] [CommRing A] [CommRing B]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] [Subsingleton A] :
    IsFiniteEtaleTorsor G A B ∧ ¬ FaithfulSMul G B := by
  have : Subsingleton B := Module.subsingleton A B
  refine ⟨inferInstance, fun h ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (h.eq_of_smul_eq_smul fun _ ↦ Subsingleton.elim _ _)

/-- *test_field_zero_algebra*: over a field the zero algebra has a bijective Galois map but is
not a torsor. -/
example (G K B : Type*) [Group G] [Finite G] [Field K] [CommRing B] [Algebra K B]
    [MulSemiringAction G B] [SMulCommClass G K B] [Subsingleton B] :
    Function.Bijective (MulSemiringAction.tensorToPi K B G) ∧ ¬ IsFiniteEtaleTorsor G K B := by
  have : Subsingleton (TensorProduct K B B) := Module.subsingleton B _
  refine ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun f ↦ ⟨0, Subsingleton.elim _ _⟩⟩, fun h ↦ ?_⟩
  obtain ⟨hB, -⟩ := (IsFiniteEtaleTorsor.iff_field K).mp h
  exact not_nontrivial B hB

section Trivial

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

end Trivial

end TauCeti.Algebra
