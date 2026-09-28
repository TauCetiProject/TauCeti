/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The cyclotomic character of an absolute Galois group

The character `localCyclotomicCharacter p K` records the action of
`Field.absoluteGaloisGroup K` on roots of unity of `p`-power order in an algebraic closure.
It is Mathlib's cyclotomic character restricted from ring automorphisms to the Galois group.
The pointwise equation fixes this choice of character for later arithmetic comparisons.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`. -/
noncomputable def localCyclotomicCharacter :
    Field.absoluteGaloisGroup K →* ℤ_[p]ˣ :=
  MonoidHom.mk' (fun σ => cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv)
    (fun _σ _τ => map_mul (cyclotomicCharacter (AlgebraicClosure K) p) _ _)

/-- The local character is Mathlib's cyclotomic character evaluated on the underlying
ring automorphism. -/
@[simp]
theorem localCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    localCyclotomicCharacter p K σ =
      cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv :=
  (rfl)

/-- The cyclotomic character is continuous for the Krull topology on the absolute
Galois group and the `p`-adic topology on the units. -/
theorem localCyclotomicCharacter_continuous :
    Continuous (localCyclotomicCharacter p K) := by
  have h : Continuous (fun σ : Field.absoluteGaloisGroup K =>
      cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv) :=
    cyclotomicCharacter.continuous p K (AlgebraicClosure K)
  have heq : (localCyclotomicCharacter p K : _ → _) =
      (fun σ => cyclotomicCharacter (AlgebraicClosure K) p σ.toRingEquiv) := by
    funext σ
    exact localCyclotomicCharacter_apply p K σ
  rw [heq]
  exact h

end TauCeti
