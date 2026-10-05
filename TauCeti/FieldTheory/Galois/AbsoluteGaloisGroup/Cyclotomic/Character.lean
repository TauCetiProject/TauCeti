/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The cyclotomic character of an absolute Galois group

The character `localCyclotomicCharacter p K` records the action of
`Field.absoluteGaloisGroup K` on roots of unity of `p`-power order in an algebraic closure.
It is Mathlib's cyclotomic character restricted from ring automorphisms to the Galois group.
The pointwise equation fixes this choice of character for later arithmetic comparisons.
Its bundled form `continuousLocalCyclotomicCharacter p K` is the continuous homomorphism that the
twisted coefficients `TauCeti.ZModTwist` and the prescription property
`TauCeti.HasPrescriptionProperty` take.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`. -/
noncomputable def localCyclotomicCharacter :
    Field.absoluteGaloisGroup K →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure K) p).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K))

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
  exact cyclotomicCharacter.continuous p K (AlgebraicClosure K)

/-- The `p`-adic cyclotomic character on the absolute Galois group of `K`, as a continuous
homomorphism. -/
noncomputable def continuousLocalCyclotomicCharacter :
    Field.absoluteGaloisGroup K →ₜ* ℤ_[p]ˣ :=
  ⟨localCyclotomicCharacter p K, localCyclotomicCharacter_continuous p K⟩

/-- The bundled continuous character takes the values of the cyclotomic character. -/
@[simp]
theorem continuousLocalCyclotomicCharacter_apply (σ : Field.absoluteGaloisGroup K) :
    continuousLocalCyclotomicCharacter p K σ = localCyclotomicCharacter p K σ :=
  (rfl)

end TauCeti
