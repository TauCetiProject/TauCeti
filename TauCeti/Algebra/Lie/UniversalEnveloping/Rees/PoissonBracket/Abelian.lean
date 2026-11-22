/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.DividedCommutator.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.PoissonBracket.Basic

/-!
# Zero-fibre Poisson bracket of an abelian Lie algebra

When `L` is an abelian Lie algebra free over a commutative ring `R`, the divided commutator on
`reesAlgebra R L` vanishes (`reesDividedCommutator_eq_zero`), so the zero-fibre Poisson bracket
`reesZeroFiberBracket R L` on `SymmetricAlgebra R L` vanishes identically.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

/-- Over an abelian Lie algebra free over `R`, the zero-fibre Poisson bracket vanishes. -/
@[simp]
theorem reesZeroFiberBracket_eq_zero (R : Type u) (L : Type v) [CommRing R] [LieRing L]
    [LieAlgebra R L] [Module.Free R L] [IsLieAbelian L] (p q : SymmetricAlgebra R L) :
    reesZeroFiberBracket R L p q = 0 := by
  obtain ⟨a, rfl⟩ := reesSpecializationZero_surjective R L p
  obtain ⟨b, rfl⟩ := reesSpecializationZero_surjective R L q
  simp [reesZeroFiberBracket_reesSpecializationZero]

end TauCeti.UniversalEnvelopingAlgebra
