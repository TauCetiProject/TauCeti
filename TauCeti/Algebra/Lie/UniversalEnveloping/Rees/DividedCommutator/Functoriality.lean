/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.DividedCommutator.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Functoriality

/-!
# Functoriality of the PBW Rees divided commutator

Naturality of `reesDividedCommutator` along Lie algebra homomorphisms `f : L →ₗ⁅R⁆ M`.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section Functoriality

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Naturality of `reesDividedCommutator` along a Lie algebra homomorphism. -/
@[simp]
theorem reesMap_reesDividedCommutator (f : L →ₗ⁅R⁆ M) (a b : reesAlgebra R L) :
    reesMap R f (reesDividedCommutator R L a b) =
      reesDividedCommutator R M (reesMap R f a) (reesMap R f b) :=
  ((reesDividedCommutator_eq_iff R M).mpr <| by
    calc
      reesMap R f a * reesMap R f b - reesMap R f b * reesMap R f a
        = reesMap R f (a * b - b * a) := by simp
      _ = reesMap R f (reesParameter R L * reesDividedCommutator R L a b) := by
          rw [← reesParameter_mul_reesDividedCommutator]
      _ = reesParameter R M * reesMap R f (reesDividedCommutator R L a b) := by
          rw [map_mul, reesMap_reesParameter]).symm

end Functoriality

end TauCeti.UniversalEnvelopingAlgebra
