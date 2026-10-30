/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Killing pairings of root spaces

This file records consequences of the non-degeneracy of the Killing form for the root spaces of a
splitting Cartan subalgebra, and the vanishing of brackets inside the Cartan subalgebra itself.

## Main results

* `TauCeti.killingForm_ne_zero_of_mem_rootSpace`: nonzero vectors in opposite root spaces have
  nonzero Killing pairing.
* `TauCeti.rootSpace_neg_eq_bot_iff`: the roots are closed under negation, so a functional on the
  Cartan subalgebra is a root exactly when its negative is.
* `TauCeti.lie_cartan_cartan_eq_zero`: the Cartan subalgebra is abelian, so two of its elements
  have zero bracket in the ambient Lie algebra.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- Nonzero vectors in opposite root spaces have nonzero Killing pairing. -/
theorem killingForm_ne_zero_of_mem_rootSpace {α : Weight K H L} (hα : α.IsNonZero) {e f : L}
    (he : e ∈ rootSpace H α) (he₀ : e ≠ 0) (hf : f ∈ rootSpace H (-α)) (hf₀ : f ≠ 0) :
    killingForm K L e f ≠ 0 := by
  intro hef
  refine he₀ ?_
  rw [← Submodule.mem_bot K, ← ker_killingForm_eq_bot K L]
  refine mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H he fun y hy ↦ ?_
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp <|
    (toSubmodule_rootSpace_eq_span (-α) hα.neg f hf₀ hf).le hy
  simp [hef]

omit [CharZero K] in
/-- The roots of a Lie algebra with non-degenerate Killing form are closed under negation, so a
functional on the Cartan subalgebra is a root exactly when its negative is. -/
@[simp]
theorem rootSpace_neg_eq_bot_iff (χ : H → K) :
    rootSpace H (-χ) = ⊥ ↔ rootSpace H χ = ⊥ := by
  have key (ψ : H → K) (hψ : rootSpace H ψ ≠ ⊥) : rootSpace H (-ψ) ≠ ⊥ :=
    (-(⟨ψ, hψ⟩ : Weight K H L)).genWeightSpace_ne_bot
  exact not_iff_not.mp ⟨fun h ↦ neg_neg χ ▸ key (-χ) h, key χ⟩

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
/-- **A Cartan subalgebra of a Lie algebra with non-degenerate Killing form is abelian**, so any
two of its elements have zero bracket in the ambient Lie algebra. -/
theorem lie_cartan_cartan_eq_zero (y z : H) : ⁅(y : L), (z : L)⁆ = 0 := by
  rw [← LieSubalgebra.coe_bracket, trivial_lie_zero, ZeroMemClass.coe_zero]

end TauCeti
