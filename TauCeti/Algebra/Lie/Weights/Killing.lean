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
splitting Cartan subalgebra.

## Main results

* `TauCeti.killingForm_ne_zero_of_mem_rootSpace`: nonzero vectors in opposite root spaces have
  nonzero Killing pairing.
* `TauCeti.root_add_zsmul_mem_range_iff`: `β + n • α` is a root of `rootSystem H` exactly when
  the weight space of `n • α + β` is non-trivial.
* `TauCeti.rootSpace_neg_eq_bot_iff`: the roots are closed under negation, so a functional on the
  Cartan subalgebra is a root exactly when its negative is.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- A root of the form `β + n • α` exists in the root system of a Killing Lie algebra exactly when
the Lie weight space of `n • α + β` is nontrivial, for linearly independent roots `α, β`. -/
theorem root_add_zsmul_mem_range_iff {α β : H.root}
    (hlin : LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β]) (n : ℤ) :
    (rootSystem H).root β + n • (rootSystem H).root α ∈ Set.range (rootSystem H).root ↔
      rootSpace H (n • (α : Weight K H L) + (β : Weight K H L)) ≠ ⊥ := by
  have hab : LinearIndependent K
      ![((α : Weight K H L) : Module.Dual K H), ((β : Weight K H L) : Module.Dual K H)] := by
    simpa only [rootSystem_root_apply] using hlin
  constructor
  · rintro ⟨c, hc⟩
    have hc' : (c.1 : H → K) = n • ((α : Weight K H L) : H → K) + (β : Weight K H L) := by
      ext z
      simpa only [rootSystem_root_apply, Weight.toLinear_apply,
        LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, add_comm] using DFunLike.congr_fun hc z
    simpa only [hc'] using c.1.genWeightSpace_ne_bot
  · intro h
    let c : Weight K H L :=
      ⟨n • ((α : Weight K H L) : H → K) + (β : Weight K H L), h⟩
    have hc : c.IsNonZero := by
      intro hc₀
      -- Definitional equality: `c.IsNonZero` is `(c : H → K) ≠ 0`, so `hc₀` means `c.1 = 0`.
      change n • ((α : Weight K H L) : H → K) + (β : Weight K H L) = 0 at hc₀
      have hrel : (n : K) • ((α : Weight K H L) : Module.Dual K H) +
          (1 : K) • ((β : Weight K H L) : Module.Dual K H) = 0 := by
        ext z
        simpa [Weight.toLinear_apply] using congrFun hc₀ z
      exact one_ne_zero (hab.eq_zero_of_pair hrel).2
    refine ⟨⟨c, by simpa [LieSubalgebra.root] using hc⟩, ?_⟩
    ext z
    simp [c, Weight.toLinear_apply, add_comm]

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

end TauCeti
