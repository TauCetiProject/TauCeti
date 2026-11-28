/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A common zero of fewer linear functionals than the dimension

Let `V` be a vector space over a division ring `F`, and let `φ i : V → F` be linear functionals
indexed by a finite type `ι`. If `ι` has fewer elements than `dim V`, which forces `V` to be
finite-dimensional, then some nonzero `v ∈ V` satisfies `φ i v = 0` for every `i`
(`TauCeti.exists_ne_zero_forall_apply_eq_zero_of_card_lt_finrank`). This is Mathlib's
`LinearMap.ker_ne_bot_of_finrank_lt` for the map `v ↦ (φ i v)_i` into `ι → F`.

Auxiliary polynomial constructions use it: the coefficients of the polynomial are the unknowns,
and each prescribed vanishing condition is one functional.
-/

public section

namespace TauCeti

/-- **Fewer linear functionals than the dimension have a common nonzero zero.** If the finite
family `φ` has fewer members than `dim V`, then some `v ≠ 0` satisfies `φ i v = 0` for every
`i`. -/
theorem exists_ne_zero_forall_apply_eq_zero_of_card_lt_finrank {F V ι : Type*} [DivisionRing F]
    [AddCommGroup V] [Module F V] [Finite ι] (φ : ι → V →ₗ[F] F)
    (h : Nat.card ι < Module.finrank F V) : ∃ v : V, v ≠ 0 ∧ ∀ i, φ i v = 0 := by
  have := Fintype.ofFinite ι
  -- `V` is finite-dimensional, since its `finrank` is positive.
  have : FiniteDimensional F V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi φ)
      (by simpa [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using h))
  exact ⟨v, hv0, fun i => congrFun (LinearMap.mem_ker.mp hv) i⟩

end TauCeti
