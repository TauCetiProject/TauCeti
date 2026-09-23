/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Functionals normalised at a vector

A functional `f` with `f x = 1` splits a module into the line through `x` and the kernel of `f`.
This file records the projection `id - f(·) • x` that this splitting defines, and the dimension
count for the trace of `ker f` on a subspace on which `f` does not vanish.

## Main results

* `Module.Dual.ker_id_sub_smulRight`: if `f x = 1`, the kernel of `id - f(·) • x` is the line
  through `x`.
* `Module.Dual.finrank_ker_inf_add_one`: if `f` does not vanish on a finite-dimensional subspace
  `U`, then `ker f ⊓ U` has codimension one in `U`. This is the relative form of Mathlib's
  `Module.Dual.finrank_ker_add_one_of_ne_zero`.
-/

public section

namespace Module.Dual

open Module

section Semiring

variable {K V : Type*} [Semiring K] [AddCommGroup V] [Module K V]

/-- If `f x = 1`, the kernel of `id - f(·) • x` is the line through `x`. -/
theorem ker_id_sub_smulRight (f : Dual K V) {x : V} (hfx : f x = 1) :
    LinearMap.ker (LinearMap.id - LinearMap.smulRight f x) = K ∙ x := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, sub_eq_zero, Submodule.mem_span_singleton]
  exact ⟨fun h => ⟨f y, h.symm⟩, by rintro ⟨c, rfl⟩; simp [hfx]⟩

end Semiring

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If a functional `f` does not vanish on a finite-dimensional subspace `U`, then `ker f ⊓ U` has
codimension one in `U`. -/
theorem finrank_ker_inf_add_one {f : Dual K V} {U : Submodule K V} [FiniteDimensional K U]
    (hU : ¬ U ≤ LinearMap.ker f) :
    finrank K ↥(LinearMap.ker f ⊓ U) + 1 = finrank K U := by
  have hne : f.domRestrict U ≠ 0 := fun h => hU fun x hx => by
    simpa using LinearMap.congr_fun h ⟨x, hx⟩
  have hker : LinearMap.ker (f.domRestrict U) = (LinearMap.ker f ⊓ U).comap U.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  have hfin := finrank_ker_add_one_of_ne_zero hne
  rwa [hker, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at hfin

end DivisionRing

end Module.Dual
