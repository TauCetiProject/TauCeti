/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear functionals and hyperplanes

A functional `f` with `f x = 1` splits a module into the line through `x` and the kernel of `f`.
This file records the projection `id - f(·) • x` that this splitting defines, and the dimension
count for the trace of `ker f` on a subspace on which `f` does not vanish.
A codimension-one subspace, even in an infinite-dimensional ambient space, is the kernel
of a nonzero functional. Since functionals separate points, a vector space whose endomorphism
algebra is finite-dimensional is itself finite-dimensional.

## Main results

* `Module.Dual.ker_id_sub_smulRight`: if `f x = 1`, the kernel of `id - f(·) • x` is the line
  through `x`.
* `Module.Dual.finrank_ker_inf_add_one`: if `f` does not vanish on a finite-dimensional subspace
  `U`, then `ker f ⊓ U` has codimension one in `U`. This is the relative form of Mathlib's
  `Module.Dual.finrank_ker_add_one_of_ne_zero`.
* `Module.Dual.finrank_quotient_ker_eq_one_of_ne_zero`: the kernel of a nonzero functional has
  codimension one.
* `Submodule.exists_dual_ker_eq_of_finrank_quotient_eq_one`: every codimension-one subspace
  is the kernel of a nonzero functional.
* `Module.Finite.of_finite_end`: a vector space is finite-dimensional once its endomorphism
  algebra is.
-/

public section

namespace Module.Dual

open Module

section Semiring

variable {K V : Type*} [Semiring K] [AddCommGroup V] [Module K V]

/-- If `f x = 1`, the kernel of `id - f(·) • x` is the line through `x`. -/
@[simp]
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

/-- The kernel of a nonzero functional has codimension one. The ambient vector space need not be
finite-dimensional. -/
theorem finrank_quotient_ker_eq_one_of_ne_zero {f : Dual K V} (hf : f ≠ 0) :
    finrank K (V ⧸ LinearMap.ker f) = 1 := by
  rw [(f.quotKerEquivOfSurjective (LinearMap.surjective_iff_ne_zero.2 hf)).finrank_eq,
    finrank_self]

end DivisionRing

end Module.Dual

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A subspace of codimension one is the kernel of a nonzero linear functional.
The ambient vector space need not be finite-dimensional. -/
theorem exists_dual_ker_eq_of_finrank_quotient_eq_one (W : Submodule K V)
    (hW : Module.finrank K (V ⧸ W) = 1) :
    ∃ ℓ : Module.Dual K V, ℓ ≠ 0 ∧ LinearMap.ker ℓ = W := by
  have : FiniteDimensional K (V ⧸ W) := Module.finite_of_finrank_pos (by omega)
  let e := LinearEquiv.ofFinrankEq (R := K) (V ⧸ W) K (by simpa using hW)
  refine ⟨e.toLinearMap.comp W.mkQ, ?_, ?_⟩
  · intro h
    have he : Function.Surjective (e.toLinearMap.comp W.mkQ) :=
      e.surjective.comp W.mkQ_surjective
    obtain ⟨v, hv⟩ := he 1
    simp [h] at hv
  · ext v
    simp

end Submodule

namespace Module.Finite

/-- A vector space whose endomorphism algebra is finite-dimensional is finite-dimensional: for
`x ≠ 0`, evaluation at `x` maps `End_K S` onto `S`. -/
theorem of_finite_end (K S : Type*) [Field K] [AddCommGroup S] [Module K S]
    [Module.Finite K (Module.End K S)] : Module.Finite K S := by
  rcases subsingleton_or_nontrivial S with _ | _
  · infer_instance
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  obtain ⟨φ, hφ⟩ : ∃ φ : Dual K S, φ x ≠ 0 := by
    by_contra! h
    exact hx ((forall_dual_apply_eq_zero_iff K x).1 h)
  exact Module.Finite.of_surjective (LinearMap.applyₗ x)
    fun y ↦ ⟨(φ x)⁻¹ • φ.smulRight y, by simp [hφ]⟩

end Module.Finite
