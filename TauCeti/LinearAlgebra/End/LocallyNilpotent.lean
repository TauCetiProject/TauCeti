/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Inverting `1 + f` for a locally nilpotent endomorphism

An endomorphism `f` of a module is *locally nilpotent* when every vector is annihilated by some
power of `f`.  Then `1 + f` is invertible.  No global nilpotence bound is needed, so the statement
applies to operators which lower a filtration by direct summands without being nilpotent on the
whole module, such as those of homological perturbation theory on bar constructions.

## Main results

* `Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`: `1 + f` is a unit when `f` is
  locally nilpotent.
-/

public section

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- If every vector is annihilated by some power of `f`, then `1 + f` is invertible. -/
theorem Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) : IsUnit (1 + f) := by
  have hneg : ∀ (n : ℕ) (x : M), (f ^ n) x = 0 → ((-f) ^ n) x = 0 := by
    intro n x hx
    rw [neg_pow, Module.End.mul_apply, hx, map_zero]
  rw [Module.End.isUnit_iff]
  refine ⟨(injective_iff_map_eq_zero (1 + f)).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hf x
    have h := LinearMap.congr_fun (geom_sum_mul_neg (-f) n) x
    rw [sub_neg_eq_add, Module.End.mul_apply, hx, map_zero, LinearMap.sub_apply,
      Module.End.one_apply, hneg n x hn, sub_zero] at h
    exact h.symm
  · obtain ⟨n, hn⟩ := hf y
    refine ⟨(∑ i ∈ Finset.range n, (-f) ^ i) y, ?_⟩
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) n) y
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      hneg n y hn, sub_zero] at h
