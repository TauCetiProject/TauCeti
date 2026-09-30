/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Inverting `1 + f` for a locally nilpotent endomorphism

An endomorphism `f` of a module is *locally nilpotent* when every vector is annihilated by some
power of `f`.  Then `1 + f` is invertible.  No global nilpotence bound is needed, so the statement
applies to operators which lower a filtration by direct summands without being nilpotent on the
whole module, such as those of homological perturbation theory on bar constructions.

## Main results

* `Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`: `1 + f` is a unit when `f` is
  locally nilpotent.
* `TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add`: the inverse of `1 + f` has degree zero
  when `f` is locally nilpotent of degree zero.
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


section Ring

variable {S N : Type*} [Ring S] [AddCommGroup N] [Module S N]

/-- If `f` is locally nilpotent and homogeneous of degree zero for a grading by submodules, then so
is the inverse of `1 + f`: on a homogeneous vector it is a finite geometric series in `-f`. -/
theorem TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add {ι : Type*} [AddMonoid ι]
    {𝒜 : ι → Submodule S N} {f : Module.End S N}
    (hf : TauCeti.LinearMap.IsHomogeneous f 𝒜 𝒜 0) (hnil : ∀ x, ∃ n, (f ^ n) x = 0) :
    TauCeti.LinearMap.IsHomogeneous (Ring.inverse (1 + f)) 𝒜 𝒜 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  obtain ⟨n, hn⟩ := hnil x
  have hpow : ∀ i : ℕ, ((-f) ^ i) x ∈ 𝒜 p := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      simpa only [add_zero] using neg_mem (hf.map_mem ih)
  set y := (∑ i ∈ Finset.range n, (-f) ^ i) x with hy_def
  have hy : (1 + f) y = x := by
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) n) x
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      neg_pow, Module.End.mul_apply, hn, map_zero, sub_zero] at h
  have hinv : Ring.inverse (1 + f) x = y := by
    rw [← hy, ← Module.End.mul_apply,
      Ring.inverse_mul_cancel _ (Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f
        hnil), Module.End.one_apply]
  rw [hinv, add_zero, hy_def, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ hpow i

end Ring
