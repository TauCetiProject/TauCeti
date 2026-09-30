/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Inverting `1 + f` for a locally nilpotent endomorphism

An endomorphism `f` of a module is *locally nilpotent* when every vector is annihilated by some
power of `f`.  Then `1 + f` is invertible.  No global nilpotence bound is needed, so the statement
applies to operators which lower a filtration by direct summands without being nilpotent on the
whole module, such as those of homological perturbation theory on bar constructions.

On a free module `ι →₀ R` over a finite basis, an endomorphism is locally nilpotent as soon as it
strictly lowers a weight on the basis.

## Main results

* `Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`: `1 + f` is a unit when `f` is
  locally nilpotent.
* `TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add`: the inverse of `1 + f` has degree zero
  when `f` is locally nilpotent of degree zero.
* `Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt`: an endomorphism of `ι →₀ R`,
  for a finite type `ι`, that strictly lowers a weight on the basis is locally nilpotent.
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

section Finsupp

open Finsupp

variable {R ι α : Type*} [Semiring R] [Finite ι] [Preorder α]

/-- **Strictly lowering a weight on a finite basis is locally nilpotent.** If an endomorphism `f`
of `ι →₀ R`, for a finite type `ι`, sends each basis vector `single i 1` into the span of the basis
vectors of strictly smaller weight, then every vector is killed by a power of `f`. -/
theorem Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt (w : ι → α)
    (f : Module.End R (ι →₀ R)) (hf : ∀ i, ∀ j ∈ (f (single i 1)).support, w j < w i)
    (x : ι →₀ R) : ∃ k, (f ^ k) x = 0 := by
  let N : Submodule R (ι →₀ R) :=
    { carrier := {x | ∃ k, (f ^ k) x = 0}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨max a b, ?_⟩
        rw [map_add, Module.End.pow_map_zero_of_le (le_max_left _ _) ha,
          Module.End.pow_map_zero_of_le (le_max_right _ _) hb, add_zero]
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨a, by rw [map_smul, ha, smul_zero]⟩ }
  have hN : ∀ x, x ∈ N ↔ ∃ k, (f ^ k) x = 0 := fun _ ↦ Iff.rfl
  let r : ι → ι → Prop := fun j i ↦ w j < w i
  have : IsTrans ι r := ⟨fun _ _ _ ↦ lt_trans⟩
  have : Std.Irrefl r := ⟨fun _ ↦ lt_irrefl _⟩
  have hsingle : ∀ i, single i (1 : R) ∈ N := by
    intro i
    induction i using (Finite.wellFounded_of_trans_of_irrefl r).induction with
    | _ i ih =>
      have hfi : f (single i 1) ∈ N := by
        rw [← Finsupp.sum_single (f (single i 1))]
        refine Submodule.sum_mem _ fun j hj ↦ ?_
        rw [← Finsupp.smul_single_one]
        exact N.smul_mem _ (ih j (hf i j hj))
      obtain ⟨k, hk⟩ := (hN _).1 hfi
      exact ⟨k + 1, by rw [pow_succ, Module.End.mul_apply, hk]⟩
  have hx : x ∈ N := by
    induction x using Finsupp.induction_linear with
    | zero => exact N.zero_mem
    | add x y hx hy => exact N.add_mem hx hy
    | single i c =>
      rw [← Finsupp.smul_single_one]
      exact N.smul_mem _ (hsingle i)
  exact hx

end Finsupp
