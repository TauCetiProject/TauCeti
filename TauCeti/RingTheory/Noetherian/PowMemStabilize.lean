/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Noetherian.Basic

/-!
# Stabilization of iterated preimages into an invariant submodule

For a linear map g : P →ₗ[R] M out of a Noetherian R-module P, an R-linear endomorphism
 : Module.End R M, and an -invariant submodule N : Submodule R M, the ascending chain of
preimages {z ∈ P | (f ^ m) (g z) ∈ N} stabilizes at some finite exponent k. In particular, for
an element ϖ of an R-compatible semiring A acting on M, a Noetherian R-submodule F of
M, and an A-submodule N of M, there exists k such that ϖ ^ m • z ∈ N implies
ϖ ^ k • z ∈ N for all m ≥ k and z ∈ F.

## Main results

* TauCeti.IsNoetherian.exists_pow_apply_mem_of_le: stabilization of {z ∈ P | (f ^ m) (g z) ∈ N}
  for a linear map g : P →ₗ[R] M from a Noetherian R-module and an -invariant submodule N.
* TauCeti.IsNoetherian.exists_pow_smul_mem_of_le: scalar-multiplication specialization for a
  Noetherian R-submodule F of an A-module M, an A-submodule N, and ϖ : A.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/Cohomology/ProperBaseChange/LineCharts.lean
(New.Variety.exists_pow_smul_mem_range_of_pow_succ_smul_mem_range), generalized from the range
of an A-linear map B × C →ₗ[A] D and a single step k + 1 to arbitrary -invariant
submodules, arbitrary linear maps out of Noetherian modules, and all exponents m ≥ k.
-/

@[expose] public section

namespace TauCeti.IsNoetherian

/-- For a linear map g : P →ₗ[R] M from a Noetherian R-module P, an endomorphism
 : Module.End R M, and an -invariant submodule N : Submodule R M, there exists k : ℕ
such that (f ^ m) (g z) ∈ N implies (f ^ k) (g z) ∈ N for all m ≥ k and z : P. -/
theorem exists_pow_apply_mem_of_le {R P M : Type*} [Semiring R] [AddCommMonoid P]
    [AddCommMonoid M] [Module R P] [Module R M] [IsNoetherian R P]
    (g : P →ₗ[R] M) (f : Module.End R M) (N : Submodule R M) (hN : ∀ x ∈ N, f x ∈ N) :
    ∃ k : ℕ, ∀ m ≥ k, ∀ z : P, (f ^ m) (g z) ∈ N → (f ^ k) (g z) ∈ N := by
  have hmono : Monotone fun m : ℕ ↦ N.comap ((f ^ m).comp g) :=
    monotone_nat_of_le_succ fun m z hz ↦ by
      have hstep : (f ^ (m + 1)) (g z) = f ((f ^ m) (g z)) := by
        rw [pow_succ', mul_apply_eq_comp]
      rw [Submodule.mem_comap, LinearMap.comp_apply, hstep]
      exact hN _ hz
  obtain ⟨k, hk⟩ := WellFoundedGT.monotone_chain_condition ⟨_, hmono⟩
  exact ⟨k, fun m hm z hz ↦ (hk m hm).symm.le hz⟩

/-- Let F be a Noetherian R-submodule of an A-module M, let N be an A-submodule of M,
and let ϖ : A. Then there exists k : ℕ such that for all m ≥ k and z ∈ F,
ϖ ^ m • z ∈ N implies ϖ ^ k • z ∈ N. -/
theorem exists_pow_smul_mem_of_le {R A M : Type*} [Semiring R] [Semiring A] [SMul R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] [SMulCommClass R A M]
    (F : Submodule R M) [IsNoetherian R F] (N : Submodule A M) (ϖ : A) :
    ∃ k : ℕ, ∀ m ≥ k, ∀ z ∈ F, ϖ ^ m • z ∈ N → ϖ ^ k • z ∈ N := by
  let f : Module.End R M :=
    { toFun := (ϖ • ·)
      map_add' := smul_add ϖ
      map_smul' := fun r x ↦ (smul_comm r ϖ x).symm }
  have hf_pow (m : ℕ) (x : M) : (f ^ m) x = ϖ ^ m • x := by
    induction m with
    | zero => simp [f]
    | succ m ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, pow_succ', mul_smul]
      rfl
  obtain ⟨k, hk⟩ := exists_pow_apply_mem_of_le F.subtype f (N.restrictScalars R)
    (fun x hx ↦ N.smul_mem ϖ hx)
  refine ⟨k, fun m hm z hz hzm ↦ ?_⟩
  have hzk := hk m hm ⟨z, hz⟩
    (by simpa only [Submodule.subtype_apply, hf_pow, Submodule.restrictScalars_mem] using hzm)
  simpa only [Submodule.subtype_apply, hf_pow, Submodule.restrictScalars_mem] using hzk

end TauCeti.IsNoetherian
