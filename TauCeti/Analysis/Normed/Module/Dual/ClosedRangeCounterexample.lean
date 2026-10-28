/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import TauCeti.Analysis.Normed.Module.Dual.Submodule

/-!
# An incomplete-domain counterexample to the closed-range theorem

`TauCeti.finiteSupportL2` is the submodule of finitely supported sequences in native `lp` at
exponent two. Its subtype norm is the inherited ℓ² norm, rather than the usual ℓ¹ norm on
`Finsupp`. Finite coordinate sums show that its inclusion has dense range, while the geometric
sequence with coordinates `2⁻ⁿ` lies outside that range. The submodule is consequently neither
closed nor complete.

The adjoint of the inclusion is nevertheless surjective: this is the existing restriction
theorem `Submodule.surjective_precomp_subtypeL`. Thus completeness of the domain is necessary
for the implication from closed adjoint range to closed operator range.

The density argument uses Mathlib's `lp.hasSum_single`, and the dual restriction result uses
the Hahn–Banach extension theorem.
-/

public section

open Function Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section NormedField

variable (𝕜 : Type*) [NormedField 𝕜]

/-- Finitely supported sequences, with the norm inherited from `ℓ²(ℕ, 𝕜)`. -/
noncomputable def finiteSupportL2 : Submodule 𝕜 (lp (fun _ : ℕ ↦ 𝕜) 2) :=
  (lpSubmodule 𝕜 (fun _ : ℕ ↦ 𝕜) 0).comap
    (lpSubmodule 𝕜 (fun _ : ℕ ↦ 𝕜) 2).subtype

/-- Membership in `finiteSupportL2` means finite coordinate support. -/
@[simp]
theorem mem_finiteSupportL2_iff (x : lp (fun _ : ℕ ↦ 𝕜) 2) :
    x ∈ finiteSupportL2 𝕜 ↔ (support fun n ↦ x n).Finite :=
  memℓp_zero_iff

/-- Finite coordinate sums are dense in `ℓ²`. -/
theorem dense_finiteSupportL2 : Dense (finiteSupportL2 𝕜 : Set (lp (fun _ : ℕ ↦ 𝕜) 2)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) x)
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i hi
  rw [mem_finiteSupportL2_iff]
  exact (lp.memℓp (lp.single (E := fun _ : ℕ ↦ 𝕜) 0 i (x i))).finite_dsupport

end NormedField

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The geometric sequence `2⁻ⁿ`, considered as an element of `ℓ²`. -/
private noncomputable def geometricL2 : lp (fun _ : ℕ ↦ 𝕜) 2 :=
  ⟨fun n ↦ ((2 : 𝕜)⁻¹) ^ n, by
    apply Memℓp.of_exponent_ge (q := 1) _ (by norm_num)
    apply memℓp_gen
    simpa [norm_pow, norm_inv] using summable_geometric_two⟩

/-- The geometric sequence has infinite support, so the finite-support submodule is proper. -/
private theorem geometricL2_not_mem_finiteSupportL2 : geometricL2 𝕜 ∉ finiteSupportL2 𝕜 := by
  rw [mem_finiteSupportL2_iff]
  simpa [support, geometricL2] using (Set.infinite_univ (α := ℕ))

/-- The finite-support submodule of `ℓ²` is not closed. -/
theorem not_isClosed_finiteSupportL2 :
    ¬ IsClosed (finiteSupportL2 𝕜 : Set (lp (fun _ : ℕ ↦ 𝕜) 2)) := by
  intro h
  apply geometricL2_not_mem_finiteSupportL2 𝕜
  have hx := dense_finiteSupportL2 𝕜 (geometricL2 𝕜)
  rwa [h.closure_eq] at hx

/-- The inherited ℓ² norm does not make the finite-support submodule complete. -/
theorem not_completeSpace_finiteSupportL2 : ¬ CompleteSpace (finiteSupportL2 𝕜) := by
  intro h
  apply not_isClosed_finiteSupportL2 𝕜
  exact (completeSpace_coe_iff_isComplete.mp h).isClosed

end TauCeti
