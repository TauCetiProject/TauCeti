/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Symmetric continuous multilinear maps

A continuous multilinear map `f : M [×ι]→L[R] N` is *symmetric* when it is invariant under every
permutation of its arguments, `f (v ∘ σ) = f v`. The symmetric maps form a submodule
`ContinuousMultilinearMap.symmetric R M N ι`. Iterated derivatives of `C^k` maps over `ℝ` or `ℂ`
are symmetric, and the symmetric `m`-linear forms on a tangent space are the symmetric cotangent
tensors of degree `m`, in which the top-order jets of functions vanishing to order `m` at a point
take their values.
-/

public section

namespace ContinuousMultilinearMap

variable (R : Type*) [CommSemiring R] (M N : Type*) [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] [ContinuousAdd N]
  [ContinuousConstSMul R N] (ι : Type*)

/-- The submodule of symmetric continuous multilinear maps `M [×ι]→L[R] N`, those invariant
under every permutation of their arguments. -/
def symmetric : Submodule R (ContinuousMultilinearMap R (fun _ : ι ↦ M) N) where
  carrier := {f | ∀ (v : ι → M) (σ : Equiv.Perm ι), f (v ∘ σ) = f v}
  add_mem' hf hg v σ := by simp [hf v σ, hg v σ]
  zero_mem' _ _ := rfl
  smul_mem' c f hf v σ := by simp [hf v σ]

variable {R M N ι}

theorem mem_symmetric {f : ContinuousMultilinearMap R (fun _ : ι ↦ M) N} :
    f ∈ symmetric R M N ι ↔ ∀ (v : ι → M) (σ : Equiv.Perm ι), f (v ∘ σ) = f v :=
  Iff.rfl

/-- A symmetric map takes the same value on a tuple and on any permutation of it. -/
@[simp]
theorem symmetric_apply_comp_perm (f : symmetric R M N ι) (v : ι → M) (σ : Equiv.Perm ι) :
    (f : ContinuousMultilinearMap R (fun _ : ι ↦ M) N) (v ∘ σ) =
      (f : ContinuousMultilinearMap R (fun _ : ι ↦ M) N) v :=
  f.property v σ

end ContinuousMultilinearMap
