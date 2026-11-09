/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Monoid

/-!
# Termwise differentiation of locally finite sums

If the supports of a family of functions `φ k : 𝕜 → F` form a locally finite family, then near
each point the sum `y ↦ ∑ᶠ k, φ k y` is a finite sum, so it may be differentiated termwise
(`LocallyFinite.hasSum_deriv_finsum`).
-/

public section

open Filter Topology

/-- **Termwise differentiation of a locally finite sum.** If the supports of the functions `φ k`
form a locally finite family and every `φ k` is differentiable at `x`, then the derivative of
`y ↦ ∑ᶠ k, φ k y` at `x` is the sum of the derivatives of the `φ k` at `x`. -/
theorem LocallyFinite.hasSum_deriv_finsum {ι 𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {φ : ι → 𝕜 → F}
    (hlf : LocallyFinite fun k ↦ Function.support (φ k)) {x : 𝕜}
    (hd : ∀ k, DifferentiableAt 𝕜 (φ k) x) :
    HasSum (fun k ↦ deriv (φ k) x) (deriv (fun y ↦ ∑ᶠ k, φ k y) x) := by
  obtain ⟨I, hI⟩ := hlf.exists_finset_support x
  have hsum : (fun y ↦ ∑ᶠ k, φ k y) =ᶠ[𝓝 x] fun y ↦ ∑ k ∈ I, φ k y :=
    hI.mono fun y hy ↦ finsum_eq_sum_of_support_subset _ hy
  rw [hsum.deriv_eq, deriv_fun_sum fun k _ ↦ hd k]
  refine hasSum_sum_of_ne_finset_zero fun k hk ↦ ?_
  have : φ k =ᶠ[𝓝 x] fun _ ↦ 0 := hI.mono fun y hy ↦ by_contra fun h ↦ hk (hy h)
  rw [this.deriv_eq, deriv_const]
