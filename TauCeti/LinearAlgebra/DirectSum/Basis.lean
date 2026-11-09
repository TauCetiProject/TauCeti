/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Homogeneous bases of homogeneous subspaces

A subspace closed under the components of an internal direct sum has a basis consisting of
homogeneous vectors. This allows basis arguments in a graded module to retain the degrees of
its vectors, without requiring finite-dimensionality of the whole module or of its pieces.
-/

public section

namespace Submodule

variable {k V ι : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [DecidableEq ι]
  (H : Submodule k V) (ℳ : ι → Submodule k V) [DirectSum.Decomposition ℳ]

/-- A homogeneous subspace has a basis of homogeneous vectors, indexed by a subset of itself. -/
theorem exists_basis_isHomogeneousElem_of_isHomogeneous (hH : H.IsHomogeneous ℳ) :
    ∃ (t : Set H) (b : Module.Basis t k H), ∀ i, SetLike.IsHomogeneousElem ℳ (b i : V) := by
  classical
  let s : Set H := {x | ∃ d, (x : V) ∈ ℳ d}
  obtain ⟨t, hts, htspan, htli⟩ := exists_linearIndependent k s
  have hs : Submodule.span k s = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    let c (d : ι) : H := ⟨DirectSum.decompose ℳ (x : V) d, hH d x.property⟩
    have hx : x = ∑ d ∈ (DirectSum.decompose ℳ (x : V)).support, c d := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using (DirectSum.sum_support_decompose ℳ (x : V)).symm
    rw [hx]
    exact Submodule.sum_mem _ fun d _ ↦ Submodule.subset_span ⟨d, SetLike.coe_mem _⟩
  have ht : Submodule.span k t = ⊤ := htspan.trans hs
  let b : Module.Basis t k H := .mk htli (by rw [Subtype.range_coe, ht])
  refine ⟨t, b, fun i ↦ ?_⟩
  -- `Basis.mk` uses the chosen independent vectors themselves as basis vectors.
  simpa only [b, Module.Basis.mk_apply, s, Set.mem_ofPred_eq, SetLike.IsHomogeneousElem]
    using hts i.property

end Submodule
