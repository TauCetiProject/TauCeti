/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.VectorPartition.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Basic.Finite.Sum
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Real vector-partition polyhedra

`Matrix.nonnegFiber A b`, specialized to real matrices, satisfies `TauCeti.IsConvexPolyhedron`
when the row index type is finite. A covector strictly positive on every column makes the real
fiber compact. These results do not require unimodularity.
-/

public section

namespace Matrix

variable {m : Type*} {n : Type*} [Fintype n]

/-- A real vector-partition fiber is a convex polyhedron, even when unbounded or empty. -/
theorem isConvexPolyhedron_nonnegFiber [Finite m] (A : Matrix m n ℝ) (b : m → ℝ) :
    TauCeti.IsConvexPolyhedron (A.nonnegFiber b) := by
  let coord (j : n) : (n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let row (i : m) : (n → ℝ) →L[ℝ] ℝ := ∑ j, A i j • coord j
  let g : n ⊕ (m ⊕ m) → (n → ℝ) →ᴬ[ℝ] ℝ :=
    Sum.elim (fun j => -(coord j).toContinuousAffineMap)
      (Sum.elim (fun i => (row i).toContinuousAffineMap -
          ContinuousAffineMap.const ℝ (n → ℝ) (b i))
        (fun i => ContinuousAffineMap.const ℝ (n → ℝ) (b i) -
          (row i).toContinuousAffineMap))
  convert TauCeti.isConvexPolyhedron_setOf_forall g using 1
  ext x
  simp only [mem_nonnegFiber, Set.mem_ofPred_eq, Sum.forall, g, Sum.elim_inl, Sum.elim_inr,
    ContinuousAffineMap.neg_apply, ContinuousAffineMap.sub_apply,
    ContinuousAffineMap.coe_const, Function.const_apply, neg_nonpos, sub_nonpos, row, coord,
    ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.proj_apply,
    sum_apply, smul_apply, smul_eq_mul, Pi.le_def, Pi.zero_apply, funext_iff, mulVec,
    dotProduct]
  exact ⟨fun ⟨hx, he⟩ => ⟨hx, fun i => (he i).le, fun i => (he i).ge⟩,
    fun ⟨hx, hlo, hhi⟩ => ⟨hx, fun i => le_antisymm (hlo i) (hhi i)⟩⟩

/-- If a covector is strictly positive on every column, every real fiber is compact. -/
theorem isCompact_nonnegFiber [Fintype m] (A : Matrix m n ℝ)
    (hA : ∃ h : m → ℝ, ∀ j, 0 < (h ᵥ* A) j) (b : m → ℝ) :
    IsCompact (A.nonnegFiber b) := by
  obtain ⟨h, hh⟩ := hA
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : n → ℝ)
    (fun j => (h ⬝ᵥ b) / (h ᵥ* A) j))).of_isClosed_subset
      (A.isConvexPolyhedron_nonnegFiber b).isClosed ?_
  intro x hx
  exact ⟨((mem_nonnegFiber A b x).mp hx).1,
    fun j => A.apply_le_div_of_mem_nonnegFiber hh hx j⟩

end Matrix
