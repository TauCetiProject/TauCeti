/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Topology.MetricSpace.Ultra.Completion

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.UniformSpace.CompleteSeparated
import TauCeti.Analysis.Normed.Field.Approximation

/-!
# Complete nonarchimedean fields with a dense algebraically closed subfield

A complete nonarchimedean normed field `L` containing a dense algebraically closed subfield `K`
is algebraically closed, in every characteristic. Mathlib's `IsAlgClosed.of_denseRange` proves
this when `L` has characteristic zero, through Krasner's lemma, which needs separability. Here
continuity of roots replaces Krasner's lemma: a root `x` of a polynomial over `L`, taken in an
algebraic closure of `L` with the spectral norm, is a limit of roots of nearby polynomials over
`K` (`IsAlgebraic.mem_closure_setOf_isAlgebraic`). Those roots lie in `K`, so `x` lies in the
closure of the image of `L`, which is closed since `L` is complete. A trivially normed `L` is
discrete, so `K` maps onto it.

In particular the completion of an algebraically closed nonarchimedean normed field is
algebraically closed, hence perfect: this covers `ℂ_p`, the completion of `ℚ_p^alg`, and the
completion of an algebraic closure of `𝔽_q((t))` in characteristic `p`, although the latter
algebraic closure is not complete.

## Main results

* `IsAlgClosed.of_isAlgClosed_of_denseRange`: a complete nonarchimedean normed field with a
  dense algebraically closed subfield is algebraically closed.
* `UniformSpace.Completion.instIsAlgClosed`: the completion of an algebraically closed
  nonarchimedean normed field is algebraically closed.

## References

* B. Conrad, *Math 248A. Completion of algebraic closure*, Theorem 1.1 and its proof in §2.
* K. S. Kedlaya, *Slope filtrations revisited*, Convention 2.2.16.
-/

public section

open Polynomial

namespace IsAlgClosed

/-- The nontrivially normed case of `IsAlgClosed.of_isAlgClosed_of_denseRange`. -/
private theorem of_isAlgClosed_of_denseRange_of_nontrivial {K L : Type*} [Field K]
    [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
    [IsAlgClosed K] (hi : DenseRange (algebraMap K L)) : IsAlgClosed L := by
  let : NormedField (AlgebraicClosure L) := spectralNorm.normedField L (AlgebraicClosure L)
  let : NormedAlgebra L (AlgebraicClosure L) := spectralNorm.normedAlgebra L (AlgebraicClosure L)
  -- the image of `L` is complete, hence closed
  have hcl : IsClosed (Set.range (algebraMap L (AlgebraicClosure L))) :=
    (AddMonoidHomClass.isometry_of_norm _ fun x ↦
      norm_algebraMap' (AlgebraicClosure L) x).isUniformInducing.isComplete_range.isClosed
  -- elements algebraic over the algebraically closed field `K` come from `K`, hence from `L`
  have hsub : {y : AlgebraicClosure L | IsAlgebraic K y} ⊆
      Set.range (algebraMap L (AlgebraicClosure L)) := by
    intro y hy
    obtain ⟨k, rfl⟩ := minpoly.mem_range_of_degree_eq_one K y
      (degree_eq_one_of_irreducible K (minpoly.irreducible hy.isIntegral))
    exact ⟨algebraMap K L k, (IsScalarTower.algebraMap_apply K L _ k).symm⟩
  refine of_exists_root L fun f _ hf ↦ ?_
  obtain ⟨x, hx⟩ := exists_aeval_eq_zero (AlgebraicClosure L) f (degree_pos_of_irreducible hf).ne'
  obtain ⟨c, rfl⟩ := hcl.closure_subset_iff.mpr hsub
    ((Algebra.IsAlgebraic.isAlgebraic (R := L) x).mem_closure_setOf_isAlgebraic hi)
  refine ⟨c, (algebraMap L (AlgebraicClosure L)).injective ?_⟩
  rw [map_zero, ← hx, aeval_algebraMap_apply_eq_algebraMap_eval]

/-- **A complete nonarchimedean normed field with a dense algebraically closed subfield is
algebraically closed**, in every characteristic. This drops the `CharZero` hypothesis of
Mathlib's `IsAlgClosed.of_denseRange` and allows a trivially normed `L`. -/
theorem of_isAlgClosed_of_denseRange {K L : Type*} [Field K] [NormedField L] [CompleteSpace L]
    [IsUltrametricDist L] [Algebra K L] [IsAlgClosed K] (hi : DenseRange (algebraMap K L)) :
    IsAlgClosed L := by
  by_cases h : ∃ x : L, x ≠ 0 ∧ ‖x‖ ≠ 1
  · let := NontriviallyNormedField.ofNormNeOne h
    exact of_isAlgClosed_of_denseRange_of_nontrivial hi
  -- a trivially normed `L` is discrete, so `algebraMap K L` is onto
  push Not at h
  have hsurj : Function.Surjective (algebraMap K L) := fun y ↦ by
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hi y 1 one_pos
    refine ⟨k, by_contra fun hne ↦ hk.ne ?_⟩
    rw [dist_eq_norm, h _ (sub_ne_zero.mpr (Ne.symm hne))]
  let e := RingEquiv.ofBijective _ ⟨(algebraMap K L).injective, hsurj⟩
  exact ⟨fun f ↦ by simpa only [Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom,
    Polynomial.map_id] using (IsAlgClosed.splits (f.map e.symm.toRingHom)).map e.toRingHom⟩

end IsAlgClosed

namespace UniformSpace.Completion

/-- **The completion of an algebraically closed nonarchimedean normed field is algebraically
closed**, in every characteristic: for instance `ℂ_p`, and the completion of an algebraic closure
of `𝔽_q((t))`. -/
instance instIsAlgClosed {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] :
    IsAlgClosed (Completion K) :=
  IsAlgClosed.of_isAlgClosed_of_denseRange (K := K) denseRange_coe

end UniformSpace.Completion
