/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Topology.PartitionOfUnity.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Manifold partitions of unity

This file collects basic facts about `BumpCovering` and `SmoothPartitionOfUnity` on manifolds:

* `BumpCovering.contMDiff_toPartitionOfUnity_of_contMDiff`: a `BumpCovering` whose functions are
  all `C^n` (`n : ℕ∞ω`) produces a `C^n` partition of unity, without assuming `C^∞` regularity,
  `σ`-compactness, or finite-dimensionality of the model space.
* `SmoothPartitionOfUnity.IsSubordinate.mem_of_mem_finsupport`: every index `i ∈ ρ.finsupport x`
  has `x ∈ U i` for any cover `U` to which `ρ` is subordinate.
* `SmoothPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq`: a weighted sum
  `∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands `w i` all equal `v` is `v`.
-/

public section

open Function Set
open scoped ContDiff Manifold

section BumpCovering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If every function in a `BumpCovering` is `C^n`, each weight of its associated partition of
unity is `C^n`. Adapted from Mathlib's `BumpCovering.contMDiff_toPartitionOfUnity`, generalized
from `C^∞` to `C^n`. -/
theorem BumpCovering.contMDiff_toPartitionOfUnity_of_contMDiff {ι : Type*} {s : Set M} {n : ℕ∞ω}
    (f : BumpCovering ι M s) (hf : ∀ i, ContMDiff I 𝓘(ℝ) n (f i)) (i : ι) :
    ContMDiff I 𝓘(ℝ) n (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ ↦ contMDiff_const.sub (hf j)) <| by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

end BumpCovering

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  {ρ : SmoothPartitionOfUnity ι I M s} {x : M}

/-- If `ρ` is subordinate to `U` and the bump `ρ i` does not vanish at `x`, then `x ∈ U i`. -/
theorem IsSubordinate.mem_of_mem_finsupport {U : ι → Set M} (hρ : ρ.IsSubordinate U) {i : ι}
    (hi : i ∈ ρ.finsupport x) : x ∈ U i :=
  hρ.toPartitionOfUnity.mem_of_mem_finsupport hi

/-- At a point `x ∈ s`, a weighted sum `∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands with
`ρ i x ≠ 0` all equal `v` is `v`. -/
theorem sum_finsupport_smul_eq_of_forall_eq {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (hx : x ∈ s) {w : ι → A} {v : A} (hw : ∀ i ∈ ρ.finsupport x, w i = v) :
    ∑ i ∈ ρ.finsupport x, ρ i x • w i = v :=
  ρ.toPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq hx hw

end SmoothPartitionOfUnity
