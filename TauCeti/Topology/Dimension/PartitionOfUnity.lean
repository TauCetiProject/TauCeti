/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.PartitionOfUnity
public import TauCeti.Topology.Dimension.Covering
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Normed.Module.GeneralPosition

/-!
# Partitions of unity of bounded order and maps avoiding a point

In a paracompact normal space of covering dimension at most `d`, every open cover has a
subordinate partition of unity of order at most `d + 1`: at every point at most `d + 1` of its
functions are nonzero (`TauCeti.HasCoveringDimensionLE.exists_partitionOfUnity`). It is obtained
from a subordinate partition of unity of an open shrinking of order at most `d + 1`.

Such partitions of unity approximate maps by maps whose value at each point is a convex
combination of at most `d + 1` prescribed points. Let `X` be a compact normal space of covering
dimension at most `d` and `E` a real normed space of dimension greater than `d`. Every continuous
map `f : X → E` is uniformly close to a convex combination `x ↦ ∑ ρᵢ(x) yᵢ` of points `yᵢ` near
values of `f`, with at most `d + 1` nonzero coefficients at each point. Choosing the `yᵢ` so that
every `d + 1` of them are linearly independent, such a combination never vanishes. Hence the
continuous maps `X → E` missing `0` are dense
(`TauCeti.HasCoveringDimensionLE.dense_setOf_forall_ne_zero`).

For `E = 𝕜ⁿ` with `𝕜 = ℝ` or `ℂ` these maps are the unimodular rows of `C(X, 𝕜)`, so this gives the
upper bounds in Vaserstein's computation of the stable range of `C(X, 𝕜)`.

## References

* L. N. Vaserstein, *Stable rank of rings and dimensionality of topological spaces*, Funct. Anal.
  Appl. 5 (1971), 102–110, §2 (stable values of maps into `ℝⁿ` and the stable rank of `C(X)`).
* M. A. Rieffel, *Dimension and stable rank in the K-theory of C*-algebras*, Proc. London Math.
  Soc. (3) 46 (1983), 301–333 (the topological stable rank of `C(X)` from covering dimension).
-/

public section

open Function Module Metric Set

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- In a paracompact normal space of covering dimension at most `d`, every open cover `U` has a
subordinate partition of unity of order at most `d + 1`: at every point at most `d + 1` of its
functions are nonzero. -/
theorem HasCoveringDimensionLE.exists_partitionOfUnity [NormalSpace X] [ParacompactSpace X]
    {d : ℕ} (h : HasCoveringDimensionLE X d) {ι : Type*} {U : ι → Set X}
    (hUo : ∀ i, IsOpen (U i)) (hU : ⋃ i, U i = univ) :
    ∃ ρ : PartitionOfUnity ι X univ, ρ.IsSubordinate U ∧
      ∀ x, {i | ρ i x ≠ 0}.encard ≤ ((d + 1 : ℕ) : ℕ∞) := by
  obtain ⟨V, hVo, hVU, hV, hVm⟩ := h.exists_shrinking hUo hU
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ V hVo hV.ge
  exact ⟨ρ, fun i ↦ (hρ i).trans (hVU i), fun x ↦
    (encard_le_encard fun i hi ↦ hρ i (subset_tsupport _ hi)).trans (hVm x)⟩

/-- **Maps avoiding `0` are dense.** Let `X` be a compact normal space of covering dimension at
most `d`, and `E` a real normed space of dimension greater than `d`. Then the continuous maps
`X → E` that never vanish are dense in `C(X, E)` for the uniform metric. -/
theorem HasCoveringDimensionLE.dense_setOf_forall_ne_zero [CompactSpace X] [NormalSpace X]
    {d : ℕ} (h : HasCoveringDimensionLE X d) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hd : d < finrank ℝ E) :
    Dense {g : C(X, E) | ∀ x, g x ≠ 0} := by
  refine Metric.dense_iff.2 fun f ε hε ↦ ?_
  have hδ : 0 < ε / 3 := by positivity
  -- Cover `X` by finitely many sets `U i` on which `f` stays within `ε / 3` of `f i`, and take a
  -- subordinate partition of unity `ρ` of order at most `d + 1`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ f ⁻¹' ball (f x) (ε / 3))
    (fun x ↦ isOpen_ball.preimage f.continuous) fun x _ ↦ mem_iUnion.2 ⟨x, mem_ball_self hδ⟩
  obtain ⟨ρ, hρU, hρm⟩ := h.exists_partitionOfUnity (U := fun i : t ↦ f ⁻¹' ball (f i) (ε / 3))
    (fun i ↦ isOpen_ball.preimage f.continuous) <| eq_univ_of_forall fun x ↦ by
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hx⟩
  -- Choose `y i` within `ε / 3` of `f i`, every `d + 1` of them linearly independent.
  obtain ⟨y, hyf, hy⟩ := exists_forall_mem_and_linearIndepOn (k := d + 1) hd
    (O := fun i : t ↦ ball (f i) (ε / 3)) (fun _ ↦ isOpen_ball) fun _ ↦ nonempty_ball.2 hδ
  have hρf {x : X} {i : t} (hi : ρ i x ≠ 0) : dist (f x) (f i) < ε / 3 :=
    hρU i (subset_tsupport _ hi)
  let g : C(X, E) := ⟨fun x ↦ ∑ᶠ i, ρ i x • y i,
    ρ.continuous_finsum_smul fun _ _ _ ↦ continuousAt_const⟩
  have hg (x : X) : g x = ∑ᶠ i, ρ i x • y i := congrFun (ContinuousMap.coe_mk _ _) x
  refine ⟨g, ?_, fun x hx ↦ ?_⟩
  · -- `g x` is a convex combination of points within `2ε / 3` of `f x`.
    rw [mem_ball, ContinuousMap.dist_lt_iff hε]
    intro x
    have hgx : g x ∈ closedBall (f x) (2 * (ε / 3)) := hg x ▸
      ρ.finsum_smul_mem_convex (g := fun i _ ↦ y i) (mem_univ x) (fun i hi ↦ by
        rw [mem_closedBall, two_mul]
        exact (dist_triangle_right _ _ _).trans (add_lt_add (hyf i) (hρf hi)).le)
        (convex_closedBall _ _)
    exact (mem_closedBall.1 hgx).trans_lt (by linarith)
  · -- At most `d + 1` points `y i` enter `g x`, and they are linearly independent.
    have hs : {i | ρ i x ≠ 0}.Finite := toFinite _
    have hsum : ∑ i ∈ hs.toFinset, ρ i x • y i = 0 :=
      (finsum_eq_sum_of_support_subset _ fun i hi ↦ by
        simpa using left_ne_zero_of_smul hi).symm.trans ((hg x).symm.trans hx)
    have h0 := linearIndepOn_iff'.1 (hy _ (hρm x)) hs.toFinset (fun i ↦ ρ i x) (by simp) hsum
    obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ x)
    exact hi.ne' (h0 i (by simpa using hi.ne'))

end TauCeti
