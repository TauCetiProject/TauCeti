/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Pointwise sums over the finite support of a smooth partition of unity

Two facts about the finite set `ρ.finsupport x` of indices whose bump does not vanish at `x`, for a
smooth partition of unity `ρ`: every such index `i` has `x ∈ U i` for any cover `U` to which `ρ` is
subordinate (`SmoothPartitionOfUnity.IsSubordinate.mem_of_mem_finsupport`), and a weighted sum
`∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands `w i` all equal `v` is `v`
(`SmoothPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq`). Together they collapse the
partition-of-unity sums that glue local constructions over the members of a cover.
-/

public section

open Set

namespace SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
  {ρ : SmoothPartitionOfUnity ι I M s} {x : M}

/-- If `ρ` is subordinate to `U` and the bump `ρ i` does not vanish at `x`, then `x ∈ U i`. -/
theorem IsSubordinate.mem_of_mem_finsupport {U : ι → Set M} (hρ : ρ.IsSubordinate U) {i : ι}
    (hi : i ∈ ρ.finsupport x) : x ∈ U i :=
  hρ i (subset_tsupport _ ((ρ.mem_finsupport x).1 hi))

/-- At a point `x ∈ s`, a weighted sum `∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands with
`ρ i x ≠ 0` all equal `v` is `v`. -/
theorem sum_finsupport_smul_eq_of_forall_eq {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (hx : x ∈ s) {w : ι → A} {v : A} (hw : ∀ i ∈ ρ.finsupport x, w i = v) :
    ∑ i ∈ ρ.finsupport x, ρ i x • w i = v := by
  rw [Finset.sum_congr rfl fun i hi ↦ congrArg (ρ i x • ·) (hw i hi), ← Finset.sum_smul,
    ρ.sum_finsupport x hx, one_smul]

end SmoothPartitionOfUnity
