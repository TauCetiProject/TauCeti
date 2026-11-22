/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Pointwise sums and finite localization by partitions of unity

Provides `PartitionOfUnity.IsSubordinate.mem_of_mem_finsupport`,
`PartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq`, and
`PartitionOfUnity.exists_finset_eq_sum_smul`: pointwise finite-support sum rules and finite
localization of compactly supported functions by a partition of unity.
-/

public section

open Set

namespace PartitionOfUnity

section

variable {ι X : Type*} [TopologicalSpace X] {s : Set X} {ρ : PartitionOfUnity ι X s} {x : X}

/-- If `ρ` is subordinate to `U` and `ρ i` does not vanish at `x`, then `x ∈ U i`. -/
theorem IsSubordinate.mem_of_mem_finsupport {U : ι → Set X} (hρ : ρ.IsSubordinate U) {i : ι}
    (hi : i ∈ ρ.finsupport x) : x ∈ U i :=
  hρ i (subset_tsupport _ ((ρ.mem_finsupport x).1 hi))

/-- At a point `x ∈ s`, a weighted sum `∑ i ∈ ρ.finsupport x, ρ i x • w i` whose summands with
`ρ i x ≠ 0` all equal `v` is `v`. -/
theorem sum_finsupport_smul_eq_of_forall_eq {A : Type*} [AddCommMonoid A] [Module ℝ A]
    (hx : x ∈ s) {w : ι → A} {v : A} (hw : ∀ i ∈ ρ.finsupport x, w i = v) :
    ∑ i ∈ ρ.finsupport x, ρ i x • w i = v := by
  rw [Finset.sum_congr rfl fun i hi ↦ congrArg (ρ i x • ·) (hw i hi), ← Finset.sum_smul,
    ρ.sum_finsupport hx, one_smul]

end

/-- A partition of unity covering the compact topological support of `f : X → V` localizes `f` into
finitely many terms, with all remaining terms vanishing identically. -/
theorem exists_finset_eq_sum_smul {ι X V : Type*} [TopologicalSpace X] [AddCommMonoid V]
    [Module ℝ V] {t : Set X} (ρ : PartitionOfUnity ι X t) (f : X → V)
    (hc : IsCompact (_root_.tsupport f)) (ht : _root_.tsupport f ⊆ t) :
    ∃ s : Finset ι,
      f = (fun x ↦ ∑ i ∈ s, ρ i x • f x) ∧ ∀ i ∉ s, (fun x ↦ ρ i x • f x) = 0 := by
  classical
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  let s := hfin.toFinset
  have hmem (i : ι) (x : X) (hρ : ρ i x ≠ 0) (hf : f x ≠ 0) : i ∈ s :=
    hfin.mem_toFinset.mpr ⟨x, subset_tsupport (ρ i) hρ, subset_tsupport f hf⟩
  refine ⟨s, funext fun x ↦ ?_, fun i hi ↦ funext fun x ↦ ?_⟩
  · by_cases hx : f x = 0; · simp [hx]
    have hs : ρ.finsupport x ⊆ s := fun i hi ↦
      hmem i x (by simpa only [mem_finsupport, Function.mem_support] using hi) hx
    rw [← Finset.sum_smul, ρ.sum_finsupport' (ht (subset_tsupport f hx)) hs, one_smul]
  · by_cases hf : f x = 0; · simp [hf]
    simp [by_contra fun h ↦ hi (hmem i x h hf)]

end PartitionOfUnity
