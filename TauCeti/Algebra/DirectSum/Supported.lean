/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import TauCeti.Algebra.DirectSum.HomogeneousExtend

/-!
# Sums over selected homogeneous components

For an internal module grading, the sum of the pieces indexed by any set is
characterized by vanishing of all excluded components. Such sums are stable
under homogeneous projections. These criteria detect membership and homogeneity
of `TauCeti.supportedLieSubalgebra`.

The linear projection `TauCeti.DirectSum.supportedProj` onto such a sum keeps the components
indexed by the set and discards the others. Composing two of them projects onto the intersection
of the index sets, so operators prescribed by their effect on the homogeneous pieces can be cut
down to a range of types, as in the Deligne complex of a Dolbeault complex.

We use Mathlib's `DirectSum.decompose_of_mem_ne` and
`DirectSum.sum_support_decompose` to detect and reconstruct the allowed support.

Adapted from `Mei/Algebra/DirectSum/Supported.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original notice: Copyright (c) 2026 Mei contributors. All rights reserved.
Authors: Codex.
-/

public section

namespace TauCeti.DirectSum

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M) [DecidableEq ι] [_root_.DirectSum.Decomposition ℳ]
  (S : Set ι)

/-- Membership in a sum of selected pieces means that every excluded component vanishes. -/
theorem mem_iSup_iff_decompose_eq_zero {x : M} :
    x ∈ ⨆ i : S, ℳ i ↔
      ∀ i, i ∉ S → (_root_.DirectSum.decompose ℳ x i : M) = 0 := by
  classical
  constructor
  · intro hx i hi
    exact Submodule.iSup_induction _
      (motive := fun x => (_root_.DirectSum.decompose ℳ x i : M) = 0) hx
      (fun j x hx => _root_.DirectSum.decompose_of_mem_ne ℳ hx
        (fun h => hi (h ▸ j.property)))
      (by simp) (fun x y hx hy => by simp [hx, hy])
  · intro hx
    rw [← _root_.DirectSum.sum_support_decompose ℳ x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ S
    · exact Submodule.mem_iSup_of_mem ⟨i, hi⟩
        (_root_.DirectSum.decompose ℳ x i).property
    · rw [hx i hi]
      exact Submodule.zero_mem _

/-- A sum of selected homogeneous pieces is stable under homogeneous projections. -/
theorem isHomogeneous_iSup :
    _root_.DirectSum.SetLike.IsHomogeneous ℳ (⨆ i : S, ℳ i) := by
  classical
  intro i x hx
  by_cases hi : i ∈ S
  · exact Submodule.mem_iSup_of_mem ⟨i, hi⟩
      (_root_.DirectSum.decompose ℳ x i).property
  · rw [(mem_iSup_iff_decompose_eq_zero ℳ S).mp hx i hi]
    exact Submodule.zero_mem _

open scoped Classical in
/-- The projection onto the sum of the pieces indexed by `S`: it fixes every piece indexed by
`S` and kills every other piece. -/
noncomputable def supportedProj : M →ₗ[R] M :=
  _root_.DirectSum.homogeneousExtend ℳ fun i ↦ if i ∈ S then (ℳ i).subtype else 0

variable {ℳ S}

/-- The projection onto the pieces indexed by `S` fixes a piece indexed by `S`. -/
theorem supportedProj_of_mem {i : ι} {x : M} (hx : x ∈ ℳ i) (hi : i ∈ S) :
    supportedProj ℳ S x = x := by
  simp [supportedProj, _root_.DirectSum.homogeneousExtend_of_mem ℳ _ hx, hi]

/-- The projection onto the pieces indexed by `S` kills a piece not indexed by `S`. -/
theorem supportedProj_of_notMem {i : ι} {x : M} (hx : x ∈ ℳ i) (hi : i ∉ S) :
    supportedProj ℳ S x = 0 := by
  simp [supportedProj, _root_.DirectSum.homogeneousExtend_of_mem ℳ _ hx, hi]

/-- The projection onto the pieces indexed by `S` fixes the sum of those pieces. -/
theorem supportedProj_eq_self {x : M} (hx : x ∈ ⨆ i : S, ℳ i) : supportedProj ℳ S x = x :=
  Submodule.iSup_induction _ (motive := fun x ↦ supportedProj ℳ S x = x) hx
    (fun i _ hx ↦ supportedProj_of_mem hx i.property) (map_zero _)
    (fun _ _ hx hy ↦ by rw [map_add, hx, hy])

/-- Projecting an element of the sum of the pieces indexed by `T` onto the pieces indexed by `S`
lands in the sum of the pieces indexed by `S ∩ T`. -/
theorem supportedProj_mem_iSup_inter {T : Set ι} {x : M} (hx : x ∈ ⨆ i : T, ℳ i) :
    supportedProj ℳ S x ∈ ⨆ i : ↥(S ∩ T), ℳ i := by
  refine Submodule.iSup_induction _
    (motive := fun x ↦ supportedProj ℳ S x ∈ ⨆ i : ↥(S ∩ T), ℳ i) hx ?_ (by simp)
    (fun _ _ hx hy ↦ by simpa only [map_add] using add_mem hx hy)
  intro i x hx
  by_cases hi : (i : ι) ∈ S
  · rw [supportedProj_of_mem hx hi]
    exact Submodule.mem_iSup_of_mem ⟨i, hi, i.property⟩ hx
  · rw [supportedProj_of_notMem hx hi]
    exact Submodule.zero_mem _

variable (ℳ S)

/-- The projection onto the pieces indexed by `S` lands in the sum of those pieces. -/
theorem supportedProj_mem_iSup (x : M) : supportedProj ℳ S x ∈ ⨆ i : S, ℳ i := by
  have hx : x ∈ ⨆ i : (Set.univ : Set ι), ℳ i := by
    rw [mem_iSup_iff_decompose_eq_zero ℳ _]
    simp
  have h := supportedProj_mem_iSup_inter (S := S) hx
  rwa [Set.inter_univ] at h

/-- Projecting onto the pieces indexed by `T` and then onto those indexed by `S` is projecting
onto the pieces indexed by `S ∩ T`. -/
theorem supportedProj_supportedProj (T : Set ι) (x : M) :
    supportedProj ℳ S (supportedProj ℳ T x) = supportedProj ℳ (S ∩ T) x := by
  induction x using _root_.DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i x =>
    by_cases hT : i ∈ T
    · rw [supportedProj_of_mem x.property hT]
      by_cases hS : i ∈ S
      · rw [supportedProj_of_mem x.property hS,
          supportedProj_of_mem x.property (Set.mem_inter hS hT)]
      · rw [supportedProj_of_notMem x.property hS, supportedProj_of_notMem x.property
          fun h ↦ hS (Set.mem_of_mem_inter_left h)]
    · rw [supportedProj_of_notMem x.property hT, map_zero,
        supportedProj_of_notMem x.property fun h ↦ hT (Set.mem_of_mem_inter_right h)]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end TauCeti.DirectSum
