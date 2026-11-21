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
down to a range of types, as in the Deligne complex of a Dolbeault complex. An additive map
carrying each piece into a piece of another grading carries sums of pieces into sums of pieces
(`TauCeti.DirectSum.map_mem_iSup`) and intertwines the corresponding projections
(`TauCeti.DirectSum.map_supportedProj`).

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

/-- The projection onto all the pieces is the identity. -/
@[simp]
theorem supportedProj_univ (x : M) : supportedProj ℳ Set.univ x = x :=
  supportedProj_eq_self <| (mem_iSup_iff_decompose_eq_zero ℳ _).2 fun _ hi ↦ (hi trivial).elim

/-- The projection onto no pieces is zero. -/
@[simp]
theorem supportedProj_empty (x : M) : supportedProj ℳ ∅ x = 0 := by
  simpa using supportedProj_mem_iSup ℳ ∅ x

/-- The components of the projection onto the pieces indexed by `S` are those of the vector at
the indices in `S`, and vanish at the others. -/
@[simp]
theorem decompose_supportedProj (x : M) (i : ι) [Decidable (i ∈ S)] :
    (_root_.DirectSum.decompose ℳ (supportedProj ℳ S x) i : M) =
      if i ∈ S then (_root_.DirectSum.decompose ℳ x i : M) else 0 := by
  induction x using _root_.DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    by_cases hj : j ∈ S
    · rw [supportedProj_of_mem x.property hj]
      split_ifs with hi
      · rfl
      · exact _root_.DirectSum.decompose_of_mem_ne ℳ x.property fun h ↦ hi (h ▸ hj)
    · rw [supportedProj_of_notMem x.property hj, _root_.DirectSum.decompose_zero]
      split_ifs with hi
      · exact (_root_.DirectSum.decompose_of_mem_ne ℳ x.property fun h ↦ hj (h ▸ hi)).symm
      · rfl
  | add x y hx hy =>
    simp only [map_add, _root_.DirectSum.decompose_add, _root_.DirectSum.add_apply,
      Submodule.coe_add, hx, hy]
    split_ifs <;> simp

/-- Projecting onto the pieces indexed by `T` and then onto those indexed by `S` is projecting
onto the pieces indexed by `S ∩ T`. -/
@[simp]
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

section Map

variable {ℳ S} {R' N κ F : Type*} [Semiring R'] [AddCommMonoid N] [Module R' N]
  {𝒩 : κ → Submodule R' N} {T : Set κ} [FunLike F M N] [AddMonoidHomClass F M N]

omit [DecidableEq ι] [_root_.DirectSum.Decomposition ℳ] in
/-- An additive map sending each piece `ℳ i` into `𝒩 (e i)` carries the sum of the pieces indexed
by `S` into the sum of the pieces indexed by `T`, provided `e` maps `S` into `T`. -/
theorem map_mem_iSup (f : F) {e : ι → κ} (hf : ∀ i x, x ∈ ℳ i → f x ∈ 𝒩 (e i))
    (hST : ∀ i ∈ S, e i ∈ T) {x : M} (hx : x ∈ ⨆ i : S, ℳ i) : f x ∈ ⨆ j : T, 𝒩 j :=
  Submodule.iSup_induction _ (motive := fun x ↦ f x ∈ ⨆ j : T, 𝒩 j) hx
    (fun i _ hx ↦ Submodule.mem_iSup_of_mem ⟨_, hST i i.property⟩ (hf i _ hx))
    (by simp) (fun _ _ hx hy ↦ by simpa only [map_add] using add_mem hx hy)

variable [DecidableEq κ] [_root_.DirectSum.Decomposition 𝒩]

/-- An additive map sending each piece `ℳ i` into `𝒩 (e i)` intertwines the projection onto the
pieces indexed by `S` with the projection onto those indexed by `T`, provided `e i ∈ T` exactly
when `i ∈ S`. -/
theorem map_supportedProj (f : F) {e : ι → κ} (hf : ∀ i x, x ∈ ℳ i → f x ∈ 𝒩 (e i))
    (hST : ∀ i, e i ∈ T ↔ i ∈ S) (x : M) :
    f (supportedProj ℳ S x) = supportedProj 𝒩 T (f x) := by
  induction x using _root_.DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i x =>
    by_cases hi : i ∈ S
    · rw [supportedProj_of_mem x.property hi,
        supportedProj_of_mem (hf i _ x.property) ((hST i).2 hi)]
    · rw [supportedProj_of_notMem x.property hi,
        supportedProj_of_notMem (hf i _ x.property) (mt (hST i).1 hi), map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

end Map

end TauCeti.DirectSum
