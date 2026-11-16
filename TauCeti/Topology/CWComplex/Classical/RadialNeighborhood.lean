/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Radial.Push
public import TauCeti.Topology.CWComplex.Classical.Quotient
public import TauCeti.Topology.CWComplex.Classical.Skeleton.CellDeformation
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
public import TauCeti.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Radial neighborhoods of subcomplexes

Let `A` be a subcomplex of a relative CW complex `C` with base `D`. Its **radial neighborhood**
`Topology.RelCWComplex.Subcomplex.radialNeighborhood A` is built cell by cell, in order of
dimension. It contains the base and every open cell of `A`. A point `map n j y`, `‖y‖ < 1`, of an
open cell outside `A` belongs to it exactly when it lies in the outer half `2⁻¹ < ‖y‖` of its cell
and its radial projection `map n j (‖y‖⁻¹ • y)` to the frontier of the cell belongs to it. This is
Hatcher's neighborhood `N_ε(A)` with every `ε` equal to `2⁻¹`.

* It is open in `C`
  (`Topology.RelCWComplex.Subcomplex.isOpen_preimage_val_radialNeighborhood`).
* `A` is a strong deformation retract of it
  (`Topology.RelCWComplex.Subcomplex.exists_strong_deformation_retraction_radialNeighborhood`).
  The deformation pushes the outer half of each open cell outside `A` radially onto its frontier,
  the cells of dimension `m` during the time interval `[2⁻¹ ^ (m + 1), 2⁻¹ ^ m]`. A point of
  `skeletonLT C (m + 1)` is moved by finitely many of these pushes only, which makes the infinite
  concatenation continuous.
* Since the same radius is used for every cell, radial neighborhoods are compatible with
  intersections and unions of subcomplexes
  (`Topology.RelCWComplex.Subcomplex.radialNeighborhood_inf`,
  `Topology.RelCWComplex.Subcomplex.radialNeighborhood_sup`). So the open sets `N(A)`,
  `N(B)`, `N(A ⊓ B) = N(A) ∩ N(B)` and `N(A ⊔ B) = N(A) ∪ N(B)` deformation retract onto `A`,
  `B`, `A ⊓ B` and `A ⊔ B`.
  This is the input for excision along the preimages of two subcomplexes under a Serre
  fibration, where open sets are needed.

## Main definitions

* `Topology.RelCWComplex.Subcomplex.radialNeighborhood`: the radial neighborhood of a subcomplex.
* `Topology.RelCWComplex.Subcomplex.radialDeformation`: the deformation of the radial
  neighborhood onto the subcomplex.
* `Topology.RelCWComplex.Subcomplex.radialNeighborhoodRetraction`,
  `Topology.RelCWComplex.Subcomplex.radialNeighborhoodDeformation`: the resulting retraction of
  the radial neighborhood onto the subcomplex, and the homotopy rel the subcomplex from the
  identity to it.

## Main results

* `Topology.RelCWComplex.Subcomplex.map_mem_radialNeighborhood_iff`: membership of a point of a
  closed cell.
* `Topology.RelCWComplex.Subcomplex.subset_radialNeighborhood`: a subcomplex lies in its radial
  neighborhood.
* `Topology.RelCWComplex.Subcomplex.isOpen_preimage_val_radialNeighborhood`,
  `Topology.RelCWComplex.Subcomplex.isOpen_radialNeighborhood`: the radial neighborhood is open
  in the complex, and so open in the space when the complex is.
* `Topology.RelCWComplex.Subcomplex.continuousOn_radialDeformation`,
  `Topology.RelCWComplex.Subcomplex.radialDeformation_map_of_le`,
  `Topology.RelCWComplex.Subcomplex.radialDeformation_map_of_ge`: the radial deformation is
  continuous, and on each closed cell outside the subcomplex it is a radial push followed by the
  deformation of the frontier.
* `Topology.RelCWComplex.Subcomplex.exists_strong_deformation_retraction_radialNeighborhood`: the
  subcomplex is a strong deformation retract of its radial neighborhood.
* `Topology.RelCWComplex.Subcomplex.radialNeighborhood_inf`,
  `Topology.RelCWComplex.Subcomplex.radialNeighborhood_sup`: compatibility with intersections
  and unions.
* `Topology.RelCWComplex.Subcomplex.radialNeighborhood_top`,
  `Topology.RelCWComplex.Subcomplex.radialNeighborhood_eq_empty_iff`: the radial neighborhood of
  the whole complex is the complex, and that of an empty subcomplex is empty.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Proposition A.5 and the construction of the neighborhoods `N_ε(A)` before it.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex TauCeti unitInterval

universe u

namespace Topology.RelCWComplex.Subcomplex

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- The part of the radial neighborhood of `A` in `skeletonLT C n`, defined by induction on `n`:
it is the base, then a point of an open `n`-cell is added when the cell lies in `A`, or when the
point lies in the outer half of its cell and its radial projection to the frontier was already
added. -/
private def radialNeighborhoodLT (A : Subcomplex C) : ℕ → Set X
  | 0 => D
  | n + 1 => radialNeighborhoodLT A n ∪ ⋃ j : cell C n, map n j ''
      {y | ‖y‖ < 1 ∧ (j ∈ A.I n ∨
        (2⁻¹ < ‖y‖ ∧ map n j (‖y‖⁻¹ • y) ∈ radialNeighborhoodLT A n))}

/-- The **radial neighborhood** of a subcomplex `A`. A point of an open cell of `A`, or of the
base, belongs to it; a point `map n j y` of an open cell not in `A` belongs to it exactly when
`2⁻¹ < ‖y‖` and its radial projection `map n j (‖y‖⁻¹ • y)` to the frontier of the cell belongs
to it (`Topology.RelCWComplex.Subcomplex.map_mem_radialNeighborhood_iff`). It is open in the complex
(`Topology.RelCWComplex.Subcomplex.isOpen_preimage_val_radialNeighborhood`) and deformation
retracts onto `A`
(`Topology.RelCWComplex.Subcomplex.exists_strong_deformation_retraction_radialNeighborhood`). -/
def radialNeighborhood (A : Subcomplex C) : Set X :=
  ⋃ n, radialNeighborhoodLT A n

variable (A : Subcomplex C)

private lemma radialNeighborhoodLT_succ (n : ℕ) :
    radialNeighborhoodLT A (n + 1) = radialNeighborhoodLT A n ∪ ⋃ j : cell C n, map n j ''
      {y | ‖y‖ < 1 ∧ (j ∈ A.I n ∨
        (2⁻¹ < ‖y‖ ∧ map n j (‖y‖⁻¹ • y) ∈ radialNeighborhoodLT A n))} := rfl

private lemma radialNeighborhoodLT_mono_succ (n : ℕ) :
    radialNeighborhoodLT A n ⊆ radialNeighborhoodLT A (n + 1) :=
  subset_union_left

private lemma radialNeighborhoodLT_mono {n m : ℕ} (h : n ≤ m) :
    radialNeighborhoodLT A n ⊆ radialNeighborhoodLT A m :=
  monotone_nat_of_le_succ (radialNeighborhoodLT_mono_succ A) h

private lemma radialNeighborhoodLT_subset_radialNeighborhood (n : ℕ) :
    radialNeighborhoodLT A n ⊆ A.radialNeighborhood :=
  subset_iUnion (radialNeighborhoodLT A) n

/-- A vector of the outer half of the unit ball has a radial projection of norm one. -/
private lemma norm_inv_norm_smul_of_half_le {n : ℕ} {y : Fin n → ℝ} (hy : 2⁻¹ ≤ ‖y‖) :
    ‖‖y‖⁻¹ • y‖ = 1 :=
  norm_smul_inv_norm (norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hy))

/-- The radial projection `y ↦ map n j (‖y‖⁻¹ • y)` is continuous on the outer half of the closed
unit ball. -/
private lemma continuousOn_map_inv_norm_smul (n : ℕ) (j : cell C n) :
    ContinuousOn (fun y : closedBall (0 : Fin n → ℝ) 1 ↦ map n j (‖(y : Fin n → ℝ)‖⁻¹ • y))
      {y | 2⁻¹ < ‖(y : Fin n → ℝ)‖} := by
  refine (continuousOn n j).comp ?_ fun y hy ↦
    mem_closedBall_zero_iff.2 (norm_inv_norm_smul_of_half_le hy.le).le
  refine ContinuousOn.smul (f := fun y : closedBall (0 : Fin n → ℝ) 1 ↦ ‖(y : Fin n → ℝ)‖⁻¹)
    (g := fun y ↦ (y : Fin n → ℝ)) ?_ continuous_subtype_val.continuousOn
  exact ((continuous_norm.comp continuous_subtype_val).continuousOn).inv₀
    fun y hy ↦ (lt_trans (by norm_num) hy).ne'

section

variable [T2Space X]

private lemma radialNeighborhoodLT_subset_skeletonLT (n : ℕ) :
    radialNeighborhoodLT A n ⊆ (skeletonLT C (n : ℕ∞) : Set X) := by
  induction n with
  | zero => exact (skeletonLT_zero_eq_base (C := C)).symm.subset
  | succ n ih =>
    refine union_subset (ih.trans (skeletonLT_mono (mod_cast n.le_succ)))
      (iUnion_subset fun j ↦ ?_)
    rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
    exact map_mem_skeletonLT_succ j hy.le

/-- The radial projection of a point of the outer half of an `n`-cell lies in `skeletonLT C n`. -/
private lemma map_inv_norm_smul_mem_skeletonLT {n : ℕ} (j : cell C n) {y : Fin n → ℝ}
    (hy : 2⁻¹ ≤ ‖y‖) : map n j (‖y‖⁻¹ • y) ∈ (skeletonLT C (n : ℕ∞) : Set X) :=
  cellFrontier_subset_skeletonLT n j ⟨_, mem_sphere_zero_iff_norm.2
    (norm_inv_norm_smul_of_half_le hy), rfl⟩

/-- The radial neighborhood meets `skeletonLT C n` in its `n`-th stage. -/
private lemma radialNeighborhood_inter_skeletonLT (n : ℕ) :
    A.radialNeighborhood ∩ (skeletonLT C (n : ℕ∞) : Set X) = radialNeighborhoodLT A n := by
  refine subset_antisymm ?_ fun x hx ↦
    ⟨radialNeighborhoodLT_subset_radialNeighborhood A n hx,
      radialNeighborhoodLT_subset_skeletonLT A n hx⟩
  rintro x ⟨hx, hxn⟩
  obtain ⟨m, hm⟩ := mem_iUnion.1 hx
  -- A point of a later stage lying in `skeletonLT C n` misses the open cells of the dimensions
  -- added after `n`, so it was already in the `n`-th stage.
  induction m with
  | zero => exact radialNeighborhoodLT_mono A (Nat.zero_le n) hm
  | succ m ih =>
    rcases le_or_gt (m + 1) n with h | h
    · exact radialNeighborhoodLT_mono A h hm
    refine ih ?_
    rcases hm with hm | hm
    · exact hm
    obtain ⟨j, y, ⟨hy, -⟩, rfl⟩ := mem_iUnion.1 hm
    exact absurd (skeletonLT_mono (by exact_mod_cast Nat.lt_succ_iff.1 h) hxn)
      (map_notMem_skeletonLT j hy)

/-- The radial neighborhood lies in the complex. -/
lemma radialNeighborhood_subset_complex : A.radialNeighborhood ⊆ C :=
  iUnion_subset fun n ↦ (radialNeighborhoodLT_subset_skeletonLT A n).trans
    (skeletonLT C n).subset_complex

end

/-- The radial neighborhood contains the base. -/
lemma base_subset_radialNeighborhood : D ⊆ A.radialNeighborhood :=
  radialNeighborhoodLT_subset_radialNeighborhood A 0

section

variable [T2Space X]

/-- A point of the frontier of an `n`-cell lies in the radial neighborhood exactly when it lies in
its `n`-th stage. -/
private lemma map_mem_radialNeighborhood_iff_of_norm_eq_one {n : ℕ} (j : cell C n)
    {y : Fin n → ℝ} (hy : ‖y‖ = 1) :
    map n j y ∈ A.radialNeighborhood ↔ map n j y ∈ radialNeighborhoodLT A n := by
  rw [← radialNeighborhood_inter_skeletonLT, mem_inter_iff, iff_self_and]
  exact fun _ ↦ cellFrontier_subset_skeletonLT n j ⟨y, mem_sphere_zero_iff_norm.2 hy, rfl⟩

private lemma map_mem_radialNeighborhood_iff_of_norm_lt {n : ℕ} (j : cell C n) {y : Fin n → ℝ}
    (hy : ‖y‖ < 1) :
    map n j y ∈ A.radialNeighborhood ↔
      j ∈ A.I n ∨ (2⁻¹ < ‖y‖ ∧ map n j (‖y‖⁻¹ • y) ∈ A.radialNeighborhood) := by
  have hN : map n j y ∈ A.radialNeighborhood ↔ map n j y ∈ radialNeighborhoodLT A (n + 1) := by
    rw [← radialNeighborhood_inter_skeletonLT A (n + 1), mem_inter_iff, iff_self_and]
    exact fun _ ↦ map_mem_skeletonLT_succ j hy.le
  rw [hN, radialNeighborhoodLT_succ]
  constructor
  · rintro (h | h)
    · exact absurd (radialNeighborhoodLT_subset_skeletonLT A n h) (map_notMem_skeletonLT j hy)
    obtain ⟨i, z, ⟨hz, hzA⟩, hzy⟩ := mem_iUnion.1 h
    obtain ⟨rfl, rfl⟩ := (map_eq_map_iff hz hy).1 hzy
    refine hzA.imp_right fun ⟨h2, h⟩ ↦ ⟨h2, ?_⟩
    exact (map_mem_radialNeighborhood_iff_of_norm_eq_one A i
      (norm_inv_norm_smul_of_half_le h2.le)).2 h
  · refine fun h ↦ .inr (mem_iUnion.2 ⟨j, y, ⟨hy, h.imp_right fun ⟨h2, h⟩ ↦ ⟨h2, ?_⟩⟩, rfl⟩)
    exact (map_mem_radialNeighborhood_iff_of_norm_eq_one A j
      (norm_inv_norm_smul_of_half_le h2.le)).1 h

/-- **A subcomplex lies in its radial neighborhood.** -/
lemma subset_radialNeighborhood : (A : Set X) ⊆ A.radialNeighborhood := by
  rw [← A.union]
  refine union_subset (base_subset_radialNeighborhood A) (iUnion₂_subset fun n j ↦ ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact (map_mem_radialNeighborhood_iff_of_norm_lt A j (mem_ball_zero_iff.1 hy)).2 (.inl j.2)

/-- **Membership of a point of a closed cell in the radial neighborhood.** The point `map n j y`,
`‖y‖ ≤ 1`, lies in the radial neighborhood of `A` exactly when the cell lies in `A`, or the point
lies in the outer half of its cell and its radial projection `map n j (‖y‖⁻¹ • y)` lies in the
radial neighborhood. -/
lemma map_mem_radialNeighborhood_iff {n : ℕ} (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    map n j y ∈ A.radialNeighborhood ↔
      j ∈ A.I n ∨ (2⁻¹ < ‖y‖ ∧ map n j (‖y‖⁻¹ • y) ∈ A.radialNeighborhood) := by
  rcases hy.lt_or_eq with hy | hy
  · exact map_mem_radialNeighborhood_iff_of_norm_lt A j hy
  by_cases hj : j ∈ A.I n
  · exact iff_of_true (subset_radialNeighborhood A
      (A.closedCell_subset_of_mem hj ⟨y, mem_closedBall_zero_iff.2 hy.le, rfl⟩)) (.inl hj)
  · -- On the unit sphere the radial projection is the identity.
    rw [hy, inv_one, one_smul, or_iff_right hj]
    exact ⟨fun h ↦ ⟨by norm_num, h⟩, fun h ↦ h.2⟩

/-- On a closed cell outside `A`, a point lies in the radial neighborhood exactly when it lies in
the outer half of the cell and its radial projection lies in the radial neighborhood. -/
private lemma map_mem_radialNeighborhood_iff_of_norm_le {n : ℕ} {j : cell C n} (hj : j ∉ A.I n)
    {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    map n j y ∈ A.radialNeighborhood ↔
      2⁻¹ < ‖y‖ ∧ map n j (‖y‖⁻¹ • y) ∈ A.radialNeighborhood := by
  rw [map_mem_radialNeighborhood_iff A j hy, or_iff_right hj]

/-- If the cell of `map n j y` lies in `A`, its radial projection lies in the radial
neighborhood of `A`. -/
private lemma map_inv_norm_smul_mem_of_mem_I {n : ℕ} {j : cell C n} (hj : j ∈ A.I n)
    {y : Fin n → ℝ} (hy : 2⁻¹ < ‖y‖) : map n j (‖y‖⁻¹ • y) ∈ A.radialNeighborhood :=
  subset_radialNeighborhood A <| A.cellFrontier_subset_of_mem hj
    ⟨_, mem_sphere_zero_iff_norm.2
      (norm_inv_norm_smul_of_half_le hy.le), rfl⟩

/-- **Radial neighborhoods of an intersection.** The radial neighborhood of the intersection of
two subcomplexes is the intersection of their radial neighborhoods. -/
@[simp]
lemma radialNeighborhood_inf (A B : Subcomplex C) :
    (A ⊓ B).radialNeighborhood = A.radialNeighborhood ∩ B.radialNeighborhood := by
  refine subset_antisymm (fun x hx ↦ ?_) fun x ⟨hxA, hxB⟩ ↦ ?_
  · have hxC := radialNeighborhood_subset_complex (A ⊓ B) hx
    revert hx
    refine forall_mem_complex_of_map (P := fun x ↦ x ∈ (A ⊓ B).radialNeighborhood →
      x ∈ A.radialNeighborhood ∩ B.radialNeighborhood) (fun x hx _ ↦
        ⟨base_subset_radialNeighborhood A hx, base_subset_radialNeighborhood B hx⟩)
      (fun n j y hy ih ↦ ?_) x hxC
    rw [mem_inter_iff, map_mem_radialNeighborhood_iff (A ⊓ B) j hy.le,
      map_mem_radialNeighborhood_iff A j hy.le, map_mem_radialNeighborhood_iff B j hy.le, inf_I]
    rintro (⟨hA, hB⟩ | ⟨h2, hp⟩)
    · exact ⟨.inl hA, .inl hB⟩
    · have := ih _ (map_inv_norm_smul_mem_skeletonLT j h2.le) hp
      exact ⟨.inr ⟨h2, this.1⟩, .inr ⟨h2, this.2⟩⟩
  · have hxC := radialNeighborhood_subset_complex A hxA
    revert hxA hxB
    refine forall_mem_complex_of_map (P := fun x ↦ x ∈ A.radialNeighborhood →
      x ∈ B.radialNeighborhood → x ∈ (A ⊓ B).radialNeighborhood)
      (fun x hx _ _ ↦ base_subset_radialNeighborhood (A ⊓ B) hx) (fun n j y hy ih ↦ ?_) x hxC
    rw [map_mem_radialNeighborhood_iff (A ⊓ B) j hy.le, map_mem_radialNeighborhood_iff A j hy.le,
      map_mem_radialNeighborhood_iff B j hy.le, inf_I]
    have hp (h2 : 2⁻¹ < ‖y‖) := map_inv_norm_smul_mem_skeletonLT (C := C) j h2.le
    rintro (hA | ⟨h2, hpA⟩) (hB | ⟨h2', hpB⟩)
    · exact .inl ⟨hA, hB⟩
    · exact .inr ⟨h2', ih _ (hp h2') (map_inv_norm_smul_mem_of_mem_I A hA h2') hpB⟩
    · exact .inr ⟨h2, ih _ (hp h2) hpA (map_inv_norm_smul_mem_of_mem_I B hB h2)⟩
    · exact .inr ⟨h2, ih _ (hp h2) hpA hpB⟩

/-- **Radial neighborhoods of a union.** The radial neighborhood of the union of two subcomplexes
is the union of their radial neighborhoods. -/
@[simp]
lemma radialNeighborhood_sup (A B : Subcomplex C) :
    (A ⊔ B).radialNeighborhood = A.radialNeighborhood ∪ B.radialNeighborhood := by
  ext x
  by_cases hxC : x ∈ C
  swap
  · exact iff_of_false (fun hx ↦ hxC (radialNeighborhood_subset_complex (A ⊔ B) hx))
      fun hx ↦ hxC (hx.elim (radialNeighborhood_subset_complex A ·)
        (radialNeighborhood_subset_complex B ·))
  refine forall_mem_complex_of_map (P := fun x ↦ x ∈ (A ⊔ B).radialNeighborhood ↔
      x ∈ A.radialNeighborhood ∪ B.radialNeighborhood)
    (fun x hx ↦ iff_of_true (base_subset_radialNeighborhood (A ⊔ B) hx)
      (.inl (base_subset_radialNeighborhood A hx)))
    (fun n j y hy ih ↦ ?_) x hxC
  have hp (h2 : 2⁻¹ < ‖y‖) := ih _ (map_inv_norm_smul_mem_skeletonLT j h2.le)
  rw [mem_union, map_mem_radialNeighborhood_iff (A ⊔ B) j hy.le,
    map_mem_radialNeighborhood_iff A j hy.le, map_mem_radialNeighborhood_iff B j hy.le, sup_I]
  constructor
  · rintro ((hA | hB) | ⟨h2, hpE⟩)
    · exact .inl (.inl hA)
    · exact .inr (.inl hB)
    · exact ((hp h2).1 hpE).imp (fun hpA ↦ .inr ⟨h2, hpA⟩) fun hpB ↦ .inr ⟨h2, hpB⟩
  · rintro ((hA | ⟨h2, hpA⟩) | (hB | ⟨h2, hpB⟩))
    · exact .inl (.inl hA)
    · exact .inr ⟨h2, (hp h2).2 (.inl hpA)⟩
    · exact .inl (.inr hB)
    · exact .inr ⟨h2, (hp h2).2 (.inr hpB)⟩

/-- Radial neighborhoods are monotone in the subcomplex. -/
@[gcongr]
lemma radialNeighborhood_mono {A B : Subcomplex C} (h : A ≤ B) :
    A.radialNeighborhood ⊆ B.radialNeighborhood := by
  rw [← sup_eq_right.2 h, radialNeighborhood_sup]
  exact subset_union_left

/-- The radial neighborhood of the whole complex is the complex. -/
@[simp]
lemma radialNeighborhood_top : (⊤ : Subcomplex C).radialNeighborhood = C :=
  (radialNeighborhood_subset_complex ⊤).antisymm (subset_radialNeighborhood (⊤ : Subcomplex C))

/-- The radial neighborhood of a subcomplex is empty exactly when the subcomplex is. -/
@[simp]
lemma radialNeighborhood_eq_empty_iff : A.radialNeighborhood = ∅ ↔ (A : Set X) = ∅ := by
  refine ⟨fun h ↦ subset_empty_iff.1 (h ▸ subset_radialNeighborhood A), fun h ↦ ?_⟩
  refine eq_empty_of_forall_notMem fun x hx ↦ forall_mem_complex_of_map
    (P := fun x ↦ x ∉ A.radialNeighborhood)
    (fun x hx ↦ (notMem_empty x (h ▸ A.base_subset hx)).elim)
    (fun n j y hy ih ↦ ?_) x (radialNeighborhood_subset_complex A hx) hx
  rw [map_mem_radialNeighborhood_iff A j hy.le, not_or]
  refine ⟨fun hj ↦ notMem_empty _ (h ▸ A.closedCell_subset_of_mem hj
    ⟨y, mem_closedBall_zero_iff.2 hy.le, rfl⟩), fun ⟨h2, hp⟩ ↦ ?_⟩
  exact ih _ (map_inv_norm_smul_mem_skeletonLT j h2.le) hp

/-- Over an empty base, the radial neighborhood of the bottom subcomplex is empty. -/
lemma radialNeighborhood_bot_of_base_eq_empty (hD : D = ∅) :
    (⊥ : Subcomplex C).radialNeighborhood = ∅ :=
  radialNeighborhood_eq_empty_iff ⊥ |>.2 (coe_bot.trans hD)

/-- For a CW complex, the radial neighborhood of the bottom subcomplex is empty. -/
@[simp]
lemma radialNeighborhood_bot {C : Set X} [RelCWComplex C ∅] :
    (⊥ : Subcomplex C).radialNeighborhood = ∅ :=
  radialNeighborhood_bot_of_base_eq_empty rfl

/-! ### Openness -/

/-- Membership in the radial neighborhood is continuous along every closed cell: its preimage
under each characteristic map is open in the closed unit ball. -/
private lemma continuous_mem_radialNeighborhood_map (n : ℕ) (j : cell C n) :
    Continuous fun y : closedBall (0 : Fin n → ℝ) 1 ↦ map n j y ∈ A.radialNeighborhood := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- By induction, membership is continuous on `skeletonLT C n`, which carries the frontier.
  have hskel : Continuous fun x : (skeletonLT C (n : ℕ∞) : Set X) ↦
      (x : X) ∈ A.radialNeighborhood := by
    rw [continuous_complex_iff]
    refine ⟨fun m ⟨i, hi⟩ ↦ ih m (by
      simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hi) i, ?_⟩
    exact continuous_const.congr fun d ↦ (eq_true (base_subset_radialNeighborhood A d.2)).symm
  by_cases hj : j ∈ A.I n
  · -- A closed cell of `A` lies in `A`.
    exact continuous_const.congr fun y ↦ (eq_true (subset_radialNeighborhood A
      (A.closedCell_subset_of_mem hj ⟨_, y.2, rfl⟩))).symm
  have hskel' : IsOpen {x : (skeletonLT C (n : ℕ∞) : Set X) | (x : X) ∈ A.radialNeighborhood} :=
    isOpen_iff_continuous_mem.2 hskel
  obtain ⟨V, hV, hVN⟩ := isOpen_induced_iff.1 hskel'
  -- On the outer half of the closed ball, membership is that of the radial projection.
  let f : closedBall (0 : Fin n → ℝ) 1 → X := fun y ↦ map n j (‖(y : Fin n → ℝ)‖⁻¹ • y)
  have hU : IsOpen {y : closedBall (0 : Fin n → ℝ) 1 | 2⁻¹ < ‖(y : Fin n → ℝ)‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have hf : ContinuousOn f {y | 2⁻¹ < ‖(y : Fin n → ℝ)‖} := continuousOn_map_inv_norm_smul n j
  refine (isOpen_iff_continuous_mem
    (s := {y : closedBall (0 : Fin n → ℝ) 1 | map n j y ∈ A.radialNeighborhood})).1 ?_
  convert hf.isOpen_inter_preimage hU hV using 1
  ext y
  have hfy (h2 : 2⁻¹ < ‖(y : Fin n → ℝ)‖) : f y ∈ V ↔ f y ∈ A.radialNeighborhood := by
    have hfs : f y ∈ (skeletonLT C (n : ℕ∞) : Set X) := map_inv_norm_smul_mem_skeletonLT j h2.le
    exact (Set.ext_iff.1 hVN ⟨f y, hfs⟩)
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [map_mem_radialNeighborhood_iff_of_norm_le A hj (mem_closedBall_zero_iff.1 y.2)]
  exact and_congr_right fun h2 ↦ (hfy h2).symm

/-- **The radial neighborhood of a subcomplex is open in the complex.** -/
theorem isOpen_preimage_val_radialNeighborhood : IsOpen ((↑) ⁻¹' A.radialNeighborhood : Set C) := by
  rw [isOpen_iff_continuous_mem, continuous_complex_iff]
  exact ⟨continuous_mem_radialNeighborhood_map A, continuous_const.congr fun d ↦
    (eq_true (base_subset_radialNeighborhood A d.2)).symm⟩

/-- **The radial neighborhood of a subcomplex of an open complex is open.** This applies to a CW
complex structure on the whole space. -/
theorem isOpen_radialNeighborhood (hC : IsOpen C) : IsOpen A.radialNeighborhood := by
  rw [← inter_eq_right.2 (radialNeighborhood_subset_complex A), ← Subtype.image_preimage_coe]
  exact hC.isOpenMap_subtype_val _ (isOpen_preimage_val_radialNeighborhood A)

end

/-! ### The radial deformation -/

/-- Stage `m` of the radial deformation at time `s`: the radial push `TauCeti.radialPush 2⁻¹`
in every open `m`-cell outside `A`. -/
private def stage (m : ℕ) (s : I) (x : X) : X :=
  cellDeformation {j : cell C m | j ∉ A.I m}
    ⟨fun q ↦ radialPush 2⁻¹ q.1 q.2, continuous_radialPush (by norm_num)⟩ (s, x)

/-- A stage fixes every point outside the open `m`-cells not in `A`. -/
private lemma stage_of_forall_notMem {m : ℕ} {s : I} {x : X}
    (hx : ∀ j : cell C m, j ∉ A.I m → x ∉ openCell m j) : stage A m s x = x :=
  cellDeformation_of_notMem fun j hj ↦ hx j hj

/-- A stage fixes the points of `A`. -/
private lemma stage_of_mem {m : ℕ} {s : I} {x : X} (hx : x ∈ A) : stage A m s x = x :=
  stage_of_forall_notMem A fun _ hj hxj ↦ hj ((A.mem_I_iff_of_mem_openCell hxj).2 hx)

/-- Through the characteristic map of a cell outside `A`, a stage is the radial push. -/
private lemma stage_map {m : ℕ} {j : cell C m} (hj : j ∉ A.I m) (s : I) {y : Fin m → ℝ}
    (hy : ‖y‖ ≤ 1) : stage A m s (map m j y) = map m j (radialPush 2⁻¹ s y) :=
  cellDeformation_map (fun t _ hy ↦ radialPush_of_norm_eq_one (by norm_num) (by norm_num) t hy)
    (A := {j : cell C m | j ∉ A.I m}) hj s hy

/-- At time `0` a stage is the identity. -/
private lemma stage_zero (m : ℕ) (x : X) : stage A m 0 x = x := by
  by_cases h : ∃ j : cell C m, j ∉ A.I m ∧ x ∈ openCell m j
  · obtain ⟨j, hj, hx⟩ := h
    rw [stage, cellDeformation_of_mem (A := {j : cell C m | j ∉ A.I m}) hj hx]
    simp only [ContinuousMap.coe_mk, radialPush_zero]
    exact map_map_symm m hx
  · push Not at h
    exact stage_of_forall_notMem A h

section

variable [T2Space X]

/-- A stage fixes the lower skeleton. -/
private lemma stage_of_mem_skeletonLT {m : ℕ} {s : I} {x : X}
    (hx : x ∈ (skeletonLT C (m : ℕ∞) : Set X)) : stage A m s x = x :=
  cellDeformation_of_mem_skeletonLT hx

/-- A stage keeps the radial neighborhood inside itself. -/
private lemma stage_mem {m : ℕ} (s : I) {x : X} (hx : x ∈ A.radialNeighborhood) :
    stage A m s x ∈ A.radialNeighborhood := by
  by_cases h : ∃ j : cell C m, j ∉ A.I m ∧ x ∈ openCell m j
  · obtain ⟨j, hj, y, hy, rfl⟩ := h
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
    obtain ⟨h2, hp⟩ := ((map_mem_radialNeighborhood_iff A j hy1.le).1 hx).resolve_left hj
    rw [stage_map A hj s hy1.le, map_mem_radialNeighborhood_iff_of_norm_le A hj
      (norm_radialPush_le_one s hy1.le), inv_norm_smul_radialPush (by norm_num) s]
    exact ⟨h2.trans_le (norm_le_norm_radialPush (by norm_num) (by norm_num) s hy1.le), hp⟩
  · push Not at h
    rwa [stage_of_forall_notMem A h]

/-- **At time `1`, stage `m` carries the points of the radial neighborhood in `skeletonLT C (m + 1)`
into `skeletonLT C m`, unless they lie in `A`.** -/
private lemma stage_one_mem {m : ℕ} {x : X}
    (hx : x ∈ A.radialNeighborhood ∩ (skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) ∪ A) :
    stage A m 1 x ∈ A.radialNeighborhood ∩ (skeletonLT C (m : ℕ∞) : Set X) ∪ A := by
  obtain ⟨hxN, hxm⟩ | hxA := hx
  · obtain hxm | ⟨j, y, hy, rfl⟩ := mem_skeletonLT_or_exists_map hxm
    · rw [stage_of_mem_skeletonLT A hxm]
      exact .inl ⟨hxN, hxm⟩
    by_cases hj : j ∈ A.I m
    · have hA := A.openCell_subset_of_mem hj ⟨y, mem_ball_zero_iff.2 hy, rfl⟩
      rw [stage_of_mem A hA]
      exact .inr hA
    obtain ⟨h2, hp⟩ := ((map_mem_radialNeighborhood_iff A j hy.le).1 hxN).resolve_left hj
    rw [stage_map A hj 1 hy.le, radialPush_one_of_le_norm (by norm_num) h2.le]
    exact .inl ⟨hp, map_inv_norm_smul_mem_skeletonLT j h2.le⟩
  · rw [stage_of_mem A hxA]
    exact .inr hxA

end

/-- Stage `m` runs during the time interval `[2⁻¹ ^ (m + 1), 2⁻¹ ^ m]`. -/
private def stageTime (m : ℕ) (t : I) : I :=
  projIcc 0 1 zero_le_one (2 ^ (m + 1) * (t : ℝ) - 1)

private lemma stageTime_def (m : ℕ) (t : I) :
    stageTime m t = projIcc 0 1 zero_le_one (2 ^ (m + 1) * (t : ℝ) - 1) :=
  rfl

private lemma continuous_stageTime (m : ℕ) : Continuous (stageTime m) :=
  continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private lemma stageTime_of_le {m : ℕ} {t : I} (ht : (t : ℝ) ≤ ((2 : ℝ) ^ (m + 1))⁻¹) :
    stageTime m t = 0 := by
  refine projIcc_of_le_left _ ?_
  rw [sub_nonpos, ← le_div_iff₀' (by positivity), one_div]
  exact ht

private lemma stageTime_of_ge {m : ℕ} {t : I} (ht : ((2 : ℝ) ^ m)⁻¹ ≤ t) : stageTime m t = 1 := by
  refine projIcc_of_right_le _ ?_
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have : (1 : ℝ) ≤ 2 ^ m * t := by rwa [inv_le_iff_one_le_mul₀' h2] at ht
  rw [pow_succ]
  nlinarith

private lemma stageTime_one (m : ℕ) : stageTime m 1 = 1 :=
  stageTime_of_ge (by simpa using inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))

/-- The stages `0, …, m` at time `t`, the higher ones first. -/
private def stagesUpTo : ℕ → I → X → X
  | 0, t, x => stage A 0 (stageTime 0 t) x
  | m + 1, t, x => stagesUpTo m t (stage A (m + 1) (stageTime (m + 1) t) x)

private lemma stagesUpTo_succ (m : ℕ) (t : I) (x : X) :
    stagesUpTo A (m + 1) t x = stagesUpTo A m t (stage A (m + 1) (stageTime (m + 1) t) x) :=
  rfl

/-- Before time `2⁻¹ ^ (m + 1)` the stages `0, …, m` have not started. -/
private lemma stagesUpTo_of_le {m : ℕ} {t : I} (ht : (t : ℝ) ≤ ((2 : ℝ) ^ (m + 1))⁻¹) (x : X) :
    stagesUpTo A m t x = x := by
  induction m generalizing x with
  | zero => rw [stagesUpTo, stageTime_of_le ht, stage_zero]
  | succ m ih =>
    rw [stagesUpTo_succ, stageTime_of_le ht, stage_zero]
    refine ih (ht.trans ?_) x
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (Nat.le_succ _))

private lemma stagesUpTo_zero (m : ℕ) (x : X) : stagesUpTo A m 0 x = x :=
  stagesUpTo_of_le A (by simp) x

private lemma stagesUpTo_of_mem {m : ℕ} (t : I) {x : X} (hx : x ∈ A) :
    stagesUpTo A m t x = x := by
  induction m with
  | zero => exact stage_of_mem A hx
  | succ m ih => rw [stagesUpTo_succ, stage_of_mem A hx, ih]

variable [T2Space X]

private lemma stagesUpTo_mem {m : ℕ} (t : I) {x : X} (hx : x ∈ A.radialNeighborhood) :
    stagesUpTo A m t x ∈ A.radialNeighborhood := by
  induction m generalizing x with
  | zero => exact stage_mem A _ hx
  | succ m ih => exact ih (stage_mem A _ hx)

/-- The stages above the dimension of a point fix it. -/
private lemma stagesUpTo_eq_of_le {M M' : ℕ} (h : M ≤ M') (t : I) {x : X}
    (hx : x ∈ (skeletonLT C ((M + 1 : ℕ) : ℕ∞) : Set X)) :
    stagesUpTo A M' t x = stagesUpTo A M t x := by
  induction M', h using Nat.le_induction with
  | base => rfl
  | succ M' h ih =>
    rw [stagesUpTo_succ, stage_of_mem_skeletonLT A
      (skeletonLT_mono (by exact_mod_cast Nat.succ_le_succ h) hx), ih]

/-- At time `1`, the stages carry the radial neighborhood into `A`. -/
private lemma stagesUpTo_one_mem {m : ℕ} {x : X}
    (hx : x ∈ A.radialNeighborhood ∩ (skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) ∪ A) :
    stagesUpTo A m 1 x ∈ A := by
  induction m generalizing x with
  | zero =>
    have h := stage_one_mem A hx
    rw [stagesUpTo, stageTime_one]
    obtain ⟨-, h⟩ | h := h
    · exact A.base_subset (by simpa [skeletonLT_zero_eq_base] using h)
    · exact h
  | succ m ih =>
    rw [stagesUpTo_succ, stageTime_one]
    exact ih (stage_one_mem A hx)

/-- The **radial deformation** of the radial neighborhood of `A`. It pushes the outer half of each
open `m`-cell outside `A` radially onto the frontier of the cell, during the time interval
`[2⁻¹ ^ (m + 1), 2⁻¹ ^ m]`, so on each skeleton only finitely many of these pushes act
(`Topology.RelCWComplex.Subcomplex.radialDeformation_map_of_le`,
`Topology.RelCWComplex.Subcomplex.radialDeformation_map_of_ge`). It is continuous on the radial
neighborhood (`Topology.RelCWComplex.Subcomplex.continuousOn_radialDeformation`), keeps it inside
itself, fixes `A`, is the identity at time `0` and carries the radial neighborhood into `A` at
time `1`. -/
def radialDeformation (t : I) (x : X) : X :=
  open Classical in
  stagesUpTo A (if h : ∃ M, x ∈ (skeletonLT C ((M + 1 : ℕ) : ℕ∞) : Set X) then Nat.find h else 0)
    t x

private lemma radialDeformation_eq {M : ℕ} (t : I) {x : X}
    (hx : x ∈ (skeletonLT C ((M + 1 : ℕ) : ℕ∞) : Set X)) :
    A.radialDeformation t x = stagesUpTo A M t x := by
  classical
  have h : ∃ M, x ∈ (skeletonLT C ((M + 1 : ℕ) : ℕ∞) : Set X) := ⟨M, hx⟩
  rw [radialDeformation, dite_eq_left h]
  exact (stagesUpTo_eq_of_le A (Nat.find_min' h hx) t (Nat.find_spec h)).symm

/-- Every point of the complex lies in a skeleton `skeletonLT C (M + 1)` on which the radial
deformation is given by the stages `0, …, M`. -/
private lemma exists_mem_skeletonLT_radialDeformation_eq {x : X} (hx : x ∈ C) :
    ∃ M : ℕ, x ∈ (skeletonLT C ((M + 1 : ℕ) : ℕ∞) : Set X) ∧
      ∀ t, A.radialDeformation t x = stagesUpTo A M t x := by
  obtain ⟨M, hM⟩ := exists_mem_skeletonLT_add 1 hx
  rw [Nat.add_comm] at hM
  exact ⟨M, hM, fun t ↦ radialDeformation_eq A t hM⟩

/-- At time `0` the radial deformation is the identity. -/
@[simp]
lemma radialDeformation_zero (x : X) : A.radialDeformation 0 x = x :=
  stagesUpTo_zero A _ x

/-- The radial deformation fixes the points of `A` at all times. -/
@[simp]
lemma radialDeformation_of_mem (t : I) {x : X} (hx : x ∈ A) : A.radialDeformation t x = x :=
  stagesUpTo_of_mem A t hx

/-- The radial deformation keeps the radial neighborhood inside itself. -/
lemma radialDeformation_mem (t : I) {x : X} (hx : x ∈ A.radialNeighborhood) :
    A.radialDeformation t x ∈ A.radialNeighborhood := by
  obtain ⟨M, -, hM⟩ :=
    exists_mem_skeletonLT_radialDeformation_eq A (radialNeighborhood_subset_complex A hx)
  rw [hM]
  exact stagesUpTo_mem A t hx

/-- At time `1` the radial deformation carries the radial neighborhood into `A`. -/
lemma radialDeformation_one_mem {x : X} (hx : x ∈ A.radialNeighborhood) :
    A.radialDeformation 1 x ∈ A := by
  obtain ⟨M, hxM, hM⟩ :=
    exists_mem_skeletonLT_radialDeformation_eq A (radialNeighborhood_subset_complex A hx)
  rw [hM]
  exact stagesUpTo_one_mem A (.inl ⟨hx, hxM⟩)

/-- On a point of `skeletonLT C n`, the radial deformation is stationary until time `2⁻¹ ^ n`. -/
lemma radialDeformation_of_le {n : ℕ} {t : I} (ht : (t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹)
    {x : X} (hx : x ∈ (skeletonLT C (n : ℕ∞) : Set X)) :
    A.radialDeformation t x = x := by
  cases n with
  | zero =>
    rw [Nat.cast_zero, skeletonLT_zero_eq_base] at hx
    exact radialDeformation_of_mem A t (A.base_subset hx)
  | succ m => rw [radialDeformation_eq A t hx, stagesUpTo_of_le A ht]

/-- **The radial deformation on a closed cell outside `A`, until time `2⁻¹ ^ n`.** Until then, it
moves a point of a closed `n`-cell outside `A` by the radial push `TauCeti.radialPush 2⁻¹` of the
cell, at the time `2 ^ (n + 1) * t - 1` clamped to `[0, 1]`. -/
lemma radialDeformation_map_of_le {n : ℕ} {j : cell C n} (hj : j ∉ A.I n) {t : I}
    (ht : (t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹) {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    A.radialDeformation t (map n j y) =
      map n j (radialPush 2⁻¹ (projIcc 0 1 zero_le_one (2 ^ (n + 1) * (t : ℝ) - 1)) y) := by
  rw [radialDeformation_eq A t (map_mem_skeletonLT_succ j hy)]
  cases n with
  | zero => rw [stagesUpTo, stage_map A hj _ hy, stageTime_def]
  | succ m => rw [stagesUpTo_succ, stage_map A hj _ hy, stagesUpTo_of_le A ht, stageTime_def]

/-- **The radial deformation on a closed cell outside `A`, from time `2⁻¹ ^ n` on.** By then a
point of the outer half of a closed `n`-cell outside `A` has been pushed to the frontier, and it
moves as its radial projection `map n j (‖y‖⁻¹ • y)`. -/
lemma radialDeformation_map_of_ge {n : ℕ} {j : cell C n} (hj : j ∉ A.I n) {t : I}
    (ht : ((2 : ℝ) ^ n)⁻¹ ≤ t) {y : Fin n → ℝ} (hy2 : 2⁻¹ ≤ ‖y‖) (hy : ‖y‖ ≤ 1) :
    A.radialDeformation t (map n j y) = A.radialDeformation t (map n j (‖y‖⁻¹ • y)) := by
  cases n with
  | zero => norm_num [Subsingleton.elim y 0] at hy2
  | succ m =>
    rw [radialDeformation_eq A t (map_mem_skeletonLT_succ j hy), stagesUpTo_succ,
      stage_map A hj _ hy, stageTime_of_ge ht, radialPush_one_of_le_norm (by norm_num) hy2,
      ← radialDeformation_eq A t (map_inv_norm_smul_mem_skeletonLT j hy2)]

/-- If the radial deformation is continuous along the closed cells of dimension below `n`, at the
points of the radial neighborhood, it is continuous on the radial neighborhood in
`skeletonLT C n`. -/
private lemma continuousOn_radialDeformation_skeletonLT {n : ℕ}
    (ih : ∀ m < n, ∀ j : cell C m, ContinuousOn
      (fun p : I × closedBall (0 : Fin m → ℝ) 1 ↦ radialDeformation A p.1 (map m j p.2))
      {p | map m j p.2 ∈ A.radialNeighborhood}) :
    ContinuousOn (fun p : I × X ↦ radialDeformation A p.1 p.2)
      (univ ×ˢ (A.radialNeighborhood ∩ (skeletonLT C (n : ℕ∞) : Set X))) := by
  refine continuousOn_prod_of_continuousOn_map (C := (skeletonLT C (n : ℕ∞) : Set X))
    inter_subset_right ?_ (fun m ⟨i, hi⟩ ↦ (ih m (by
      simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hi) i).mono
        fun p hp ↦ hp.1) ?_
  · convert (isOpen_preimage_val_radialNeighborhood A).preimage (continuous_subtype_val.subtype_mk
      fun x : (skeletonLT C (n : ℕ∞) : Set X) ↦ (skeletonLT C n).subset_complex x.2) using 1
    ext x
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, x.2⟩⟩
  · refine (continuous_subtype_val.comp continuous_snd).continuousOn.congr fun p _ ↦ ?_
    exact radialDeformation_of_mem A _ (A.base_subset p.2.2)

/-- **Continuity of the radial deformation along the closed cells**, at the points of the radial
neighborhood. -/
private lemma continuousOn_radialDeformation_map (n : ℕ) (j : cell C n) :
    ContinuousOn
      (fun p : I × closedBall (0 : Fin n → ℝ) 1 ↦ radialDeformation A p.1 (map n j p.2))
      {p | map n j p.2 ∈ A.radialNeighborhood} := by
  -- By induction on the dimension: on a cell outside `A` the deformation is the radial push until
  -- the point reaches the frontier, and from then on it is the deformation of the frontier point,
  -- in the lower skeleton.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hj : j ∈ A.I n
  · -- A closed cell of `A` is fixed.
    refine ((continuousOn n j).comp_continuous (continuous_subtype_val.comp continuous_snd)
      fun p ↦ p.2.2).continuousOn.congr fun p _ ↦ ?_
    exact radialDeformation_of_mem A _ (A.closedCell_subset_of_mem hj ⟨_, p.2.2, rfl⟩)
  -- The points of the radial neighborhood lie in the outer half of the cell, and their radial
  -- projections in the radial neighborhood.
  have hS : ∀ p ∈ {p : I × closedBall (0 : Fin n → ℝ) 1 | map n j p.2 ∈ A.radialNeighborhood},
      2⁻¹ < ‖(p.2 : Fin n → ℝ)‖ ∧ map n j (‖(p.2 : Fin n → ℝ)‖⁻¹ • p.2) ∈ A.radialNeighborhood :=
    fun p ↦ (map_mem_radialNeighborhood_iff_of_norm_le A hj (mem_closedBall_zero_iff.1 p.2.2)).1
  cases n with
  | zero =>
    -- There is no outer half in dimension `0`.
    intro p hp
    have h0 : ‖(p.2 : Fin 0 → ℝ)‖ = 0 := by rw [Subsingleton.elim (p.2 : Fin 0 → ℝ) 0, norm_zero]
    linarith [(hS p hp).1]
  | succ m =>
  let c : ℝ := ((2 : ℝ) ^ (m + 1))⁻¹
  let G : I × closedBall (0 : Fin (m + 1) → ℝ) 1 → X := fun p ↦
    if (p.1 : ℝ) ≤ c then map (m + 1) j (radialPush 2⁻¹ (stageTime (m + 1) p.1) p.2)
    else radialDeformation A p.1 (map (m + 1) j (‖(p.2 : Fin (m + 1) → ℝ)‖⁻¹ • p.2))
  have hG : ∀ p ∈ {p : I × closedBall (0 : Fin (m + 1) → ℝ) 1 |
      map (m + 1) j p.2 ∈ A.radialNeighborhood},
      radialDeformation A p.1 (map (m + 1) j p.2) = G p := by
    intro p hp
    have hp1 := mem_closedBall_zero_iff.1 p.2.2
    by_cases ht : (p.1 : ℝ) ≤ c
    · rw [radialDeformation_map_of_le A hj ht hp1]
      exact (ite_eq_left ht).symm
    · rw [radialDeformation_map_of_ge A hj (not_le.1 ht).le (hS p hp).1.le hp1]
      exact (ite_eq_right ht).symm
  refine ContinuousOn.congr ?_ hG
  have hc1 : Continuous fun p : I × closedBall (0 : Fin (m + 1) → ℝ) 1 ↦ (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  refine ContinuousOn.if ?_ ?_ ?_
  · -- At time `c` the push has reached the frontier, which is still stationary.
    intro p ⟨hp, hpf⟩
    have hpc : (p.1 : ℝ) = c := frontier_le_subset_eq hc1 continuous_const hpf
    obtain ⟨h2, -⟩ := hS p hp
    rw [stageTime_of_ge hpc.ge, radialPush_one_of_le_norm (by norm_num) h2.le,
      radialDeformation_of_le A hpc.le (map_inv_norm_smul_mem_skeletonLT j h2.le)]
  · refine ((continuousOn (m + 1) j).comp_continuous ?_ fun p ↦
      mem_closedBall_zero_iff.2 (norm_radialPush_le_one _
        (mem_closedBall_zero_iff.1 p.2.2))).continuousOn
    exact continuous_radialPush (E := Fin (m + 1) → ℝ) (by norm_num) |>.comp
      ((continuous_stageTime (m + 1)).comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd))
  · refine (continuousOn_radialDeformation_skeletonLT A ih).comp
      (continuous_fst.continuousOn.prodMk ?_) fun p hp ↦
      ⟨mem_univ _, (hS p hp.1).2, map_inv_norm_smul_mem_skeletonLT j (hS p hp.1).1.le⟩
    exact (continuousOn_map_inv_norm_smul (m + 1) j).comp continuous_snd.continuousOn
      fun p hp ↦ (hS p hp.1).1

/-- **The radial deformation is continuous on the radial neighborhood.** -/
lemma continuousOn_radialDeformation :
    ContinuousOn (fun p : I × X ↦ A.radialDeformation p.1 p.2) (univ ×ˢ A.radialNeighborhood) :=
  continuousOn_prod_of_continuousOn_map (radialNeighborhood_subset_complex A)
    (isOpen_preimage_val_radialNeighborhood A) (continuousOn_radialDeformation_map A)
    ((continuous_subtype_val.comp continuous_snd).continuousOn.congr fun p _ ↦
      radialDeformation_of_mem A _ (A.base_subset p.2.2))

private lemma continuous_radialDeformation_radialNeighborhood :
    Continuous fun p : I × A.radialNeighborhood ↦ A.radialDeformation p.1 p.2 :=
  (continuousOn_radialDeformation A).comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    fun p ↦ ⟨mem_univ _, p.2.2⟩

/-- The **radial retraction** of the radial neighborhood of `A` onto `A`: the radial deformation
`Topology.RelCWComplex.Subcomplex.radialDeformation` at time `1`. -/
def radialNeighborhoodRetraction : C(A.radialNeighborhood, A) where
  toFun x := ⟨A.radialDeformation 1 x, radialDeformation_one_mem A x.2⟩
  continuous_toFun := ((continuous_radialDeformation_radialNeighborhood A).comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

@[simp]
lemma coe_radialNeighborhoodRetraction_apply (x : A.radialNeighborhood) :
    (A.radialNeighborhoodRetraction x : X) = A.radialDeformation 1 x :=
  (rfl)

/-- The radial retraction fixes the points of `A`. -/
@[simp]
lemma radialNeighborhoodRetraction_inclusion (a : A) :
    A.radialNeighborhoodRetraction (Set.inclusion (subset_radialNeighborhood A) a) = a :=
  Subtype.ext (radialDeformation_of_mem A 1 a.2)

/-- The radial deformation `Topology.RelCWComplex.Subcomplex.radialDeformation`, as a homotopy
rel `A` from the identity of the radial neighborhood to the radial retraction
`Topology.RelCWComplex.Subcomplex.radialNeighborhoodRetraction` followed by the inclusion. -/
def radialNeighborhoodDeformation :
    (ContinuousMap.id A.radialNeighborhood).HomotopyRel
      ((ContinuousMap.inclusion (subset_radialNeighborhood A)).comp
        A.radialNeighborhoodRetraction) {x | (x : X) ∈ A} where
  toFun p := ⟨A.radialDeformation p.1 p.2, radialDeformation_mem A p.1 p.2.2⟩
  continuous_toFun := (continuous_radialDeformation_radialNeighborhood A).subtype_mk _
  map_zero_left x := Subtype.ext (radialDeformation_zero A x)
  map_one_left _ := rfl
  prop' t _ hx := Subtype.ext (radialDeformation_of_mem A t hx)

@[simp]
lemma coe_radialNeighborhoodDeformation_apply (p : I × A.radialNeighborhood) :
    (A.radialNeighborhoodDeformation p : X) = A.radialDeformation p.1 p.2 :=
  (rfl)

/-- **A subcomplex is a strong deformation retract of its radial neighborhood** (Hatcher,
Proposition A.5). Explicit witnesses are
`Topology.RelCWComplex.Subcomplex.radialNeighborhoodRetraction` and
`Topology.RelCWComplex.Subcomplex.radialNeighborhoodDeformation`. -/
theorem exists_strong_deformation_retraction_radialNeighborhood :
    ∃ r : C(A.radialNeighborhood, A),
      (∀ a, r (ContinuousMap.inclusion (subset_radialNeighborhood A) a) = a) ∧
      Nonempty (((ContinuousMap.inclusion (subset_radialNeighborhood A)).comp r).HomotopyRel
        (.id A.radialNeighborhood) {x | (x : X) ∈ A}) :=
  ⟨A.radialNeighborhoodRetraction, radialNeighborhoodRetraction_inclusion A,
    ⟨A.radialNeighborhoodDeformation.symm⟩⟩

end Topology.RelCWComplex.Subcomplex
