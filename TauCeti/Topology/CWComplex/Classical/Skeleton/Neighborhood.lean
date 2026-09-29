/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Topology.CWComplex.Classical.Quotient

/-!
# The skeleton with the cores of its top cells removed

Let `C` be a relative CW complex and `n : ℕ`, and write `Xⁿ = skeletonLT C (n + 1)` and
`Xⁿ⁻¹ = skeletonLT C n` for the skeleta made of the cells of dimension at most `n` and below `n`.
Removing from `Xⁿ` the image `map n j '' ball 0 2⁻¹` of the inner half of every open `n`-cell
leaves `TauCeti.skeletonNeighborhood C n`: `Xⁿ⁻¹` together with the outer halves of the open
`n`-cells.  It is a neighbourhood of `Xⁿ⁻¹` in `Xⁿ`, and it deformation retracts onto `Xⁿ⁻¹`, so
`(Xⁿ, Xⁿ⁻¹)` is a good pair in the sense of Hatcher.

The deformation is one homotopy `TauCeti.skeletonNeighborhoodHomotopy C n` of the whole of
`Xⁿ`, starting at the identity.  Inside each closed `n`-cell, read through the characteristic map,
it pushes
points radially outwards: the point `y` of the closed unit ball moves along the segment from `y`
to `2 • y` if `‖y‖ ≤ 2⁻¹`, and to `‖y‖⁻¹ • y` otherwise.  It fixes `Xⁿ⁻¹` pointwise at all times,
keeps `skeletonNeighborhood C n` inside itself at all times, and at the end sends
`skeletonNeighborhood C n` into `Xⁿ⁻¹`.  Consequently the inclusion of pairs
`(Xⁿ, Xⁿ⁻¹) ⟶ (Xⁿ, skeletonNeighborhood C n)` is a homotopy equivalence of pairs, while in the
second pair `Xⁿ⁻¹` lies in the interior of the subspace and can
be excised.

## Main definitions

* `TauCeti.skeletonNeighborhood C n`: `Xⁿ` minus the inner halves of the open `n`-cells.
* `TauCeti.skeletonNeighborhoodHomotopy C n`: the homotopy of `Xⁿ` from the identity to
  `TauCeti.skeletonNeighborhoodEndpoint C n`.

## Main results

* `TauCeti.isClosed_iUnion_map_closedBall`: the closed cores of radius `r < 1` of the open
  `n`-cells form a closed set.
* `TauCeti.skeletonLT_subset_interior_skeletonNeighborhood`: `skeletonNeighborhood C n` is a
  neighbourhood of `Xⁿ⁻¹` in `Xⁿ`.
* `TauCeti.skeletonNeighborhoodHomotopy_apply_of_mem`: the homotopy fixes `Xⁿ⁻¹`.
* `TauCeti.skeletonNeighborhoodHomotopy_mem`: the homotopy keeps
  `skeletonNeighborhood C n` inside itself.
* `TauCeti.skeletonNeighborhoodEndpoint_mem`: its endpoint sends
  `skeletonNeighborhood C n` into `Xⁿ⁻¹`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1 (good pairs) and Section 2.2, Lemma 2.34, whose proof uses that `(Xⁿ, Xⁿ⁻¹)` is a
  good pair.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

universe u v

namespace TauCeti

section Radial

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar form of the straight-line homotopy to the scaled radial retraction. -/
private def radialFactor (t : I) (y : E) : ℝ := (1 - (t : ℝ)) + (t : ℝ) * (max ‖y‖ 2⁻¹)⁻¹

/-- The radial push of the closed unit ball, interpolating with the scaled radial retraction. -/
private def radialPush (t : I) (y : E) : E :=
  (1 - (t : ℝ)) • y + (t : ℝ) • ((2 : ℝ) • radialRetraction 2⁻¹ y)

omit [NormedSpace ℝ E] in
private lemma max_norm_pos (y : E) : 0 < max ‖y‖ (2 : ℝ)⁻¹ :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

private lemma continuous_radialPush : Continuous fun p : I × E ↦ radialPush p.1 p.2 := by
  unfold radialPush
  refine ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    continuous_snd).add ?_
  refine (continuous_subtype_val.comp continuous_fst).smul ?_
  exact ((lipschitzWith_radialRetraction (E := E) (r := 2⁻¹)
    (by norm_num)).continuous.comp continuous_snd).const_smul (2 : ℝ)

private lemma radialPush_eq_factor (t : I) (y : E) :
    radialPush t y = radialFactor t y • y := by
  have hret : (2 : ℝ) • radialRetraction (2⁻¹ : ℝ) y =
      (max ‖y‖ 2⁻¹)⁻¹ • y := by
    rcases le_total ‖y‖ (2⁻¹ : ℝ) with h | h
    · rw [radialRetraction_of_norm_le h, max_eq_right h]
      simp [two_smul]
    · rw [radialRetraction_of_le_norm h, max_eq_left h]
      simp [div_eq_mul_inv, smul_smul]
  rw [radialPush, hret, smul_smul, ← add_smul]
  rfl

private lemma radialPush_zero (y : E) : radialPush 0 y = y := by
  simp [radialPush]

omit [NormedSpace ℝ E] in
private lemma one_le_radialFactor (t : I) {y : E} (hy : ‖y‖ ≤ 1) : 1 ≤ radialFactor t y := by
  have h : 1 ≤ (max ‖y‖ (2 : ℝ)⁻¹)⁻¹ :=
    one_le_inv₀ (max_norm_pos y) |>.2 (max_le hy (by norm_num))
  have ht := t.2.1
  unfold radialFactor
  nlinarith

private lemma norm_radialPush (t : I) {y : E} (hy : ‖y‖ ≤ 1) :
    ‖radialPush t y‖ = radialFactor t y * ‖y‖ := by
  rw [radialPush_eq_factor, norm_smul,
    Real.norm_of_nonneg (by linarith [one_le_radialFactor t hy])]

private lemma norm_le_norm_radialPush (t : I) {y : E} (hy : ‖y‖ ≤ 1) :
    ‖y‖ ≤ ‖radialPush t y‖ := by
  rw [norm_radialPush t hy]
  exact le_mul_of_one_le_left (norm_nonneg y) (one_le_radialFactor t hy)

private lemma norm_radialPush_le_one (t : I) {y : E} (hy : ‖y‖ ≤ 1) : ‖radialPush t y‖ ≤ 1 := by
  rw [norm_radialPush t hy, radialFactor, add_mul, mul_assoc]
  have h : (max ‖y‖ (2 : ℝ)⁻¹)⁻¹ * ‖y‖ ≤ 1 := by
    rw [inv_mul_le_iff₀ (max_norm_pos y), mul_one]
    exact le_max_left _ _
  have ht := t.2.1
  have ht' := t.2.2
  nlinarith [norm_nonneg y]

private lemma radialPush_of_norm_eq_one (t : I) {y : E} (hy : ‖y‖ = 1) : radialPush t y = y := by
  rw [radialPush_eq_factor]
  have h : max ‖y‖ (2 : ℝ)⁻¹ = 1 := by rw [hy]; norm_num
  simp [radialFactor, h]

private lemma norm_radialPush_one {y : E} (hy : (2 : ℝ)⁻¹ ≤ ‖y‖) : ‖radialPush 1 y‖ = 1 := by
  have h : ‖(2 : ℝ) • radialRetraction 2⁻¹ y‖ = 1 := by
    rw [norm_smul, norm_radialRetraction (by norm_num : 0 ≤ (2 : ℝ)⁻¹), min_eq_right hy]
    norm_num
  simpa [radialPush] using h

end Radial

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The `n`-skeleton `Xⁿ = skeletonLT C (n + 1)` of a relative CW complex with the inner half
`map n j '' ball 0 2⁻¹` of every open `n`-cell removed: `Xⁿ⁻¹ = skeletonLT C n` together with the
outer halves of the open `n`-cells.  It is a neighbourhood of `Xⁿ⁻¹` in `Xⁿ`
(`TauCeti.skeletonLT_subset_interior_skeletonNeighborhood`) which deformation retracts onto
`Xⁿ⁻¹` through `TauCeti.skeletonNeighborhoodHomotopy`. -/
def skeletonNeighborhood (n : ℕ) : Set X :=
  (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) \ ⋃ j : cell C n, map n j '' ball 0 2⁻¹

variable {C}

@[simp]
lemma mem_skeletonNeighborhood {n : ℕ} {x : X} :
    x ∈ skeletonNeighborhood C n ↔ x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ∧
      ∀ (j : cell C n) (y : Fin n → ℝ), ‖y‖ < 2⁻¹ → map n j y ≠ x := by
  simp [skeletonNeighborhood]

variable (C)

lemma skeletonNeighborhood_subset_skeletonLT_succ (n : ℕ) :
    skeletonNeighborhood C n ⊆ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) :=
  sdiff_subset

variable {C}

/-- The characteristic map of an `n`-cell sends the open unit ball into its open cell, which is
disjoint from `skeletonLT C n`. -/
private lemma map_notMem_skeletonLT {n : ℕ} (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ < 1) :
    map n j y ∉ (skeletonLT C (n : ℕ∞) : Set X) := fun h ↦
  (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left h ⟨y, mem_ball_zero_iff.2 hy, rfl⟩

omit [T2Space X] in
/-- Two points of open unit balls with the same image under characteristic maps of `n`-cells come
from the same cell and are equal. -/
private lemma map_eq_map_iff {n : ℕ} {i j : cell C n} {y z : Fin n → ℝ} (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) : map n i y = map n j z ↔ i = j ∧ y = z := by
  refine ⟨fun h ↦ ?_, fun ⟨hij, hyz⟩ ↦ hij ▸ hyz ▸ rfl⟩
  obtain rfl : i = j := by
    by_contra hne
    refine (disjoint_openCell_of_ne (by simpa using hne)).ne_of_mem
      ⟨y, mem_ball_zero_iff.2 hy, rfl⟩ ⟨z, mem_ball_zero_iff.2 hz, rfl⟩ h
  refine ⟨rfl, (map n i).injOn ?_ ?_ h⟩ <;> rw [source_eq] <;> simpa

/-- A point of `skeletonLT C (n + 1)` lies in `skeletonLT C n` or is the image of a point of the
open unit ball under the characteristic map of an `n`-cell. -/
private lemma mem_skeletonLT_or_exists_map {n : ℕ} {x : X}
    (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    x ∈ (skeletonLT C (n : ℕ∞) : Set X) ∨
      ∃ (j : cell C n) (y : Fin n → ℝ), ‖y‖ < 1 ∧ map n j y = x := by
  rw [Nat.cast_succ, ← skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ] at hx
  obtain hx | hx := hx
  · exact .inl hx
  obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.1 hx
  rcases (mem_closedBall_zero_iff.1 hy).lt_or_eq with hy | hy
  · exact .inr ⟨j, y, hy, rfl⟩
  · exact .inl (cellFrontier_subset_skeletonLT n j ⟨y, mem_sphere_zero_iff_norm.2 hy, rfl⟩)

lemma skeletonLT_subset_skeletonNeighborhood (n : ℕ) :
    (skeletonLT C (n : ℕ∞) : Set X) ⊆ skeletonNeighborhood C n := by
  refine fun x hx ↦ mem_skeletonNeighborhood.2 ⟨skeletonLT_mono (mod_cast n.le_succ) hx, ?_⟩
  rintro j y hy rfl
  exact map_notMem_skeletonLT j (hy.trans (by norm_num)) hx

/-- **The closed cores of the open `n`-cells form a closed set**: for `r < 1`, the union over all
`n`-cells of the images of the closed ball of radius `r` under the characteristic maps is closed.
Each core lies in its open cell, so it meets a closed cell only if that cell is its own, and
there the intersection is compact. -/
theorem isClosed_iUnion_map_closedBall (n : ℕ) {r : ℝ} (hr : r < 1) :
    IsClosed (⋃ j : cell C n, map n j '' closedBall 0 r) := by
  have hcore (j : cell C n) : map n j '' closedBall 0 r ⊆ openCell n j :=
    image_mono (closedBall_subset_ball hr)
  refine isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell (C := C) ?_ ?_
    fun m _ i ↦ ?_
  · exact iUnion_subset fun j ↦ (hcore j).trans (openCell_subset_complex n j)
  · convert isClosed_empty
    refine eq_empty_of_forall_notMem fun x ⟨hx, hxD⟩ ↦ ?_
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact (disjointBase n j).notMem_of_mem_left (hcore j hj) hxD
  by_cases hm : m = n
  · subst hm
    right
    -- Only the core of `i` meets the closed cell of `i`: a point of another open `m`-cell lies
    -- neither in the open cell of `i` nor in its frontier, which is in `skeletonLT C m`.
    convert (isCompact_closedBall (0 : Fin m → ℝ) r |>.image_of_continuousOn
      ((continuousOn m i).mono (closedBall_subset_closedBall hr.le))).isClosed using 1
    refine subset_antisymm (fun x ⟨hx, hxi⟩ ↦ ?_) fun x hx ↦
      ⟨mem_iUnion.2 ⟨i, hx⟩, openCell_subset_closedCell m i (hcore i hx)⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    rw [← cellFrontier_union_openCell_eq_closedCell] at hxi
    obtain hxi | hxi := hxi
    · exact absurd (hcore j hj) fun h ↦ (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left
        (cellFrontier_subset_skeletonLT m i hxi) h
    · obtain rfl : j = i := by
        by_contra hne
        exact (disjoint_openCell_of_ne (by simpa using hne)).notMem_of_mem_left (hcore j hj) hxi
      exact hj
  · left
    refine disjoint_iUnion_left.2 fun j ↦ ((disjoint_openCell_of_ne ?_).mono_left (hcore j))
    simp [Ne.symm hm]

variable (C) in
/-- **`TauCeti.skeletonNeighborhood C n` is a neighbourhood of `Xⁿ⁻¹ = skeletonLT C n` in
`Xⁿ = skeletonLT C (n + 1)`.** -/
theorem skeletonLT_subset_interior_skeletonNeighborhood (n : ℕ) :
    (Subtype.val ⁻¹' (skeletonLT C n : Set X) : Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) ⊆
      interior (Subtype.val ⁻¹' skeletonNeighborhood C n) := by
  -- The complement of the closed cores of radius `2⁻¹` is open, contains `skeletonLT C n`, and
  -- lies in `TauCeti.skeletonNeighborhood C n`.
  have hK := isClosed_iUnion_map_closedBall (C := C) n (r := 2⁻¹) (by norm_num)
  refine fun x hx ↦ interior_maximal (t := (Subtype.val ⁻¹'
    (⋃ j : cell C n, map n j '' closedBall 0 2⁻¹))ᶜ) (fun y hy ↦ ?_)
    (hK.preimage continuous_subtype_val).isOpen_compl ?_
  · refine mem_skeletonNeighborhood.2 ⟨y.2, fun j z hz h ↦ hy (mem_iUnion.2 ⟨j, z, ?_, h⟩)⟩
    exact mem_closedBall_zero_iff.2 hz.le
  · rintro hx'
    obtain ⟨j, y, hy, hxy⟩ := mem_iUnion.1 hx'
    exact map_notMem_skeletonLT j ((mem_closedBall_zero_iff.1 hy).trans_lt (by norm_num))
      (hxy ▸ hx)

/-- The radial push of the `n`-cells at time `t`, as a map of `X`: a point of an open `n`-cell is
pushed through the characteristic map, and every other point is fixed. -/
private def pushVal (n : ℕ) (p : I × X) : X :=
  open Classical in
  if h : ∃ (j : cell C n) (y : Fin n → ℝ), ‖y‖ < 1 ∧ map n j y = p.2 then
    map n h.choose (radialPush p.1 h.choose_spec.choose)
  else p.2

omit [T2Space X] in
private lemma pushVal_of_notMem {n : ℕ} {t : I} {x : X}
    (hx : ∀ (j : cell C n) (y : Fin n → ℝ), ‖y‖ < 1 → map n j y ≠ x) :
    pushVal (C := C) n (t, x) = x := by
  rw [pushVal, dite_eq_right fun ⟨j, y, hy, h⟩ ↦ hx j y hy h]

private lemma pushVal_of_mem_skeletonLT {n : ℕ} (t : I) {x : X}
    (hx : x ∈ (skeletonLT C (n : ℕ∞) : Set X)) : pushVal (C := C) n (t, x) = x :=
  pushVal_of_notMem fun j _ hy h ↦ map_notMem_skeletonLT j hy (h ▸ hx)

/-- Through the characteristic map of an `n`-cell, the radial push of the cells is the radial
push of the closed unit ball. -/
private lemma pushVal_map {n : ℕ} (t : I) (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    pushVal (C := C) n (t, map n j y) = map n j (radialPush t y) := by
  rcases hy.lt_or_eq with hy | hy
  · have h : ∃ (i : cell C n) (z : Fin n → ℝ), ‖z‖ < 1 ∧ map n i z = map n j y :=
      ⟨j, y, hy, rfl⟩
    obtain ⟨hij, hz⟩ := (map_eq_map_iff h.choose_spec.choose_spec.1 hy).1
      h.choose_spec.choose_spec.2
    rw [pushVal, dite_eq_left h]
    rw [hz, hij]
  · rw [radialPush_of_norm_eq_one t hy]
    exact pushVal_of_mem_skeletonLT t
      (cellFrontier_subset_skeletonLT n j ⟨y, mem_sphere_zero_iff_norm.2 hy, rfl⟩)

private lemma map_mem_skeletonLT_succ {n : ℕ} (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    map n j y ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  rw [Nat.cast_succ]
  exact closedCell_subset_skeletonLT n j ⟨y, mem_closedBall_zero_iff.2 hy, rfl⟩

private lemma pushVal_mem {n : ℕ} (t : I) {x : X}
    (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    pushVal (C := C) n (t, x) ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  obtain hx' | ⟨j, y, hy, rfl⟩ := mem_skeletonLT_or_exists_map hx
  · rwa [pushVal_of_mem_skeletonLT t hx']
  · rw [pushVal_map t j hy.le]
    exact map_mem_skeletonLT_succ j (norm_radialPush_le_one t hy.le)

private lemma continuous_pushVal (n : ℕ) :
    Continuous fun p : I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) ↦
      pushVal (C := C) n (p.1, p.2) := by
  rw [continuous_prod_complex_iff]
  refine ⟨fun m ⟨j, hj⟩ ↦ ?_, ?_⟩
  · have hm : m < n + 1 := by
      simpa only [RelCWComplex.skeletonLT_I, mem_ofPred_eq, Nat.cast_lt] using hj
    rcases (Nat.lt_succ_iff.1 hm).lt_or_eq with hm | rfl
    · -- A cell of dimension below `n` lies in `skeletonLT C n`, which the push fixes.
      refine ((continuousOn m j).comp_continuous (continuous_subtype_val.comp continuous_snd)
        fun p ↦ p.2.2).congr fun p ↦ (pushVal_of_mem_skeletonLT p.1 ?_).symm
      exact skeletonLT_mono (mod_cast hm) (closedCell_subset_skeletonLT m j ⟨p.2, p.2.2, rfl⟩)
    · -- On an `n`-cell the push is the radial push of the closed unit ball.
      have hball (p : I × closedBall (0 : Fin m → ℝ) 1) :
          ‖radialPush p.1 (p.2 : Fin m → ℝ)‖ ≤ 1 :=
        norm_radialPush_le_one p.1 (mem_closedBall_zero_iff.1 p.2.2)
      refine ((continuousOn m j).comp_continuous (continuous_radialPush.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
        fun p ↦ mem_closedBall_zero_iff.2 (hball p)).congr fun p ↦ ?_
      exact (pushVal_map p.1 j (mem_closedBall_zero_iff.1 p.2.2)).symm
  · -- The base lies in `skeletonLT C n`, which the push fixes.
    exact (continuous_subtype_val.comp continuous_snd).congr fun p ↦
      (pushVal_of_mem_skeletonLT p.1 ((skeletonLT C n).base_subset p.2.2)).symm

variable (C) in
/-- The radial push of the `n`-cells as a homotopy of `skeletonLT C (n + 1)`. -/
private def pushMap (n : ℕ) :
    C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :=
  ⟨fun p ↦ ⟨pushVal (C := C) n (p.1, p.2), pushVal_mem p.1 p.2.2⟩,
    (continuous_pushVal n).subtype_mk _⟩

private lemma pushMap_apply_coe {n : ℕ} (p : I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    (pushMap C n p : X) = pushVal (C := C) n (p.1, (p.2 : X)) :=
  (rfl)

variable (C) in
/-- The endpoint of `TauCeti.skeletonNeighborhoodHomotopy`: the self-map of
`Xⁿ = skeletonLT C (n + 1)`
which pushes the outer half of every open `n`-cell onto its boundary and expands the inner half
over the whole cell.  It sends `TauCeti.skeletonNeighborhood C n` into `Xⁿ⁻¹ = skeletonLT C n`. -/
def skeletonNeighborhoodEndpoint (n : ℕ) :
    C(skeletonLT C ((n + 1 : ℕ) : ℕ∞), skeletonLT C ((n + 1 : ℕ) : ℕ∞)) :=
  (pushMap C n).curry 1

variable (C) in
/-- The radial deformation of the `n`-skeleton `Xⁿ = skeletonLT C (n + 1)` of a relative CW
complex: inside each closed `n`-cell, read through the characteristic map, it moves `y` along the
segment from `y` to `2 • y` if `‖y‖ ≤ 2⁻¹` and to `‖y‖⁻¹ • y` otherwise.  It fixes
`Xⁿ⁻¹ = skeletonLT C n`, keeps `TauCeti.skeletonNeighborhood C n` inside itself, and ends at
`TauCeti.skeletonNeighborhoodEndpoint C n`. -/
def skeletonNeighborhoodHomotopy (n : ℕ) :
    (ContinuousMap.id _).Homotopy (skeletonNeighborhoodEndpoint C n) where
  toContinuousMap := pushMap C n
  map_zero_left x := by
    refine Subtype.ext ?_
    obtain hx | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
    · exact pushVal_of_mem_skeletonLT 0 hx
    · rw [ContinuousMap.toFun_eq_coe, pushMap_apply_coe, ContinuousMap.id_apply, ← hxy,
        pushVal_map 0 j hy.le, radialPush_zero]
  map_one_left _ := rfl

private lemma coe_skeletonNeighborhoodHomotopy_apply {n : ℕ} (t : I)
    (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    (skeletonNeighborhoodHomotopy C n (t, x) : X) = pushVal (C := C) n (t, (x : X)) :=
  (rfl)

/-- The deformation fixes `Xⁿ⁻¹ = skeletonLT C n` pointwise. -/
@[simp]
lemma skeletonNeighborhoodHomotopy_apply_of_mem {n : ℕ} (t : I)
    (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) (hx : (x : X) ∈ (skeletonLT C n : Set X)) :
    skeletonNeighborhoodHomotopy C n (t, x) = x :=
  Subtype.ext (pushVal_of_mem_skeletonLT t hx)

/-- The endpoint of the deformation fixes `Xⁿ⁻¹ = skeletonLT C n` pointwise. -/
@[simp]
lemma skeletonNeighborhoodEndpoint_apply_of_mem {n : ℕ}
    (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (hx : (x : X) ∈ (skeletonLT C n : Set X)) :
    skeletonNeighborhoodEndpoint C n x = x := by
  rw [← (skeletonNeighborhoodHomotopy C n).apply_one,
    skeletonNeighborhoodHomotopy_apply_of_mem 1 x hx]

/-- The deformation keeps `TauCeti.skeletonNeighborhood C n` inside itself at every time. -/
lemma skeletonNeighborhoodHomotopy_mem {n : ℕ} (t : I)
    (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (hx : (x : X) ∈ skeletonNeighborhood C n) :
    (skeletonNeighborhoodHomotopy C n (t, x) : X) ∈ skeletonNeighborhood C n := by
  obtain hx' | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
  · rw [skeletonNeighborhoodHomotopy_apply_of_mem t x hx']
    exact hx
  have hy2 : (2 : ℝ)⁻¹ ≤ ‖y‖ := not_lt.1 fun h ↦ (mem_skeletonNeighborhood.1 hx).2 j y h hxy
  rw [coe_skeletonNeighborhoodHomotopy_apply, ← hxy, pushVal_map t j hy.le]
  set z := radialPush t y
  have hz : ‖y‖ ≤ ‖z‖ := norm_le_norm_radialPush t hy.le
  rcases (norm_radialPush_le_one t hy.le).lt_or_eq with hz1 | hz1
  · refine mem_skeletonNeighborhood.2 ⟨map_mem_skeletonLT_succ j hz1.le, fun i w hw h ↦ ?_⟩
    obtain ⟨-, rfl⟩ := (map_eq_map_iff (hw.trans (by norm_num)) hz1).1 h
    linarith
  · exact skeletonLT_subset_skeletonNeighborhood n
      (cellFrontier_subset_skeletonLT n j ⟨z, mem_sphere_zero_iff_norm.2 hz1, rfl⟩)

/-- The endpoint of the deformation sends `TauCeti.skeletonNeighborhood C n` into
`Xⁿ⁻¹ = skeletonLT C n`. -/
lemma skeletonNeighborhoodEndpoint_mem {n : ℕ} (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (hx : (x : X) ∈ skeletonNeighborhood C n) :
    (skeletonNeighborhoodEndpoint C n x : X) ∈ (skeletonLT C n : Set X) := by
  obtain hx' | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map x.2
  · rw [← (skeletonNeighborhoodHomotopy C n).apply_one,
      skeletonNeighborhoodHomotopy_apply_of_mem 1 x hx']
    exact hx'
  have hy2 : (2 : ℝ)⁻¹ ≤ ‖y‖ := not_lt.1 fun h ↦ (mem_skeletonNeighborhood.1 hx).2 j y h hxy
  rw [← (skeletonNeighborhoodHomotopy C n).apply_one, coe_skeletonNeighborhoodHomotopy_apply, ← hxy,
    pushVal_map 1 j hy.le]
  exact cellFrontier_subset_skeletonLT n j
    ⟨_, mem_sphere_zero_iff_norm.2 (norm_radialPush_one hy2), rfl⟩

end TauCeti
