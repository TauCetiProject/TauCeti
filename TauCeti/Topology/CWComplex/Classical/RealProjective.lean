/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Data.Fin.Basic
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# The CW structure on real projective space

Real projective space `RPⁿ`, the quotient of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` by the antipodal map
(`TauCeti.RealProjectiveSpace`), is a finite CW complex with one cell in each dimension
`0, 1, …, n` (`TauCeti.RealProjectiveSpace.cwComplex`).

Write `RPⁱ ⊆ RPⁿ` for the classes of unit vectors whose coordinates beyond `i` vanish. The open
`i`-cell is `RPⁱ ∖ RPⁱ⁻¹`, the classes of unit vectors `y` with `yᵢ ≠ 0` and `yⱼ = 0` for `j > i`
(`TauCeti.RealProjectiveSpace.openCell`). Its characteristic map
(`TauCeti.RealProjectiveSpace.cellMap`) sends a point `v` of the closed unit disk `Dⁱ` to the class
of the point `(v, √(1 - ‖v‖²), 0, …, 0)` of the upper hemisphere of `Sⁱ ⊆ Sⁿ`
(`TauCeti.RealProjectiveSpace.hemispherePoint`). Since every class in the open cell has exactly one
representative with `yᵢ > 0`, it maps the open disk bijectively onto the open cell, and on the
boundary sphere `Sⁱ⁻¹` it is the double cover `Sⁱ⁻¹ → RPⁱ⁻¹`, which lands in the cells of lower
dimension. The domains of the characteristic maps of Mathlib's `Topology.CWComplex` are closed
balls of the sup norm on `Fin i → ℝ`; they are carried onto Euclidean disks by the radial
homeomorphism `ContinuousLinearEquiv.unitBallHomeomorph`.

## Main declarations

* `TauCeti.RealProjectiveSpace.hemispherePoint`: the upper hemisphere of `Sⁱ ⊆ Sⁿ` over `Dⁱ`.
* `TauCeti.RealProjectiveSpace.openCell`: the open `i`-cell `RPⁱ ∖ RPⁱ⁻¹`.
* `TauCeti.RealProjectiveSpace.cellMap`: the characteristic map of the `i`-cell, with
  `TauCeti.RealProjectiveSpace.cellMap_apply` its formula on the closed ball and
  `TauCeti.RealProjectiveSpace.cellMap_symm_mk` the formula for its inverse.
* `TauCeti.RealProjectiveSpace.cwComplex`: the CW structure on `RPⁿ`, with characteristic maps
  `cellMap` (`TauCeti.RealProjectiveSpace.map_cwComplex`); it is finite
  (`TauCeti.RealProjectiveSpace.finite_cwComplex`) with one cell in each dimension `m ≤ n`
  (`TauCeti.RealProjectiveSpace.nat_card_cell_cwComplex`).
* `TauCeti.RealProjectiveSpace.finiteCWType`: `RPⁿ` has finite CW type.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.4.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace RealProjectiveSpace

variable {n : ℕ}

variable (n) in
/-- The point of the upper hemisphere of `Sᵏ ⊆ Sⁿ` lying over `v ∈ ℝᵏ`: its first `k`
coordinates are those of `v`, its coordinate `k` is `√(1 - ‖v‖²)`, and the remaining ones vanish.
For `k ≤ n` and `‖v‖ ≤ 1` it lies on the unit sphere (`norm_hemispherePoint`). This is the
coordinate form, for `p = eₖ` and composed with the inclusion `Sᵏ ⊆ Sⁿ`, of the lift
`y ↦ y + √(1 - ‖y‖²) • p` inverting `TauCeti.hemisphereHomeomorph`. -/
def hemispherePoint {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun j =>
    if h : (j : ℕ) < k then v ⟨j, h⟩ else if (j : ℕ) = k then √(1 - ‖v‖ ^ 2) else 0

/-- The coordinates of `hemispherePoint n v` before `k` are those of `v`. -/
theorem hemispherePoint_apply_of_lt {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) {j : Fin (n + 1)}
    (hj : (j : ℕ) < k) : hemispherePoint n v j = v ⟨j, hj⟩ := by
  simp [hemispherePoint, hj]

/-- The coordinate `k` of `hemispherePoint n v` is `√(1 - ‖v‖²)`. -/
theorem hemispherePoint_apply_of_eq {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) {j : Fin (n + 1)}
    (hj : (j : ℕ) = k) : hemispherePoint n v j = √(1 - ‖v‖ ^ 2) := by
  simp [hemispherePoint, hj]

/-- The coordinates of `hemispherePoint n v` beyond `k` vanish. -/
theorem hemispherePoint_apply_of_gt {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) {j : Fin (n + 1)}
    (hj : k < (j : ℕ)) : hemispherePoint n v j = 0 := by
  simp [hemispherePoint, hj.not_gt, hj.ne']

/-- `hemispherePoint n` is continuous. -/
theorem continuous_hemispherePoint {k : ℕ} :
    Continuous (hemispherePoint n : EuclideanSpace ℝ (Fin k) → _) :=
  (PiLp.continuous_toLp _ _).comp <| continuous_pi fun j => by
    split_ifs <;> fun_prop

/-- For `k ≤ n`, `hemispherePoint n` maps the closed unit disk of `ℝᵏ` into the unit sphere
of `ℝⁿ⁺¹`. -/
theorem norm_hemispherePoint {k : ℕ} {v : EuclideanSpace ℝ (Fin k)} (hk : k ≤ n)
    (hv : ‖v‖ ≤ 1) : ‖hemispherePoint n v‖ = 1 := by
  have hsq : ‖hemispherePoint n v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_eq_sum_castLE_add ⟨k, by omega⟩ _
      fun j hj => by rw [hemispherePoint_apply_of_gt v hj, sq, zero_mul],
      hemispherePoint_apply_of_eq v rfl,
      Real.sq_sqrt (by nlinarith [norm_nonneg v] : 0 ≤ 1 - ‖v‖ ^ 2)]
    have hc (j : Fin k) : hemispherePoint n v (Fin.castLE (by omega) j) = v j := by
      simp [hemispherePoint]
    simp only [hc, ← EuclideanSpace.real_norm_sq_eq v]
    ring
  nlinarith [norm_nonneg (hemispherePoint n v)]

/-- The first `i` coordinates of a vector of `ℝⁿ⁺¹`. -/
private def truncate (i : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin i) :=
  WithLp.toLp 2 fun j => y (Fin.castLE i.is_lt.le j)

private theorem continuous_truncate (i : Fin (n + 1)) : Continuous (truncate i) :=
  (PiLp.continuous_toLp _ _).comp <| continuous_pi fun _ => PiLp.continuous_apply _ _ _

private theorem truncate_neg (i : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    truncate i (-y) = -truncate i y := by
  ext j
  simp [truncate]

private theorem truncate_hemispherePoint (i : Fin (n + 1)) (v : EuclideanSpace ℝ (Fin i)) :
    truncate i (hemispherePoint n v) = v := by
  ext j
  simp [truncate, hemispherePoint_apply_of_lt v (j := Fin.castLE i.is_lt.le j) j.is_lt]

/-- For a vector whose coordinates beyond `i` vanish, the squared norm splits into that of its
first `i` coordinates and the square of coordinate `i`. -/
private theorem norm_truncate_sq_add_sq {i : Fin (n + 1)} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : ∀ j : Fin (n + 1), i < j → y j = 0) : ‖truncate i y‖ ^ 2 + y i ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_eq_sum_castLE_add i _ fun j hj => by rw [hy j hj, sq, zero_mul]]
  simp [truncate]

variable (n) in
/-- The open `i`-cell of `RPⁿ`: the classes of the unit vectors whose coordinate `i` is nonzero
and whose later coordinates vanish. -/
def openCell (i : Fin (n + 1)) : Set (RealProjectiveSpace n) :=
  mk n '' {y | (y : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0 ∧
    ∀ j : Fin (n + 1), i < j → (y : EuclideanSpace ℝ (Fin (n + 1))) j = 0}

/-- The class of a unit vector `y` lies in the open `i`-cell exactly when `yᵢ ≠ 0` and the
coordinates of `y` beyond `i` vanish. -/
@[simp]
theorem mk_mem_openCell_iff {i : Fin (n + 1)}
    {y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1} :
    mk n y ∈ openCell n i ↔ (y : EuclideanSpace ℝ (Fin (n + 1))) i ≠ 0 ∧
      ∀ j : Fin (n + 1), i < j → (y : EuclideanSpace ℝ (Fin (n + 1))) j = 0 := by
  refine ⟨?_, fun hy => ⟨y, hy, rfl⟩⟩
  rintro ⟨y', hy', h⟩
  obtain rfl | rfl := (mk_eq_mk_iff n y' y).1 h
  · exact hy'
  · simpa [coe_neg_sphere] using hy'

/-- Distinct open cells of `RPⁿ` are disjoint. -/
theorem disjoint_openCell {i i' : Fin (n + 1)} (h : i ≠ i') :
    Disjoint (openCell n i) (openCell n i') := by
  wlog hlt : i < i' generalizing i i'
  · exact (this h.symm (lt_of_le_of_ne (not_lt.1 hlt) h.symm)).symm
  refine Set.disjoint_left.2 fun p hp hp' => ?_
  obtain ⟨y, rfl⟩ := mk_surjective n p
  exact (mk_mem_openCell_iff.1 hp').1 ((mk_mem_openCell_iff.1 hp).2 i' hlt)

/-- The class of a unit vector whose coordinates from `k` on vanish lies in an open cell of
dimension less than `k`: the one indexed by its last nonzero coordinate. -/
theorem exists_lt_mk_mem_openCell (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) {k : ℕ}
    (hy : ∀ j : Fin (n + 1), k ≤ j → (y : EuclideanSpace ℝ (Fin (n + 1))) j = 0) :
    ∃ i : Fin (n + 1), (i : ℕ) < k ∧ mk n y ∈ openCell n i := by
  set S := Finset.univ.filter fun j : Fin (n + 1) => (y : EuclideanSpace ℝ (Fin (n + 1))) j ≠ 0
  have hS : S.Nonempty := by
    by_contra hS
    have h0 : (y : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
      ext j
      by_contra hj
      exact hS ⟨j, by simpa [S] using hj⟩
    simpa [h0] using norm_eq_of_mem_sphere y
  have hmem := Finset.mem_filter.1 (S.max'_mem hS)
  refine ⟨S.max' hS, ?_, mk_mem_openCell_iff.2 ⟨hmem.2, fun j hj => ?_⟩⟩
  · by_contra hk
    exact hmem.2 (hy _ (not_lt.1 hk))
  · by_contra hj'
    exact (S.le_max' j (by simpa [S] using hj')).not_gt hj

/-- The first `i` coordinates of whichever of `±y` has positive coordinate `i`, read in the
sup-norm ball through the radial homeomorphism. -/
private def cellChart (i : Fin (n + 1)) (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Fin i → ℝ :=
  (EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph ((y.1 i / |y.1 i|) • truncate i y.1)

private theorem cellChart_neg (i : Fin (n + 1))
    (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    cellChart i (-y) = cellChart i y := by
  simp only [cellChart, coe_neg_sphere, truncate_neg, PiLp.neg_apply, abs_neg, neg_div, neg_smul,
    smul_neg, neg_neg]

/-- The inverse of the characteristic map of the `i`-cell on the open cell. -/
private def cellMapInv (i : Fin (n + 1)) : RealProjectiveSpace n → (Fin i → ℝ) :=
  RealProjectiveSpace.lift n (cellChart i) (cellChart_neg i)

private theorem cellMapInv_mk (i : Fin (n + 1))
    (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    cellMapInv i (mk n y) = (EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph
      ((y.1 i / |y.1 i|) • truncate i y.1) :=
  RealProjectiveSpace.lift_mk n _ (cellChart_neg i) y

/-- The point of `Sⁿ` over a point `x` of the closed sup-norm ball of `Fin i → ℝ`: the radial
homeomorphism onto the Euclidean disk, followed by `hemispherePoint`. -/
private def cellSpherePoint (i : Fin (n + 1)) (x : closedBall (0 : Fin i → ℝ) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨hemispherePoint n ((EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph.symm x),
    mem_sphere_zero_iff_norm.2 (norm_hemispherePoint i.is_le
      ((EuclideanSpace.equiv (Fin i) ℝ).norm_unitBallHomeomorph_symm_le_one_iff.2
        (mem_closedBall_zero_iff.1 x.2)))⟩

open scoped Classical in
/-- The characteristic map of the `i`-cell of `RPⁿ` (Hatcher, Example 0.4). On the closed unit
ball of `Fin i → ℝ` with the sup norm, it is the radial homeomorphism onto the Euclidean disk `Dⁱ`
followed by the upper hemisphere `hemispherePoint` of `Sⁱ ⊆ Sⁿ` and the quotient map to `RPⁿ`
(`cellMap_apply`). It maps the open ball bijectively onto `openCell n i`. -/
def cellMap (i : Fin (n + 1)) : PartialEquiv (Fin i → ℝ) (RealProjectiveSpace n) where
  toFun x := if hx : x ∈ closedBall 0 1 then mk n (cellSpherePoint i ⟨x, hx⟩)
    else Classical.arbitrary _
  invFun := cellMapInv i
  source := ball 0 1
  target := openCell n i
  map_source' x hx := by
    rw [dite_eq_left (ball_subset_closedBall hx), mk_mem_openCell_iff]
    refine ⟨?_, fun j hj => hemispherePoint_apply_of_gt _ hj⟩
    set v := (EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph.symm x
    have hv : ‖v‖ < 1 := by simpa [v] using hx
    rw [cellSpherePoint, hemispherePoint_apply_of_eq _ rfl]
    exact (Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])).ne'
  map_target' p hp := by
    obtain ⟨y, rfl⟩ := mk_surjective n p
    obtain ⟨hyi, hy⟩ := mk_mem_openCell_iff.1 hp
    have hnorm := norm_truncate_sq_add_sq hy
    rw [norm_eq_of_mem_sphere y] at hnorm
    simp only [cellMapInv_mk, mem_ball_zero_iff,
      ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff, norm_smul, norm_div,
      Real.norm_eq_abs, abs_abs, div_self (abs_ne_zero.2 hyi), one_mul]
    nlinarith [norm_nonneg (truncate i y.1), sq_pos_of_ne_zero hyi]
  left_inv' x hx := by
    set v := (EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph.symm x with hv_def
    have hv : ‖v‖ < 1 := by simpa [v] using hx
    have hpos : 0 < hemispherePoint n v i := by
      rw [hemispherePoint_apply_of_eq _ rfl]
      exact Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])
    rw [dite_eq_left (ball_subset_closedBall hx), cellMapInv_mk, cellSpherePoint,
      abs_of_pos hpos, div_self hpos.ne', one_smul, truncate_hemispherePoint,
      Homeomorph.apply_symm_apply]
  right_inv' p hp := by
    obtain ⟨y, rfl⟩ := mk_surjective n p
    obtain ⟨hyi, hy⟩ := mk_mem_openCell_iff.1 hp
    set s := y.1 i / |y.1 i| with hs
    have habs : |s| = 1 := by rw [hs, abs_div, abs_abs, div_self (abs_ne_zero.2 hyi)]
    have hsy : s * y.1 i = |y.1 i| := by
      rw [hs, div_mul_eq_mul_div, ← sq, ← sq_abs, sq, mul_self_div_self]
    have hnorm := norm_truncate_sq_add_sq hy
    rw [norm_eq_of_mem_sphere y, one_pow] at hnorm
    have hw : ‖s • truncate i y.1‖ = ‖truncate i y.1‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs, one_mul]
    have hx : cellMapInv i (mk n y) ∈ closedBall 0 1 := by
      rw [cellMapInv_mk, mem_closedBall_zero_iff,
        ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff, hw]
      nlinarith [norm_nonneg (truncate i y.1), sq_nonneg (y.1 i)]
    have key : (cellSpherePoint i ⟨_, hx⟩ : EuclideanSpace ℝ (Fin (n + 1))) = s • y.1 := by
      simp only [cellSpherePoint, cellMapInv_mk, Homeomorph.symm_apply_apply]
      ext j
      rcases lt_trichotomy (j : ℕ) i with h | h | h
      · rw [hemispherePoint_apply_of_lt _ h]
        simp [truncate, Fin.castLE, hs]
      · rw [hemispherePoint_apply_of_eq _ h, hw, show j = i from Fin.ext h, PiLp.smul_apply,
          smul_eq_mul, hsy, show 1 - ‖truncate i y.1‖ ^ 2 = y.1 i ^ 2 by linarith,
          Real.sqrt_sq_eq_abs]
      · rw [hemispherePoint_apply_of_gt _ h, PiLp.smul_apply, hy j (Fin.lt_def.2 h), smul_zero]
    rw [dite_eq_left hx, mk_eq_mk_iff]
    rcases (abs_eq zero_le_one).1 habs with h | h
    · exact Or.inl (Subtype.ext (by rw [key, h, one_smul]))
    · exact Or.inr (Subtype.ext (by rw [key, h, coe_neg_sphere, neg_one_smul]))

/-- The source of the characteristic map of the `i`-cell is the open unit ball. -/
@[simp]
theorem cellMap_source (i : Fin (n + 1)) : (cellMap i).source = ball 0 1 :=
  (rfl)

/-- The target of the characteristic map of the `i`-cell is the open `i`-cell. -/
@[simp]
theorem cellMap_target (i : Fin (n + 1)) : (cellMap i).target = openCell n i :=
  (rfl)

/-- On the closed unit ball, the characteristic map of the `i`-cell is the radial homeomorphism
onto the Euclidean disk followed by `hemispherePoint` and the quotient map. -/
theorem cellMap_apply (i : Fin (n + 1)) {x : Fin i → ℝ} (hx : x ∈ closedBall 0 1) :
    cellMap i x = mk n ⟨hemispherePoint n
      ((EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph.symm x),
      mem_sphere_zero_iff_norm.2 (norm_hemispherePoint i.is_le
        ((EuclideanSpace.equiv (Fin i) ℝ).norm_unitBallHomeomorph_symm_le_one_iff.2
          (mem_closedBall_zero_iff.1 hx)))⟩ :=
  dite_eq_left hx

/-- The inverse of the characteristic map of the `i`-cell sends the class of a unit vector `y` to
its first `i` coordinates, multiplied by the sign `yᵢ / |yᵢ|` of its coordinate `i` and read in the
sup-norm ball through the radial homeomorphism. On the open cell, where `yᵢ ≠ 0`, this is the
truncation of whichever of `±y` has positive coordinate `i`. -/
theorem cellMap_symm_mk (i : Fin (n + 1)) (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (cellMap i).symm (mk n y) = (EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph
      ((y.1 i / |y.1 i|) • WithLp.toLp 2 fun j => y.1 (Fin.castLE i.is_lt.le j)) :=
  cellMapInv_mk i y

/-- The characteristic map of the `i`-cell maps the open unit ball onto the open `i`-cell. -/
theorem image_cellMap_ball (i : Fin (n + 1)) : cellMap i '' ball 0 1 = openCell n i :=
  (cellMap i).image_source_eq_target

/-- The characteristic map of the `i`-cell is continuous on the closed unit ball. -/
theorem continuousOn_cellMap (i : Fin (n + 1)) : ContinuousOn (cellMap i) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (cellSpherePoint i) := (continuous_hemispherePoint.comp
    ((Homeomorph.continuous _).comp continuous_subtype_val)).subtype_mk _
  exact ((continuous_mk n).comp hc).congr fun x => (cellMap_apply i x.2).symm

/-- The inverse of the characteristic map of the `i`-cell is continuous on the open `i`-cell. -/
theorem continuousOn_cellMap_symm (i : Fin (n + 1)) :
    ContinuousOn (cellMap i).symm (cellMap i).target := by
  intro p hp
  obtain ⟨y, rfl⟩ := mk_surjective n p
  have hyi := (mk_mem_openCell_iff.1 hp).1
  have hc : Continuous fun y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 => y.1 i :=
    (PiLp.continuous_apply _ _ _).comp continuous_subtype_val
  refine (continuousAt_lift n (cellChart_neg i) ?_).continuousWithinAt
  exact (Homeomorph.continuous _).continuousAt.comp ((hc.continuousAt.div hc.continuousAt.abs
    (abs_ne_zero.2 hyi)).smul ((continuous_truncate i).comp continuous_subtype_val).continuousAt)

/-- The characteristic map of the `i`-cell sends the boundary sphere of the sup-norm ball into the
open cells of dimension less than `i`. -/
theorem exists_lt_cellMap_mem_openCell (i : Fin (n + 1)) {x : Fin i → ℝ}
    (hx : x ∈ sphere 0 1) : ∃ i' : Fin (n + 1), i' < i ∧ cellMap i x ∈ openCell n i' := by
  have hv : ‖(EuclideanSpace.equiv (Fin i) ℝ).unitBallHomeomorph.symm x‖ = 1 := by
    simpa using hx
  rw [cellMap_apply i (sphere_subset_closedBall hx)]
  refine exists_lt_mk_mem_openCell _ fun j hj => ?_
  rcases hj.eq_or_lt with h | h
  · rw [hemispherePoint_apply_of_eq _ h.symm, hv]
    simp
  · exact hemispherePoint_apply_of_gt _ h

/-- The closed cells cover `RPⁿ`. -/
theorem iUnion_image_cellMap_closedBall :
    ⋃ i : Fin (n + 1), cellMap i '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun p => ?_
  obtain ⟨y, rfl⟩ := mk_surjective n p
  obtain ⟨i, -, hi⟩ := exists_lt_mk_mem_openCell y (k := n + 1) fun j hj => absurd j.is_lt hj.not_gt
  rw [← image_cellMap_ball] at hi
  exact mem_iUnion.2 ⟨i, image_mono ball_subset_closedBall hi⟩

variable (n) in
/-- The cells of dimension `m` of the CW structure on `RPⁿ`: one if `m ≤ n`, none otherwise. -/
private abbrev Cell (m : ℕ) : Type := PLift (m < n + 1)

private theorem pairwiseDisjoint_cellMap :
    (univ : Set (Σ m, Cell n m)).PairwiseDisjoint
      (fun c ↦ cellMap (⟨c.1, c.2.down⟩ : Fin (n + 1)) '' ball 0 1) := by
  rintro ⟨m, ⟨hm⟩⟩ - ⟨m', ⟨hm'⟩⟩ - hne
  simp only [Function.onFun, image_cellMap_ball]
  refine disjoint_openCell fun h => hne ?_
  obtain rfl : m = m' := congrArg Fin.val h
  rfl

private theorem mapsTo_cellMap (m : ℕ) (c : Cell n m) :
    MapsTo (cellMap (⟨m, c.down⟩ : Fin (n + 1))) (sphere 0 1)
      (⋃ (k < m) (c' : Cell n k), cellMap (⟨k, c'.down⟩ : Fin (n + 1)) '' closedBall 0 1) := by
  intro x hx
  obtain ⟨i', hi', hx'⟩ := exists_lt_cellMap_mem_openCell _ hx
  rw [← image_cellMap_ball] at hx'
  exact mem_iUnion₂.2 ⟨i', hi', mem_iUnion.2 ⟨⟨i'.is_lt⟩, image_mono ball_subset_closedBall hx'⟩⟩

variable (n) in
/-- The CW structure on `RPⁿ` with one cell in each dimension `0, …, n` (Hatcher, Example 0.4):
the characteristic map of the `i`-cell is `cellMap i`, which identifies the open `i`-cell with
`RPⁱ ∖ RPⁱ⁻¹` and attaches it along the double cover `Sⁱ⁻¹ → RPⁱ⁻¹`. -/
@[instance_reducible]
def cwComplex : CWComplex (univ : Set (RealProjectiveSpace n)) :=
  CWComplex.mkFinite _ (Cell n) (fun m c => cellMap ⟨m, c.down⟩)
    (Filter.eventually_atTop.2 ⟨n + 1, fun _ hm => ⟨fun c => absurd c.down (by omega)⟩⟩)
    (fun _ => inferInstance) (fun _ _ => rfl) (fun _ _ => continuousOn_cellMap _)
    (fun _ _ => continuousOn_cellMap_symm _) pairwiseDisjoint_cellMap mapsTo_cellMap <| by
      refine eq_univ_of_forall fun p => ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 (iUnion_image_cellMap_closedBall ▸ mem_univ p)
      exact mem_iUnion₂.2 ⟨i, ⟨i.is_lt⟩, hi⟩

/-- The characteristic map of the `i`-cell of `cwComplex n` is `cellMap i`. -/
theorem map_cwComplex (i : Fin (n + 1))
    (c : letI := cwComplex n; cell (univ : Set (RealProjectiveSpace n)) i) :
    letI := cwComplex n
    map (C := univ) i c = cellMap i :=
  (rfl)

/-- The CW structure on `RPⁿ` is finite. -/
theorem finite_cwComplex :
    letI := cwComplex n
    RelCWComplex.Finite (univ : Set (RealProjectiveSpace n)) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

/-- The CW structure on `RPⁿ` has one cell in each dimension `m ≤ n` and none above. -/
theorem nat_card_cell_cwComplex (m : ℕ) :
    letI := cwComplex n
    Nat.card (cell (univ : Set (RealProjectiveSpace n)) m) = if m ≤ n then 1 else 0 := by
  -- Unfolding the definition of `CWComplex.mkFinite`, the cells of `cwComplex n` in dimension `m`
  -- are `Cell n m`.
  change Nat.card (Cell n m) = _
  split_ifs with h
  · have : Unique (Cell n m) := ⟨⟨⟨by omega⟩⟩, fun _ => rfl⟩
    exact Nat.card_unique
  · have : IsEmpty (Cell n m) := ⟨fun c => h (by have := c.down; omega)⟩
    exact Nat.card_of_isEmpty

/-- Real projective space has finite CW type. -/
instance finiteCWType : FiniteCWType (RealProjectiveSpace n) :=
  letI := cwComplex n
  have := finite_cwComplex (n := n)
  (Homeomorph.Set.univ _).symm.finiteCWType

end RealProjectiveSpace

end TauCeti
