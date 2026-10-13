/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Analysis.Normed.Module.Ball.Action
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Data.Fin.Basic
public import TauCeti.Topology.ComplexProjectiveSpace
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# The CW structure on complex projective space

Complex projective space `CPⁿ`, the quotient of the unit sphere `S²ⁿ⁺¹ ⊆ ℂⁿ⁺¹` by the unit
complex scalars (`TauCeti.ComplexProjectiveSpace`), is a finite CW complex with one cell in each
even dimension `0, 2, …, 2n` and none in odd dimensions
(`TauCeti.ComplexProjectiveSpace.cwComplex`).

Write `CPⁱ ⊆ CPⁿ` for the classes of unit vectors whose coordinates beyond `i` vanish. The open
`2i`-cell is `CPⁱ ∖ CPⁱ⁻¹`, the classes of unit vectors `y` with `yᵢ ≠ 0` and `yⱼ = 0` for `j > i`
(`TauCeti.ComplexProjectiveSpace.openCell`). Its characteristic map
(`TauCeti.ComplexProjectiveSpace.cellMap`) sends a point `v` of the closed unit disk `D²ⁱ ⊆ ℂⁱ`
to the class of `(v, √(1 - ‖v‖²), 0, …, 0)` (`TauCeti.ComplexProjectiveSpace.hemispherePoint`).
Every class in the open cell has exactly one representative with `yᵢ` real and positive, obtained
by multiplying by the unit scalar `|yᵢ| / yᵢ`, so the map is a bijection from the open disk
onto the open cell. On the boundary sphere `S²ⁱ⁻¹` it is the quotient map `S²ⁱ⁻¹ → CPⁱ⁻¹`, which
lands in the cells of lower dimension. The domains of the characteristic maps of Mathlib's
`Topology.CWComplex` are closed balls of the sup norm on `Fin (2i) → ℝ`; they are carried onto
the Euclidean disks of `ℂⁱ` by the radial homeomorphism `ContinuousLinearEquiv.unitBallHomeomorph`
of the real coordinates `TauCeti.complexEuclideanRealCoords`.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.hemispherePoint`: the unit vector over a point of `D²ⁱ`.
* `TauCeti.ComplexProjectiveSpace.openCell`: the open `2i`-cell `CPⁱ ∖ CPⁱ⁻¹`.
* `TauCeti.ComplexProjectiveSpace.cellMap`: the characteristic map of the `2i`-cell, with
  `TauCeti.ComplexProjectiveSpace.cellMap_apply` its formula on the closed ball and
  `TauCeti.ComplexProjectiveSpace.cellMap_symm_mk` the formula for its inverse.
* `TauCeti.ComplexProjectiveSpace.cwComplex`: the CW structure on `CPⁿ`, with characteristic maps
  `cellMap` (`TauCeti.ComplexProjectiveSpace.map_cwComplex`); it is finite
  (`TauCeti.ComplexProjectiveSpace.finite_cwComplex`) with one cell in each even dimension
  `m ≤ 2n` and none otherwise (`TauCeti.ComplexProjectiveSpace.nat_card_cell_cwComplex`).
* `TauCeti.ComplexProjectiveSpace.finiteCWType`: `CPⁿ` has finite CW type.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6.
* The construction adapts Tau Ceti's CW structure on real projective space in
  `TauCeti/Topology/CWComplex/Classical/RealProjective.lean`.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace ComplexProjectiveSpace

variable {n : ℕ}

variable (n) in
/-- The unit vector of `ℂⁿ⁺¹` lying over `v ∈ ℂᵏ`: its first `k` coordinates are those of `v`,
its coordinate `k` is the real number `√(1 - ‖v‖²)`, and the remaining ones vanish. For `k ≤ n`
and `‖v‖ ≤ 1` it lies on the unit sphere (`norm_hemispherePoint`). -/
def hemispherePoint {k : ℕ} (v : EuclideanSpace ℂ (Fin k)) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun j =>
    if h : (j : ℕ) < k then v ⟨j, h⟩ else if (j : ℕ) = k then (√(1 - ‖v‖ ^ 2) : ℂ) else 0

/-- The coordinates of `hemispherePoint n v` before `k` are those of `v`. -/
theorem hemispherePoint_apply_of_lt {k : ℕ} (v : EuclideanSpace ℂ (Fin k)) {j : Fin (n + 1)}
    (hj : (j : ℕ) < k) : hemispherePoint n v j = v ⟨j, hj⟩ := by
  simp [hemispherePoint, hj]

/-- The coordinate `k` of `hemispherePoint n v` is `√(1 - ‖v‖²)`. -/
theorem hemispherePoint_apply_of_eq {k : ℕ} (v : EuclideanSpace ℂ (Fin k)) {j : Fin (n + 1)}
    (hj : (j : ℕ) = k) : hemispherePoint n v j = (√(1 - ‖v‖ ^ 2) : ℂ) := by
  simp [hemispherePoint, hj]

/-- The coordinates of `hemispherePoint n v` beyond `k` vanish. -/
theorem hemispherePoint_apply_of_gt {k : ℕ} (v : EuclideanSpace ℂ (Fin k)) {j : Fin (n + 1)}
    (hj : k < (j : ℕ)) : hemispherePoint n v j = 0 := by
  simp [hemispherePoint, hj.not_gt, hj.ne']

/-- `hemispherePoint n` is continuous. -/
theorem continuous_hemispherePoint {k : ℕ} :
    Continuous (hemispherePoint n : EuclideanSpace ℂ (Fin k) → _) :=
  (PiLp.continuous_toLp _ _).comp <| continuous_pi fun j => by
    split_ifs <;> fun_prop

/-- For `k ≤ n`, `hemispherePoint n` maps the closed unit disk of `ℂᵏ` into the unit sphere
of `ℂⁿ⁺¹`. -/
theorem norm_hemispherePoint {k : ℕ} {v : EuclideanSpace ℂ (Fin k)} (hk : k ≤ n)
    (hv : ‖v‖ ≤ 1) : ‖hemispherePoint n v‖ = 1 := by
  have hsq : ‖hemispherePoint n v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_eq_sum_castLE_add ⟨k, by omega⟩ _
      fun j hj => by rw [hemispherePoint_apply_of_gt v hj, norm_zero, sq, zero_mul],
      hemispherePoint_apply_of_eq v rfl, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by nlinarith [norm_nonneg v] : 0 ≤ 1 - ‖v‖ ^ 2)]
    have hc (j : Fin k) : hemispherePoint n v (Fin.castLE (by omega) j) = v j := by
      simp [hemispherePoint]
    simp only [hc, ← EuclideanSpace.norm_sq_eq v]
    ring
  nlinarith [norm_nonneg (hemispherePoint n v)]

/-- The first `i` coordinates of a vector of `ℂⁿ⁺¹`. -/
private def truncate (i : Fin (n + 1)) (y : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin i) :=
  WithLp.toLp 2 fun j => y (Fin.castLE i.is_lt.le j)

private theorem continuous_truncate (i : Fin (n + 1)) : Continuous (truncate i) :=
  (PiLp.continuous_toLp _ _).comp <| continuous_pi fun _ => PiLp.continuous_apply _ _ _

private theorem truncate_smul (i : Fin (n + 1)) (c : ℂ) (y : EuclideanSpace ℂ (Fin (n + 1))) :
    truncate i (c • y) = c • truncate i y := by
  ext j
  simp [truncate]

private theorem truncate_hemispherePoint (i : Fin (n + 1)) (v : EuclideanSpace ℂ (Fin i)) :
    truncate i (hemispherePoint n v) = v := by
  ext j
  simp [truncate, hemispherePoint_apply_of_lt v (j := Fin.castLE i.is_lt.le j) j.is_lt]

/-- For a vector whose coordinates beyond `i` vanish, the squared norm splits into that of its
first `i` coordinates and the squared norm of coordinate `i`. -/
private theorem norm_truncate_sq_add_sq {i : Fin (n + 1)} {y : EuclideanSpace ℂ (Fin (n + 1))}
    (hy : ∀ j : Fin (n + 1), i < j → y j = 0) : ‖truncate i y‖ ^ 2 + ‖y i‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_eq_sum_castLE_add i _ fun j hj => by rw [hy j hj, norm_zero, sq, zero_mul]]
  simp [truncate]

/-- The unit scalar `|a| / a`, which rotates a nonzero complex number `a` onto the positive real
axis (`phase_mul_self`). -/
private def phase (a : ℂ) : ℂ :=
  (‖a‖ : ℂ) / a

private theorem phase_mul_self {a : ℂ} (ha : a ≠ 0) : phase a * a = (‖a‖ : ℂ) :=
  div_mul_cancel₀ _ ha

private theorem norm_phase {a : ℂ} (ha : a ≠ 0) : ‖phase a‖ = 1 := by
  rw [phase, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 ha)]

/-- Multiplying `a` by a unit scalar `c` multiplies its phase by `c⁻¹`. -/
private theorem phase_mul_mul {c : ℂ} (hc : ‖c‖ = 1) (a : ℂ) : phase (c * a) * c = phase a := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hc]; exact one_ne_zero)
  rw [phase, phase, norm_mul, hc, one_mul, div_mul_eq_mul_div, mul_comm c a,
    mul_div_mul_right _ _ hc0]

private theorem phase_ofReal {r : ℝ} (hr : 0 < r) : phase r = 1 := by
  rw [phase, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    div_self (Complex.ofReal_ne_zero.2 hr.ne')]

private theorem continuousAt_phase {a : ℂ} (ha : a ≠ 0) : ContinuousAt phase a :=
  (Complex.continuous_ofReal.comp continuous_norm).continuousAt.div continuousAt_id ha

variable (n) in
/-- The open `2i`-cell of `CPⁿ`: the classes of the unit vectors whose coordinate `i` is nonzero
and whose later coordinates vanish. -/
def openCell (i : Fin (n + 1)) : Set (ComplexProjectiveSpace n) :=
  mk n '' {y | (y : EuclideanSpace ℂ (Fin (n + 1))) i ≠ 0 ∧
    ∀ j : Fin (n + 1), i < j → (y : EuclideanSpace ℂ (Fin (n + 1))) j = 0}

/-- The class of a unit vector `y` lies in the open `2i`-cell exactly when `yᵢ ≠ 0` and the
coordinates of `y` beyond `i` vanish. -/
@[simp]
theorem mk_mem_openCell_iff {i : Fin (n + 1)}
    {y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1} :
    mk n y ∈ openCell n i ↔ (y : EuclideanSpace ℂ (Fin (n + 1))) i ≠ 0 ∧
      ∀ j : Fin (n + 1), i < j → (y : EuclideanSpace ℂ (Fin (n + 1))) j = 0 := by
  refine ⟨?_, fun hy => ⟨y, hy, rfl⟩⟩
  rintro ⟨y', hy', h⟩
  obtain ⟨c, rfl⟩ := (mk_eq_mk_iff n y' y).1 h
  have hc : (c : ℂ) ≠ 0 := ne_zero_of_mem_unit_sphere c
  simpa [hc] using hy'

/-- Distinct open cells of `CPⁿ` are disjoint. -/
theorem disjoint_openCell {i i' : Fin (n + 1)} (h : i ≠ i') :
    Disjoint (openCell n i) (openCell n i') := by
  wlog hlt : i < i' generalizing i i'
  · exact (this h.symm (lt_of_le_of_ne (not_lt.1 hlt) h.symm)).symm
  refine Set.disjoint_left.2 fun p hp hp' => ?_
  obtain ⟨y, rfl⟩ := mk_surjective n p
  exact (mk_mem_openCell_iff.1 hp').1 ((mk_mem_openCell_iff.1 hp).2 i' hlt)

/-- The class of a unit vector whose coordinates from `k` on vanish lies in an open cell `2i` with
`i < k`: the one indexed by its last nonzero coordinate. -/
theorem exists_lt_mk_mem_openCell (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) {k : ℕ}
    (hy : ∀ j : Fin (n + 1), k ≤ j → (y : EuclideanSpace ℂ (Fin (n + 1))) j = 0) :
    ∃ i : Fin (n + 1), (i : ℕ) < k ∧ mk n y ∈ openCell n i := by
  set S := Finset.univ.filter fun j : Fin (n + 1) => (y : EuclideanSpace ℂ (Fin (n + 1))) j ≠ 0
  have hS : S.Nonempty := by
    by_contra hS
    have h0 : (y : EuclideanSpace ℂ (Fin (n + 1))) = 0 := by
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

/-- The first `i` coordinates of the representative of `[y]` whose coordinate `i` is real and
nonnegative, read in the sup-norm ball through the radial homeomorphism of the real
coordinates. -/
private def cellChart (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m)
    (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) : Fin m → ℝ :=
  (complexEuclideanRealCoords hm).unitBallHomeomorph (phase (y.1 i) • truncate i y.1)

private theorem cellChart_smul (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m)
    (c : sphere (0 : ℂ) 1) (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    cellChart i hm (c • y) = cellChart i hm y := by
  simp only [cellChart, Sphere.coe_sphere_smul, PiLp.smul_apply, smul_eq_mul, truncate_smul,
    smul_smul, phase_mul_mul (norm_eq_of_mem_sphere c)]

/-- The inverse of the characteristic map of the `2i`-cell on the open cell. -/
private def cellMapInv (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    ComplexProjectiveSpace n → (Fin m → ℝ) :=
  ComplexProjectiveSpace.lift n (cellChart i hm) (cellChart_smul i hm)

private theorem cellMapInv_mk (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m)
    (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    cellMapInv i hm (mk n y) =
      (complexEuclideanRealCoords hm).unitBallHomeomorph (phase (y.1 i) • truncate i y.1) :=
  ComplexProjectiveSpace.lift_mk n _ (cellChart_smul i hm) y

/-- The point of `S²ⁿ⁺¹` over a point `x` of the closed sup-norm ball of `Fin (2i) → ℝ`: the
radial homeomorphism onto the Euclidean disk of `ℂⁱ`, followed by `hemispherePoint`. -/
private def cellSpherePoint (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m)
    (x : closedBall (0 : Fin m → ℝ) 1) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
  ⟨hemispherePoint n ((complexEuclideanRealCoords hm).unitBallHomeomorph.symm x),
    mem_sphere_zero_iff_norm.2 (norm_hemispherePoint i.is_le
      ((complexEuclideanRealCoords hm).norm_unitBallHomeomorph_symm_le_one_iff.2
        (mem_closedBall_zero_iff.1 x.2)))⟩

/-- On the open cell, `hemispherePoint` of the truncated rotated representative recovers the
rotated unit vector. -/
private theorem hemispherePoint_phase_smul_truncate {i : Fin (n + 1)}
    {y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1} (hyi : y.1 i ≠ 0)
    (hy : ∀ j : Fin (n + 1), i < j → y.1 j = 0) :
    hemispherePoint n (phase (y.1 i) • truncate i y.1) = phase (y.1 i) • y.1 := by
  have hnorm := norm_truncate_sq_add_sq hy
  rw [norm_eq_of_mem_sphere y, one_pow] at hnorm
  have hw : ‖phase (y.1 i) • truncate i y.1‖ = ‖truncate i y.1‖ := by
    rw [norm_smul, norm_phase hyi, one_mul]
  ext j
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · rw [hemispherePoint_apply_of_lt _ h]
    simp [truncate, Fin.castLE]
  · have hji : j = i := Fin.ext h
    have hsq : 1 - ‖truncate i y.1‖ ^ 2 = ‖y.1 i‖ ^ 2 := by linarith
    rw [hemispherePoint_apply_of_eq _ h, hw, hji, PiLp.smul_apply, smul_eq_mul,
      phase_mul_self hyi, hsq, Real.sqrt_sq (norm_nonneg _)]
  · rw [hemispherePoint_apply_of_gt _ h, PiLp.smul_apply, hy j (Fin.lt_def.2 h), smul_zero]

open scoped Classical in
/-- The characteristic map of the `2i`-cell of `CPⁿ` (Hatcher, Example 0.6), for `m = 2i`. On the
closed unit ball of `Fin m → ℝ` with the sup norm, it is the radial homeomorphism onto the
Euclidean disk of `ℂⁱ`, followed by `hemispherePoint` and the quotient map to `CPⁿ`
(`cellMap_apply`). It maps the open ball bijectively onto `openCell n i`. -/
def cellMap (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    PartialEquiv (Fin m → ℝ) (ComplexProjectiveSpace n) where
  toFun x := if hx : x ∈ closedBall 0 1 then mk n (cellSpherePoint i hm ⟨x, hx⟩)
    else Classical.arbitrary _
  invFun := cellMapInv i hm
  source := ball 0 1
  target := openCell n i
  map_source' x hx := by
    rw [dite_eq_left (ball_subset_closedBall hx), mk_mem_openCell_iff]
    refine ⟨?_, fun j hj => hemispherePoint_apply_of_gt _ hj⟩
    set v := (complexEuclideanRealCoords hm).unitBallHomeomorph.symm x
    have hv : ‖v‖ < 1 := by simpa [v] using hx
    rw [cellSpherePoint, hemispherePoint_apply_of_eq _ rfl]
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])).ne'
  map_target' p hp := by
    obtain ⟨y, rfl⟩ := mk_surjective n p
    obtain ⟨hyi, hy⟩ := mk_mem_openCell_iff.1 hp
    have hnorm := norm_truncate_sq_add_sq hy
    rw [norm_eq_of_mem_sphere y] at hnorm
    simp only [cellMapInv_mk, mem_ball_zero_iff,
      ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff, norm_smul, norm_phase hyi,
      one_mul]
    nlinarith [norm_nonneg (truncate i y.1), norm_pos_iff.2 hyi]
  left_inv' x hx := by
    set v := (complexEuclideanRealCoords hm).unitBallHomeomorph.symm x
    have hv : ‖v‖ < 1 := by simpa [v] using hx
    have hpos : 0 < √(1 - ‖v‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])
    rw [dite_eq_left (ball_subset_closedBall hx), cellMapInv_mk, cellSpherePoint,
      hemispherePoint_apply_of_eq _ rfl, phase_ofReal hpos, one_smul, truncate_hemispherePoint,
      Homeomorph.apply_symm_apply]
  right_inv' p hp := by
    obtain ⟨y, rfl⟩ := mk_surjective n p
    obtain ⟨hyi, hy⟩ := mk_mem_openCell_iff.1 hp
    have hnorm := norm_truncate_sq_add_sq hy
    rw [norm_eq_of_mem_sphere y, one_pow] at hnorm
    have hx : cellMapInv i hm (mk n y) ∈ closedBall 0 1 := by
      rw [cellMapInv_mk, mem_closedBall_zero_iff,
        ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff, norm_smul, norm_phase hyi,
        one_mul]
      nlinarith [norm_nonneg (truncate i y.1), norm_nonneg (y.1 i)]
    let s : sphere (0 : ℂ) 1 := ⟨phase (y.1 i), mem_sphere_zero_iff_norm.2 (norm_phase hyi)⟩
    have key : cellSpherePoint i hm ⟨_, hx⟩ = s • y := Subtype.ext <| by
      simp only [cellSpherePoint, cellMapInv_mk, Homeomorph.symm_apply_apply,
        Sphere.coe_sphere_smul, s]
      exact hemispherePoint_phase_smul_truncate hyi hy
    rw [dite_eq_left hx, key, mk_smul]

/-- The source of the characteristic map of the `2i`-cell is the open unit ball. -/
@[simp]
theorem cellMap_source (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    (cellMap i hm).source = ball 0 1 :=
  (rfl)

/-- The target of the characteristic map of the `2i`-cell is the open `2i`-cell. -/
@[simp]
theorem cellMap_target (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    (cellMap i hm).target = openCell n i :=
  (rfl)

/-- On the closed unit ball, the characteristic map of the `2i`-cell is the radial homeomorphism
onto the Euclidean disk of `ℂⁱ` followed by `hemispherePoint` and the quotient map. -/
theorem cellMap_apply (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) {x : Fin m → ℝ}
    (hx : x ∈ closedBall 0 1) :
    cellMap i hm x = mk n ⟨hemispherePoint n
      ((complexEuclideanRealCoords hm).unitBallHomeomorph.symm x),
      mem_sphere_zero_iff_norm.2 (norm_hemispherePoint i.is_le
        ((complexEuclideanRealCoords hm).norm_unitBallHomeomorph_symm_le_one_iff.2
          (mem_closedBall_zero_iff.1 hx)))⟩ :=
  dite_eq_left hx

/-- The inverse of the characteristic map of the `2i`-cell sends the class of a unit vector `y`
to its first `i` coordinates, multiplied by the scalar `|yᵢ| / yᵢ` and read in the
sup-norm ball through the radial homeomorphism of the real coordinates. On the open cell, where
`yᵢ ≠ 0`, this is the truncation of the representative of `[y]` whose coordinate `i` is real and
positive. -/
theorem cellMap_symm_mk (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m)
    (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (cellMap i hm).symm (mk n y) = (complexEuclideanRealCoords hm).unitBallHomeomorph
      (((‖y.1 i‖ : ℂ) / y.1 i) • WithLp.toLp 2 fun j => y.1 (Fin.castLE i.is_lt.le j)) :=
  cellMapInv_mk i hm y

/-- The characteristic map of the `2i`-cell maps the open unit ball onto the open `2i`-cell. -/
theorem image_cellMap_ball (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    cellMap i hm '' ball 0 1 = openCell n i :=
  (cellMap i hm).image_source_eq_target

/-- The characteristic map of the `2i`-cell is continuous on the closed unit ball. -/
theorem continuousOn_cellMap (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    ContinuousOn (cellMap i hm) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (cellSpherePoint i hm) := (continuous_hemispherePoint.comp
    ((Homeomorph.continuous _).comp continuous_subtype_val)).subtype_mk _
  exact ((continuous_mk n).comp hc).congr fun x => (cellMap_apply i hm x.2).symm

/-- The inverse of the characteristic map of the `2i`-cell is continuous on the open cell. -/
theorem continuousOn_cellMap_symm (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m) :
    ContinuousOn (cellMap i hm).symm (cellMap i hm).target := by
  intro p hp
  obtain ⟨y, rfl⟩ := mk_surjective n p
  have hyi := (mk_mem_openCell_iff.1 hp).1
  have hc : Continuous fun y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 => y.1 i :=
    (PiLp.continuous_apply _ _ _).comp continuous_subtype_val
  refine (continuousAt_lift n (cellChart_smul i hm) ?_).continuousWithinAt
  exact (Homeomorph.continuous _).continuousAt.comp (((continuousAt_phase hyi).comp
    (f := fun y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 => y.1 i) hc.continuousAt).smul
    ((continuous_truncate i).comp continuous_subtype_val).continuousAt)

/-- The characteristic map of the `2i`-cell sends the boundary sphere of the sup-norm ball into
the open cells `2i'` with `i' < i`. -/
theorem exists_lt_cellMap_mem_openCell (i : Fin (n + 1)) {m : ℕ} (hm : 2 * (i : ℕ) = m)
    {x : Fin m → ℝ} (hx : x ∈ sphere 0 1) :
    ∃ i' : Fin (n + 1), i' < i ∧ cellMap i hm x ∈ openCell n i' := by
  have hv : ‖(complexEuclideanRealCoords hm).unitBallHomeomorph.symm x‖ = 1 := by
    simpa using hx
  rw [cellMap_apply i hm (sphere_subset_closedBall hx)]
  refine exists_lt_mk_mem_openCell _ fun j hj => ?_
  rcases hj.eq_or_lt with h | h
  · rw [hemispherePoint_apply_of_eq _ h.symm, hv]
    simp
  · exact hemispherePoint_apply_of_gt _ h

variable (n) in
/-- The cells of dimension `m` of the CW structure on `CPⁿ`: the indices `i ≤ n` with
`2i = m`. -/
private abbrev Cell (m : ℕ) : Type := {i : Fin (n + 1) // 2 * (i : ℕ) = m}

private theorem pairwiseDisjoint_cellMap :
    (univ : Set (Σ m, Cell n m)).PairwiseDisjoint (fun c ↦ cellMap c.2.1 c.2.2 '' ball 0 1) := by
  rintro ⟨m, i, hi⟩ - ⟨m', i', hi'⟩ - hne
  simp only [Function.onFun, image_cellMap_ball]
  refine disjoint_openCell fun h => hne ?_
  subst h hi hi'
  rfl

private theorem mapsTo_cellMap (m : ℕ) (c : Cell n m) :
    MapsTo (cellMap c.1 c.2) (sphere 0 1)
      (⋃ (k < m) (c' : Cell n k), cellMap c'.1 c'.2 '' closedBall 0 1) := by
  intro x hx
  obtain ⟨i', hi', hx'⟩ := exists_lt_cellMap_mem_openCell _ c.2 hx
  rw [← image_cellMap_ball i' rfl] at hx'
  have : 2 * (i' : ℕ) < m := by have := Fin.lt_def.1 hi'; have := c.2; omega
  exact mem_iUnion₂.2 ⟨_, this, mem_iUnion.2 ⟨⟨i', rfl⟩, image_mono ball_subset_closedBall hx'⟩⟩

variable (n) in
/-- The CW structure on `CPⁿ` with one cell in each even dimension `0, 2, …, 2n` (Hatcher,
Example 0.6): the characteristic map of the `2i`-cell is `cellMap i`, which identifies the open
`2i`-cell with `CPⁱ ∖ CPⁱ⁻¹` and attaches it along the quotient map `S²ⁱ⁻¹ → CPⁱ⁻¹`. -/
@[instance_reducible]
def cwComplex : CWComplex (univ : Set (ComplexProjectiveSpace n)) :=
  CWComplex.mkFinite _ (Cell n) (fun _ c => cellMap c.1 c.2)
    (Filter.eventually_atTop.2 ⟨2 * n + 1, fun _ hm =>
      ⟨fun c => absurd c.2 (by have := c.1.is_lt; omega)⟩⟩)
    (fun _ => inferInstance) (fun _ _ => rfl) (fun _ c => continuousOn_cellMap c.1 c.2)
    (fun _ c => continuousOn_cellMap_symm c.1 c.2) pairwiseDisjoint_cellMap mapsTo_cellMap <| by
      refine eq_univ_of_forall fun p => ?_
      obtain ⟨y, rfl⟩ := mk_surjective n p
      obtain ⟨i, -, hi⟩ :=
        exists_lt_mk_mem_openCell y (k := n + 1) fun j hj => absurd j.is_lt hj.not_gt
      rw [← image_cellMap_ball i rfl] at hi
      exact mem_iUnion₂.2 ⟨_, ⟨i, rfl⟩, image_mono ball_subset_closedBall hi⟩

/-- The characteristic map of the `2i`-cell of `cwComplex n` is `cellMap i`. -/
theorem map_cwComplex (i : Fin (n + 1))
    (c : letI := cwComplex n; cell (univ : Set (ComplexProjectiveSpace n)) (2 * i)) :
    letI := cwComplex n
    map (C := univ) (2 * i) c = cellMap i rfl := by
  -- Unfolding the definition of `CWComplex.mkFinite`, the cells of `cwComplex n` in dimension
  -- `2 * i` are the indices `i'` with `2 * i' = 2 * i`, so `i' = i`.
  change Cell n (2 * i) at c
  obtain ⟨i', hi'⟩ := c
  obtain rfl : i' = i := Fin.ext (by omega)
  rfl

/-- The CW structure on `CPⁿ` is finite. -/
theorem finite_cwComplex :
    letI := cwComplex n
    RelCWComplex.Finite (univ : Set (ComplexProjectiveSpace n)) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

/-- The CW structure on `CPⁿ` has one cell in each even dimension `m ≤ 2n` and none in other
dimensions. -/
theorem nat_card_cell_cwComplex (m : ℕ) :
    letI := cwComplex n
    Nat.card (cell (univ : Set (ComplexProjectiveSpace n)) m) =
      if Even m ∧ m ≤ 2 * n then 1 else 0 := by
  -- Unfolding the definition of `CWComplex.mkFinite`, the cells of `cwComplex n` in dimension `m`
  -- are `Cell n m`.
  change Nat.card (Cell n m) = _
  split_ifs with h
  · obtain ⟨⟨k, rfl⟩, hk⟩ := h
    exact Nat.card_eq_one_iff_exists.2 ⟨⟨⟨k, by omega⟩, by simp; omega⟩,
      fun c => Subtype.ext (Fin.ext (by have := c.2; simp; omega))⟩
  · have : IsEmpty (Cell n m) := ⟨fun c => h ⟨⟨c.1, by have := c.2; omega⟩, by
      have := c.1.is_lt; have := c.2; omega⟩⟩
    exact Nat.card_of_isEmpty

/-- Complex projective space has finite CW type. -/
instance finiteCWType : FiniteCWType (ComplexProjectiveSpace n) :=
  letI := cwComplex n
  have := finite_cwComplex (n := n)
  (Homeomorph.Set.univ _).symm.finiteCWType

end ComplexProjectiveSpace

end TauCeti
