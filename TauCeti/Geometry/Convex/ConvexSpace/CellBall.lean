/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Convex.CoordinateSimplex

/-!
# Explicit radial homeomorphism from the cell ball to the ordered standard simplex

This file constructs the explicit radial homeomorphism
`TauCeti.standardCellBallToOrderedSimplex n` from the sup-norm closed unit ball
`Metric.closedBall (0 : Fin n → ℝ) 1` (the domain of classical CW characteristic maps) onto the
ordered standard `n`-simplex `Convexity.StdSimplex ℝ (Fin (n + 1))`.

The center `0` is sent to the barycenter `(1 / (n + 1), …, 1 / (n + 1))`. Any point `z` defines the
zero-sum tangent vector `w = (-∑ j, z j, z 0, …, z (n - 1))` in the ordered tangent basis
`e_{j + 1} - e_0`, with maximal negative component `m = max_i (-w_i)`; its image has barycentric
weights `1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * m)` (evaluating to `1 / (n + 1)` at `z = 0`). In
dimension `0`, every point of the ball is `0` and maps to the unique point of the `0`-simplex.

Because the smallest weight is `(1 - ‖z‖) / (n + 1)`, attained where `-w_i = m`, the boundary
sphere `‖z‖ = 1` maps onto the simplicial boundary `{y | ∃ i, y.weights i = 0}`
(`TauCeti.exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff`), and the open ball
`‖z‖ < 1` maps onto the open interior `{y | ∀ i, 0 < y.weights i}`
(`TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff`).

## Main definitions

* `TauCeti.standardCellBallToOrderedSimplex`: the explicit radial homeomorphism from the sup-norm
  closed unit ball of `Fin n → ℝ` onto `Convexity.StdSimplex ℝ (Fin (n + 1))`.

## Main results

* `TauCeti.weights_standardCellBallToOrderedSimplex` and
  `TauCeti.weights_standardCellBallToOrderedSimplex_zero`: barycentric weight formulas.
* `TauCeti.standardCellBallToOrderedSimplex_zero`,
  `TauCeti.standardCellBallToOrderedSimplex_symm_subBarycenter`, and
  `TauCeti.coe_standardCellBallToOrderedSimplex_symm_apply`: center-to-barycenter and inverse
  formulas.
* `TauCeti.exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff`,
  `TauCeti.norm_standardCellBallToOrderedSimplex_symm_eq_one_iff`, and
  `TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff`: boundary and interior
  characterizations.
* `TauCeti.standardCellBallToOrderedSimplex_one_one`,
  `TauCeti.standardCellBallToOrderedSimplex_one_neg_one`, and
  `TauCeti.weights_standardCellBallToOrderedSimplex_two_single`: explicit boundary evaluations in
  dimensions `1` and `2`.
-/

public section

noncomputable section

open Convexity Metric Set
open scoped Pointwise

namespace TauCeti

namespace StandardCellBallToOrderedSimplex

/-- The zero-sum tangent vector `(-∑ j, z j, z 0, …, z (n - 1))` associated to `z : Fin n → ℝ` in
the ordered tangent basis `e_{j + 1} - e_0` of the standard `n`-simplex. -/
def tangentVec {n : ℕ} (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (α := fun _ ↦ ℝ) (-∑ j, z j) z

@[simp]
lemma tangentVec_zero_coord {n : ℕ} (z : Fin n → ℝ) :
    tangentVec z 0 = -∑ j, z j :=
  (rfl)

@[simp]
lemma tangentVec_succ_coord {n : ℕ} (z : Fin n → ℝ) (j : Fin n) :
    tangentVec z j.succ = z j :=
  (rfl)

private lemma sum_tangentVec {n : ℕ} (z : Fin n → ℝ) :
    ∑ i, tangentVec z i = 0 := by
  simp [tangentVec, Fin.sum_univ_succ]

private lemma tangentVec_eq_zero_iff {n : ℕ} (z : Fin n → ℝ) :
    tangentVec z = 0 ↔ z = 0 := by
  constructor
  · intro h
    ext j
    simpa [tangentVec] using congrFun h j.succ
  · rintro rfl
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [tangentVec]

@[simp]
lemma tangentVec_zero {n : ℕ} : tangentVec (0 : Fin n → ℝ) = 0 :=
  (tangentVec_eq_zero_iff 0).2 rfl

private lemma tangentVec_smul {n : ℕ} (t : ℝ) (z : Fin n → ℝ) :
    tangentVec (t • z) = t • tangentVec z := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [tangentVec, Finset.mul_sum]
  · intro j
    simp [tangentVec]

private lemma continuous_tangentVec {n : ℕ} (i : Fin (n + 1)) :
    Continuous fun z : Fin n → ℝ ↦ tangentVec z i := by
  refine Fin.cases ?_ ?_ i
  · simp only [tangentVec, Fin.cons_zero]
    fun_prop
  · intro j
    simp only [tangentVec, Fin.cons_succ]
    fun_prop

/-- The maximum of `-v i` over `i : Fin (n + 1)`. For a zero-sum vector `v`, this is nonnegative
and strictly positive precisely when `v ≠ 0`. -/
def maxOfNeg {n : ℕ} (v : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ -v i

private lemma neg_le_maxOfNeg {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    -v i ≤ maxOfNeg v :=
  Finset.le_sup' (f := fun i ↦ -v i) (Finset.mem_univ i)

private lemma exists_maxOfNeg_eq {n : ℕ} (v : Fin (n + 1) → ℝ) :
    ∃ i : Fin (n + 1), maxOfNeg v = -v i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i ↦ -v i
  exact ⟨i, hi⟩

private lemma maxOfNeg_le_iff {n : ℕ} (v : Fin (n + 1) → ℝ) (c : ℝ) :
    maxOfNeg v ≤ c ↔ ∀ i, -v i ≤ c := by
  simp [maxOfNeg, Finset.sup'_le_iff]

@[simp]
lemma maxOfNeg_zero {n : ℕ} : maxOfNeg (0 : Fin (n + 1) → ℝ) = 0 := by
  apply le_antisymm
  · rw [maxOfNeg_le_iff]; intro i; simp
  · simpa using neg_le_maxOfNeg (0 : Fin (n + 1) → ℝ) 0

/-- If every `-v j` is at most `c` and `-v i = c` at some vertex `i`, then `maxOfNeg v = c`. -/
lemma maxOfNeg_eq_of_attained {n : ℕ} {v : Fin (n + 1) → ℝ} {c : ℝ}
    (hle : ∀ j, -v j ≤ c) {i : Fin (n + 1)} (heq : -v i = c) :
    maxOfNeg v = c :=
  le_antisymm ((maxOfNeg_le_iff v c).2 hle) (heq ▸ neg_le_maxOfNeg v i)

private lemma maxOfNeg_nonneg_of_sum_eq_zero {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : ∑ i, v i = 0) :
    0 ≤ maxOfNeg v := by
  by_contra h
  push Not at h
  have hpos : ∀ i ∈ Finset.univ, 0 < v i := fun i _ ↦ by
    linarith [neg_le_maxOfNeg v i]
  have hsum : 0 < ∑ i : Fin (n + 1), v i := Finset.sum_pos hpos Finset.univ_nonempty
  linarith

private lemma maxOfNeg_pos_of_sum_eq_zero {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : ∑ i, v i = 0) (hne : v ≠ 0) : 0 < maxOfNeg v := by
  refine lt_of_le_of_ne (maxOfNeg_nonneg_of_sum_eq_zero hv) (fun h0 ↦ hne ?_)
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ v i := fun i _ ↦ by
    have := neg_le_maxOfNeg v i
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hv
  ext i
  exact hall i (Finset.mem_univ i)

private lemma maxOfNeg_tangentVec_pos {n : ℕ} {z : Fin n → ℝ} (hz : z ≠ 0) :
    0 < maxOfNeg (tangentVec z) :=
  maxOfNeg_pos_of_sum_eq_zero (sum_tangentVec z) (mt (tangentVec_eq_zero_iff z).1 hz)

private lemma maxOfNeg_smul_of_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (v : Fin (n + 1) → ℝ) :
    maxOfNeg (t • v) = t * maxOfNeg v := by
  apply le_antisymm
  · rw [maxOfNeg_le_iff]
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_maxOfNeg v i) ht
  · obtain ⟨i, hi⟩ := exists_maxOfNeg_eq v
    rw [hi]
    have h := neg_le_maxOfNeg (t • v) i
    simpa [Pi.smul_apply, smul_eq_mul, mul_neg] using h

/-- The barycenter offset vector `(1 / (n + 1), …, 1 / (n + 1))` in `Fin n → ℝ`. -/
private def barycenterOffset (n : ℕ) : Fin n → ℝ :=
  fun _ ↦ 1 / (n + 1 : ℝ)

/-- The target polytope obtained by translating `TauCeti.coordinateSimplex (Fin n)` by the negative
barycenter `-barycenterOffset n`. Adding the barycenter to `tangentVec z` identifies `targetSet n`
affinely with the ordered standard `n`-simplex. -/
private def targetSet (n : ℕ) : Set (Fin n → ℝ) :=
  (-barycenterOffset n) +ᵥ coordinateSimplex (Fin n)

private lemma mem_targetSet_iff_mem_coordinateSimplex {n : ℕ} {z : Fin n → ℝ} :
    z ∈ targetSet n ↔ z + barycenterOffset n ∈ coordinateSimplex (Fin n) := by
  simp [targetSet, mem_vadd_set_iff_neg_vadd_mem, add_comm]

private lemma mem_targetSet_iff {n : ℕ} {z : Fin n → ℝ} :
    z ∈ targetSet n ↔ ∀ i : Fin (n + 1), -tangentVec z i ≤ 1 / (n + 1 : ℝ) := by
  rw [mem_targetSet_iff_mem_coordinateSimplex, mem_coordinateSimplex, Fin.forall_fin_succ]
  have hsum : ∑ j : Fin n, (z + barycenterOffset n) j =
      ∑ j : Fin n, z j + n * (1 / (n + 1 : ℝ)) := by
    simp [barycenterOffset, Finset.sum_add_distrib]
  have h1 : (n : ℝ) * (1 / (n + 1 : ℝ)) + 1 / (n + 1 : ℝ) = 1 := by
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [and_comm]
  refine and_congr ?_ (forall_congr' fun j ↦ by
    simp only [Pi.add_apply, barycenterOffset, tangentVec_succ_coord]
    constructor <;> intro h <;> linarith)
  simp only [tangentVec_zero_coord, neg_neg, hsum]
  constructor <;> intro h <;> linarith

private lemma mem_targetSet_iff_maxOfNeg {n : ℕ} {z : Fin n → ℝ} :
    z ∈ targetSet n ↔ (n + 1 : ℝ) * maxOfNeg (tangentVec z) ≤ 1 := by
  simp only [mem_targetSet_iff, maxOfNeg_le_iff, mul_comm (n + 1 : ℝ),
    ← le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)]

private lemma convex_targetSet (n : ℕ) : Convex ℝ (targetSet n) :=
  (convex_coordinateSimplex (Fin n)).vadd (-barycenterOffset n)

private lemma isCompact_targetSet (n : ℕ) : IsCompact (targetSet n) := by
  simpa [targetSet, ← image_vadd] using
    (isCompact_coordinateSimplex (Fin n)).image (continuous_const_vadd (-barycenterOffset n))

private lemma isClosed_targetSet (n : ℕ) : IsClosed (targetSet n) :=
  (isCompact_targetSet n).isClosed

private lemma targetSet_mem_nhds_zero (n : ℕ) : targetSet n ∈ nhds (0 : Fin n → ℝ) := by
  rw [← mem_interior_iff_mem_nhds, targetSet, interior_vadd, mem_vadd_set_iff_neg_vadd_mem,
    neg_neg, vadd_eq_add, add_zero, interior_coordinateSimplex]
  refine ⟨fun _ ↦ by dsimp [barycenterOffset]; positivity, ?_⟩
  simp [barycenterOffset, ← div_eq_mul_inv, div_lt_one (by positivity : (0 : ℝ) < n + 1)]

private lemma isVonNBounded_targetSet (n : ℕ) :
    Bornology.IsVonNBounded ℝ (targetSet n) :=
  NormedSpace.isVonNBounded_of_isBounded ℝ (isCompact_targetSet n).isBounded

private lemma gauge_targetSet (n : ℕ) (z : Fin n → ℝ) :
    gauge (targetSet n) z = (n + 1 : ℝ) * maxOfNeg (tangentVec z) := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have hm : 0 < maxOfNeg (tangentVec z) := maxOfNeg_tangentVec_pos hz
    have hpos : 0 < (n + 1 : ℝ) * maxOfNeg (tangentVec z) := by positivity
    rw [gauge_def']
    have hset : {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • z ∈ targetSet n} =
        Set.Ici ((n + 1 : ℝ) * maxOfNeg (tangentVec z)) := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_Ici, mem_targetSet_iff_maxOfNeg,
        tangentVec_smul]
      constructor
      · rintro ⟨hr, hmem⟩
        rw [maxOfNeg_smul_of_nonneg (inv_nonneg.2 hr.le)] at hmem
        rwa [mul_left_comm, inv_mul_le_iff₀ hr, mul_one] at hmem
      · intro hle
        have hr : 0 < r := hpos.trans_le hle
        refine ⟨hr, ?_⟩
        rw [maxOfNeg_smul_of_nonneg (inv_nonneg.2 hr.le)]
        rwa [mul_left_comm, inv_mul_le_iff₀ hr, mul_one]
    rw [hset, csInf_Ici]

/-- The offset of a simplex point from the barycenter of the standard `n`-simplex. -/
def offset {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  y.weights i - 1 / (n + 1 : ℝ)

private lemma sum_offset {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    ∑ i, offset y i = 0 := by
  unfold offset
  rw [Finset.sum_sub_distrib, StdSimplex.total_of_fintype]
  simp [mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)]

/-- The last `n` components of the offset of a simplex point from the barycenter. -/
def offsetTail {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) (j : Fin n) : ℝ :=
  offset y j.succ

private lemma tangentVec_offsetTail {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    tangentVec (offsetTail y) = offset y := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp only [tangentVec, Fin.cons_zero, offsetTail]
    have h := sum_offset y
    rw [Fin.sum_univ_succ] at h
    linarith
  · intro j
    simp [tangentVec, offsetTail]

private lemma maxOfNeg_offset_le {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    maxOfNeg (offset y) ≤ 1 / (n + 1 : ℝ) := by
  rw [maxOfNeg_le_iff]
  intro i
  have h := y.weights_nonneg i
  unfold offset
  linarith

private def rescaleHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  gaugeRescaleHomeomorph (closedBall (0 : Fin n → ℝ) 1) (targetSet n)
    (convex_closedBall 0 1) (closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1)
    (convex_targetSet n) (targetSet_mem_nhds_zero n) (isVonNBounded_targetSet n)

private lemma rescaleHomeomorph_apply (n : ℕ) (z : Fin n → ℝ) :
    rescaleHomeomorph n z = gaugeRescale (closedBall (0 : Fin n → ℝ) 1) (targetSet n) z :=
  rfl

private lemma rescaleHomeomorph_symm_apply (n : ℕ) (z : Fin n → ℝ) :
    (rescaleHomeomorph n).symm z =
      gaugeRescale (targetSet n) (closedBall (0 : Fin n → ℝ) 1) z :=
  rfl

private lemma image_rescaleHomeomorph_closedBall (n : ℕ) :
    rescaleHomeomorph n '' closedBall (0 : Fin n → ℝ) 1 = targetSet n := by
  have h := image_gaugeRescaleHomeomorph_closure
    (convex_closedBall (0 : Fin n → ℝ) 1) (closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1)
    (convex_targetSet n) (targetSet_mem_nhds_zero n) (isVonNBounded_targetSet n)
  rwa [isClosed_closedBall.closure_eq, (isClosed_targetSet n).closure_eq] at h

private def ballToTarget (n : ℕ) : closedBall (0 : Fin n → ℝ) 1 ≃ₜ targetSet n :=
  (rescaleHomeomorph n).subtype fun z ↦ by
    rw [← (rescaleHomeomorph n).injective.mem_set_image, image_rescaleHomeomorph_closedBall]

private def targetToSimplexFun (n : ℕ) (z : targetSet n) : StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm fun i ↦ 1 / (n + 1 : ℝ) + tangentVec z.val i
  nonneg i := by
    have hle := mem_targetSet_iff.1 z.property i
    dsimp
    linarith
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [Finset.sum_add_distrib, sum_tangentVec,
      mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)]

private def simplexToTargetFun (n : ℕ) (y : StdSimplex ℝ (Fin (n + 1))) : targetSet n :=
  ⟨offsetTail y, by
    rw [mem_targetSet_iff, tangentVec_offsetTail]
    intro i
    exact (neg_le_maxOfNeg (offset y) i).trans (maxOfNeg_offset_le y)⟩

private def targetToSimplex (n : ℕ) : targetSet n ≃ₜ StdSimplex ℝ (Fin (n + 1)) where
  toFun := targetToSimplexFun n
  invFun := simplexToTargetFun n
  left_inv z := by
    apply Subtype.ext
    ext j
    simp [simplexToTargetFun, targetToSimplexFun, offsetTail, offset]
  right_inv y := by
    ext i
    simp [targetToSimplexFun, simplexToTargetFun, tangentVec_offsetTail, offset]
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff,
      continuous_pi_iff]
    intro i
    exact continuous_const.add ((continuous_tangentVec i).comp continuous_subtypeVal)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun j ↦ ?_) _
    exact (StdSimplex.continuous_weights_apply (R := ℝ) j.succ).sub continuous_const

end StandardCellBallToOrderedSimplex

open StandardCellBallToOrderedSimplex

/-- The explicit radial homeomorphism from the sup-norm closed unit `n`-ball onto the ordered
standard `n`-simplex. It sends `0` to the barycenter `(1 / (n + 1), …, 1 / (n + 1))` and any
`z` to the barycentric weights `1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * maxOfNeg w)`, where
`w = (-∑ j, z j, z 0, …, z (n - 1))`. -/
def standardCellBallToOrderedSimplex (n : ℕ) :
    closedBall (0 : Fin n → ℝ) 1 ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (ballToTarget n).trans (targetToSimplex n)

private lemma weights_standardCellBallToOrderedSimplex_eq (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) (i : Fin (n + 1)) :
    (standardCellBallToOrderedSimplex n z).weights i =
      1 / (n + 1 : ℝ) + tangentVec (rescaleHomeomorph n z.val) i :=
  rfl

/-- The barycentric weight of `standardCellBallToOrderedSimplex n z` at vertex `i`. -/
lemma weights_standardCellBallToOrderedSimplex (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) (i : Fin (n + 1)) :
    (standardCellBallToOrderedSimplex n z).weights i =
      1 / (n + 1 : ℝ) +
        ‖z.val‖ * tangentVec z.val i / ((n + 1 : ℝ) * maxOfNeg (tangentVec z.val)) := by
  rw [weights_standardCellBallToOrderedSimplex_eq, rescaleHomeomorph_apply, gaugeRescale_def,
    gauge_closedBall zero_le_one, div_one, gauge_targetSet]
  by_cases hz : z.val = 0
  · simp [hz]
  · rw [tangentVec_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- At `z = 0`, all barycentric weights of `standardCellBallToOrderedSimplex n` equal `1 / (n + 1)`.
-/
lemma weights_standardCellBallToOrderedSimplex_zero (n : ℕ) (i : Fin (n + 1)) :
    (standardCellBallToOrderedSimplex n ⟨0, mem_closedBall_self zero_le_one⟩).weights i =
      1 / (n + 1 : ℝ) := by
  simp [weights_standardCellBallToOrderedSimplex]

/-- The center `0` of the ball maps to the barycenter of the standard simplex. -/
@[simp]
lemma standardCellBallToOrderedSimplex_zero (n : ℕ) :
    standardCellBallToOrderedSimplex n ⟨0, mem_closedBall_self zero_le_one⟩ =
      StdSimplex.subBarycenter Finset.univ Finset.univ_nonempty := by
  ext i
  simp [weights_standardCellBallToOrderedSimplex, StdSimplex.weights_subBarycenter]

/-- The inverse of `standardCellBallToOrderedSimplex n` sends the barycenter of the standard
simplex to `0`. -/
@[simp]
lemma standardCellBallToOrderedSimplex_symm_subBarycenter (n : ℕ) :
    (standardCellBallToOrderedSimplex n).symm
        (StdSimplex.subBarycenter Finset.univ Finset.univ_nonempty) =
      ⟨0, mem_closedBall_self zero_le_one⟩ :=
  (standardCellBallToOrderedSimplex n).symm_apply_eq.2
    (standardCellBallToOrderedSimplex_zero n).symm

private lemma coe_standardCellBallToOrderedSimplex_symm_eq (n : ℕ)
    (y : StdSimplex ℝ (Fin (n + 1))) :
    (((standardCellBallToOrderedSimplex n).symm y : closedBall (0 : Fin n → ℝ) 1) :
        Fin n → ℝ) =
      (rescaleHomeomorph n).symm (offsetTail y) :=
  -- `(standardCellBallToOrderedSimplex n).symm` unfolds through `Homeomorph.trans`
  -- (`ballToTarget` and `targetToSimplex`), `simplexToTargetFun`, and `Homeomorph.subtype`
  -- to `(rescaleHomeomorph n).symm ∘ offsetTail`.
  rfl

/-- Explicit formula for the inverse of `standardCellBallToOrderedSimplex n` in `Fin n → ℝ`. -/
lemma coe_standardCellBallToOrderedSimplex_symm_apply (n : ℕ)
    (y : StdSimplex ℝ (Fin (n + 1))) :
    (((standardCellBallToOrderedSimplex n).symm y : closedBall (0 : Fin n → ℝ) 1) : Fin n → ℝ) =
      ((n + 1 : ℝ) * maxOfNeg (offset y) / ‖offsetTail y‖) • offsetTail y := by
  rw [coe_standardCellBallToOrderedSimplex_symm_eq, rescaleHomeomorph_symm_apply, gaugeRescale_def,
    gauge_targetSet, tangentVec_offsetTail, gauge_closedBall zero_le_one, div_one]

/-- A point of the closed unit ball lies on the unit sphere precisely when its image under
`standardCellBallToOrderedSimplex n` has a vanishing barycentric weight. -/
@[simp]
lemma exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) :
    (∃ i : Fin (n + 1), (standardCellBallToOrderedSimplex n z).weights i = 0) ↔ ‖z.val‖ = 1 := by
  have hfr_ball : frontier (closedBall (0 : Fin n → ℝ) 1) = sphere (0 : Fin n → ℝ) 1 := by
    by_cases hn : n = 0
    · subst hn
      rw [show closedBall (0 : Fin 0 → ℝ) 1 = Set.univ from Set.eq_univ_of_forall fun x ↦ by
          rw [Subsingleton.elim x 0]
          simp,
        frontier_univ]
      ext x
      rw [mem_empty_iff_false, false_iff, Subsingleton.elim x 0, mem_sphere_zero_iff_norm,
        norm_zero]
      norm_num
    · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      exact frontier_closedBall' 0 1
  have hfr : rescaleHomeomorph n '' frontier (closedBall (0 : Fin n → ℝ) 1) =
      frontier (targetSet n) := by
    have hi := image_gaugeRescaleHomeomorph_interior
      (convex_closedBall (0 : Fin n → ℝ) 1) (closedBall_mem_nhds 0 one_pos)
      (NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1)
      (convex_targetSet n) (targetSet_mem_nhds_zero n) (isVonNBounded_targetSet n)
    have hc := image_gaugeRescaleHomeomorph_closure
      (convex_closedBall (0 : Fin n → ℝ) 1) (closedBall_mem_nhds 0 one_pos)
      (NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1)
      (convex_targetSet n) (targetSet_mem_nhds_zero n) (isVonNBounded_targetSet n)
    change rescaleHomeomorph n '' interior (closedBall (0 : Fin n → ℝ) 1) =
      interior (targetSet n) at hi
    change rescaleHomeomorph n '' closure (closedBall (0 : Fin n → ℝ) 1) =
      closure (targetSet n) at hc
    simp_rw [← closure_sdiff_interior, Set.image_sdiff (rescaleHomeomorph n).injective, hi, hc]
  have hnorm : ‖z.val‖ = 1 ↔ rescaleHomeomorph n z.val ∈ frontier (targetSet n) := by
    rw [← hfr, (rescaleHomeomorph n).injective.mem_set_image, hfr_ball, mem_sphere_zero_iff_norm]
  have hfr_target : frontier (targetSet n) =
      (-barycenterOffset n) +ᵥ frontier (coordinateSimplex (Fin n)) := by
    rw [targetSet, ← image_vadd, ← image_vadd]
    exact ((Homeomorph.vadd (-barycenterOffset n)).image_frontier (coordinateSimplex (Fin n))).symm
  rw [hnorm, hfr_target, mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add,
    add_comm (barycenterOffset n), mem_frontier_coordinateSimplex]
  have hmem : rescaleHomeomorph n z.val + barycenterOffset n ∈ coordinateSimplex (Fin n) := by
    rw [← mem_targetSet_iff_mem_coordinateSimplex, ← image_rescaleHomeomorph_closedBall]
    exact ⟨z.val, z.property, rfl⟩
  rw [mem_coordinateSimplex] at hmem
  rw [and_iff_right hmem, Fin.exists_fin_succ, or_comm]
  refine or_congr (exists_congr fun j ↦ ?_) ?_
  · simp [weights_standardCellBallToOrderedSimplex_eq, barycenterOffset, add_comm]
  · rw [weights_standardCellBallToOrderedSimplex_eq, tangentVec_zero_coord]
    simp only [Pi.add_apply, barycenterOffset, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    constructor <;> intro h <;> field_simp at h ⊢ <;> linarith

/-- A point of the ordered standard `n`-simplex maps to the unit sphere under
`(standardCellBallToOrderedSimplex n).symm` exactly when it has a vanishing barycentric weight. -/
lemma norm_standardCellBallToOrderedSimplex_symm_eq_one_iff (n : ℕ)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    ‖((standardCellBallToOrderedSimplex n).symm w).val‖ = 1 ↔
      ∃ i : Fin (n + 1), w.weights i = 0 := by
  rw [← exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff, Homeomorph.apply_symm_apply]

/-- A point of the closed unit ball lies in the open unit ball precisely when all barycentric
weights of its image under `standardCellBallToOrderedSimplex n` are strictly positive. -/
@[simp]
lemma forall_weights_standardCellBallToOrderedSimplex_pos_iff (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) :
    (∀ i : Fin (n + 1), 0 < (standardCellBallToOrderedSimplex n z).weights i) ↔ ‖z.val‖ < 1 := by
  have hle : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.1 z.property
  rw [lt_iff_le_and_ne, and_iff_right hle, ne_eq,
    ← exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff]
  push Not
  exact ⟨fun h i ↦ (h i).ne',
    fun h i ↦ lt_of_le_of_ne ((standardCellBallToOrderedSimplex n z).weights_nonneg i) (h i).symm⟩

/-- In dimension `1`, `standardCellBallToOrderedSimplex 1` sends `1` to vertex `1`. -/
lemma standardCellBallToOrderedSimplex_one_one :
    standardCellBallToOrderedSimplex 1 ⟨fun _ ↦ 1, by simp [Pi.norm_def]⟩ =
      StdSimplex.single 1 := by
  ext i
  have hnorm : ‖(fun _ : Fin 1 ↦ (1 : ℝ))‖ = 1 := by simp [Pi.norm_def]
  have hmax : maxOfNeg (tangentVec (fun _ : Fin 1 ↦ (1 : ℝ))) = 1 :=
    maxOfNeg_eq_of_attained (fun k ↦ by fin_cases k <;> norm_num [tangentVec])
      (i := 0) (by norm_num [tangentVec])
  rw [weights_standardCellBallToOrderedSimplex, hnorm, hmax]
  fin_cases i <;> norm_num [tangentVec, StdSimplex.weights_single]

/-- In dimension `1`, `standardCellBallToOrderedSimplex 1` sends `-1` to vertex `0`. -/
lemma standardCellBallToOrderedSimplex_one_neg_one :
    standardCellBallToOrderedSimplex 1 ⟨fun _ ↦ -1, by simp [Pi.norm_def]⟩ =
      StdSimplex.single 0 := by
  ext i
  have hnorm : ‖(fun _ : Fin 1 ↦ (-1 : ℝ))‖ = 1 := by simp [Pi.norm_def]
  have hmax : maxOfNeg (tangentVec (fun _ : Fin 1 ↦ (-1 : ℝ))) = 1 :=
    maxOfNeg_eq_of_attained (fun k ↦ by fin_cases k <;> norm_num [tangentVec])
      (i := 1) (by norm_num [tangentVec])
  rw [weights_standardCellBallToOrderedSimplex, hnorm, hmax]
  fin_cases i <;> norm_num [tangentVec, StdSimplex.weights_single]

/-- In dimension `2`, `standardCellBallToOrderedSimplex 2` sends `(1, 0)` to `(0, 2 / 3, 1 / 3)` on
the face opposite vertex `0`. -/
lemma weights_standardCellBallToOrderedSimplex_two_single :
    let z : closedBall (0 : Fin 2 → ℝ) 1 := ⟨![1, 0], by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro j; fin_cases j <;> norm_num⟩
    (standardCellBallToOrderedSimplex 2 z).weights 0 = 0 ∧
      (standardCellBallToOrderedSimplex 2 z).weights 1 = 2 / 3 ∧
      (standardCellBallToOrderedSimplex 2 z).weights 2 = 1 / 3 := by
  intro z
  have hnorm : ‖z.val‖ = 1 := by
    apply le_antisymm (mem_closedBall_zero_iff.1 z.property)
    simpa [z] using norm_le_pi_norm z.val 0
  have hmax : maxOfNeg (tangentVec z.val) = 1 :=
    maxOfNeg_eq_of_attained (fun k ↦ by fin_cases k <;> norm_num [z, tangentVec, Fin.sum_univ_two])
      (i := 0) (by norm_num [z, tangentVec, Fin.sum_univ_two])
  simp only [weights_standardCellBallToOrderedSimplex, hnorm, hmax]
  norm_num [z, tangentVec, Fin.sum_univ_two]

end TauCeti
