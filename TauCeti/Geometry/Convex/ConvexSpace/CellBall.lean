/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Order.Lattice
public import TauCeti.Geometry.Convex.ConvexSpace.Topology

/-!
# Canonical radial homeomorphism from the cell ball to the ordered standard simplex

This file constructs the explicit radial homeomorphism
`TauCeti.standardCellBallToOrderedSimplex n` from the sup-norm closed unit ball
`Metric.closedBall (0 : Fin n → ℝ) 1` (the domain of classical CW characteristic maps) onto the
ordered standard `n`-simplex `Convexity.StdSimplex ℝ (Fin (n + 1))`.

The center `0` is sent to the barycenter `(1 / (n + 1), …, 1 / (n + 1))`. A nonzero point `z`
defines the zero-sum tangent vector `w = (-∑ j, z j, z 0, …, z (n - 1))` in the ordered tangent
basis `e_{j + 1} - e_0`, with maximal negative component `m = max_i (-w_i) > 0`; its image has
barycentric weights `1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * m)`. In dimension `0`, every point of the
ball is `0` and maps to the unique point of the `0`-simplex.

Because the radial factor `‖z‖ / ((n + 1) * m)` reaches `1 / (n + 1)` precisely when `‖z‖ = 1`,
the boundary sphere `‖z‖ = 1` maps onto the simplex boundary `{y | ∃ i, y.weights i = 0}`
(`TauCeti.exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff`), and the open ball
`‖z‖ < 1` maps onto the open interior `{y | ∀ i, 0 < y.weights i}`
(`TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff`).

## Main definitions

* `TauCeti.standardCellBallToOrderedSimplex`: the radial homeomorphism from the sup-norm closed
  unit ball of `Fin n → ℝ` onto `Convexity.StdSimplex ℝ (Fin (n + 1))`.

## Main results

* `TauCeti.standardCellBallToOrderedSimplex_zero`: `0` maps to the barycenter of the simplex.
* `TauCeti.exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff`: boundary points of the
  ball correspond precisely to points of the simplex with a vanishing barycentric weight.
* `TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff`: interior points of the ball
  correspond precisely to points of the simplex with all barycentric weights strictly positive.
* `TauCeti.standardCellBallToOrderedSimplex_one_one`,
  `TauCeti.standardCellBallToOrderedSimplex_one_neg_one`, and
  `TauCeti.weights_standardCellBallToOrderedSimplex_two_single`: explicit boundary evaluations in
  dimensions `1` and `2`.
-/

public section

noncomputable section

open Convexity Metric Set

namespace TauCeti

namespace StandardCellBallToOrderedSimplex

/-- The zero-sum tangent vector `(-∑ j, z j, z 0, …, z (n - 1))` associated to `z : Fin n → ℝ` in
the ordered tangent basis `e_{j + 1} - e_0` of the standard `n`-simplex. -/
private def tangentVec {n : ℕ} (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (α := fun _ ↦ ℝ) (-∑ j, z j) z

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
private def negMax {n : ℕ} (v : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ -v i

private lemma neg_le_negMax {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    -v i ≤ negMax v :=
  Finset.le_sup' (f := fun i ↦ -v i) (Finset.mem_univ i)

private lemma exists_negMax_eq {n : ℕ} (v : Fin (n + 1) → ℝ) :
    ∃ i : Fin (n + 1), negMax v = -v i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i ↦ -v i
  exact ⟨i, hi⟩

private lemma negMax_le_iff {n : ℕ} (v : Fin (n + 1) → ℝ) (c : ℝ) :
    negMax v ≤ c ↔ ∀ i, -v i ≤ c := by
  simp [negMax, Finset.sup'_le_iff]

private lemma negMax_nonneg_of_sum_eq_zero {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : ∑ i, v i = 0) :
    0 ≤ negMax v := by
  by_contra h
  push Not at h
  have hpos : ∀ i ∈ Finset.univ, 0 < v i := fun i _ ↦ by
    linarith [neg_le_negMax v i]
  have hsum : 0 < ∑ i : Fin (n + 1), v i := Finset.sum_pos hpos Finset.univ_nonempty
  linarith

private lemma negMax_pos_of_sum_eq_zero {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : ∑ i, v i = 0) (hne : v ≠ 0) : 0 < negMax v := by
  refine lt_of_le_of_ne (negMax_nonneg_of_sum_eq_zero hv) (fun h0 ↦ hne ?_)
  have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ v i := fun i _ ↦ by
    have := neg_le_negMax v i
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hv
  ext i
  exact hall i (Finset.mem_univ i)

private lemma negMax_smul_of_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (v : Fin (n + 1) → ℝ) :
    negMax (t • v) = t * negMax v := by
  apply le_antisymm
  · rw [negMax_le_iff]
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_le_negMax v i) ht
  · obtain ⟨i, hi⟩ := exists_negMax_eq v
    rw [hi]
    have h := neg_le_negMax (t • v) i
    simpa [Pi.smul_apply, smul_eq_mul, mul_neg] using h

private lemma abs_le_mul_negMax_of_sum_eq_zero {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : ∑ i, v i = 0) (i : Fin (n + 1)) :
    |v i| ≤ (n + 1 : ℝ) * negMax v := by
  have hm : 0 ≤ negMax v := negMax_nonneg_of_sum_eq_zero hv
  have hlow : -((n + 1 : ℝ) * negMax v) ≤ v i := by
    have h1 : -v i ≤ negMax v := neg_le_negMax v i
    have h2 : negMax v ≤ (n + 1 : ℝ) * negMax v := by nlinarith
    linarith
  have hhigh : v i ≤ (n + 1 : ℝ) * negMax v := by
    have hsplit := Finset.add_sum_erase Finset.univ v (Finset.mem_univ i)
    have hvi : v i = ∑ j ∈ Finset.univ.erase i, (-v j) := by
      rw [Finset.sum_neg_distrib]
      linarith
    rw [hvi]
    calc ∑ j ∈ Finset.univ.erase i, (-v j)
        ≤ ∑ _j ∈ Finset.univ.erase i, negMax v :=
          Finset.sum_le_sum fun j _ ↦ neg_le_negMax v j
      _ = (n : ℝ) * negMax v := by simp
      _ ≤ (n + 1 : ℝ) * negMax v := by nlinarith
  exact abs_le.2 ⟨hlow, hhigh⟩

private lemma continuous_negMax {n : ℕ} :
    Continuous (negMax (n := n)) := by
  have h : (negMax (n := n)) =
      Finset.univ.sup' Finset.univ_nonempty (fun i (v : Fin (n + 1) → ℝ) ↦ -v i) := by
    funext v
    simp [negMax]
  rw [h]
  exact Finset.sup'_induction (p := Continuous) Finset.univ_nonempty
    (fun i (v : Fin (n + 1) → ℝ) ↦ -v i) (fun _ hf _ hg ↦ hf.sup hg)
    fun i _ ↦ (continuous_apply i).neg

/-- The `i`-th barycentric weight of the radial map from `Fin n → ℝ` to the affine hyperplane of
the standard `n`-simplex. -/
private def weightsFun (n : ℕ) (z : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  1 / (n + 1 : ℝ) +
    if z = 0 then 0 else ‖z‖ * tangentVec z i / ((n + 1 : ℝ) * negMax (tangentVec z))

private lemma weightsFun_zero (n : ℕ) (i : Fin (n + 1)) :
    weightsFun n 0 i = 1 / (n + 1 : ℝ) := by
  simp [weightsFun]

private lemma weightsFun_nonneg {n : ℕ} {z : Fin n → ℝ} (hz : ‖z‖ ≤ 1) (i : Fin (n + 1)) :
    0 ≤ weightsFun n z i := by
  unfold weightsFun
  split_ifs with h0
  · positivity
  · have hm : 0 < negMax (tangentVec z) :=
      negMax_pos_of_sum_eq_zero (sum_tangentVec z) (mt (tangentVec_eq_zero_iff z).1 h0)
    have hden : 0 < (n + 1 : ℝ) * negMax (tangentVec z) := by positivity
    have hle : ‖z‖ * (-tangentVec z i) ≤ negMax (tangentVec z) := by
      calc ‖z‖ * (-tangentVec z i)
          ≤ ‖z‖ * negMax (tangentVec z) :=
            mul_le_mul_of_nonneg_left (neg_le_negMax (tangentVec z) i) (norm_nonneg z)
        _ ≤ 1 * negMax (tangentVec z) := mul_le_mul_of_nonneg_right hz hm.le
        _ = negMax (tangentVec z) := one_mul _
    rw [div_add_div _ _ (by positivity) hden.ne']
    refine div_nonneg ?_ (by positivity)
    nlinarith

private lemma sum_weightsFun {n : ℕ} (z : Fin n → ℝ) :
    ∑ i, weightsFun n z i = 1 := by
  unfold weightsFun
  rw [Finset.sum_add_distrib]
  have h1 : ∑ _i : Fin (n + 1), (1 / (n + 1 : ℝ)) = 1 := by
    simp [mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)]
  rw [h1]
  split_ifs with h0
  · simp
  · have h2 : ∑ i : Fin (n + 1), ‖z‖ * tangentVec z i / ((n + 1 : ℝ) * negMax (tangentVec z)) =
        (‖z‖ / ((n + 1 : ℝ) * negMax (tangentVec z))) * ∑ i, tangentVec z i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [h2, sum_tangentVec, mul_zero, add_zero]

private lemma continuous_weightsFun (n : ℕ) (i : Fin (n + 1)) :
    Continuous fun z : Fin n → ℝ ↦ weightsFun n z i := by
  rw [continuous_iff_continuousAt]
  intro z₀
  by_cases h0 : z₀ = 0
  · subst h0
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun z hz ↦ ?_⟩
    rw [Real.dist_eq, weightsFun_zero]
    unfold weightsFun
    rw [add_sub_cancel_left]
    split_ifs with hz0
    · simpa [abs_zero] using hε
    · have hm : 0 < negMax (tangentVec z) :=
        negMax_pos_of_sum_eq_zero (sum_tangentVec z) (mt (tangentVec_eq_zero_iff z).1 hz0)
      have hden : 0 < (n + 1 : ℝ) * negMax (tangentVec z) := by positivity
      have habs : |‖z‖ * tangentVec z i / ((n + 1 : ℝ) * negMax (tangentVec z))| ≤ ‖z‖ := by
        rw [abs_div, abs_mul, abs_norm, abs_of_pos hden, div_le_iff₀ hden]
        exact mul_le_mul_of_nonneg_left
          (abs_le_mul_negMax_of_sum_eq_zero (sum_tangentVec z) i) (norm_nonneg z)
      exact lt_of_le_of_lt habs (by simpa [dist_zero_right] using hz)
  · have hopen : {z : Fin n → ℝ | z ≠ 0} ∈ nhds z₀ := isOpen_ne.mem_nhds h0
    have hm : 0 < negMax (tangentVec z₀) :=
      negMax_pos_of_sum_eq_zero (sum_tangentVec z₀) (mt (tangentVec_eq_zero_iff z₀).1 h0)
    have hcont : ContinuousAt
        (fun z : Fin n → ℝ ↦
          1 / (n + 1 : ℝ) + ‖z‖ * tangentVec z i / ((n + 1 : ℝ) * negMax (tangentVec z))) z₀ := by
      refine continuousAt_const.add ?_
      refine (continuous_norm.continuousAt.mul (continuous_tangentVec i).continuousAt).div ?_
        (by positivity)
      exact continuousAt_const.mul (continuous_negMax.comp
        (continuous_pi continuous_tangentVec)).continuousAt
    refine hcont.congr ?_
    filter_upwards [hopen] with z hz
    simp [weightsFun, hz]

private def toSimplex (n : ℕ) (z : closedBall (0 : Fin n → ℝ) 1) :
    StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (weightsFun n z.1)
  nonneg i := weightsFun_nonneg (mem_closedBall_zero_iff.1 z.2) i
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using sum_weightsFun z.1

private lemma toSimplex_weights (n : ℕ) (z : closedBall (0 : Fin n → ℝ) 1) (i : Fin (n + 1)) :
    (toSimplex n z).weights i = weightsFun n z.1 i := (rfl)

private lemma continuous_toSimplex (n : ℕ) : Continuous (toSimplex n) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff,
    continuous_pi_iff]
  intro i
  exact (continuous_weightsFun n i).comp continuous_subtype_val

/-- The offset of a simplex point from the barycenter. -/
private def offset {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  y.weights i - 1 / (n + 1 : ℝ)

private lemma sum_offset {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    ∑ i, offset y i = 0 := by
  unfold offset
  rw [Finset.sum_sub_distrib, StdSimplex.total_of_fintype]
  simp [mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)]

/-- The last `n` components of the offset from the barycenter. -/
private def offsetTail {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) (j : Fin n) : ℝ :=
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

private lemma negMax_offset_le {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    negMax (offset y) ≤ 1 / (n + 1 : ℝ) := by
  rw [negMax_le_iff]
  intro i
  have h := y.weights_nonneg i
  unfold offset
  linarith

private def invVec (n : ℕ) (y : StdSimplex ℝ (Fin (n + 1))) : Fin n → ℝ :=
  if offsetTail y = 0 then 0
  else ((n + 1 : ℝ) * negMax (offset y) / ‖offsetTail y‖) • offsetTail y

private lemma invVec_mem_closedBall (n : ℕ) (y : StdSimplex ℝ (Fin (n + 1))) :
    invVec n y ∈ closedBall (0 : Fin n → ℝ) 1 := by
  rw [mem_closedBall_zero_iff]
  unfold invVec
  split_ifs with h0
  · simp
  · have hm : 0 ≤ negMax (offset y) := negMax_nonneg_of_sum_eq_zero (sum_offset y)
    have hnorm : 0 < ‖offsetTail y‖ := norm_pos_iff.2 h0
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hnorm.ne']
    have hle := negMax_offset_le y
    calc (n + 1 : ℝ) * negMax (offset y)
        ≤ (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 := mul_one_div_cancel (by positivity)

private def fromSimplex (n : ℕ) (y : StdSimplex ℝ (Fin (n + 1))) :
    closedBall (0 : Fin n → ℝ) 1 :=
  ⟨invVec n y, invVec_mem_closedBall n y⟩

private lemma fromSimplex_toSimplex (n : ℕ) (z : closedBall (0 : Fin n → ℝ) 1) :
    fromSimplex n (toSimplex n z) = z := by
  apply Subtype.ext
  dsimp only [fromSimplex]
  by_cases hz : z.1 = 0
  · have htail : offsetTail (toSimplex n z) = 0 := by
      ext j
      simp [offsetTail, offset, toSimplex_weights, weightsFun, hz]
    simp [invVec, htail, hz]
  · have hm : 0 < negMax (tangentVec z.1) :=
      negMax_pos_of_sum_eq_zero (sum_tangentVec z.1) (mt (tangentVec_eq_zero_iff z.1).1 hz)
    set c : ℝ := ‖z.1‖ / ((n + 1 : ℝ) * negMax (tangentVec z.1)) with hc_def
    have hc : 0 < c := by positivity
    have hoff : offset (toSimplex n z) = c • tangentVec z.1 := by
      ext i
      simp only [offset, toSimplex_weights, weightsFun, hz, ↓reduceIte, add_sub_cancel_left,
        Pi.smul_apply, smul_eq_mul, hc_def]
      ring
    have htail : offsetTail (toSimplex n z) = c • z.1 := by
      ext j
      have := congrFun hoff j.succ
      simpa [offsetTail, tangentVec] using this
    have htail_ne : offsetTail (toSimplex n z) ≠ 0 := by
      rw [htail]
      exact smul_ne_zero hc.ne' hz
    have hnegMax : negMax (offset (toSimplex n z)) = c * negMax (tangentVec z.1) := by
      rw [hoff, negMax_smul_of_nonneg hc.le]
    have hmul : (n + 1 : ℝ) * negMax (offset (toSimplex n z)) = ‖z.1‖ := by
      rw [hnegMax, hc_def]
      field_simp
    unfold invVec
    simp only [htail_ne, ↓reduceIte]
    rw [hmul, htail, norm_smul, Real.norm_of_nonneg hc.le, smul_smul]
    have hcoef : ‖z.1‖ / (c * ‖z.1‖) * c = 1 := by field_simp
    rw [hcoef, one_smul]

private lemma toSimplex_fromSimplex (n : ℕ) (y : StdSimplex ℝ (Fin (n + 1))) :
    toSimplex n (fromSimplex n y) = y := by
  ext i
  rw [toSimplex_weights]
  dsimp only [fromSimplex]
  by_cases htail : offsetTail y = 0
  · have hoff : offset y = 0 := by
      rw [← tangentVec_offsetTail y, htail, (tangentVec_eq_zero_iff _).2 rfl]
    have hi := congrFun hoff i
    simp only [offset, Pi.zero_apply, sub_eq_zero] at hi
    simp [invVec, htail, weightsFun, hi]
  · have hnorm : 0 < ‖offsetTail y‖ := norm_pos_iff.2 htail
    have hm : 0 < negMax (offset y) :=
      negMax_pos_of_sum_eq_zero (sum_offset y) (by
        rw [← tangentVec_offsetTail y]
        exact mt (tangentVec_eq_zero_iff _).1 htail)
    set t : ℝ := (n + 1 : ℝ) * negMax (offset y) / ‖offsetTail y‖ with ht_def
    have ht : 0 < t := by positivity
    have hinv : invVec n y = t • offsetTail y := by simp [invVec, htail, ht_def]
    have hinv_ne : invVec n y ≠ 0 := by
      rw [hinv]
      exact smul_ne_zero ht.ne' htail
    have hinv_norm : ‖invVec n y‖ = (n + 1 : ℝ) * negMax (offset y) := by
      rw [hinv, norm_smul, Real.norm_of_nonneg ht.le, ht_def, div_mul_cancel₀ _ hnorm.ne']
    have htan : tangentVec (invVec n y) = t • offset y := by
      rw [hinv, tangentVec_smul, tangentVec_offsetTail]
    have hneg : negMax (tangentVec (invVec n y)) = t * negMax (offset y) := by
      rw [htan, negMax_smul_of_nonneg ht.le]
    unfold weightsFun
    simp only [hinv_ne, ↓reduceIte]
    rw [hinv_norm, hneg, htan, Pi.smul_apply, smul_eq_mul]
    have hfrac : (n + 1 : ℝ) * negMax (offset y) * (t * offset y i) /
        ((n + 1 : ℝ) * (t * negMax (offset y))) = offset y i := by
      field_simp
    rw [hfrac, offset]
    ring

end StandardCellBallToOrderedSimplex

open StandardCellBallToOrderedSimplex

/-- The canonical radial homeomorphism from the sup-norm closed unit `n`-ball onto the ordered
standard `n`-simplex. It sends `0` to the barycenter `(1 / (n + 1), …, 1 / (n + 1))` and any
nonzero `z` to the barycentric weights `1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * max_j (-w_j))`, where
`w = (-∑ j, z j, z 0, …, z (n - 1))`. -/
def standardCellBallToOrderedSimplex (n : ℕ) :
    closedBall (0 : Fin n → ℝ) 1 ≃ₜ StdSimplex ℝ (Fin (n + 1)) :=
  (continuous_toSimplex n).homeoOfEquivCompactToT2
    (f := {
      toFun := toSimplex n
      invFun := fromSimplex n
      left_inv := fromSimplex_toSimplex n
      right_inv := toSimplex_fromSimplex n })

/-- The barycentric weight of `standardCellBallToOrderedSimplex n z` at vertex `i`. -/
lemma weights_standardCellBallToOrderedSimplex (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) (i : Fin (n + 1)) :
    (standardCellBallToOrderedSimplex n z).weights i =
      1 / (n + 1 : ℝ) +
        if z.1 = 0 then 0
        else ‖z.1‖ * Fin.cons (α := fun _ ↦ ℝ) (-∑ j, z.1 j) z.1 i /
          ((n + 1 : ℝ) *
            Finset.univ.sup' Finset.univ_nonempty
              fun k ↦ -Fin.cons (α := fun _ ↦ ℝ) (-∑ j, z.1 j) z.1 k) :=
  (rfl)

/-- The center `0` of the ball maps to the barycenter of the standard simplex. -/
@[simp]
lemma standardCellBallToOrderedSimplex_zero (n : ℕ) :
    standardCellBallToOrderedSimplex n ⟨0, mem_closedBall_self zero_le_one⟩ =
      StdSimplex.subBarycenter Finset.univ Finset.univ_nonempty := by
  ext i
  simp [weights_standardCellBallToOrderedSimplex, StdSimplex.weights_subBarycenter]

/-- A point of the closed unit ball lies on the unit sphere precisely when its image under
`standardCellBallToOrderedSimplex n` has a vanishing barycentric weight. -/
@[simp]
lemma exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) :
    (∃ i : Fin (n + 1), (standardCellBallToOrderedSimplex n z).weights i = 0) ↔ ‖z.1‖ = 1 := by
  constructor
  · rintro ⟨i, hi⟩
    rw [weights_standardCellBallToOrderedSimplex] at hi
    by_cases hz : z.1 = 0
    · simp only [hz, ↓reduceIte, add_zero, one_div, inv_eq_zero] at hi
      exact absurd hi (by positivity)
    · simp only [hz, ↓reduceIte] at hi
      -- Rewrite in terms of `tangentVec` and `negMax` to apply the bounds proved above.
      change 1 / (n + 1 : ℝ) +
        ‖z.1‖ * tangentVec z.1 i / ((n + 1 : ℝ) * negMax (tangentVec z.1)) = 0 at hi
      have hm : 0 < negMax (tangentVec z.1) :=
        negMax_pos_of_sum_eq_zero (sum_tangentVec z.1) (mt (tangentVec_eq_zero_iff z.1).1 hz)
      have heq : ‖z.1‖ * (-tangentVec z.1 i) = negMax (tangentVec z.1) := by
        have h := congrArg (· * ((n + 1 : ℝ) * negMax (tangentVec z.1))) hi
        field_simp at h
        linarith
      have hle : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.1 z.2
      have hge : 1 ≤ ‖z.1‖ := by
        by_contra hlt
        push Not at hlt
        have := mul_le_mul_of_nonneg_left (neg_le_negMax (tangentVec z.1) i) (norm_nonneg z.1)
        nlinarith
      exact le_antisymm hle hge
  · intro h1
    have hz : z.1 ≠ 0 := fun h ↦ by simp [h] at h1
    have hm : 0 < negMax (tangentVec z.1) :=
      negMax_pos_of_sum_eq_zero (sum_tangentVec z.1) (mt (tangentVec_eq_zero_iff z.1).1 hz)
    obtain ⟨i, hi⟩ := exists_negMax_eq (tangentVec z.1)
    refine ⟨i, ?_⟩
    simp only [weights_standardCellBallToOrderedSimplex, hz, ↓reduceIte]
    -- Rewrite in terms of `tangentVec` and `negMax` to substitute `hi`.
    change 1 / (n + 1 : ℝ) +
      ‖z.1‖ * tangentVec z.1 i / ((n + 1 : ℝ) * negMax (tangentVec z.1)) = 0
    rw [h1, one_mul, show tangentVec z.1 i = -negMax (tangentVec z.1) by linarith]
    field_simp
    ring

/-- A point of the closed unit ball lies in the open unit ball precisely when all barycentric
weights of its image under `standardCellBallToOrderedSimplex n` are strictly positive. -/
@[simp]
lemma forall_weights_standardCellBallToOrderedSimplex_pos_iff (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) :
    (∀ i : Fin (n + 1), 0 < (standardCellBallToOrderedSimplex n z).weights i) ↔ ‖z.1‖ < 1 := by
  have hle : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.1 z.2
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
  have hne : (fun _ : Fin 1 ↦ (1 : ℝ)) ≠ 0 := fun h ↦ by simpa using congrFun h 0
  simp only [weights_standardCellBallToOrderedSimplex, hne, ↓reduceIte]
  have hnorm : ‖(fun _ : Fin 1 ↦ (1 : ℝ))‖ = 1 := by simp [Pi.norm_def]
  have hsup : (Finset.univ.sup' Finset.univ_nonempty
      fun k : Fin 2 ↦ -Fin.cons (α := fun _ ↦ ℝ) (-∑ _j : Fin 1, (1 : ℝ))
        (fun _ ↦ (1 : ℝ)) k) = 1 := by
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro k _
      fin_cases k <;> norm_num
    · exact le_trans (by norm_num) (Finset.le_sup' (f := fun k : Fin 2 ↦
        -Fin.cons (α := fun _ ↦ ℝ) (-∑ _j : Fin 1, (1 : ℝ)) (fun _ ↦ (1 : ℝ)) k)
        (Finset.mem_univ 0))
  rw [hnorm, hsup]
  fin_cases i <;> norm_num [StdSimplex.weights_single]

/-- In dimension `1`, `standardCellBallToOrderedSimplex 1` sends `-1` to vertex `0`. -/
lemma standardCellBallToOrderedSimplex_one_neg_one :
    standardCellBallToOrderedSimplex 1
        ⟨fun _ ↦ -1, by simp [Pi.norm_def]⟩ =
      StdSimplex.single 0 := by
  ext i
  have hne : (fun _ : Fin 1 ↦ (-1 : ℝ)) ≠ 0 := fun h ↦ by simpa using congrFun h 0
  simp only [weights_standardCellBallToOrderedSimplex, hne, ↓reduceIte]
  have hnorm : ‖(fun _ : Fin 1 ↦ (-1 : ℝ))‖ = 1 := by simp [Pi.norm_def]
  have hsup : (Finset.univ.sup' Finset.univ_nonempty
      fun k : Fin 2 ↦ -Fin.cons (α := fun _ ↦ ℝ) (-∑ _j : Fin 1, (-1 : ℝ))
        (fun _ ↦ (-1 : ℝ)) k) = 1 := by
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro k _
      fin_cases k <;> norm_num
    · exact le_trans (by norm_num) (Finset.le_sup' (f := fun k : Fin 2 ↦
        -Fin.cons (α := fun _ ↦ ℝ) (-∑ _j : Fin 1, (-1 : ℝ)) (fun _ ↦ (-1 : ℝ)) k)
        (Finset.mem_univ 1))
  rw [hnorm, hsup]
  fin_cases i <;> norm_num [StdSimplex.weights_single]

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
  have hne : z.1 ≠ 0 := fun h ↦ by simpa [z] using congrFun h 0
  have hnorm : ‖z.1‖ = 1 := by
    apply le_antisymm (mem_closedBall_zero_iff.1 z.2)
    simpa [z] using norm_le_pi_norm z.1 0
  have hsup : (Finset.univ.sup' Finset.univ_nonempty
      fun k : Fin 3 ↦ -Fin.cons (α := fun _ ↦ ℝ) (-∑ j : Fin 2, z.1 j) z.1 k) = 1 := by
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro k _
      fin_cases k <;> norm_num [z, Fin.sum_univ_two]
    · exact le_trans (by norm_num [z, Fin.sum_univ_two]) (Finset.le_sup' (f := fun k : Fin 3 ↦
        -Fin.cons (α := fun _ ↦ ℝ) (-∑ j : Fin 2, z.1 j) z.1 k) (Finset.mem_univ 0))
  simp only [weights_standardCellBallToOrderedSimplex, hne, ↓reduceIte, hnorm, hsup]
  norm_num [z, Fin.sum_univ_two]

end TauCeti
