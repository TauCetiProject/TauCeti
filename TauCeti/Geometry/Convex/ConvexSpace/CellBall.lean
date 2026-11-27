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
import Mathlib.Topology.Order.Lattice

/-!
# Explicit radial homeomorphism from the cell ball to the ordered standard simplex

This file constructs the explicit radial homeomorphism
`TauCeti.standardCellBallToOrderedSimplex n` from the sup-norm closed unit ball
`Metric.closedBall (0 : Fin n → ℝ) 1` (the domain of classical CW characteristic maps) onto the
ordered standard `n`-simplex `Convexity.StdSimplex ℝ (Fin (n + 1))`.

The center `0` is sent to the barycenter `(1 / (n + 1), …, 1 / (n + 1))`. A nonzero point `z`
defines the zero-sum tangent vector `w = (-∑ j, z j, z 0, …, z (n - 1))` in the ordered tangent
basis `e_{j + 1} - e_0`, with maximal negative component `m = max_i (-w_i) > 0`; its image has
barycentric weights `1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * m)`. In dimension `0`, every point of the
ball is `0` and maps to the unique point of the `0`-simplex.

Because the smallest weight is `(1 - ‖z‖) / (n + 1)`, attained where `-w_i = m`, the boundary
sphere `‖z‖ = 1` maps onto the simplicial boundary `{y | ∃ i, y.weights i = 0}`
(`TauCeti.exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff`), and the open ball
`‖z‖ < 1` maps onto the open interior `{y | ∀ i, 0 < y.weights i}`
(`TauCeti.forall_weights_standardCellBallToOrderedSimplex_pos_iff`).

## Main definitions

* `TauCeti.standardCellBallToOrderedSimplex`: the explicit radial homeomorphism from the sup-norm
  closed unit ball of `Fin n → ℝ` onto `Convexity.StdSimplex ℝ (Fin (n + 1))`.

## Main results

* `TauCeti.weights_standardCellBallToOrderedSimplex`,
  `TauCeti.weights_standardCellBallToOrderedSimplex_zero`, and
  `TauCeti.weights_standardCellBallToOrderedSimplex_of_ne_zero`: barycentric weight formulas at zero
  and away from zero.
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
def negMax {n : ℕ} (v : Fin (n + 1) → ℝ) : ℝ :=
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

@[simp]
lemma negMax_zero {n : ℕ} : negMax (0 : Fin (n + 1) → ℝ) = 0 := by
  apply le_antisymm
  · rw [negMax_le_iff]; intro i; simp
  · simpa using neg_le_negMax (0 : Fin (n + 1) → ℝ) 0

/-- If every `-v j` is at most `c` and `-v i = c` at some vertex `i`, then `negMax v = c`. -/
lemma negMax_eq_of_attained {n : ℕ} {v : Fin (n + 1) → ℝ} {c : ℝ}
    (hle : ∀ j, -v j ≤ c) {i : Fin (n + 1)} (heq : -v i = c) :
    negMax v = c :=
  le_antisymm ((negMax_le_iff v c).2 hle) (heq ▸ neg_le_negMax v i)

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

private lemma negMax_tangentVec_pos {n : ℕ} {z : Fin n → ℝ} (hz : z ≠ 0) :
    0 < negMax (tangentVec z) :=
  negMax_pos_of_sum_eq_zero (sum_tangentVec z) (mt (tangentVec_eq_zero_iff z).1 hz)

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

/-- The target polytope `{z | (n + 1) * negMax (tangentVec z) ≤ 1}`, which identifies affinely
with the ordered standard `n`-simplex by adding the barycenter to `tangentVec z`. -/
private def targetSet (n : ℕ) : Set (Fin n → ℝ) :=
  {z | (n + 1 : ℝ) * negMax (tangentVec z) ≤ 1}

private lemma mem_targetSet_iff {n : ℕ} {z : Fin n → ℝ} :
    z ∈ targetSet n ↔ ∀ i : Fin (n + 1), -tangentVec z i ≤ 1 / (n + 1 : ℝ) := by
  simp only [targetSet, Set.mem_ofPred_eq, mul_comm (n + 1 : ℝ), ← le_div_iff₀ (by positivity :
    (0 : ℝ) < n + 1), negMax_le_iff]

private lemma convex_targetSet (n : ℕ) : Convex ℝ (targetSet n) := by
  intro x hx y hy a b ha hb hab
  rw [mem_targetSet_iff] at hx hy ⊢
  intro i
  have hadd : tangentVec (a • x + b • y) = a • tangentVec x + b • tangentVec y := by
    ext k
    refine Fin.cases ?_ ?_ k
    · simp [tangentVec, Finset.mul_sum, Finset.sum_add_distrib]
      ring
    · simp [tangentVec]
  rw [hadd, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, neg_add]
  calc -(a * tangentVec x i) + -(b * tangentVec y i)
      = a * (-tangentVec x i) + b * (-tangentVec y i) := by ring
    _ ≤ a * (1 / (n + 1 : ℝ)) + b * (1 / (n + 1 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = 1 / (n + 1 : ℝ) := by rw [← add_mul, hab, one_mul]

private lemma isClosed_targetSet (n : ℕ) : IsClosed (targetSet n) :=
  isClosed_le (continuous_const.mul (continuous_negMax.comp (continuous_pi continuous_tangentVec)))
    continuous_const

private lemma targetSet_mem_nhds_zero (n : ℕ) : targetSet n ∈ nhds (0 : Fin n → ℝ) := by
  have hopen : IsOpen {z : Fin n → ℝ | (n + 1 : ℝ) * negMax (tangentVec z) < 1} :=
    isOpen_lt (continuous_const.mul (continuous_negMax.comp (continuous_pi continuous_tangentVec)))
      continuous_const
  have h0 : (0 : Fin n → ℝ) ∈ {z : Fin n → ℝ | (n + 1 : ℝ) * negMax (tangentVec z) < 1} := by
    simp
  refine Filter.mem_of_superset (hopen.mem_nhds h0) fun z hz ↦ ?_
  simp only [targetSet, Set.mem_ofPred_eq] at hz ⊢
  exact le_of_lt hz

private lemma targetSet_subset_closedBall (n : ℕ) :
    targetSet n ⊆ closedBall (0 : Fin n → ℝ) 1 := by
  intro z hz
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  have hle : |tangentVec z j.succ| ≤ (n + 1 : ℝ) * negMax (tangentVec z) :=
    abs_le_mul_negMax_of_sum_eq_zero (sum_tangentVec z) j.succ
  exact hle.trans hz

private lemma isVonNBounded_targetSet (n : ℕ) :
    Bornology.IsVonNBounded ℝ (targetSet n) :=
  (NormedSpace.isVonNBounded_closedBall ℝ (Fin n → ℝ) 1).subset (targetSet_subset_closedBall n)

private lemma gauge_targetSet (n : ℕ) (z : Fin n → ℝ) :
    gauge (targetSet n) z = (n + 1 : ℝ) * negMax (tangentVec z) := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have hm : 0 < negMax (tangentVec z) := negMax_tangentVec_pos hz
    have hpos : 0 < (n + 1 : ℝ) * negMax (tangentVec z) := by positivity
    rw [gauge_def']
    have hset : {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • z ∈ targetSet n} =
        Set.Ici ((n + 1 : ℝ) * negMax (tangentVec z)) := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_Ioi, Set.mem_Ici, targetSet, tangentVec_smul]
      constructor
      · rintro ⟨hr, hmem⟩
        rw [negMax_smul_of_nonneg (inv_nonneg.2 hr.le)] at hmem
        rwa [mul_left_comm, inv_mul_le_iff₀ hr, mul_one] at hmem
      · intro hle
        have hr : 0 < r := hpos.trans_le hle
        refine ⟨hr, ?_⟩
        rw [negMax_smul_of_nonneg (inv_nonneg.2 hr.le)]
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

private lemma offsetTail_eq_zero_iff {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    offsetTail y = 0 ↔ y = StdSimplex.subBarycenter Finset.univ Finset.univ_nonempty := by
  constructor
  · intro h
    have hoff : offset y = 0 := by
      rw [← tangentVec_offsetTail y, h, tangentVec_zero]
    ext i
    have hi := congrFun hoff i
    simp only [offset, Pi.zero_apply, sub_eq_zero] at hi
    simpa [StdSimplex.weights_subBarycenter] using hi
  · rintro rfl
    ext j
    simp [offsetTail, offset, StdSimplex.weights_subBarycenter]

private lemma negMax_offset_le {n : ℕ} (y : StdSimplex ℝ (Fin (n + 1))) :
    negMax (offset y) ≤ 1 / (n + 1 : ℝ) := by
  rw [negMax_le_iff]
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
    exact (neg_le_negMax (offset y) i).trans (negMax_offset_le y)⟩

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
nonzero `z` to the barycentric weights `1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * max_j (-w_j))`, where
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
        if z.val = 0 then 0
        else ‖z.val‖ * tangentVec z.val i / ((n + 1 : ℝ) * negMax (tangentVec z.val)) := by
  rw [weights_standardCellBallToOrderedSimplex_eq, rescaleHomeomorph_apply, gaugeRescale_def,
    gauge_closedBall zero_le_one, div_one, gauge_targetSet]
  split_ifs with hz
  · simp [hz]
  · rw [tangentVec_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- At `z = 0`, all barycentric weights of `standardCellBallToOrderedSimplex n` equal `1 / (n + 1)`.
-/
lemma weights_standardCellBallToOrderedSimplex_zero (n : ℕ) (i : Fin (n + 1)) :
    (standardCellBallToOrderedSimplex n ⟨0, mem_closedBall_self zero_le_one⟩).weights i =
      1 / (n + 1 : ℝ) := by
  simp [weights_standardCellBallToOrderedSimplex]

/-- Away from `0`, the `i`-th barycentric weight of `standardCellBallToOrderedSimplex n z` is
`1 / (n + 1) + ‖z‖ * w_i / ((n + 1) * negMax w)`, where `w = tangentVec z.val`. -/
lemma weights_standardCellBallToOrderedSimplex_of_ne_zero {n : ℕ}
    {z : closedBall (0 : Fin n → ℝ) 1} (hz : z.val ≠ 0) (i : Fin (n + 1)) :
    (standardCellBallToOrderedSimplex n z).weights i =
      1 / (n + 1 : ℝ) +
        ‖z.val‖ * tangentVec z.val i / ((n + 1 : ℝ) * negMax (tangentVec z.val)) := by
  simp [weights_standardCellBallToOrderedSimplex, hz]

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

open scoped Classical in
/-- Explicit formula for the inverse of `standardCellBallToOrderedSimplex n` in `Fin n → ℝ`. -/
lemma coe_standardCellBallToOrderedSimplex_symm_apply (n : ℕ)
    (y : StdSimplex ℝ (Fin (n + 1))) :
    (((standardCellBallToOrderedSimplex n).symm y : closedBall (0 : Fin n → ℝ) 1) : Fin n → ℝ) =
      if y = StdSimplex.subBarycenter Finset.univ Finset.univ_nonempty then 0
      else ((n + 1 : ℝ) * negMax (offset y) / ‖offsetTail y‖) • offsetTail y := by
  rw [coe_standardCellBallToOrderedSimplex_symm_eq, rescaleHomeomorph_symm_apply, gaugeRescale_def,
    gauge_targetSet, tangentVec_offsetTail, gauge_closedBall zero_le_one, div_one]
  split_ifs with hy
  · have htail : offsetTail y = 0 := (offsetTail_eq_zero_iff y).2 hy
    simp [htail]
  · rfl

/-- A point of the closed unit ball lies on the unit sphere precisely when its image under
`standardCellBallToOrderedSimplex n` has a vanishing barycentric weight. -/
@[simp]
lemma exists_weights_standardCellBallToOrderedSimplex_eq_zero_iff (n : ℕ)
    (z : closedBall (0 : Fin n → ℝ) 1) :
    (∃ i : Fin (n + 1), (standardCellBallToOrderedSimplex n z).weights i = 0) ↔ ‖z.val‖ = 1 := by
  let u : Fin n → ℝ := rescaleHomeomorph n z.val
  have hu : u ∈ targetSet n :=
    (image_rescaleHomeomorph_closedBall n).subset ⟨z.val, z.property, rfl⟩
  have hgauge : gauge (targetSet n) u = ‖z.val‖ := by
    calc gauge (targetSet n) u
        = gauge (closedBall (0 : Fin n → ℝ) 1) z.val :=
          gauge_gaugeRescale (closedBall (0 : Fin n → ℝ) 1)
            (absorbent_nhds_zero (targetSet_mem_nhds_zero n)) (isVonNBounded_targetSet n) z.val
      _ = ‖z.val‖ := by rw [gauge_closedBall zero_le_one, div_one]
  have h1 : (∃ i : Fin (n + 1), (standardCellBallToOrderedSimplex n z).weights i = 0) ↔
      negMax (tangentVec u) = 1 / (n + 1 : ℝ) := by
    constructor
    · rintro ⟨i, hi⟩
      rw [weights_standardCellBallToOrderedSimplex_eq] at hi
      exact negMax_eq_of_attained (mem_targetSet_iff.1 hu)
        (by rw [add_comm] at hi; exact neg_eq_of_add_eq_zero_right hi)
    · intro hmax
      obtain ⟨i, hi⟩ := exists_negMax_eq (tangentVec u)
      refine ⟨i, ?_⟩
      rw [weights_standardCellBallToOrderedSimplex_eq, ← neg_neg (tangentVec u i), ← hi, hmax]
      ring
  have h2 : negMax (tangentVec u) = 1 / (n + 1 : ℝ) ↔
      (n + 1 : ℝ) * negMax (tangentVec u) = 1 := by
    rw [mul_comm, ← eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)]
  rw [h1, h2, ← gauge_targetSet n u, hgauge]

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
  have hne : (fun _ : Fin 1 ↦ (1 : ℝ)) ≠ 0 := fun h ↦ by simpa using congrFun h 0
  have hnorm : ‖(fun _ : Fin 1 ↦ (1 : ℝ))‖ = 1 := by simp [Pi.norm_def]
  have hmax : negMax (tangentVec (fun _ : Fin 1 ↦ (1 : ℝ))) = 1 :=
    negMax_eq_of_attained (fun k ↦ by fin_cases k <;> norm_num [tangentVec])
      (i := 0) (by norm_num [tangentVec])
  rw [weights_standardCellBallToOrderedSimplex_of_ne_zero hne, hnorm, hmax]
  fin_cases i <;> norm_num [tangentVec, StdSimplex.weights_single]

/-- In dimension `1`, `standardCellBallToOrderedSimplex 1` sends `-1` to vertex `0`. -/
lemma standardCellBallToOrderedSimplex_one_neg_one :
    standardCellBallToOrderedSimplex 1 ⟨fun _ ↦ -1, by simp [Pi.norm_def]⟩ =
      StdSimplex.single 0 := by
  ext i
  have hne : (fun _ : Fin 1 ↦ (-1 : ℝ)) ≠ 0 := fun h ↦ by simpa using congrFun h 0
  have hnorm : ‖(fun _ : Fin 1 ↦ (-1 : ℝ))‖ = 1 := by simp [Pi.norm_def]
  have hmax : negMax (tangentVec (fun _ : Fin 1 ↦ (-1 : ℝ))) = 1 :=
    negMax_eq_of_attained (fun k ↦ by fin_cases k <;> norm_num [tangentVec])
      (i := 1) (by norm_num [tangentVec])
  rw [weights_standardCellBallToOrderedSimplex_of_ne_zero hne, hnorm, hmax]
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
  have hne : z.val ≠ 0 := fun h ↦ by simpa [z] using congrFun h 0
  have hnorm : ‖z.val‖ = 1 := by
    apply le_antisymm (mem_closedBall_zero_iff.1 z.property)
    simpa [z] using norm_le_pi_norm z.val 0
  have hmax : negMax (tangentVec z.val) = 1 :=
    negMax_eq_of_attained (fun k ↦ by fin_cases k <;> norm_num [z, tangentVec, Fin.sum_univ_two])
      (i := 0) (by norm_num [z, tangentVec, Fin.sum_univ_two])
  simp only [weights_standardCellBallToOrderedSimplex_of_ne_zero hne, hnorm, hmax]
  norm_num [z, tangentVec, Fin.sum_univ_two]

end TauCeti
