/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Ultra
public import TauCeti.Algebra.Order.BigOperators.ProdSubProd
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The closed unit ball and products of elements close to one in ultrametric normed rings

An ultrametric seminormed ring is a nonarchimedean topological ring: its open balls about zero
are open additive subgroups. In an ultrametric seminormed ring with `‖1‖ = 1`, the closed unit
ball is an open subring. In an ultrametric normed ring, a finite product of elements each within
`ε ≤ 1` of `1` is again within `ε` of `1`. A series `∑_{n ≥ 1} f(qⁿ w)` of terms bounded by their
arguments is bounded by its first argument `q w`, and for `1`-Lipschitz `f` it depends on `w` in a
`‖q‖`-Lipschitz way. The rational functions `t / (1 - t)²`, `t² / (1 - t)³` and `-t / (1 - t)³` are
`1`-Lipschitz on the open unit ball of an ultrametric field, and `(1 - v)³ / v` is `1`-Lipschitz on
its unit sphere.

Integer casts have norm at most `‖1‖`, without requiring the seminorm to be normalized. When
`‖1‖ = 1`, arbitrarily large natural numbers have norm exactly one.

## Main results

* `IsUltrametricDist.exists_lt_norm_natCast_eq_one`: arbitrarily large natural numbers have norm
  one in an ultrametric seminormed ring with `‖1‖ = 1`.
* `IsUltrametricDist.nonarchimedeanRing`: an ultrametric seminormed ring is a nonarchimedean
  ring.
* `Subring.unitClosedBall`: the closed unit ball of an ultrametric seminormed ring with
  `‖1‖ = 1`, an open subring.
* `TauCeti.norm_one_sub_of_norm_lt_one`: subtracting an element of norm less than one from one
  leaves the norm equal to one; `TauCeti.norm_eq_one_of_norm_one_sub_lt_one`: an element within
  less than one of one has norm one; `TauCeti.norm_div_one_sub_pow`: dividing by a power of such
  a `1 - w` does not change norms.
* `TauCeti.norm_tsum_le_norm_mul`: a one-sided series `∑_{n ≥ 1} f(qⁿ w)` whose terms are bounded
  by their arguments has norm at most `‖q w‖`.
* `TauCeti.norm_tsum_sub_tsum_le_norm_mul`: for `f` vanishing at zero and `1`-Lipschitz on the
  open unit ball, `∑_{n ≥ 1} f(qⁿ w)` and `∑_{n ≥ 1} f(qⁿ w')` differ by at most `‖q (w - w')‖`.
* `TauCeti.norm_div_one_sub_sq_sub_div_one_sub_sq_le`,
  `TauCeti.norm_sq_div_one_sub_pow_three_sub_sq_div_one_sub_pow_three_le`,
  `TauCeti.norm_neg_div_one_sub_pow_three_sub_neg_div_one_sub_pow_three_le`: three rational
  functions are `1`-Lipschitz on the open unit ball;
  `TauCeti.norm_one_sub_pow_three_div_sub_one_sub_pow_three_div_le`: `(1 - v)³ / v` is
  `1`-Lipschitz on the unit sphere.
* `TauCeti.one_le_norm_one_sub_of_norm_ne_one`: subtracting an element whose norm is not one
  from one gives norm at least one.
* `TauCeti.norm_mul_sub_one_lt` and `TauCeti.norm_prod_sub_one_lt`
* `TauCeti.norm_prod_sub_prod_le`: a uniform perturbation bound for finite products.
-/

public section

/-- Integer casts in an ultrametric seminormed ring have norm at most the norm of one. -/
theorem IsUltrametricDist.norm_intCast_le_norm_one {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] (z : ℤ) : ‖(z : R)‖ ≤ ‖(1 : R)‖ := by
  simpa using IsUltrametricDist.norm_zsmul_le (1 : R) z

/-- In an ultrametric seminormed ring with `‖1‖ = 1`, arbitrarily large natural numbers have norm
one: of two consecutive natural numbers, one has norm one, since their difference does. -/
theorem IsUltrametricDist.exists_lt_norm_natCast_eq_one (R : Type*) [SeminormedRing R]
    [NormOneClass R] [IsUltrametricDist R] (N : ℕ) : ∃ m, N < m ∧ ‖(m : R)‖ = 1 := by
  by_contra! h
  have h1 := (IsUltrametricDist.norm_natCast_le_one R (N + 1)).lt_of_ne (h _ (by omega))
  have h2 := (IsUltrametricDist.norm_natCast_le_one R (N + 2)).lt_of_ne (h _ (by omega))
  have h3 := IsUltrametricDist.norm_add_le_max ((N + 2 : ℕ) : R) (-((N + 1 : ℕ) : R))
  have hsum : ((N + 2 : ℕ) : R) + -((N + 1 : ℕ) : R) = 1 := by
    push_cast
    abel_nf
    norm_num
  rw [norm_neg, hsum, norm_one] at h3
  exact (h3.trans_lt (max_lt h2 h1)).false

/-- **An ultrametric seminormed ring is a nonarchimedean ring.** This is the ring form of
Mathlib's `IsUltrametricDist.nonarchimedeanAddGroup`: every neighbourhood of zero contains an open
additive subgroup, namely a small open ball. -/
instance IsUltrametricDist.nonarchimedeanRing {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] : NonarchimedeanRing R where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

section UnitClosedBall

variable (R : Type*) [SeminormedRing R] [IsUltrametricDist R] [NormOneClass R]

/-- **The closed unit ball of an ultrametric seminormed ring with `‖1‖ = 1` is a subring**: it is
the submonoid `Submonoid.unitClosedBall` and the open additive subgroup
`IsUltrametricDist.closedBall_openAddSubgroup`. -/
def Subring.unitClosedBall : Subring R :=
  { Submonoid.unitClosedBall R,
    (IsUltrametricDist.closedBall_openAddSubgroup R one_pos : AddSubgroup R) with }

variable {R} in
/-- An element lies in the closed unit ball exactly when its norm is at most one. -/
@[simp]
theorem Subring.mem_unitClosedBall {x : R} : x ∈ Subring.unitClosedBall R ↔ ‖x‖ ≤ 1 :=
  Submonoid.mem_unitClosedBall R

/-- The carrier of `Subring.unitClosedBall R` is `Metric.closedBall 0 1`. -/
@[simp]
theorem Subring.coe_unitClosedBall :
    (Subring.unitClosedBall R : Set R) = Metric.closedBall 0 1 := by
  ext
  simp

/-- The closed unit ball of an ultrametric seminormed ring is open. -/
theorem Subring.isOpen_unitClosedBall : IsOpen (Subring.unitClosedBall R : Set R) :=
  (IsUltrametricDist.closedBall_openAddSubgroup R one_pos).isOpen'

end UnitClosedBall

namespace TauCeti

/-- An element strictly smaller than one does not change the norm of one when subtracted. -/
@[simp]
theorem norm_one_sub_of_norm_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ < 1) : ‖1 - x‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simp [hx.le]
  · exact ne_of_gt (by simpa using hx)

/-- An element at distance less than one from one has norm one. -/
theorem norm_eq_one_of_norm_one_sub_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖1 - x‖ < 1) : ‖x‖ = 1 := by
  simpa using norm_one_sub_of_norm_lt_one hx

/-- Subtracting an element whose norm is not one from one gives norm at least one. -/
theorem one_le_norm_one_sub_of_norm_ne_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ ≠ 1) : 1 ≤ ‖1 - x‖ := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hx.symm)]
  simp

/-- Dividing by a power of `1 - w` with `‖w‖ < 1` does not change norms in an ultrametric normed
division ring. -/
theorem norm_div_one_sub_pow {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] (z : K)
    {w : K} (hw : ‖w‖ < 1) (k : ℕ) : ‖z / (1 - w) ^ k‖ = ‖z‖ := by
  rw [norm_div, norm_pow, norm_one_sub_of_norm_lt_one hw, one_pow, div_one]

/-- A one-sided series `∑_{n ≥ 1} f(qⁿ w)` with values in an ultrametric group, whose terms are
bounded by their arguments, has norm at most `‖q w‖` when `‖q‖ ≤ 1` and `‖q w‖ < 1`. -/
theorem norm_tsum_le_norm_mul {R E : Type*} [SeminormedRing R]
    [SeminormedAddCommGroup E] [IsUltrametricDist E] (f : R → E)
    (hf : ∀ w : R, ‖w‖ < 1 → ‖f w‖ ≤ ‖w‖) {q w : R} (hq : ‖q‖ ≤ 1) (hw : ‖q * w‖ < 1) :
    ‖∑' n : ℕ, f (q ^ (n + 1) * w)‖ ≤ ‖q * w‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  have h : ‖q ^ (n + 1) * w‖ ≤ ‖q * w‖ := (norm_pow_succ_mul_le_pow_mul q w n).trans
    (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq))
  exact (hf _ (h.trans_lt hw)).trans h

/-- Two one-sided series `∑_{n ≥ 1} f(qⁿ w)` and `∑_{n ≥ 1} f(qⁿ w')`, with values in a complete
ultrametric group, differ by at most `‖q (w - w')‖` when `f` vanishes at zero and is `1`-Lipschitz
on the open unit ball, `‖q‖ < 1`, and `‖q w‖, ‖q w'‖ < 1`. -/
theorem norm_tsum_sub_tsum_le_norm_mul {R E : Type*} [SeminormedRing R]
    [NormedAddCommGroup E] [IsUltrametricDist E] [CompleteSpace E] (f : R → E) (hf₀ : f 0 = 0)
    (hf : ∀ t t' : R, ‖t‖ < 1 → ‖t'‖ < 1 → ‖f t - f t'‖ ≤ ‖t - t'‖) {q w w' : R}
    (hq : ‖q‖ < 1) (hw : ‖q * w‖ < 1) (hw' : ‖q * w'‖ < 1) :
    ‖∑' n : ℕ, f (q ^ (n + 1) * w) - ∑' n : ℕ, f (q ^ (n + 1) * w')‖ ≤ ‖q * (w - w')‖ := by
  have hle (z : R) (n : ℕ) : ‖q ^ (n + 1) * z‖ ≤ ‖q * z‖ :=
    (norm_pow_succ_mul_le_pow_mul q z n).trans
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le))
  -- the terms are bounded by `‖q‖ⁿ ‖q z‖`, so they tend to zero and the series converges
  have hs (z : R) (hz : ‖q * z‖ < 1) : Summable fun n : ℕ ↦ f (q ^ (n + 1) * z) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop]
    refine squeeze_zero_norm (fun n ↦ ?_) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).mul_const ‖q * z‖)
    have h := hf _ 0 ((hle z n).trans_lt hz) (by rw [norm_zero]; exact one_pos)
    rw [hf₀, sub_zero, sub_zero] at h
    exact h.trans (norm_pow_succ_mul_le_pow_mul q z n)
  rw [← (hs w hw).tsum_sub (hs w' hw')]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  refine (hf _ _ ((hle w n).trans_lt hw) ((hle w' n).trans_lt hw')).trans ?_
  rw [← mul_sub]
  exact hle _ n

section Lipschitz

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- If `a (1 - t')ᵏ - a' (1 - t)ᵏ = (t - t') P` with `‖P‖ ≤ 1` and `t, t'` in the open unit ball,
then `a / (1 - t)ᵏ` and `a' / (1 - t')ᵏ` are within `‖t - t'‖` of each other. -/
private theorem norm_div_one_sub_pow_sub_div_one_sub_pow_le {t t' a a' P : K} (k : ℕ)
    (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) (hP : ‖P‖ ≤ 1)
    (h : a * (1 - t') ^ k - (1 - t) ^ k * a' = (t - t') * P) :
    ‖a / (1 - t) ^ k - a' / (1 - t') ^ k‖ ≤ ‖t - t'‖ := by
  have hne {s : K} (hs : ‖s‖ < 1) : (1 - s) ^ k ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mp (by rw [norm_one_sub_of_norm_lt_one hs]; exact one_ne_zero))
  rw [div_sub_div _ _ (hne ht) (hne ht'), h]
  simpa [ht, ht'] using mul_le_of_le_one_right (norm_nonneg (t - t')) hP

/-- `t ↦ t / (1 - t)²` is `1`-Lipschitz on the open unit ball of an ultrametric field. -/
theorem norm_div_one_sub_sq_sub_div_one_sub_sq_le {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t / (1 - t) ^ 2 - t' / (1 - t') ^ 2‖ ≤ ‖t - t'‖ := by
  have h₁ := Subring.mem_unitClosedBall.mpr ht.le
  have h₂ := Subring.mem_unitClosedBall.mpr ht'.le
  refine norm_div_one_sub_pow_sub_div_one_sub_pow_le 2 ht ht' (P := 1 - t * t')
    (Subring.mem_unitClosedBall.mp ?_) (by ring)
  apply_rules [sub_mem, mul_mem, one_mem]

/-- `t ↦ t² / (1 - t)³` is `1`-Lipschitz on the open unit ball of an ultrametric field. -/
theorem norm_sq_div_one_sub_pow_three_sub_sq_div_one_sub_pow_three_le {t t' : K}
    (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) : ‖t ^ 2 / (1 - t) ^ 3 - t' ^ 2 / (1 - t') ^ 3‖ ≤ ‖t - t'‖ := by
  have h₁ := Subring.mem_unitClosedBall.mpr ht.le
  have h₂ := Subring.mem_unitClosedBall.mpr ht'.le
  refine norm_div_one_sub_pow_sub_div_one_sub_pow_le 3 ht ht'
    (P := t + t' - t * t' - t * t' - t * t' + t ^ 2 * t' ^ 2) (Subring.mem_unitClosedBall.mp ?_)
    (by ring)
  apply_rules [add_mem, sub_mem, mul_mem, pow_mem]

/-- `t ↦ -t / (1 - t)³` is `1`-Lipschitz on the open unit ball of an ultrametric field. -/
theorem norm_neg_div_one_sub_pow_three_sub_neg_div_one_sub_pow_three_le {t t' : K}
    (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) : ‖-t / (1 - t) ^ 3 - -t' / (1 - t') ^ 3‖ ≤ ‖t - t'‖ := by
  have h₁ := Subring.mem_unitClosedBall.mpr ht.le
  have h₂ := Subring.mem_unitClosedBall.mpr ht'.le
  refine norm_div_one_sub_pow_sub_div_one_sub_pow_le 3 ht ht'
    (P := -1 + t * t' + t * t' + t * t' - t * t' * (t + t')) (Subring.mem_unitClosedBall.mp ?_)
    (by ring)
  apply_rules [add_mem, sub_mem, mul_mem, neg_mem, one_mem]

/-- `v ↦ (1 - v)³ / v` is `1`-Lipschitz on the unit sphere of an ultrametric field. -/
theorem norm_one_sub_pow_three_div_sub_one_sub_pow_three_div_le {v w : K} (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) :
    ‖(1 - v) ^ 3 / v - (1 - w) ^ 3 / w‖ ≤ ‖v - w‖ := by
  have h₀ : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have h₀' : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have e : (1 - v) ^ 3 / v - (1 - w) ^ 3 / w =
      (w - v) * (1 - v * w - v * w - v * w + v * w * (v + w)) / (v * w) := by
    field_simp
    ring
  have h₁ := Subring.mem_unitClosedBall.mpr hv.le
  have h₂ := Subring.mem_unitClosedBall.mpr hw.le
  have hP : 1 - v * w - v * w - v * w + v * w * (v + w) ∈ Subring.unitClosedBall K := by
    apply_rules [add_mem, sub_mem, mul_mem, one_mem]
  rw [e, norm_div, norm_mul, norm_mul, hv, hw, mul_one, div_one, norm_sub_rev]
  exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp hP)

end Lipschitz

/-- In an ultrametric normed ring, if `a` and `b` are both within `ε ≤ 1` of `1`, so is
`a * b`. -/
theorem norm_mul_sub_one_lt {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {a b : R} {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a - 1‖ < ε)
    (hb : ‖b - 1‖ < ε) : ‖a * b - 1‖ < ε := by
  have hnorm : ‖a‖ ≤ 1 := by
    simpa [ha.le.trans hε] using IsUltrametricDist.norm_add_one_le_max_norm_one (a - 1)
  calc ‖a * b - 1‖ = ‖a * (b - 1) + (a - 1)‖ := by
        rw [mul_sub, mul_one, sub_add_sub_cancel]
    _ ≤ max ‖a * (b - 1)‖ ‖a - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < ε := max_lt ((norm_mul_le _ _).trans_lt
      ((mul_le_of_le_one_left (norm_nonneg _) hnorm).trans_lt hb)) ha

/-- In an ultrametric normed commutative ring, a finite product of elements each within
`ε ≤ 1` of `1` is again within `ε` of `1` (for `0 < ε`). -/
theorem norm_prod_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] (s : Finset ι) (f : ι → R) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hf : ∀ i ∈ s, ‖f i - 1‖ < ε) : ‖∏ i ∈ s, f i - 1‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact norm_mul_sub_one_lt hε (hf j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- If two finite families are bounded by `M` and differ by at most `ε` in each coordinate,
their products differ by at most `ε * M ^ (s.card - 1)`. The exponent uses natural subtraction,
so the statement includes the empty product and `M = 0`. -/
theorem norm_prod_sub_prod_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] {s : Finset ι} {f g : ι → R} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M) (hg : ∀ i ∈ s, ‖g i‖ ≤ M)
    (hfg : ∀ i ∈ s, ‖f i - g i‖ ≤ ε) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ε * M ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hε]
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hfg a (by simp)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ M ^ s.card := by
      calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := norm_prod_le_prod_norm s f
        _ ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
        _ = M ^ s.card := Finset.prod_const _
    have htail := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Nat.add_sub_cancel]
    calc ‖f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i‖ =
          ‖(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ := by
            congr 1
            ring
      _ ≤ max (‖f a - g a‖ * ‖∏ i ∈ s, f i‖)
          (‖g a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖) :=
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le_max (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ max (ε * M ^ s.card) (M * (ε * M ^ (s.card - 1))) :=
        max_le_max (mul_le_mul (hfg a (by simp)) hprod (norm_nonneg _) hε)
          (mul_le_mul (hg a (by simp)) htail (norm_nonneg _) hM)
      _ = ε * M ^ s.card := by
        have hcard : s.card - 1 + 1 = s.card := Nat.sub_add_cancel (Finset.card_pos.mpr hs)
        rw [mul_left_comm M ε, ← pow_succ', hcard, max_self]

end TauCeti
