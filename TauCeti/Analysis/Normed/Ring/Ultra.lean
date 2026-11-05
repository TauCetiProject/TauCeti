/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Ultra
public import TauCeti.Algebra.Order.BigOperators.ProdSubProd
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The closed unit ball and products of elements close to one in ultrametric normed rings

An ultrametric seminormed ring is a nonarchimedean topological ring: its open balls about zero
are open additive subgroups. In an ultrametric seminormed ring with `‖1‖ = 1`, the closed unit
ball is an open subring. In an ultrametric normed ring, a finite product of elements each within
`ε ≤ 1` of `1` is again within `ε` of `1`. A series `∑_{n ≥ 1} f(qⁿ w)` of terms bounded by their
arguments is bounded by its first argument `q w`, and it depends on `w` in a `‖q‖`-Lipschitz way
when its terms are `1`-Lipschitz. The rational functions `t / (1 - t)²`, `t / (1 - t)³` and
`t² / (1 - t)³` are Lipschitz on the open unit ball of an ultrametric field.

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
* `TauCeti.norm_div_one_sub_cube_sub_div_one_sub_cube_le` and
  `TauCeti.norm_sq_div_one_sub_cube_sub_sq_div_one_sub_cube_le_max_mul`: on the open unit ball,
  `t ↦ t / (1 - t)³` is `1`-Lipschitz and `t ↦ t² / (1 - t)³` is Lipschitz with constant the
  larger of the two norms.
* `TauCeti.norm_tsum_le_norm_mul`: a one-sided series `∑_{n ≥ 1} f(qⁿ w)` whose terms are bounded
  by their arguments has norm at most `‖q w‖`; `TauCeti.norm_tsum_sub_tsum_le_norm_mul`: if the
  terms are `1`-Lipschitz, two such series differ by at most `‖q (w - w')‖`;
  `TauCeti.norm_tsum_sub_tsum_add_tsum_sub_tsum_le`: a series at `u` and a series at `u⁻¹` of
  `1`-Lipschitz terms together depend on `u` in a `‖q‖`-Lipschitz way on the unit circle.
* `TauCeti.norm_div_one_sub_sq_sub_div_one_sub_sq_le`: the map `t ↦ t / (1 - t)²` is
  `1`-Lipschitz on the open unit ball of an ultrametric field;
  `TauCeti.norm_sub_le_of_eq_mul_div` is the estimate behind it.
* `TauCeti.norm_one_sub_cube_div_sub_one_sub_cube_div_le`: the map `v ↦ (1 - v)³ / v` is
  `1`-Lipschitz on the unit circle of an ultrametric field.
* `TauCeti.one_le_norm_one_sub_of_norm_ne_one`: subtracting an element whose norm is not one
  from one gives norm at least one.
* `TauCeti.norm_mul_sub_one_lt` and `TauCeti.norm_prod_sub_one_lt`
* `TauCeti.norm_pow_sub_one_le_norm_sub_one`: a power of an element `x` of norm at most one is
  no farther from `1` than `x`.
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

/-- The map `t ↦ t / (1 - t)³` is `1`-Lipschitz on the open unit ball of an ultrametric field. -/
theorem norm_div_one_sub_cube_sub_div_one_sub_cube_le {K : Type*} [NormedField K]
    [IsUltrametricDist K] {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t / (1 - t) ^ 3 - t' / (1 - t') ^ 3‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  have e : t / (1 - t) ^ 3 - t' / (1 - t') ^ 3 =
      (t - t') * (1 - t * t' - t * t' - t * t' + t * t' * (t + t')) /
        ((1 - t) ^ 3 * (1 - t') ^ 3) := by
    field_simp
    ring
  have hP : 1 - t * t' - t * t' - t * t' + t * t' * (t + t') ∈ Subring.unitClosedBall K := by
    have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
    have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
    apply_rules [add_mem, sub_mem, mul_mem, one_mem]
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp hP)

/-- On the open unit ball of an ultrametric field, the map `t ↦ t² / (1 - t)³` is Lipschitz with
constant `max ‖t‖ ‖t'‖` between `t` and `t'`, so it contracts near zero. -/
theorem norm_sq_div_one_sub_cube_sub_sq_div_one_sub_cube_le_max_mul {K : Type*} [NormedField K]
    [IsUltrametricDist K] {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t ^ 2 / (1 - t) ^ 3 - t' ^ 2 / (1 - t') ^ 3‖ ≤ max ‖t‖ ‖t'‖ * ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  set A := 1 - t' - t' - t' + t * t' ^ 2
  have e : t ^ 2 / (1 - t) ^ 3 - t' ^ 2 / (1 - t') ^ 3 =
      (t - t') * (t * A + t') / ((1 - t) ^ 3 * (1 - t') ^ 3) := by
    field_simp
    ring
  have hA : ‖A‖ ≤ 1 := by
    have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
    have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
    refine Subring.mem_unitClosedBall.mp ?_
    apply_rules [add_mem, sub_mem, mul_mem, pow_mem, one_mem]
  have hQ : ‖t * A + t'‖ ≤ max ‖t‖ ‖t'‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hA
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one, mul_comm]
  exact mul_le_mul_of_nonneg_right hQ (norm_nonneg _)

/-- A one-sided series `∑_{n ≥ 1} f(qⁿ w)` with values in an ultrametric group, whose terms are
bounded by their arguments, has norm at most `‖q w‖` when `‖q‖ ≤ 1` and `‖q w‖ < 1`. -/
theorem norm_tsum_le_norm_mul {R E : Type*} [SeminormedRing R]
    [SeminormedAddCommGroup E] [IsUltrametricDist E] (f : R → E)
    (hf : ∀ w : R, ‖w‖ < 1 → ‖f w‖ ≤ ‖w‖) {q w : R} (hq : ‖q‖ ≤ 1) (hw : ‖q * w‖ < 1) :
    ‖∑' n : ℕ, f (q ^ (n + 1) * w)‖ ≤ ‖q * w‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  have h := norm_pow_succ_mul_le hq w n
  exact (hf _ (h.trans_lt hw)).trans h

/-- Two convergent one-sided series `∑_{n ≥ 1} f(qⁿ w)` and `∑_{n ≥ 1} f(qⁿ w')` with values in
an ultrametric group, whose terms are `1`-Lipschitz on the open unit ball, differ by at most
`‖q (w - w')‖` when `‖q‖ ≤ 1` and `‖q w‖, ‖q w'‖ < 1`. -/
theorem norm_tsum_sub_tsum_le_norm_mul {R E : Type*} [SeminormedRing R]
    [NormedAddCommGroup E] [IsUltrametricDist E] (f : R → E)
    (hf : ∀ t t' : R, ‖t‖ < 1 → ‖t'‖ < 1 → ‖f t - f t'‖ ≤ ‖t - t'‖) {q w w' : R}
    (hq : ‖q‖ ≤ 1) (hw : ‖q * w‖ < 1) (hw' : ‖q * w'‖ < 1)
    (hs : Summable fun n : ℕ ↦ f (q ^ (n + 1) * w))
    (hs' : Summable fun n : ℕ ↦ f (q ^ (n + 1) * w')) :
    ‖∑' n : ℕ, f (q ^ (n + 1) * w) - ∑' n : ℕ, f (q ^ (n + 1) * w')‖ ≤ ‖q * (w - w')‖ := by
  rw [← hs.tsum_sub hs']
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  refine (hf _ _ ((norm_pow_succ_mul_le hq w n).trans_lt hw)
    ((norm_pow_succ_mul_le hq w' n).trans_lt hw')).trans ?_
  rw [← mul_sub]
  exact norm_pow_succ_mul_le hq _ n

/-- A one-sided series `∑_{n ≥ 1} f(qⁿ u)` at `u` and one `∑_{n ≥ 1} g(qⁿ u⁻¹)` at `u⁻¹`, with
values in an ultrametric group, together depend on `u` in a `‖q‖`-Lipschitz way on the unit
circle when their terms are `1`-Lipschitz on the open unit ball and `‖q‖ < 1`. Only the values
need to be ultrametric. -/
theorem norm_tsum_sub_tsum_add_tsum_sub_tsum_le {K E : Type*} [NormedField K]
    [NormedAddCommGroup E] [IsUltrametricDist E] {q u u' : K} (hq : ‖q‖ < 1) (hu : ‖u‖ = 1)
    (hu' : ‖u'‖ = 1) (f g : K → E) (hf : ∀ t t' : K, ‖t‖ < 1 → ‖t'‖ < 1 → ‖f t - f t'‖ ≤ ‖t - t'‖)
    (hg : ∀ t t' : K, ‖t‖ < 1 → ‖t'‖ < 1 → ‖g t - g t'‖ ≤ ‖t - t'‖)
    (hfs : Summable fun n : ℕ ↦ f (q ^ (n + 1) * u))
    (hfs' : Summable fun n : ℕ ↦ f (q ^ (n + 1) * u'))
    (hgs : Summable fun n : ℕ ↦ g (q ^ (n + 1) * u⁻¹))
    (hgs' : Summable fun n : ℕ ↦ g (q ^ (n + 1) * u'⁻¹)) :
    ‖(∑' n : ℕ, f (q ^ (n + 1) * u) - ∑' n : ℕ, f (q ^ (n + 1) * u')) +
        (∑' n : ℕ, g (q ^ (n + 1) * u⁻¹) - ∑' n : ℕ, g (q ^ (n + 1) * u'⁻¹))‖ ≤
      ‖q‖ * ‖u - u'‖ := by
  have hqw (w : K) (hw : ‖w‖ = 1) : ‖q * w‖ < 1 := by rwa [norm_mul, hw, mul_one]
  have hinv : ‖q * (u⁻¹ - u'⁻¹)‖ = ‖q‖ * ‖u - u'‖ := by
    have h₀ : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
    have h₀' : u' ≠ 0 := norm_ne_zero_iff.mp (by rw [hu']; exact one_ne_zero)
    rw [norm_mul, ← dist_eq_norm, dist_inv_inv₀ h₀ h₀', hu, hu', mul_one, div_one, dist_eq_norm]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [← norm_mul]
    exact norm_tsum_sub_tsum_le_norm_mul f hf hq.le (hqw _ hu) (hqw _ hu') hfs hfs'
  · rw [← hinv]
    exact norm_tsum_sub_tsum_le_norm_mul g hg hq.le (hqw _ (by rw [norm_inv, hu, inv_one]))
      (hqw _ (by rw [norm_inv, hu', inv_one])) hgs hgs'

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- A difference of the form `(t - t') P / ((1 - t)ᵏ (1 - t')ᵏ)` with `‖t‖, ‖t'‖ < 1` and
`‖P‖ ≤ 1` has norm at most `‖t - t'‖`. -/
theorem norm_sub_le_of_eq_mul_div {t t' a a' P : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1)
    {k : ℕ} (h : a - a' = (t - t') * P / ((1 - t) ^ k * (1 - t') ^ k)) (hP : ‖P‖ ≤ 1) :
    ‖a - a'‖ ≤ ‖t - t'‖ := by
  rw [h, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hP

/-- The map `t ↦ t / (1 - t)²` is `1`-Lipschitz on the open unit ball of an ultrametric
field. -/
theorem norm_div_one_sub_sq_sub_div_one_sub_sq_le {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t / (1 - t) ^ 2 - t' / (1 - t') ^ 2‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  refine norm_sub_le_of_eq_mul_div ht ht' (P := 1 - t * t') (k := 2) (by field_simp; ring)
    (Subring.mem_unitClosedBall.mp ?_)
  have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
  have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
  apply_rules [sub_mem, mul_mem, one_mem]

/-- The map `v ↦ (1 - v)³ / v` is `1`-Lipschitz on the unit circle of an ultrametric field. -/
theorem norm_one_sub_cube_div_sub_one_sub_cube_div_le {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖(1 - v) ^ 3 / v - (1 - w) ^ 3 / w‖ ≤ ‖v - w‖ := by
  have h₀ : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have h₀' : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have e : (1 - v) ^ 3 / v - (1 - w) ^ 3 / w =
      (w - v) * (1 - v * w - v * w - v * w + v * w * (v + w)) / (v * w) := by
    field_simp
    ring
  have h₃ : v ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr hv.le
  have h₄ : w ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr hw.le
  have hP : 1 - v * w - v * w - v * w + v * w * (v + w) ∈ Subring.unitClosedBall K := by
    apply_rules [add_mem, sub_mem, mul_mem, one_mem]
  rw [e, norm_div, norm_mul, norm_mul, hv, hw, mul_one, div_one, norm_sub_rev]
  exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp hP)

end Field

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

/-- In an ultrametric seminormed ring with `‖1‖ = 1`, a power of an element `x` of norm at most
one is no farther from `1` than `x` is: `‖x ^ n - 1‖ ≤ ‖x - 1‖`. -/
theorem norm_pow_sub_one_le_norm_sub_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  rw [← geom_sum_mul]
  refine (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ?_)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦
    (norm_pow_le x i).trans (pow_le_one₀ (norm_nonneg x) hx)

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
