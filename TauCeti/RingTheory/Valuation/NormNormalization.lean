/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Real additive valuations attached to ultrametric norms and base-change comparisons

For a multiplicative ultrametric seminorm with `‖1‖ = 1` and a base `b > 1`, `AddValuation.ofNorm`
is the real additive valuation sending `x` to `-log_b ‖x‖ = -log ‖x‖ / log b` when `‖x‖ ≠ 0` and
to `⊤` when `‖x‖ = 0`. At `b = exp 1` it takes the natural-logarithm form `-log ‖x‖` away from
elements of norm zero (`AddValuation.ofNorm_exp_one_of_norm_ne_zero`). It reverses the order of
the norm and recovers it through `‖x‖ = b ^ (-v x)`.

Two real additive valuations recovering the same norm with specified bases greater
than one differ by the ratio of the logarithms of those bases. The comparison includes
zero, whose value remains infinity. In particular, fixing the base determines the
additive valuation uniquely (`AddValuation.eq_of_norm_eq_rpow`,
`AddValuation.eq_ofNorm_of_norm_eq_rpow`); no choice of scale is installed as a global instance.
Under norm recovery, the sphere `‖x‖ = b ^ σ` is the level set `v x = -σ`
(`AddValuation.norm_eq_rpow_iff`). A norm recovered from an additive valuation with base at least
one is ultrametric (`AddValuation.isUltrametricDist`).

## Main definitions

* `AddValuation.ofNorm`: the base-`b` real additive valuation `-Real.logb b ‖x‖` attached to a
  multiplicative ultrametric seminorm with `‖1‖ = 1` and `1 < b`.

## Main results

* `AddValuation.ofNorm_eq_coe_iff` and `AddValuation.norm_eq_rpow_neg_ofNorm`: norm recovery
  `ofNorm b hb x = t ↔ ‖x‖ = b ^ (-t)`.
* `AddValuation.ofNorm_le_ofNorm_iff`, `AddValuation.coe_le_ofNorm_iff`, and
  `AddValuation.coe_lt_ofNorm_iff`: order reversal and ball descriptions.
* `AddValuation.eq_of_norm_eq_rpow` and `AddValuation.eq_ofNorm_of_norm_eq_rpow`: uniqueness of
  the real additive valuation recovering a norm at a fixed base `b > 1`.
* `AddValuation.eq_map_of_norm_eq_rpow` and `AddValuation.ofNorm_eq_map_ofNorm`: changing base
  from `b` to `b'` scales values by `Real.log b / Real.log b'`.
* `AddValuation.ofNorm_algebraMap`, `AddValuation.comap_ofNorm`, and
  `AddValuation.ofNorm_algebraMap_eq`: scalar restriction of `AddValuation.ofNorm` along a normed
  algebra map.
-/

public section

namespace AddValuation

variable {K : Type*} [NormedDivisionRing K]

/-- Changing the base in norm recovery scales a real additive valuation by the ratio
of the logarithms. At zero the comparison maps infinity to infinity. -/
theorem eq_map_of_norm_eq_rpow (v w : AddValuation K (WithTop ℝ))
    {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b')
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b' ^ (-(w x).untop₀)) (x : K) :
    w x = WithTop.map (fun t => (Real.log b / Real.log b') * t) (v x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hlog := congrArg Real.log ((hv x hx).symm.trans (hw x hx))
  rw [Real.log_rpow (zero_lt_one.trans hb), Real.log_rpow (zero_lt_one.trans hb')] at hlog
  rw [← WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hx),
    ← WithTop.coe_untop₀_of_ne_top (w.ne_top_iff.mpr hx),
    WithTop.map_coe, WithTop.coe_eq_coe]
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt (Real.log_pos hb'))]
  nlinarith

/-- For a fixed base greater than one, norm recovery uniquely specifies the real
additive valuation. -/
theorem eq_of_norm_eq_rpow (v w : AddValuation K (WithTop ℝ))
    {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    (hw : ∀ x ≠ 0, ‖x‖ = b ^ (-(w x).untop₀)) : w = v := by
  ext x
  have h := v.eq_map_of_norm_eq_rpow w hb hb hv hw x
  have hid : (fun t : ℝ => (Real.log b / Real.log b) * t) = id := by
    ext t
    simp [ne_of_gt (Real.log_pos hb)]
  rw [hid, WithTop.map_id] at h
  exact h

/-- Under norm recovery with base `b > 1`, the points of norm `b ^ σ` are exactly those of
valuation `-σ`. Zero lies on neither side. -/
theorem norm_eq_rpow_iff (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {x : K} {σ : ℝ} :
    ‖x‖ = b ^ σ ↔ v x = ((-σ : ℝ) : WithTop ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [norm_zero, map_zero]
    exact iff_of_false (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).ne WithTop.top_ne_coe
  rw [hv x hx, Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne',
    ← WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.mpr hx), WithTop.coe_eq_coe,
    WithTop.untop₀_coe, neg_eq_iff_eq_neg]

/-- A norm that is given by an additive valuation, `‖x‖ = b ^ (-v x)` for `x ≠ 0` with `1 ≤ b`, is
ultrametric. -/
theorem isUltrametricDist (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 ≤ b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) : IsUltrametricDist K := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => ?_
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hxy : x + y = 0
  · simp [hxy]
  have hvxy := v.ne_top_iff.mpr hxy
  have hmin := v.map_add x y
  rw [hv _ hx, hv _ hy, hv _ hxy]
  rcases le_total (v x) (v y) with h | h
  · rw [min_eq_left h] at hmin
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hb
      (neg_le_neg (WithTop.untop₀_le_untop₀ hvxy hmin)))
  · rw [min_eq_right h] at hmin
    exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hb
      (neg_le_neg (WithTop.untop₀_le_untop₀ hvxy hmin)))

section OfNorm

section SeminormedRing

variable {R : Type*} [SeminormedRing R]

open scoped Classical in
/-- Auxiliary function `-log_b ‖x‖` with `⊤` at elements of norm zero. -/
private noncomputable def negLogbNorm (b : ℝ) (x : R) : WithTop ℝ :=
  if ‖x‖ = 0 then ⊤ else ((-Real.logb b ‖x‖ : ℝ) : WithTop ℝ)

private theorem negLogbNorm_of_norm_eq_zero (b : ℝ) {x : R} (hx : ‖x‖ = 0) :
    negLogbNorm b x = ⊤ := by
  simp [negLogbNorm, hx]

private theorem negLogbNorm_of_norm_ne_zero (b : ℝ) {x : R} (hx : ‖x‖ ≠ 0) :
    negLogbNorm b x = ((-Real.logb b ‖x‖ : ℝ) : WithTop ℝ) := by
  simp [negLogbNorm, hx]

private theorem negLogbNorm_le_negLogbNorm_iff {b : ℝ} (hb : 1 < b) {x y : R} :
    negLogbNorm b x ≤ negLogbNorm b y ↔ ‖y‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · rw [negLogbNorm_of_norm_eq_zero b hx, hx, top_le_iff]
    by_cases hy : ‖y‖ = 0 <;> simp [negLogbNorm, hy, (norm_nonneg y).ge_iff_eq']
  by_cases hy : ‖y‖ = 0
  · simp [negLogbNorm_of_norm_eq_zero b hy, hy]
  rw [negLogbNorm_of_norm_ne_zero b hx, negLogbNorm_of_norm_ne_zero b hy, WithTop.coe_le_coe,
    neg_le_neg_iff, Real.logb_le_logb hb ((norm_nonneg y).lt_of_ne' hy)
      ((norm_nonneg x).lt_of_ne' hx)]

private theorem min_le_negLogbNorm_add [IsUltrametricDist R] {b : ℝ} (hb : 1 < b) (x y : R) :
    min (negLogbNorm b x) (negLogbNorm b y) ≤ negLogbNorm b (x + y) := by
  simp only [min_le_iff, negLogbNorm_le_negLogbNorm_iff hb]
  exact le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y)

private theorem negLogbNorm_mul [NormMulClass R] (b : ℝ) (x y : R) :
    negLogbNorm b (x * y) = negLogbNorm b x + negLogbNorm b y := by
  by_cases hx : ‖x‖ = 0
  · rw [negLogbNorm_of_norm_eq_zero b hx, WithTop.top_add,
      negLogbNorm_of_norm_eq_zero b (by rw [norm_mul, hx, zero_mul])]
  by_cases hy : ‖y‖ = 0
  · rw [negLogbNorm_of_norm_eq_zero b hy, WithTop.add_top,
      negLogbNorm_of_norm_eq_zero b (by rw [norm_mul, hy, mul_zero])]
  rw [negLogbNorm_of_norm_ne_zero b hx, negLogbNorm_of_norm_ne_zero b hy,
    negLogbNorm_of_norm_ne_zero b (by rw [norm_mul]; exact mul_ne_zero hx hy), norm_mul,
    Real.logb_mul hx hy, neg_add, WithTop.coe_add]

variable [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]

/-- The **base-`b` real additive valuation** `-log_b ‖x‖ = -log ‖x‖ / log b` attached to a
multiplicative ultrametric seminorm with `‖1‖ = 1` and `1 < b`, taking the value `⊤` on elements
of norm zero. -/
noncomputable def ofNorm (b : ℝ) (hb : 1 < b) : AddValuation R (WithTop ℝ) :=
  AddValuation.of (negLogbNorm b) (negLogbNorm_of_norm_eq_zero b norm_zero)
    (by simp [negLogbNorm]) (min_le_negLogbNorm_add hb) (negLogbNorm_mul b)

/-- Explicit `if`-expression for `AddValuation.ofNorm`. -/
theorem ofNorm_apply {b : ℝ} (hb : 1 < b) (x : R) [Decidable (‖x‖ = 0)] :
    ofNorm b hb x = if ‖x‖ = 0 then ⊤ else ((-Real.logb b ‖x‖ : ℝ) : WithTop ℝ) := by
  rw [ofNorm, AddValuation.of_apply, negLogbNorm]
  congr

/-- `AddValuation.ofNorm` is `⊤` precisely on elements of norm zero. -/
@[simp]
theorem ofNorm_eq_top_iff {b : ℝ} (hb : 1 < b) {x : R} :
    ofNorm b hb x = ⊤ ↔ ‖x‖ = 0 := by
  classical
  rw [ofNorm_apply]
  split_ifs with h <;> simp [h]

private theorem ofNorm_of_norm_eq_zero {b : ℝ} (hb : 1 < b) {x : R} (hx : ‖x‖ = 0) :
    ofNorm b hb x = ⊤ :=
  (ofNorm_eq_top_iff hb).2 hx

/-- On an element of nonzero norm, `AddValuation.ofNorm` equals `-Real.logb b ‖x‖`. -/
theorem ofNorm_of_norm_ne_zero {b : ℝ} (hb : 1 < b) {x : R} (hx : ‖x‖ ≠ 0) :
    ofNorm b hb x = ((-Real.logb b ‖x‖ : ℝ) : WithTop ℝ) := by
  classical
  simp [ofNorm_apply, hx]

/-- `WithTop.untop₀` of `AddValuation.ofNorm b hb x` is `-Real.logb b ‖x‖` for every `x`,
including elements of norm zero where both sides vanish. -/
@[simp]
theorem untop₀_ofNorm {b : ℝ} (hb : 1 < b) (x : R) :
    (ofNorm b hb x).untop₀ = -Real.logb b ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · simp [ofNorm_of_norm_eq_zero hb hx, hx]
  · rw [ofNorm_of_norm_ne_zero hb hx, WithTop.untop₀_coe]

/-- At base `Real.exp 1`, `AddValuation.ofNorm` equals `-Real.log ‖x‖` on elements of nonzero
norm. -/
theorem ofNorm_exp_one_of_norm_ne_zero {x : R} (hx : ‖x‖ ≠ 0) :
    ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one) x =
      ((-Real.log ‖x‖ : ℝ) : WithTop ℝ) := by
  rw [ofNorm_of_norm_ne_zero _ hx, Real.logb, Real.log_exp, div_one]

/-- At base `Real.exp 1`, `WithTop.untop₀` of `AddValuation.ofNorm` is `-Real.log ‖x‖`. -/
theorem untop₀_ofNorm_exp_one (x : R) :
    (ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one) x).untop₀ = -Real.log ‖x‖ := by
  rw [untop₀_ofNorm, Real.logb, Real.log_exp, div_one]

/-- **Norm recovery**: `ofNorm b hb x` equals the finite value `t` if and only if
`‖x‖ = b ^ (-t)`. -/
theorem ofNorm_eq_coe_iff {b : ℝ} (hb : 1 < b) {x : R} {t : ℝ} :
    ofNorm b hb x = t ↔ ‖x‖ = b ^ (-t) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  by_cases hx : ‖x‖ = 0
  · simp [ofNorm_of_norm_eq_zero hb hx, hx, (Real.rpow_pos_of_pos hb0 (-t)).ne]
  · rw [ofNorm_of_norm_ne_zero hb hx, WithTop.coe_eq_coe, neg_eq_iff_eq_neg,
      Real.logb_eq_iff_rpow_eq hb0 hb.ne' ((norm_nonneg x).lt_of_ne' hx), eq_comm]

/-- Every element of nonzero norm recovers its norm as `b ^ (-(ofNorm b hb x).untop₀)`. -/
theorem norm_eq_rpow_neg_ofNorm {b : ℝ} (hb : 1 < b) {x : R} (hx : ‖x‖ ≠ 0) :
    ‖x‖ = b ^ (-(ofNorm b hb x).untop₀) :=
  (ofNorm_eq_coe_iff hb).1
    (WithTop.coe_untop₀_of_ne_top ((ofNorm_eq_top_iff hb).not.2 hx)).symm

/-- `AddValuation.ofNorm` reverses the order of the norm. -/
theorem ofNorm_le_ofNorm_iff {b : ℝ} (hb : 1 < b) {x y : R} :
    ofNorm b hb x ≤ ofNorm b hb y ↔ ‖y‖ ≤ ‖x‖ := by
  rw [ofNorm, AddValuation.of_apply, AddValuation.of_apply]
  exact negLogbNorm_le_negLogbNorm_iff hb

/-- `AddValuation.ofNorm` strictly reverses the order of the norm. -/
theorem ofNorm_lt_ofNorm_iff {b : ℝ} (hb : 1 < b) {x y : R} :
    ofNorm b hb x < ofNorm b hb y ↔ ‖y‖ < ‖x‖ := by
  rw [lt_iff_not_ge, ofNorm_le_ofNorm_iff hb, not_le]

/-- `ofNorm b hb x` is at least `t` if and only if `x` lies in the closed ball `‖x‖ ≤ b ^ (-t)`. -/
theorem coe_le_ofNorm_iff {b : ℝ} (hb : 1 < b) {x : R} {t : ℝ} :
    (t : WithTop ℝ) ≤ ofNorm b hb x ↔ ‖x‖ ≤ b ^ (-t) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  by_cases hx : ‖x‖ = 0
  · simp [ofNorm_of_norm_eq_zero hb hx, hx, (Real.rpow_pos_of_pos hb0 (-t)).le]
  · rw [ofNorm_of_norm_ne_zero hb hx, WithTop.coe_le_coe, le_neg,
      Real.logb_le_iff_le_rpow hb ((norm_nonneg x).lt_of_ne' hx)]

/-- `ofNorm b hb x` is at most `t` if and only if `b ^ (-t) ≤ ‖x‖`. -/
theorem ofNorm_le_coe_iff {b : ℝ} (hb : 1 < b) {x : R} {t : ℝ} :
    ofNorm b hb x ≤ t ↔ b ^ (-t) ≤ ‖x‖ := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  by_cases hx : ‖x‖ = 0
  · simp [ofNorm_of_norm_eq_zero hb hx, hx, Real.rpow_pos_of_pos hb0 (-t)]
  · rw [ofNorm_of_norm_ne_zero hb hx, WithTop.coe_le_coe, neg_le,
      Real.le_logb_iff_rpow_le hb ((norm_nonneg x).lt_of_ne' hx)]

/-- `ofNorm b hb x` exceeds `t` if and only if `x` lies in the open ball `‖x‖ < b ^ (-t)`. -/
theorem coe_lt_ofNorm_iff {b : ℝ} (hb : 1 < b) {x : R} {t : ℝ} :
    (t : WithTop ℝ) < ofNorm b hb x ↔ ‖x‖ < b ^ (-t) := by
  rw [lt_iff_not_ge, ofNorm_le_coe_iff hb, not_le]

/-- Elements of equal norm in any two rings have the same `AddValuation.ofNorm` at base `b`. -/
theorem ofNorm_eq_of_norm_eq {S : Type*} [SeminormedRing S] [IsUltrametricDist S]
    [NormMulClass S] [NormOneClass S] {b : ℝ} (hb : 1 < b) {x : R} {y : S} (h : ‖x‖ = ‖y‖) :
    ofNorm b hb x = ofNorm b hb y := by
  classical
  simp only [ofNorm_apply, h]

/-- Changing the base from `b` to `b'` scales `AddValuation.ofNorm` by
`Real.log b / Real.log b'`. -/
theorem ofNorm_eq_map_ofNorm {b b' : ℝ} (hb : 1 < b) (hb' : 1 < b') (x : R) :
    ofNorm b' hb' x = WithTop.map (fun t ↦ (Real.log b / Real.log b') * t) (ofNorm b hb x) := by
  by_cases hx : ‖x‖ = 0
  · simp [ofNorm_of_norm_eq_zero hb hx, ofNorm_of_norm_eq_zero hb' hx]
  rw [ofNorm_of_norm_ne_zero hb hx, ofNorm_of_norm_ne_zero hb' hx, WithTop.map_coe,
    WithTop.coe_eq_coe, Real.logb, Real.logb]
  have hlog : Real.log b ≠ 0 := (Real.log_pos hb).ne'
  field_simp [hlog]

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]

/-- On a nonzero element of a normed ring, `AddValuation.ofNorm` equals `-Real.logb b ‖x‖`. -/
theorem ofNorm_of_ne_zero {b : ℝ} (hb : 1 < b) {x : R} (hx : x ≠ 0) :
    ofNorm b hb x = ((-Real.logb b ‖x‖ : ℝ) : WithTop ℝ) :=
  ofNorm_of_norm_ne_zero hb (norm_ne_zero_iff.2 hx)

/-- On a nonzero element of a normed ring, `‖x‖ = b ^ (-(ofNorm b hb x).untop₀)`. -/
theorem norm_eq_rpow_neg_ofNorm_of_ne_zero {b : ℝ} (hb : 1 < b) {x : R} (hx : x ≠ 0) :
    ‖x‖ = b ^ (-(ofNorm b hb x).untop₀) :=
  norm_eq_rpow_neg_ofNorm hb (norm_ne_zero_iff.2 hx)

end NormedRing

/-- A real additive valuation on a normed division ring recovering the norm with base `b > 1`
equals `AddValuation.ofNorm b hb`. -/
theorem eq_ofNorm_of_norm_eq_rpow {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) : v = ofNorm b hb :=
  eq_of_norm_eq_rpow (ofNorm b hb) v hb (fun _ ↦ norm_eq_rpow_neg_ofNorm_of_ne_zero hb) hv

section NormedAlgebra

variable {K A : Type*} [NormedField K]
  [SeminormedRing A] [IsUltrametricDist A] [NormMulClass A] [NormOneClass A] [NormedAlgebra K A]

/-- On a normed `K`-algebra `A` with multiplicative ultrametric seminorm and `‖1‖ = 1`,
`AddValuation.ofNorm` restricts on `K` to `AddValuation.ofNorm`. -/
@[simp]
theorem ofNorm_algebraMap [IsUltrametricDist K] {b : ℝ} (hb : 1 < b) (c : K) :
    ofNorm (R := A) b hb (algebraMap K A c) = ofNorm b hb c :=
  ofNorm_eq_of_norm_eq hb (norm_algebraMap' A c)

/-- Pulling `AddValuation.ofNorm` on a normed `K`-algebra `A` back to `K` gives
`AddValuation.ofNorm` on `K`. -/
@[simp]
theorem comap_ofNorm [IsUltrametricDist K] {b : ℝ} (hb : 1 < b) :
    (ofNorm (R := A) b hb).comap (algebraMap K A) = ofNorm b hb :=
  AddValuation.ext (ofNorm_algebraMap hb)

/-- On a normed `K`-algebra `A` with multiplicative ultrametric seminorm and `‖1‖ = 1`,
`AddValuation.ofNorm` restricts on `K` to any real additive valuation `v` recovering the norm of
`K` at base `b`. -/
theorem ofNorm_algebraMap_eq (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (c : K) :
    ofNorm (R := A) b hb (algebraMap K A c) = v c := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  rw [ofNorm_algebraMap hb c, ← v.eq_ofNorm_of_norm_eq_rpow hb hv]

end NormedAlgebra

end OfNorm

end AddValuation
