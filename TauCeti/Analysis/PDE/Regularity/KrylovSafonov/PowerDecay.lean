/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.MeasureEstimate
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.KrylovSafonov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Power decay of the superlevel sets of supersolutions

Let `u ≥ 0` be a `C²` supersolution of a non-divergence-form equation
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` with a coefficient matrix satisfying `λ ‖ξ‖² ≤ ξᵀ a ξ` and
`|ηᵀ a ξ| ≤ Λ ‖η‖ ‖ξ‖`, `Λ ≤ κ λ`, on a ball `B(c, R) ⊆ ℝⁿ`, `n ≥ 1`. If `u ≤ 1` somewhere in
the ball `B(c, r)` with `41 n r ≤ R`, and the right-hand side is small,
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then the superlevel sets of `u` decay like a power of the level:

`|{u > t} ∩ B(c, r)| ≤ C t^(-ε) |B(c, r)|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_lt_inter_ball_le_mul_rpow`). The constants `C`, `ε > 0` and
`ε₀ > 0` depend only on the dimension and on `κ`. This is the `L^ε` lemma of Krylov and Safonov:
through the layer cake formula it bounds the average of `u ^ δ` over `B(c, r)` for every `δ < ε`
in terms of these data alone. It is the core of the weak Harnack inequality for
non-divergence-form equations with merely bounded measurable coefficients, from which the Harnack
inequality and the interior Hölder estimate of Krylov and Safonov follow.

The same decay holds on a dyadic cube `Q = dyadicCube k m` of `ℝⁿ = ι → ℝ`, identified with
`EuclideanSpace ℝ ι` through `WithLp.ofLp`: if the hypotheses hold on the Euclidean ball
`B(c, 9 n 2ᵏ)` about a point `c` of `Q` and `u ≤ 1` somewhere in `B(c, 3 n 2ᵏ)`, then
`|{u > t} ∩ Q| ≤ C t^(-ε) |Q|` (`TauCeti.PDE.exists_volume_setOf_lt_inter_dyadicCube_le_mul_rpow`).

## The argument

The basic measure estimate (`TauCeti.PDE.exists_mul_volume_ball_le_volume_setOf_lt_inter_ball`),
applied to `u / s` on a Euclidean ball about the centre of a dyadic cube `Q`, says: if `u ≤ s`
somewhere in the parent of `Q`, with `s ≥ 1`, then `u ≤ M s` on a fixed fraction of `Q`, that
is `|{u > M s} ∩ Q| ≤ δ |Q|` for a fixed `δ < 1`. Contrapositively, a dyadic cube on which
`{u > M^(j+1)}` occupies more than the fraction `δ` has its parent inside `{u > M^j}`. The
Krylov–Safonov covering lemma on dyadic cubes (`TauCeti.volume_le_pow_mul_volume_dyadicCube`)
turns this into the geometric decay `|{u > M^j} ∩ Q₀| ≤ δ^j |Q₀|`, which is the power decay with
`ε = log δ⁻¹ / log M`. A ball of radius `r` is covered by `2ⁿ` dyadic cubes of side between `2 r`
and `4 r`, to each of which the cube form applies.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_lt_inter_dyadicCube_le_mul_rpow`: the power decay on a dyadic
  cube.
* `TauCeti.PDE.exists_volume_setOf_lt_inter_ball_le_mul_rpow`: the power decay on a ball.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.6.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open Metric MeasureTheory Set WithLp
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-! ### Euclidean balls and dyadic cubes -/

/-- Two points of `ℝⁿ` lying in a common dyadic cube of level `k` are at Euclidean distance less
than `n 2ᵏ`. -/
private theorem dist_lt_of_ofLp_mem_dyadicCube [Nonempty ι] {k : ℤ} {m : ι → ℤ}
    {x y : EuclideanSpace ℝ ι} (hx : ofLp x ∈ dyadicCube k m) (hy : ofLp y ∈ dyadicCube k m) :
    dist x y < Fintype.card ι * 2 ^ k := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  exact (PiLp.dist_le_sqrt_card_mul_dist_ofLp x y).trans_lt
    ((mul_lt_mul_of_pos_left (dist_lt_of_mem_dyadicCube hx hy) (by positivity)).trans_le
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.2 (Or.inr hn)) (by positivity)))

/-- The Euclidean ball about the centre of a dyadic cube whose radius is half its side lies in the
cube. -/
private theorem ball_subset_preimage_dyadicCube (k : ℤ) (m : ι → ℤ) :
    ball (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2) ⊆ ofLp ⁻¹' dyadicCube k m := by
  intro y hy
  rw [mem_preimage, dyadicCube_eq_pi]
  intro i _
  have h := (PiLp.norm_apply_le (y - toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) i).trans_lt
    (mem_ball_iff_norm.1 hy)
  rw [PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, abs_sub_lt_iff] at h
  constructor <;> linarith

omit [Fintype ι] in
/-- The centre of a dyadic cube lies in the cube. -/
private theorem ofLp_dyadicCenter_mem_dyadicCube (k : ℤ) (m : ι → ℤ) :
    ofLp (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) ∈ dyadicCube k m := by
  rw [ofLp_toLp, mem_dyadicCube]
  ext i
  rw [dyadicIndex_apply, mul_div_cancel_right₀ _ (zpow_ne_zero k two_ne_zero),
    Int.floor_intCast_add, Int.floor_eq_zero_iff.2 ⟨by norm_num, by norm_num⟩, add_zero]

/-- At a dyadic level of side `s > 2 r`, the dyadic index of a point of `(c - r, c + r)` is one of
the two consecutive integers `⌊(c - r) / s⌋` and `⌊(c - r) / s⌋ + 1`. -/
private theorem floor_div_mem_pair {x c r s : ℝ} (hs : 0 < s) (hrs : 2 * r < s)
    (hx : |x - c| < r) : ⌊x / s⌋ ∈ ({⌊(c - r) / s⌋, ⌊(c - r) / s⌋ + 1} : Finset ℤ) := by
  rw [abs_sub_lt_iff] at hx
  have h1 : ⌊(c - r) / s⌋ ≤ ⌊x / s⌋ :=
    Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le)
  have h2 : ⌊x / s⌋ < ⌊(c - r) / s⌋ + 2 := by
    have h3 := Int.lt_floor_add_one ((c - r) / s)
    have h4 : x / s < (c - r) / s + 1 := by
      rw [div_add_one hs.ne', div_lt_div_iff_of_pos_right hs]
      linarith
    rw [Int.floor_lt]
    push_cast
    linarith
  rw [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A Euclidean ball of radius `r` is covered by `2ⁿ` dyadic cubes of a level of side `2ᴷ > 2 r`,
whose corners `m 2ᴷ` lie within `n (r + 2ᴷ)` of the centre of the ball. -/
private theorem exists_card_eq_ball_subset_biUnion [Nonempty ι]
    (c : EuclideanSpace ℝ ι) {r : ℝ} {K : ℤ} (hr : 0 < r) (hK : 2 * r < 2 ^ K) :
    ∃ S : Finset (ι → ℤ), S.card = 2 ^ Fintype.card ι ∧
      ball c r ⊆ ⋃ m ∈ S, ofLp ⁻¹' dyadicCube K m ∧
      ∀ m ∈ S, dist (toLp 2 fun i ↦ (m i : ℝ) * 2 ^ K) c ≤ Fintype.card ι * (r + 2 ^ K) := by
  classical
  have hK0 : (0 : ℝ) < 2 ^ K := zpow_pos two_pos K
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  set b : ι → ℤ := fun i ↦ ⌊(c i - r) / 2 ^ K⌋
  refine ⟨Fintype.piFinset fun i ↦ ({b i, b i + 1} : Finset ℤ), ?_, fun x hx ↦ ?_, fun m hm ↦ ?_⟩
  · rw [Fintype.card_piFinset, Finset.prod_congr rfl fun i _ ↦
      Finset.card_pair (by omega : b i ≠ b i + 1), Finset.prod_const, Finset.card_univ]
  · refine mem_biUnion (x := dyadicIndex K (ofLp x)) (Fintype.mem_piFinset.2 fun i ↦ ?_)
      (mem_dyadicCube_dyadicIndex K _)
    have := (PiLp.norm_apply_le (x - c) i).trans_lt (mem_ball_iff_norm.1 hx)
    rw [PiLp.sub_apply, Real.norm_eq_abs] at this
    rw [dyadicIndex_apply]
    exact floor_div_mem_pair hK0 hK this
  · refine (PiLp.dist_le_sqrt_card_mul_dist_ofLp _ _).trans ((mul_le_mul_of_nonneg_left
      ((dist_pi_le_iff (by positivity)).2 fun i ↦ ?_) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.2 (Or.inr hn)) (by positivity)))
    have hb1 := Int.floor_le ((c i - r) / 2 ^ K)
    have hb2 := Int.lt_floor_add_one ((c i - r) / 2 ^ K)
    rw [le_div_iff₀ hK0] at hb1
    rw [div_lt_iff₀ hK0] at hb2
    have hmi := Fintype.mem_piFinset.1 hm i
    rw [Finset.mem_insert, Finset.mem_singleton] at hmi
    rw [ofLp_toLp, Real.dist_eq, abs_le]
    rcases hmi with h | h <;> rw [h] <;> push_cast <;> constructor <;> nlinarith

/-- `2ⁿ` dyadic cubes of side `2ᴷ ≤ 4 r` have total volume at most `8ⁿ / ωₙ` times the volume of
a Euclidean ball of radius `r`, where `ωₙ` is the volume of the unit ball. -/
private theorem two_pow_mul_volume_dyadicCube_le (c : EuclideanSpace ℝ ι) {r : ℝ}
    {K : ℤ} (m : ι → ℤ) (hr : 0 < r) (hK : (2 : ℝ) ^ K ≤ 4 * r) {A : ℝ} (hA : 0 ≤ A) :
    ((2 ^ Fintype.card ι : ℕ) : ℝ≥0∞) * (ENNReal.ofReal A * volume (dyadicCube K m)) ≤
      ENNReal.ofReal (A * 8 ^ Fintype.card ι / volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) *
        volume (ball c r) := by
  set N := Fintype.card ι
  set ω := volume.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  have hK0 : (0 : ℝ) < 2 ^ K := zpow_pos two_pos K
  rw [volume_dyadicCube, Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace,
    ← ofReal_measureReal (μ := volume) (s := ball (0 : EuclideanSpace ℝ ι) 1)
      measure_ball_lt_top.ne, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  calc 2 ^ N * (A * (2 ^ K) ^ N) ≤ 2 ^ N * (A * (4 * r) ^ N) := by gcongr
    _ = A * 8 ^ N / ω * (r ^ N * ω) := by
        rw [show (8 : ℝ) ^ N = 2 ^ N * 4 ^ N by rw [← mul_pow]; norm_num, mul_pow]
        field_simp

/-! ### From geometric to power decay -/

/-- If a nonincreasing function `φ` is bounded by `V` and decays geometrically along the powers of
`M > 1`, `φ (M ^ j) ≤ δ ^ j V` with `0 < δ ≤ 1`, then it decays like the power
`t ^ (-log δ⁻¹ / log M)`. -/
private theorem le_ofReal_mul_rpow_of_forall_pow_le {φ : ℝ → ℝ≥0∞} (hφ : Antitone φ)
    {V : ℝ≥0∞} {M δ : ℝ} (hM : 1 < M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hV : ∀ t, φ t ≤ V)
    (hpow : ∀ j : ℕ, φ (M ^ j) ≤ ENNReal.ofReal (δ ^ j) * V) {t : ℝ} (ht : 0 < t) :
    φ t ≤ ENNReal.ofReal (δ⁻¹ * t ^ (-(Real.log δ⁻¹ / Real.log M))) * V := by
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hε : 0 ≤ Real.log δ⁻¹ / Real.log M :=
    div_nonneg (Real.log_nonneg (one_le_inv₀ hδ0 |>.2 hδ1)) hlogM.le
  rcases lt_or_ge t 1 with ht1 | ht1
  · -- Below the level `1` the bound `V` suffices, since the right-hand factor is at least `1`.
    refine (hV t).trans (le_mul_of_one_le_left' ?_)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hδ0).2 hδ1)
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (neg_nonpos.2 hε)))
  · obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near ht1 hM
    refine (hφ hj).trans ((hpow j).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) V))
    -- `δ = M ^ (-ε)`, so `δ ^ j = δ⁻¹ (M ^ (j + 1)) ^ (-ε) ≤ δ⁻¹ t ^ (-ε)`.
    have hδM : M ^ (-(Real.log δ⁻¹ / Real.log M)) = δ := by
      rw [Real.rpow_def_of_pos (one_pos.trans hM), mul_neg, mul_div_cancel₀ _ hlogM.ne',
        Real.log_inv, neg_neg, Real.exp_log hδ0]
    have hM0 : 0 ≤ M := (one_pos.trans hM).le
    calc δ ^ j = δ⁻¹ * (M ^ (j + 1)) ^ (-(Real.log δ⁻¹ / Real.log M)) := by
          rw [← Real.rpow_natCast_mul hM0, mul_comm ((j + 1 : ℕ) : ℝ),
            Real.rpow_mul_natCast hM0, hδM, pow_succ, mul_comm _ δ, inv_mul_cancel_left₀ hδ0.ne']
      _ ≤ δ⁻¹ * t ^ (-(Real.log δ⁻¹ / Real.log M)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht hj'.le (neg_nonpos.2 hε))
            (inv_nonneg.2 hδ0.le)

/-! ### The measure estimate on dyadic cubes -/

/-- The volume of the Euclidean ball about the centre of a dyadic cube whose radius is half its
side, as a fraction of the volume of the cube. -/
private theorem volume_ball_dyadicCenter (k : ℤ) (m : ι → ℤ) :
    volume (ball (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k / 2)) =
      ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℝ ι) 1) / 2 ^ Fintype.card ι) *
        volume (dyadicCube k m) := by
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), finrank_euclideanSpace,
    ← ofReal_measureReal (μ := volume) (s := ball (0 : EuclideanSpace ℝ ι) 1)
      measure_ball_lt_top.ne, volume_dyadicCube, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  field_simp

/-- Dividing `f` by `s ≥ 1` does not increase the `Lᵖ` seminorm of its positive part. -/
private theorem eLpNorm_posPart_inv_smul_le {α : Type*} [MeasurableSpace α] {s : ℝ} (hs : 1 ≤ s)
    (f : α → ℝ) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (fun x ↦ ((s⁻¹ • f) x)⁺) p μ ≤ eLpNorm (fun x ↦ (f x)⁺) p μ := by
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.2 (zero_le_one.trans hs)
  have hpos : (fun x ↦ ((s⁻¹ • f) x)⁺) = s⁻¹ • fun x ↦ (f x)⁺ := by
    ext x
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rcases le_total 0 (f x) with h | h
    · rw [posPart_eq_self.2 h, posPart_eq_self.2 (mul_nonneg hs0 h)]
    · rw [posPart_eq_zero.2 h, posPart_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos hs0 h),
        mul_zero]
  have hs1 : ‖s⁻¹‖ₑ ≤ 1 := by
    rw [Real.enorm_eq_ofReal hs0, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hs)
  rw [hpos]
  exact eLpNorm_const_smul_le.trans (mul_le_of_le_one_left zero_le hs1)

/-- If the part of a set `S` of finite measure outside a measurable set `T` has at least the
fraction `c ≥ 0` of its measure, the part inside `T` has at most the fraction `1 - c`. -/
private theorem measure_inter_le_ofReal_one_sub_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S T : Set α} (hT : MeasurableSet T) (hS : μ S ≠ ∞) {c : ℝ} (hc : 0 ≤ c)
    (h : ENNReal.ofReal c * μ S ≤ μ (S \ T)) :
    μ (S ∩ T) ≤ ENNReal.ofReal (1 - c) * μ S := by
  have hadd := measure_inter_add_sdiff (μ := μ) S hT
  have hfin : μ (S \ T) ≠ ∞ := ne_top_of_le_ne_top hS (hadd ▸ le_add_self)
  rw [ENNReal.eq_sub_of_add_eq hfin hadd, ENNReal.ofReal_sub _ hc, ENNReal.ofReal_one,
    ENNReal.sub_mul fun _ _ ↦ hS, one_mul]
  exact tsub_le_tsub_left h _

variable [DecidableEq ι]

/-- Multiplying a supersolution `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` at a point by a constant `c ≥ 0` gives a
supersolution with right-hand side `c f`. -/
private theorem sum_mul_fderiv_fderiv_const_smul_le {c : ℝ} (hc : 0 ≤ c)
    {a : Matrix ι ι ℝ} {u : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι} {F : ℝ}
    (h : ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ F) :
    ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ (c • u)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ c * F := by
  simp only [fderiv_fderiv_const_smul, FunLike.coe_smul, smul_eq_mul, Pi.smul_apply]
  calc ∑ i, ∑ j, a i j * (c * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1))
      = c * ∑ i, ∑ j, a i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    _ ≤ c * F := mul_le_mul_of_nonneg_left h hc

/-- **The measure estimate on dyadic cubes.** There are constants `M > 1`, `0 < δ < 1` and
`ε₀ > 0`, depending only on the dimension and on `κ`, with the following property. Let `Q` be the
dyadic cube of level `k` at position `m`, with centre `z`, and let `s ≥ 1`. Let `u ≥ 0` be `C²` on
a set `D` containing the closed ball of radius `8 n 2ᵏ` about `z`, and a supersolution
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there for coefficients uniformly elliptic on `D` with `Λ ≤ κ λ`, with
`8 n 2ᵏ ‖f⁺‖_{Lⁿ(D)} ≤ ε₀ λ`. If `u ≤ s` somewhere in `B(z, 4 n 2ᵏ)`, then
`|{u > M s} ∩ Q| ≤ δ |Q|`. -/
private theorem exists_volume_setOf_lt_inter_dyadicCube_le [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ M δ ε₀ : ℝ, 1 < M ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam s : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃D : Set (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 1 ≤ s →
        closedBall (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) (8 * Fintype.card ι * 2 ^ k) ⊆ D →
        UniformlyEllipticOn D a lam Lam → Lam ≤ κ * lam → ContDiffOn ℝ 2 u D →
        (∀ x ∈ D, 0 ≤ u x) →
        (∀ x ∈ D, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal (8 * Fintype.card ι * 2 ^ k) *
          eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict D) ≤
            ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) (4 * Fintype.card ι * 2 ^ k),
          u x ≤ s) →
        volume ({x | M * s < u x} ∩ ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal δ * volume (dyadicCube k m) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  obtain ⟨M, μ, ε₀, -, hμ, hε₀, H⟩ := exists_mul_volume_ball_le_volume_setOf_lt_inter_ball
    (ι := ι) hκ (θ := 1 / (16 * n)) (by positivity) (τ := 1 / 2) (by norm_num) (by norm_num)
  set ω := volume.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  set μ' := min (μ * ω / 2 ^ Fintype.card ι) (1 / 2)
  have hμ' : 0 < μ' := lt_min (by positivity) (by norm_num)
  refine ⟨max M 2, 1 - μ', ε₀, lt_max_of_lt_right one_lt_two,
    sub_pos.2 ((min_le_right _ _).trans_lt (by norm_num)), sub_lt_self _ hμ', hε₀, ?_⟩
  intro lam Lam s k m D a u f hs hD ha hLam hu hu0 hsuper hf ⟨x₀, hx₀, hux₀⟩
  set z : EuclideanSpace ℝ ι := toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k
  set R := 8 * n * 2 ^ k
  have hR : 0 < R := by positivity
  have hBD : ball z R ⊆ D := ball_subset_closedBall.trans hD
  have hs0 : 0 < s := one_pos.trans_le hs
  have hθR : 1 / (16 * n) * R = 2 ^ k / 2 := by field_simp; ring
  have hτR : 1 / 2 * R = 4 * n * 2 ^ k := by ring
  -- The measure estimate for `s⁻¹ u` on `B(z, R)`, whose ball `B(z, θ R)` lies in `Q`.
  have h := H (R := R) (c := z) (a := a) (u := s⁻¹ • u) (f := s⁻¹ • f) hR (ha.mono_set hBD)
    hLam ((hu.continuousOn.mono hD).const_smul s⁻¹) ((hu.mono hBD).const_smul s⁻¹ :)
    (fun x hx ↦ smul_nonneg (inv_nonneg.2 hs0.le) (hu0 x (hD (sphere_subset_closedBall hx))))
    (fun x hx ↦ sum_mul_fderiv_fderiv_const_smul_le (inv_nonneg.2 hs0.le) (hsuper x (hBD hx)))
    ((mul_le_mul_right ((eLpNorm_posPart_inv_smul_le hs f _ _).trans
      (eLpNorm_mono_measure _ (Measure.restrict_mono hBD le_rfl))) _).trans hf)
    ⟨x₀, by rwa [hτR], by rwa [Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hs0, mul_one]⟩
  rw [hθR] at h
  -- `{u > max M 2 * s} ∩ Q` is `Q ∩ T` for the measurable set `T` below, and `Q \ T` contains
  -- `{u < M s} ∩ B(z, 2ᵏ / 2)`, whose volume `h` bounds below.
  have hQe : ofLp ⁻¹' dyadicCube k m ⊆ ball z R := fun y hy ↦ by
    have := dist_lt_of_ofLp_mem_dyadicCube hy (ofLp_dyadicCenter_mem_dyadicCube k m)
    have h2 := zpow_pos (two_pos : (0 : ℝ) < 2) k
    exact mem_ball.2 (this.trans_le (by simp only [R]; nlinarith))
  set T := ball z R ∩ u ⁻¹' Ioi (max M 2 * s)
  have hT : MeasurableSet T :=
    ((hu.continuousOn.mono hBD).isOpen_inter_preimage isOpen_ball isOpen_Ioi).measurableSet
  have heq : {x | max M 2 * s < u x} ∩ ofLp ⁻¹' dyadicCube k m = ofLp ⁻¹' dyadicCube k m ∩ T := by
    ext x
    exact ⟨fun ⟨hx1, hx2⟩ ↦ ⟨hx2, hQe hx2, hx1⟩, fun ⟨hx2, _, hx1⟩ ↦ ⟨hx1, hx2⟩⟩
  have hsub : {x | (s⁻¹ • u) x < M} ∩ ball z (2 ^ k / 2) ⊆ ofLp ⁻¹' dyadicCube k m \ T := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨ball_subset_preimage_dyadicCube k m hx2, fun hxT ↦ ?_⟩
    rw [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, inv_mul_lt_iff₀ hs0] at hx1
    have hxT' : max M 2 * s < u x := hxT.2
    nlinarith [le_max_left M 2]
  have hQ : volume (ofLp ⁻¹' dyadicCube k m) = volume (dyadicCube k m) :=
    (PiLp.volume_preserving_ofLp ι).measure_preimage
      (measurableSet_dyadicCube k m).nullMeasurableSet
  rw [heq, ← hQ]
  refine measure_inter_le_ofReal_one_sub_mul hT (hQ ▸ volume_dyadicCube_ne_top k m) hμ'.le ?_
  calc ENNReal.ofReal μ' * volume (ofLp ⁻¹' dyadicCube k m)
      ≤ ENNReal.ofReal μ * volume (ball z (2 ^ k / 2)) := by
        rw [hQ, volume_ball_dyadicCenter, ← mul_assoc, ← ENNReal.ofReal_mul hμ.le]
        gcongr
        exact (min_le_left _ _).trans (le_of_eq (by ring))
    _ ≤ _ := h.trans (measure_mono hsub)

/-! ### Geometric decay on a dyadic cube -/

omit [DecidableEq ι] in
/-- **Geometric decay of the superlevel sets on a dyadic cube.** Let `Q₀` be the dyadic cube of
level `k₀` at position `m₀`, `M ≥ 1` and `0 ≤ δ < 1`. Suppose that for every `j` and every dyadic
cube `Q ⊆ Q₀` of level `k ≤ k₀` with centre `z`, if `u ≤ M ^ j` somewhere in `B(z, 4 n 2ᵏ)`, then
`|{u > M ^ (j + 1)} ∩ Q| ≤ δ |Q|`. If `u ≤ 1` somewhere in the ball `B(z₀, 4 n 2^k₀)` about the
centre of `Q₀`, then `|{u > M ^ j} ∩ Q₀| ≤ δ ^ j |Q₀|` for every `j`. -/
private theorem volume_setOf_pow_lt_inter_dyadicCube_le [Nonempty ι] {M δ : ℝ} (hM : 1 ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {k₀ : ℤ} {m₀ : ι → ℤ} {u : EuclideanSpace ℝ ι → ℝ}
    (hmeas : ∀ j : ℕ, NullMeasurableSet ({x | M ^ j < u x} ∩ ofLp ⁻¹' dyadicCube k₀ m₀))
    (hstep : ∀ (j : ℕ) (k : ℤ) (m : ι → ℤ), k ≤ k₀ → dyadicCube k m ⊆ dyadicCube k₀ m₀ →
      (∃ x ∈ ball (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) (4 * Fintype.card ι * 2 ^ k),
        u x ≤ M ^ j) →
      volume ({x | M ^ (j + 1) < u x} ∩ ofLp ⁻¹' dyadicCube k m) ≤
        ENNReal.ofReal δ * volume (dyadicCube k m))
    (h0 : ∃ x ∈ ball (toLp 2 fun i ↦ ((m₀ i : ℝ) + 2⁻¹) * 2 ^ k₀) (4 * Fintype.card ι * 2 ^ k₀),
      u x ≤ 1) (j : ℕ) :
    volume ({x | M ^ j < u x} ∩ ofLp ⁻¹' dyadicCube k₀ m₀) ≤
      ENNReal.ofReal (δ ^ j) * volume (dyadicCube k₀ m₀) := by
  cases j with
  | zero =>
    rw [pow_zero, pow_zero, ENNReal.ofReal_one, one_mul,
      ← (PiLp.volume_preserving_ofLp ι).measure_preimage
      (measurableSet_dyadicCube k₀ m₀).nullMeasurableSet]
    exact measure_mono inter_subset_right
  | succ j =>
    -- In coordinates, `A i` is the part of `Q₀` where `u > M ^ (i + 1)`.
    set A : ℕ → Set (ι → ℝ) :=
      fun i ↦ toLp 2 ⁻¹' ({x | M ^ (i + 1) < u x} ∩ ofLp ⁻¹' dyadicCube k₀ m₀)
    have hvol (i : ℕ) :
        volume (A i) = volume ({x | M ^ (i + 1) < u x} ∩ ofLp ⁻¹' dyadicCube k₀ m₀) :=
      (PiLp.volume_preserving_toLp ι).measure_preimage (hmeas (i + 1))
    have hmemA {i : ℕ} {y : ι → ℝ} :
        y ∈ A i ↔ M ^ (i + 1) < u (toLp 2 y) ∧ y ∈ dyadicCube k₀ m₀ := by
      simp [A]
    have h := volume_le_pow_mul_volume_dyadicCube (A := A) (δ := ENNReal.ofReal δ)
      (fun i ↦ (hmeas (i + 1)).preimage (PiLp.volume_preserving_toLp ι).quasiMeasurePreserving)
      (fun i i' hii' y hy ↦ hmemA.2 ⟨(pow_le_pow_right₀ hM (by omega)).trans_lt (hmemA.1 hy).1,
        (hmemA.1 hy).2⟩)
      (ENNReal.ofReal_lt_one.2 hδ1) (fun y hy ↦ (hmemA.1 hy).2)
      (by rw [hvol]; exact hstep 0 k₀ m₀ le_rfl subset_rfl (by simpa using h0)) ?_ j
    · rwa [hvol, ← ENNReal.ofReal_pow hδ0] at h
    -- If the parent `Q'` of `Q` met `{u ≤ M ^ (i + 1)}`, the hypothesis would bound the part of
    -- `Q` where `u > M ^ (i + 2)` by `δ |Q|`.
    intro i k m m' hk hQ₀ hQ hlt y hy
    -- The parent `Q'` lies in `Q₀`, since it has level at most `k₀` and meets `Q₀`.
    have hQ' : dyadicCube (k + 1) m' ⊆ dyadicCube k₀ m₀ := by
      obtain ⟨x, hx⟩ := dyadicCube_nonempty k m
      rw [← mem_dyadicCube.1 (hQ₀ hx), ← mem_dyadicCube.1 (hQ hx)]
      exact dyadicCube_subset_dyadicCube (by omega) (mem_dyadicCube_dyadicIndex _ _)
    refine hmemA.2 ⟨lt_of_not_ge fun hle ↦ hlt.not_ge ?_, hQ' hy⟩
    have hdist : toLp 2 y ∈
        ball (toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) (4 * Fintype.card ι * 2 ^ k) := by
      have h1 := dist_lt_of_ofLp_mem_dyadicCube (x := toLp 2 y) (by simpa using hy)
        (hQ (ofLp_dyadicCenter_mem_dyadicCube k m))
      have h2 := zpow_pos (two_pos : (0 : ℝ) < 2) k
      have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
      rw [zpow_add_one₀ two_ne_zero] at h1
      exact mem_ball.2 (h1.trans_le (by nlinarith))
    calc volume (A (i + 1) ∩ dyadicCube k m)
        ≤ volume (toLp 2 ⁻¹' ({x | M ^ (i + 1 + 1) < u x} ∩ ofLp ⁻¹' dyadicCube k m)) :=
          measure_mono fun y hy ↦ ⟨(hmemA.1 hy.1).1, by simpa using hy.2⟩
      _ ≤ volume ({x | M ^ (i + 1 + 1) < u x} ∩ ofLp ⁻¹' dyadicCube k m) :=
          (PiLp.volume_preserving_toLp ι).measure_preimage_le _
      _ ≤ _ := hstep (i + 1) k m hk.le hQ₀ ⟨toLp 2 y, hdist, hle⟩

/-! ### Power decay -/

/-- **Power decay of the superlevel sets of a supersolution on a dyadic cube** (the `L^ε` lemma
of Krylov and Safonov; Caffarelli–Cabré, Lemma 4.6, for classical supersolutions of linear
equations). Let `κ > 0`. There are constants `C`, `ε > 0` and `ε₀ > 0`, depending only on the
dimension `n` and on `κ`, with the following property. Let `Q ⊆ ℝⁿ` be the dyadic cube of level
`k` at position `m`, let `c` be a point of `Q`, and let `ρ = 9 n 2ᵏ`. Let the coefficient matrix
`a` be uniformly elliptic on `B(c, ρ)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` on
`B(c, ρ)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there and `ρ ‖f⁺‖_{Lⁿ(B(c, ρ))} ≤ ε₀ λ`. If `u ≤ 1`
somewhere in `B(c, 3 n 2ᵏ)`, then `|{u > t} ∩ Q| ≤ C t^(-ε) |Q|` for every `t > 0`. -/
theorem exists_volume_setOf_lt_inter_dyadicCube_le_mul_rpow [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        ofLp c ∈ dyadicCube k m →
        UniformlyEllipticOn (ball c (9 * Fintype.card ι * 2 ^ k)) a lam Lam → Lam ≤ κ * lam →
        ContDiffOn ℝ 2 u (ball c (9 * Fintype.card ι * 2 ^ k)) →
        (∀ x ∈ ball c (9 * Fintype.card ι * 2 ^ k), 0 ≤ u x) →
        (∀ x ∈ ball c (9 * Fintype.card ι * 2 ^ k), ∑ i, ∑ j, a x i j *
          fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤
            f x) →
        ENNReal.ofReal (9 * Fintype.card ι * 2 ^ k) * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c (9 * Fintype.card ι * 2 ^ k))) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (3 * Fintype.card ι * 2 ^ k), u x ≤ 1) →
        ∀ t : ℝ, 0 < t → volume ({x | t < u x} ∩ ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal (C * t ^ (-ε)) * volume (dyadicCube k m) := by
  obtain ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, H⟩ := exists_volume_setOf_lt_inter_dyadicCube_le (ι := ι) hκ
  refine ⟨δ⁻¹, Real.log δ⁻¹ / Real.log M, ε₀, inv_pos.2 hδ0,
    div_pos (Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1)) (Real.log_pos hM), hε₀, ?_⟩
  intro lam Lam k m c a u f hc ha hLam hu hu0 hsuper hf ⟨x₀, hx₀, hux₀⟩ t ht
  set n : ℝ := (Fintype.card ι : ℝ)
  set ρ := 9 * n * 2 ^ k
  have hn : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have h2 := zpow_pos (two_pos : (0 : ℝ) < 2) k
  -- Every point of `Q` lies within `n 2ᵏ` of `c`.
  have hQc {y : EuclideanSpace ℝ ι} (hy : ofLp y ∈ dyadicCube k m) : dist y c < n * 2 ^ k :=
    dist_lt_of_ofLp_mem_dyadicCube hy hc
  have hQe : ofLp ⁻¹' dyadicCube k m ⊆ ball c ρ := fun y hy ↦
    mem_ball.2 ((hQc hy).trans_le (by simp only [ρ]; nlinarith))
  refine le_ofReal_mul_rpow_of_forall_pow_le
    (φ := fun t ↦ volume ({x | t < u x} ∩ ofLp ⁻¹' dyadicCube k m))
    (fun t t' htt' ↦ measure_mono (inter_subset_inter_left _ fun x hx ↦ htt'.trans_lt hx))
    hM hδ0 hδ1.le (fun t ↦ (measure_mono inter_subset_right).trans_eq
      ((PiLp.volume_preserving_ofLp ι).measure_preimage
        (measurableSet_dyadicCube k m).nullMeasurableSet))
    (volume_setOf_pow_lt_inter_dyadicCube_le hM.le hδ0.le hδ1 (fun j ↦ ?_)
      (fun j k' m' hk' hQ' hx ↦ ?_) ?_) ht
  · -- `u` is continuous on `B(c, ρ) ⊇ Q`, so its superlevel sets in `Q` are measurable.
    have heq : {x | M ^ j < u x} ∩ ofLp ⁻¹' dyadicCube k m =
        (ball c ρ ∩ u ⁻¹' Ioi (M ^ j)) ∩ ofLp ⁻¹' dyadicCube k m := by
      ext x
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨⟨hQe h2, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ ↦ ⟨h1, h2⟩⟩
    rw [heq]
    exact ((hu.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioi).measurableSet.inter
      ((measurableSet_dyadicCube k m).preimage
        (PiLp.volume_preserving_ofLp ι).measurable)).nullMeasurableSet
  · -- The measure estimate on a subcube `Q' ⊆ Q`, at the level `s = M ^ j`.
    have hkk : (2 : ℝ) ^ k' ≤ 2 ^ k := zpow_le_zpow_right₀ one_le_two hk'
    rw [pow_succ']
    refine H (one_le_pow₀ hM.le) (fun y hy ↦ ?_) ha hLam hu hu0 hsuper
      (le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by simp only [ρ]; nlinarith)) _) hf)
      hx
    have hz := hQc (hQ' (ofLp_dyadicCenter_mem_dyadicCube k' m'))
    rw [mem_closedBall] at hy
    exact mem_ball.2 ((dist_triangle _ _ _).trans_lt (by simp only [ρ]; nlinarith))
  · -- The point where `u ≤ 1` lies within `4 n 2ᵏ` of the centre of `Q`.
    have hz := hQc (ofLp_dyadicCenter_mem_dyadicCube k m)
    rw [mem_ball] at hx₀
    exact ⟨x₀, mem_ball.2 ((dist_triangle _ c _).trans_lt (by rw [dist_comm c]; linarith)), hux₀⟩

/-- **Power decay of the superlevel sets of a supersolution on a ball** (the `L^ε` lemma of Krylov
and Safonov; Caffarelli–Cabré, Lemma 4.6, for classical supersolutions of linear equations). Let
`κ > 0`. There are constants `C`, `ε > 0` and `ε₀ > 0`, depending only on the dimension `n` and
on `κ`, with the following property. Let `0 < r` and `41 n r ≤ R`. Let the coefficient matrix `a`
be uniformly elliptic on `B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` on
`B(c, R)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `u ≤ 1` somewhere
in `B(c, r)`, then `|{u > t} ∩ B(c, r)| ≤ C t^(-ε) |B(c, r)|` for every `t > 0`. -/
theorem exists_volume_setOf_lt_inter_ball_le_mul_rpow [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam r R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < r → 41 * Fintype.card ι * r ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ ball c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j *
          fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤
            f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c r, u x ≤ 1) →
        ∀ t : ℝ, 0 < t → volume ({x | t < u x} ∩ ball c r) ≤
          ENNReal.ofReal (C * t ^ (-ε)) * volume (ball c r) := by
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_lt_inter_dyadicCube_le_mul_rpow (ι := ι) hκ
  set N := Fintype.card ι
  set ω := volume.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  refine ⟨C * 8 ^ N / ω, ε, ε₀, by positivity, hε, hε₀, ?_⟩
  intro lam Lam r R c a u f hr hrR ha hLam hu hu0 hsuper hf ⟨x₀, hx₀, hux₀⟩ t ht
  set n : ℝ := (N : ℝ)
  have hn : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  -- A dyadic level `K` with `2 r < 2ᴷ ≤ 4 r`.
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℤ, 2 * r < 2 ^ K ∧ (2 : ℝ) ^ K ≤ 4 * r := by
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (by positivity : 0 < 2 * r) one_lt_two
    exact ⟨k + 1, hk2, by rw [zpow_add_one₀ two_ne_zero]; linarith⟩
  have hK0 : (0 : ℝ) < 2 ^ K := zpow_pos two_pos K
  obtain ⟨S, hcard, hcover, hcorner⟩ := exists_card_eq_ball_subset_biUnion c hr hK1
  -- The power decay on each of the `2ⁿ` cubes covering `B(c, r)`, about its corner `p = m 2ᴷ`.
  have hcube {m : ι → ℤ} (hm : m ∈ S) : volume ({x | t < u x} ∩ ofLp ⁻¹' dyadicCube K m) ≤
      ENNReal.ofReal (C * t ^ (-ε)) * volume (dyadicCube K m) := by
    set p : EuclideanSpace ℝ ι := toLp 2 fun i ↦ (m i : ℝ) * 2 ^ K
    have hp : dist p c ≤ n * (r + 2 ^ K) := hcorner m hm
    have hnK : n * 2 ^ K ≤ n * (4 * r) := mul_le_mul_of_nonneg_left hK2 (by positivity)
    have hnr : r ≤ n * r := le_mul_of_one_le_left hr.le hn
    have hsub : ball p (9 * N * 2 ^ K) ⊆ ball c R := fun y hy ↦ by
      rw [mem_ball] at hy ⊢
      exact (dist_triangle _ _ _).trans_lt (by nlinarith)
    refine H ?_ (ha.mono_set hsub) hLam (hu.mono hsub) (fun x hx ↦ hu0 x (hsub hx))
      (fun x hx ↦ hsuper x (hsub hx)) (le_trans (mul_le_mul'
        (ENNReal.ofReal_le_ofReal (by nlinarith))
        (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))) hf) ⟨x₀, ?_, hux₀⟩ t ht
    · rw [mem_dyadicCube]
      ext i
      simp [p, mul_div_cancel_right₀ _ hK0.ne']
    · rw [mem_ball] at hx₀ ⊢
      rw [dist_comm] at hp
      have hnK' : n * (2 * r) < n * 2 ^ K := mul_lt_mul_of_pos_left hK1 (by positivity)
      exact (dist_triangle _ c _).trans_lt (by nlinarith)
  obtain ⟨m₀, -⟩ := Finset.card_pos.1 (hcard ▸ Nat.two_pow_pos N)
  calc volume ({x | t < u x} ∩ ball c r)
      ≤ ∑ m ∈ S, volume ({x | t < u x} ∩ ofLp ⁻¹' dyadicCube K m) := by
        refine (measure_mono fun x hx ↦ ?_).trans (measure_biUnion_finset_le _ _)
        obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.1 (hcover hx.2)
        exact mem_biUnion hm ⟨hx.1, hxm⟩
    _ ≤ ∑ _m ∈ S, ENNReal.ofReal (C * t ^ (-ε)) * volume (dyadicCube K m₀) :=
        Finset.sum_le_sum fun m hm ↦ (hcube hm).trans_eq (by
          rw [volume_dyadicCube, volume_dyadicCube])
    _ ≤ _ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, div_mul_eq_mul_div, mul_right_comm C]
        exact two_pow_mul_volume_dyadicCube_le c m₀ hr hK2 (by positivity)

end PDE

end TauCeti
