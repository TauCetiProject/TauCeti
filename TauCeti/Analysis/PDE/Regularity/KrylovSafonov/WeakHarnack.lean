/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Sobolev
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Basic.ENNReal.Real
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.PosPart
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean
import TauCeti.Topology.Order.OrderClosed

/-!
# The weak Harnack inequality of Krylov and Safonov

Let `a` be uniformly elliptic on a ball `B(c, R) ⊆ ℝⁿ`, `n ≥ 1`, with constants `λ ≤ Λ ≤ κ λ`, and
let `u ≥ 0` be a supersolution of the non-divergence-form equation, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in
`B(c, R)`. The **weak Harnack inequality** bounds a small power mean of `u` near the centre by the
values of `u` and the size of `f⁺`: there are `p > 0` and `C`, depending only on `n` and `κ`, with

`‖u‖_{Lᵖ(B(c, R / (16 √n)))} ≤ C R^(n / p) (u(y) + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)`

for every `y ∈ B(c, R / 4)`. Dividing by `|B(c, R / (16 √n))|^(1 / p) ≈ R^(n / p)`, this says that
the `Lᵖ` mean of `u` over the small ball is at most a multiple of `inf_{B(c, R / 4)} u` plus the
right-hand-side term. The coefficients need no regularity, not even measurability, and need not
be symmetric. The estimate is stated for classical supersolutions, `u ∈ C²`
(`TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart`), and for strong supersolutions,
`u ∈ W^{2,n}` with a continuous representative, satisfying the inequality almost everywhere for
the weak Hessian (`TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart_of_wkp`).

Together with the local maximum principle
(`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`), which bounds the supremum of a
subsolution by its `Lᵖ` norms for every `p > 0`, it gives the Harnack inequality of Krylov and
Safonov for nonnegative solutions.

## The argument

Normalise by a level `m > 0` with `u(y) ≤ m` and `R ‖f⁺‖ ≤ ε₀ λ m`. Choose the dyadic scale `2ᵏ`
with `4 · 2ᵏ √n ≤ R < 8 · 2ᵏ √n`, and translate the dyadic cube of level `k` to be centred at `c`
(`TauCeti.PDE.exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul`). Its power decay,
applied to `u / m`, gives `|{u ≥ t} ∩ B(c, R / (16 √n))| ≤ C (t / m)^(-ε) (R / (4 √n))ⁿ` for all
`t > 0`: the point `y` lies within `2 · 2ᵏ √n` of the centre, and the small ball lies in the cube.
The layer-cake bound `TauCeti.lintegral_rpow_le_of_measure_lt_le_rpow_mul` at the exponent
`p = ε / 2` turns this into `∫ uᵖ ≤ (1 + C) mᵖ (R / (4 √n))ⁿ` over the small ball. Letting `m`
decrease to `u(y) + R ‖f⁺‖ / (ε₀ λ)` gives the classical estimate.

A strong supersolution is approximated, as in
`TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp`, by smooth classical
supersolutions `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` whose right-hand sides are
bounded in `Lⁿ` by `‖f⁺‖ + ζ`. The classical estimate for `w` and `ζ → 0` give the strong one.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart`: **the weak Harnack
  inequality** for classical supersolutions.
* `TauCeti.PDE.exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart_of_wkp`: the weak Harnack
  inequality for strong supersolutions in `W^{2,n}`.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Theorem 4.8.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7, Theorem 9.22.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The ball `B(c, R / (16 √n))` on which the weak Harnack inequality bounds `u` lies in
`closedBall c R`. -/
private theorem ball_div_sixteen_mul_sqrt_subset_closedBall [Nonempty ι] (c : EuclideanSpace ℝ ι)
    {R : ℝ} (hR : 0 ≤ R) : ball c (R / (16 * √(Fintype.card ι))) ⊆ closedBall c R :=
  ball_subset_closedBall.trans (closedBall_subset_closedBall (div_le_self hR (by
    nlinarith [Real.one_le_sqrt.2 (Nat.one_le_cast.2 (Fintype.card_pos (α := ι)))])))

omit [DecidableEq ι] in
/-- The ball `B(c, R / (16 √n))` has volume at most `(R / (4 √n))ⁿ`: it lies in a cube of side
`R / (8 √n)`. -/
private theorem volume_ball_div_sixteen_mul_sqrt_le [Nonempty ι] (c : EuclideanSpace ℝ ι)
    {R : ℝ} (hR : 0 < R) :
    volume (ball c (R / (16 * √(Fintype.card ι)))) ≤
      ENNReal.ofReal ((R / (4 * √(Fintype.card ι))) ^ Fintype.card ι) := by
  have hn : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  calc volume (ball c (R / (16 * √(Fintype.card ι)))) ≤
        volume (WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp c) (R / (16 * √(Fintype.card ι)))) :=
        measure_mono (PiLp.ball_subset_preimage_ofLp_ball _ _)
    _ = ENNReal.ofReal ((2 * (R / (16 * √(Fintype.card ι)))) ^ Fintype.card ι) := by
        rw [(PiLp.volume_preserving_ofLp ι).measure_preimage measurableSet_ball.nullMeasurableSet,
          Real.volume_pi_ball _ (by positivity)]
    _ ≤ _ := by
        gcongr
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

/-- **The power decay on a ball, at an arbitrary level.** There are `C > 0`, `ε > 0` and `ε₀ > 0`,
depending only on the dimension and on `κ`, with the following property. Let `u ≥ 0` be a `C²`
supersolution in `B(c, R)` with right-hand side `f`, and let `m > 0` be a level with
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ m` and `u(y) ≤ m` at some `y ∈ B(c, R / 4)`. Then
`|{u ≥ t} ∩ B(c, R / (16 √n))| ≤ C (t / m)^(-ε) (R / (4 √n))ⁿ` for every `t > 0`. -/
private theorem exists_volume_setOf_le_inter_ball_le [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R m : ℝ⦄ ⦃c y : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < m →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam * m) →
        y ∈ ball c (R / 4) → u y ≤ m →
        ∀ ⦃t : ℝ⦄, 0 < t →
          volume ({x | t ≤ u x} ∩ ball c (R / (16 * √(Fintype.card ι)))) ≤
            ENNReal.ofReal (C * (t / m) ^ (-ε) *
              (R / (4 * √(Fintype.card ι))) ^ Fintype.card ι) := by
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  refine ⟨C, ε, ε₀, hC, hε, hε₀, ?_⟩
  intro lam Lam R m c y a u f hm ha hLam hcont hu hnonneg hsuper hf hy hum t ht
  set n := Fintype.card ι
  have hn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hm' : 0 ≤ m⁻¹ := inv_nonneg.2 hm.le
  obtain ⟨k, hkR, hRk⟩ := exists_four_mul_two_zpow_mul_le_and_lt
    (by linarith [pos_of_mem_ball hy] : 0 < R) hn
  -- The power decay for `u / m` on the dyadic cube `Q` of level `k`, translated by `d` to `c`.
  have HQ := H (u := fun x ↦ m⁻¹ * u x) (f := fun x ↦ m⁻¹ * f x) hkR ha hLam
    (continuousOn_const.mul hcont) (contDiffOn_const.mul hu)
    (fun x hx ↦ mul_nonneg hm' (hnonneg x hx))
    (fun x hx ↦ by
      rw [sum_mul_fderiv_fderiv_const_mul]
      exact mul_le_mul_of_nonneg_left (hsuper x hx) hm')
    (by
      rw [eLpNorm_posPart_const_mul hm', mul_left_comm]
      calc _ ≤ ENNReal.ofReal m⁻¹ * ENNReal.ofReal (ε₀ * lam * m) := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul hm', inv_mul_eq_div, mul_div_cancel_right₀ _ hm.ne'])
    ⟨y, ball_subset_ball hRk.le hy, by rwa [inv_mul_le_one₀ hm]⟩ (div_pos ht hm)
  set c₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ 2⁻¹ * 2 ^ k
  set d := c - c₀
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' dyadicCube k 0
  have hQ : volume Q = ENNReal.ofReal ((2 ^ k) ^ n) := by
    rw [(PiLp.volume_preserving_ofLp ι).measure_preimage
      (measurableSet_dyadicCube k 0).nullMeasurableSet, volume_dyadicCube]
  -- The translated small ball lies in `Q`, since `R / (16 √n) < 2ᵏ / 2`.
  have hsub : (· + d) ⁻¹' ({x | t ≤ u x} ∩ ball c (R / (16 * √(n : ℝ)))) ⊆
      {x | t / m ≤ m⁻¹ * u (x + d)} ∩ Q := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨by rw [mem_ofPred_eq, div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hx1 hm', ?_⟩
    have hx : x ∈ ball c₀ (2 ^ k / 2) := by
      rw [mem_ball, ← dist_add_sub_eq x c c₀]
      refine (mem_ball.1 hx2).trans_le ?_
      rw [div_le_div_iff₀ (by positivity) two_pos]
      linarith
    exact toLp_preimage_ball_subset_dyadicCube k 0 (by simpa [c₀] using hx)
  calc volume ({x | t ≤ u x} ∩ ball c (R / (16 * √(n : ℝ)))) =
        volume ((· + d) ⁻¹' ({x | t ≤ u x} ∩ ball c (R / (16 * √(n : ℝ))))) :=
        (measure_preimage_add_right _ _ _).symm
    _ ≤ ENNReal.ofReal (C * (t / m) ^ (-ε)) * volume Q := (measure_mono hsub).trans HQ
    _ ≤ ENNReal.ofReal (C * (t / m) ^ (-ε)) * ENNReal.ofReal ((R / (4 * √(n : ℝ))) ^ n) := by
        rw [hQ]
        gcongr
        rw [le_div_iff₀ (by positivity)]
        linarith
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- **The integral form of the weak Harnack inequality at a fixed level.** There are `p > 0`,
`K > 0` and `ε₀ > 0`, depending only on the dimension and on `κ`, with the following property.
Let `u ≥ 0` be a `C²` supersolution in `B(c, R)` with right-hand side `f`, and let `m > 0` be a
level with `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ m` and `u(y) ≤ m` at some `y ∈ B(c, R / 4)`. Then
`∫_{B(c, R / (16 √n))} uᵖ ≤ mᵖ K (R / (4 √n))ⁿ`. -/
private theorem exists_lintegral_rpow_le_of_le [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ p K ε₀ : ℝ, 0 < p ∧ 0 < K ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R m : ℝ⦄ ⦃c y : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < m →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam * m) →
        y ∈ ball c (R / 4) → u y ≤ m →
        ∫⁻ x in ball c (R / (16 * √(Fintype.card ι))), ‖u x‖ₑ ^ p ≤
          ENNReal.ofReal (m ^ p * (K * (R / (4 * √(Fintype.card ι))) ^ Fintype.card ι)) := by
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ := exists_volume_setOf_le_inter_ball_le (ι := ι) hκ
  refine ⟨ε / 2, 1 + C, ε₀, by positivity, by positivity, hε₀, ?_⟩
  intro lam Lam R m c y a u f hm ha hLam hcont hu hnonneg hsuper hf hy hum
  set n := Fintype.card ι
  set p := ε / 2 with hp_def
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  set B := ball c (R / (16 * √(n : ℝ)))
  set A := R / (4 * √(n : ℝ)) with hA_def
  have hBR := ball_div_sixteen_mul_sqrt_subset_closedBall c hR.le
  -- The superlevel sets of `‖u‖ₑ` on `B` decay like `t^(-ε)`.
  have htail (t : ℝ) (ht : m < t) : volume.restrict B {x | ENNReal.ofReal t < ‖u x‖ₑ} ≤
      ENNReal.ofReal (t ^ (-ε)) * ENNReal.ofReal (C * m ^ ε * A ^ n) := by
    have ht0 : 0 < t := hm.trans ht
    rw [Measure.restrict_apply' measurableSet_ball]
    have hsub : {x | ENNReal.ofReal t < ‖u x‖ₑ} ∩ B ⊆ {x | t ≤ u x} ∩ B := fun x hx ↦ by
      have hx1 : ENNReal.ofReal t < ‖u x‖ₑ := hx.1
      rw [Real.eNorm_eq_ofReal (hnonneg x (hBR hx.2))] at hx1
      exact ⟨((ENNReal.ofReal_lt_ofReal_iff'.1 hx1).1).le, hx.2⟩
    refine (measure_mono hsub).trans
      ((H hm ha hLam hcont hu hnonneg hsuper hf hy hum ht0).trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), Real.div_rpow ht0.le hm.le, Real.rpow_neg hm.le,
      div_inv_eq_mul, hA_def]
    congr 1
    ring
  -- The layer-cake bound at `p = ε / 2`, where `p / (ε - p) = 1`.
  have hεp : p / (ε - p) = 1 := by rw [div_eq_one_iff_eq (by linarith)]; linarith
  have hmp : p / (ε - p) * m ^ (p - ε) * (C * m ^ ε * A ^ n) = m ^ p * (C * A ^ n) := by
    rw [hεp, one_mul, show m ^ (p - ε) * (C * m ^ ε * A ^ n) = C * A ^ n * (m ^ (p - ε) * m ^ ε)
      by ring, ← Real.rpow_add hm, sub_add_cancel]
    ring
  refine (lintegral_rpow_le_of_measure_lt_le_rpow_mul _
    ((hcont.mono hBR).aestronglyMeasurable measurableSet_ball).eNorm (by positivity)
    (by linarith) hm htail).trans ?_
  rw [← ENNReal.ofReal_mul (by rw [hεp]; positivity), hmp, Measure.restrict_apply_univ]
  calc ENNReal.ofReal (m ^ p) * volume B + ENNReal.ofReal (m ^ p * (C * A ^ n)) ≤
      ENNReal.ofReal (m ^ p) * ENNReal.ofReal (A ^ n) + ENNReal.ofReal (m ^ p * (C * A ^ n)) := by
        gcongr
        exact volume_ball_div_sixteen_mul_sqrt_le c hR
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- **The weak Harnack inequality at a fixed level.** There are `p > 0`, `K > 0` and `ε₀ > 0`,
depending only on the dimension and on `κ`, with the following property. Let `u ≥ 0` be a `C²`
supersolution in `B(c, R)` with right-hand side `f`, and let `m > 0` be a level with
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ m` and `u(y) ≤ m` at some `y ∈ B(c, R / 4)`. Then
`‖u‖_{Lᵖ(B(c, R / (16 √n)))} ≤ K R^(n / p) m`. -/
private theorem exists_eLpNorm_le_mul_rpow_mul_of_le [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ p K ε₀ : ℝ, 0 < p ∧ 0 < K ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R m : ℝ⦄ ⦃c y : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < m →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam * m) →
        y ∈ ball c (R / 4) → u y ≤ m →
        eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (ball c (R / (16 * √(Fintype.card ι))))) ≤
          ENNReal.ofReal (K * R ^ ((Fintype.card ι : ℝ) / p) * m) := by
  obtain ⟨p, K, ε₀, hp, hK, hε₀, H⟩ := exists_lintegral_rpow_le_of_le (ι := ι) hκ
  refine ⟨p, K ^ p⁻¹, ε₀, hp, by positivity, hε₀, ?_⟩
  intro lam Lam R m c y a u f hm ha hLam hcont hu hnonneg hsuper hf hy hum
  set n := Fintype.card ι
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  have hn1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  set A := R / (4 * √(n : ℝ))
  have hA : 0 ≤ A := by positivity
  -- Take the `p`-th root of the integral bound, and use `A ≤ R`.
  refine (eLpNorm_le_of_lintegral_rpow_le (t := ENNReal.ofReal (K ^ p⁻¹ * A ^ ((n : ℝ) / p) * m))
    (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
    (((hcont.mono (ball_div_sixteen_mul_sqrt_subset_closedBall c hR.le)).aestronglyMeasurable
      measurableSet_ball)) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · -- `(K^(1/p) A^(n/p) m)^p = m^p K Aⁿ`.
    have hpow : (K ^ p⁻¹ * A ^ ((n : ℝ) / p) * m) ^ p = m ^ p * (K * A ^ n) := by
      rw [Real.mul_rpow (by positivity) hm.le, Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_inv_rpow hK.le hp.ne', ← Real.rpow_mul hA, div_mul_cancel₀ _ hp.ne',
        Real.rpow_natCast]
      ring
    rw [ENNReal.toReal_ofReal hp.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le, hpow]
    exact H hm ha hLam hcont hu hnonneg hsuper hf hy hum
  · gcongr
    exact div_le_self hR.le (by linarith)

/-- **The weak Harnack inequality of Krylov and Safonov** (Gilbarg–Trudinger, Theorem 9.22;
Caffarelli–Cabré, Theorem 4.8). Let `κ > 0`. There are `p > 0` and `C > 0`, depending only on the
dimension `n ≥ 1` and on `κ`, with the following property. Let `a` be uniformly elliptic on
`B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u` be continuous on `closedBall c R`, nonnegative
there and `C²` in `B(c, R)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there. Then for every `y ∈ B(c, R / 4)`,

`‖u‖_{Lᵖ(B(c, R / (16 √n)))} ≤ C R^(n / p) (u(y) + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)`.

The coefficients need be neither measurable nor symmetric. -/
theorem exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart {κ : ℝ} (hκ : 0 < κ) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball c R) a lam Lam →
        Lam ≤ κ * lam → ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ∀ y ∈ ball c (R / 4),
          eLpNorm u (ENNReal.ofReal p)
              (volume.restrict (ball c (R / (16 * √(Fintype.card ι))))) ≤
            ENNReal.ofReal (C * R ^ ((Fintype.card ι : ℝ) / p)) *
              (ENNReal.ofReal (u y) + ENNReal.ofReal (R / lam) *
                eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R))) := by
  -- In dimension `0` the small ball has radius `R / 0 = 0`.
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, one_pos, one_pos, fun lam Lam R c a u f _ _ _ _ _ _ y _ ↦ ?_⟩
    rw [show ball c (R / (16 * √(Fintype.card ι : ℝ))) = ∅ by simp, Measure.restrict_empty,
      eLpNorm_measure_zero]
    exact zero_le
  obtain ⟨p, K, ε₀, hp, hK, hε₀, H⟩ := exists_eLpNorm_le_mul_rpow_mul_of_le (ι := ι) hκ
  refine ⟨p, K * max 1 ε₀⁻¹, hp, by positivity, ?_⟩
  intro lam Lam R c a u f ha hLam hcont hu hnonneg hsuper y hy
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  have hlam : 0 < lam := ha.pos
  have huy : 0 ≤ u y := hnonneg y (ball_subset_closedBall (ball_subset_ball (by linarith) hy))
  set E := eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R))
  rcases eq_or_ne E ∞ with hE | hE
  · rw [hE]
    exact le_ofReal_mul_add_ofReal_mul_top (by positivity) (div_pos hR hlam) _
  set F := E.toReal
  have hEF : E = ENNReal.ofReal F := (ENNReal.ofReal_toReal hE).symm
  set D := K * R ^ ((Fintype.card ι : ℝ) / p)
  -- Apply the fixed-level estimate at `m₀ + η` for `m₀ = u(y) + R F / (ε₀ λ)`, and let `η → 0`.
  set m₀ := u y + R * F / (ε₀ * lam)
  have hm₀ : 0 ≤ R * F / (ε₀ * lam) := by positivity
  have hle := ContinuousWithinAt.le_of_forall_gt_le (a := 0)
    (g := fun η ↦ ENNReal.ofReal (D * (m₀ + η)))
    (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous _)).continuousWithinAt
    fun η hη ↦ H (m := m₀ + η) (by positivity) ha hLam hcont hu hnonneg hsuper (by
      refine (congrArg (ENNReal.ofReal R * ·) hEF).le.trans ?_
      rw [← ENNReal.ofReal_mul hR.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have h : ε₀ * lam * (R * F / (ε₀ * lam)) = R * F := by field_simp
      nlinarith [mul_pos (mul_pos hε₀ hlam) hη, mul_nonneg (mul_pos hε₀ hlam).le huy]) hy
      (by linarith)
  rw [add_zero] at hle
  refine hle.trans ?_
  rw [hEF, ofReal_mul_ofReal_add_ofReal_mul_ofReal _ huy (by positivity) ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `m₀ ≤ max 1 ε₀⁻¹ (u(y) + R F / λ)`.
  have h1 : u y ≤ max 1 ε₀⁻¹ * u y := le_mul_of_one_le_left huy (le_max_left _ _)
  have h2 : R * F / (ε₀ * lam) ≤ max 1 ε₀⁻¹ * (R / lam * F) := by
    rw [show R * F / (ε₀ * lam) = ε₀⁻¹ * (R / lam * F) by field_simp]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc D * m₀ ≤ D * (max 1 ε₀⁻¹ * (u y + R / lam * F)) := by gcongr; linarith
    _ = _ := by ring

/-- **The weak Harnack inequality for strong supersolutions, with a margin `ζ > 0`.** With `p` and
`C` the constants of the classical weak Harnack inequality: let `u ∈ W^{2,n}(Ω)` have a
representative `ū` continuous on `Ω ⊇ closedBall c R` and nonnegative on `closedBall c R`, with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere in `B(c, R)` and `‖f⁺‖_{Lⁿ(B(c, R))} ≤ F`. Then for every
`y ∈ B(c, R / 4)` and `ζ > 0`,
`‖ū‖_{Lᵖ(B(c, R / (16 √n)))} ≤ C R^(n / p) (ū(y) + 2 ζ + (1 + 3 ζ) R (F + ζ) / λ)`. -/
private theorem exists_eLpNorm_le_of_wkp_of_pos [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ ⦃lam Lam R F ζ : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ closedBall c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) →
        0 ≤ F → eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) ≤
          ENNReal.ofReal F → 0 < ζ → ∀ y ∈ ball c (R / 4),
          eLpNorm ū (ENNReal.ofReal p)
              (volume.restrict (ball c (R / (16 * √(Fintype.card ι))))) ≤
            ENNReal.ofReal (C * R ^ ((Fintype.card ι : ℝ) / p) *
              (ū y + 2 * ζ + (1 + 3 * ζ) * (R / lam * (F + ζ)))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by
    have h : (1 : ℝ≥0∞) ≤ Fintype.card ι := Fact.out
    exact_mod_cast h)
  obtain ⟨p, C, hp, hC, H⟩ := exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart (ι := ι) hκ
  refine ⟨p, C, hp, hC, ?_⟩
  intro lam Lam R F ζ c Ω a ū f u hRΩ ha hLam hcont hū hnonneg hsuper hF hfF hζ y hy
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  have hlam : 0 < lam := ha.pos
  have hyR : y ∈ closedBall c R := ball_subset_closedBall (ball_subset_ball (by linarith) hy)
  have hBR := ball_div_sixteen_mul_sqrt_subset_closedBall c hR.le
  have hσ : 0 < 1 + 3 * ζ := by positivity
  -- A smooth `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` and right-hand side `g`.
  obtain ⟨w, g, hw, hwū, hwg, hg⟩ :=
    exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp (ENNReal.natCast_ne_top _) u
      hcont hū (isCompact_closedBall c R) hRΩ ball_subset_closedBall
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ha.abs_apply_le hx) hsuper
      (M := F + ζ) (by positivity) (hfF.trans (ENNReal.ofReal_le_ofReal (by linarith))) hζ
  have hw2 : ContDiff ℝ 2 w := contDiff_infty.1 hw 2
  have Hw := H ha hLam hw2.continuous.continuousOn hw2.contDiffOn
    (fun x hx ↦ (div_nonneg (hnonneg x hx) hσ.le).trans (hwū x hx).1) hwg y hy
  -- `ū ≤ (1 + 3 ζ) w` on the small ball.
  have hmono : eLpNorm ū (ENNReal.ofReal p)
      (volume.restrict (ball c (R / (16 * √(Fintype.card ι))))) ≤
      ENNReal.ofReal (1 + 3 * ζ) * eLpNorm w (ENNReal.ofReal p)
        (volume.restrict (ball c (R / (16 * √(Fintype.card ι))))) := by
    refine (eLpNorm_mono_ae_real (g := (1 + 3 * ζ) • w)
      ((hcont.mono (hBR.trans hRΩ)).aestronglyMeasurable measurableSet_ball)
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ ?_)).trans_eq ?_
    · rw [Real.norm_of_nonneg (hnonneg x (hBR hx)), Pi.smul_apply, smul_eq_mul,
        ← div_le_iff₀' hσ]
      exact (hwū x (hBR hx)).1
    · rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal hσ.le]
  calc _ ≤ ENNReal.ofReal (1 + 3 * ζ) * (ENNReal.ofReal (C * R ^ ((Fintype.card ι : ℝ) / p)) *
        (ENNReal.ofReal (w y) + ENNReal.ofReal (R / lam) * eLpNorm (fun x ↦ (g x)⁺)
          (Fintype.card ι) (volume.restrict (ball c R)))) := hmono.trans (by gcongr)
    _ ≤ ENNReal.ofReal (1 + 3 * ζ) * (ENNReal.ofReal (C * R ^ ((Fintype.card ι : ℝ) / p)) *
        (ENNReal.ofReal ((ū y + 2 * ζ) / (1 + 3 * ζ)) +
          ENNReal.ofReal (R / lam) * ENNReal.ofReal (F + ζ))) := by
        gcongr
        exact (hwū y hyR).2
    _ = _ := by
        rw [ofReal_mul_ofReal_add_ofReal_mul_ofReal _
          (div_nonneg (by linarith [hnonneg y hyR]) hσ.le) (by positivity) (by linarith),
          ← ENNReal.ofReal_mul hσ.le]
        congr 1
        field_simp

/-- **The weak Harnack inequality for strong supersolutions** (Gilbarg–Trudinger, Theorem 9.22).
Let `κ > 0`. There are `p > 0` and `C > 0`, depending only on the dimension `n ≥ 1` and on `κ`,
with the following property. Let `Ω` be an open set containing `closedBall c R`, let `a` be
uniformly elliptic on `B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ∈ W^{2,n}(Ω)` have a
representative `ū` continuous on `Ω` and nonnegative on `closedBall c R`, with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere in `B(c, R)` for the weak Hessian. Then for every
`y ∈ B(c, R / 4)`,

`‖ū‖_{Lᵖ(B(c, R / (16 √n)))} ≤ C R^(n / p) (ū(y) + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)`.

The coefficients need be neither measurable nor symmetric. -/
theorem exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart_of_wkp
    [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {κ : ℝ} (hκ : 0 < κ) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃Ω : Opens (EuclideanSpace ℝ ι)⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃ū f : EuclideanSpace ℝ ι → ℝ⦄
        (u : Wkp volume Ω (Fintype.card ι) 2), closedBall c R ⊆ Ω →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn ū Ω → (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū →
        (∀ x ∈ closedBall c R, 0 ≤ ū x) →
        (∀ᵐ x ∂volume.restrict (ball c R),
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x) →
        ∀ y ∈ ball c (R / 4),
          eLpNorm ū (ENNReal.ofReal p)
              (volume.restrict (ball c (R / (16 * √(Fintype.card ι))))) ≤
            ENNReal.ofReal (C * R ^ ((Fintype.card ι : ℝ) / p)) *
              (ENNReal.ofReal (ū y) + ENNReal.ofReal (R / lam) *
                eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R))) := by
  obtain ⟨p, C, hp, hC, H⟩ := exists_eLpNorm_le_of_wkp_of_pos (ι := ι) hκ
  refine ⟨p, C, hp, hC, ?_⟩
  intro lam Lam R c Ω a ū f u hRΩ ha hLam hcont hū hnonneg hsuper y hy
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  have hlam : 0 < lam := ha.pos
  have huy : 0 ≤ ū y := hnonneg y (ball_subset_closedBall (ball_subset_ball (by linarith) hy))
  set E := eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R))
  rcases eq_or_ne E ∞ with hE | hE
  · rw [hE]
    exact le_ofReal_mul_add_ofReal_mul_top (by positivity) (div_pos hR hlam) _
  set F := E.toReal
  have hEF : E = ENNReal.ofReal F := (ENNReal.ofReal_toReal hE).symm
  -- Apply the estimate with margin `ζ` at `F = ‖f⁺‖`, and let `ζ → 0`.
  have hle := ContinuousWithinAt.le_of_forall_gt_le (a := 0)
    (g := fun ζ ↦ ENNReal.ofReal (C * R ^ ((Fintype.card ι : ℝ) / p) *
      (ū y + 2 * ζ + (1 + 3 * ζ) * (R / lam * (F + ζ)))))
    (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous _)).continuousWithinAt
    fun ζ hζ ↦ H u hRΩ ha hLam hcont hū hnonneg hsuper ENNReal.toReal_nonneg hEF.le hζ y hy
  refine hle.trans_eq ?_
  rw [hEF, ofReal_mul_ofReal_add_ofReal_mul_ofReal _ huy (by positivity) ENNReal.toReal_nonneg]
  congr 1
  ring

end PDE

end TauCeti
