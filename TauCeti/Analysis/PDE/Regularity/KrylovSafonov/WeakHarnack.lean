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
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.PosPart
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
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
right-hand-side term. By a ball-chaining argument along line segments and a finite covering, the
same estimate extends to any concentric ball `B(x₀, θ R)` with `0 < θ < 1`
(`TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`).
The coefficients need no regularity, not even measurability, and need not
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
  inequality** for classical supersolutions on `B(c, R / (16 √n))`.
* `TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`: **the weak
  Harnack inequality** for classical supersolutions on `B(x₀, θ R)` for arbitrary `0 < θ < 1`.
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

/-- **Small-ball `Lᵖ` bound from a point bound.** Let `δ₀ = (16 √n)⁻¹`. There are `p > 0` and
`C₁ > 0`, depending only on the dimension `n ≥ 1` and on `κ`, with the following property. Let `a`
be uniformly elliptic on `B(c, ρ)` with `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be continuous on
`closedBall c ρ` and `C²` in `B(c, ρ)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there and
`‖f⁺‖_{Lⁿ(B(c, ρ))} ≤ F`, `F ≥ 0`. If `u ≤ A` at some point of `B(c, δ₀ ρ)`, then

`(δ₀ ρ)^(-n/p) ‖u‖_{Lᵖ(B(c, δ₀ ρ))} ≤ C₁ (A + ρ F / λ)`. -/
private theorem exists_rpow_neg_mul_eLpNorm_ball_le_of_exists_le_small [Nonempty ι] {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ p C₁ : ℝ, 0 < p ∧ 0 < C₁ ∧
      ∀ ⦃lam Lam ρ A F : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        0 < ρ → 0 ≤ F →
        UniformlyEllipticOn (ball c ρ) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c ρ) → ContDiffOn ℝ 2 u (ball c ρ) →
        (∀ x ∈ closedBall c ρ, 0 ≤ u x) →
        (∀ x ∈ ball c ρ, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c ρ)) ≤
          ENNReal.ofReal F →
        (∃ w ∈ ball c ((16 * √(Fintype.card ι))⁻¹ * ρ), u w ≤ A) →
        ((16 * √(Fintype.card ι))⁻¹ * ρ) ^ (-(Fintype.card ι : ℝ) / p) *
          (eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (ball c ((16 * √(Fintype.card ι))⁻¹ * ρ)))).toReal ≤
        C₁ * (A + ρ * F / lam) := by
  obtain ⟨p, C, hp, hC, H⟩ := exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart (ι := ι) hκ
  set n : ℝ := (Fintype.card ι : ℝ)
  set s : ℝ := 16 * √n
  have hs : 4 ≤ s := by
    have := Real.one_le_sqrt.2 (Nat.one_le_cast.2 (Fintype.card_pos (α := ι)))
    linarith
  refine ⟨p, C * s ^ (n / p), hp, by positivity, ?_⟩
  intro lam Lam ρ A F c a u f hρ hF ha hLam hcont hu hnn hsuper hf ⟨w, hw, huw⟩
  have hlam : 0 < lam := ha.pos
  have hw4 : w ∈ ball c (ρ / 4) := by
    refine ball_subset_ball ?_ hw
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hρ.le four_pos hs
  have hwρ : w ∈ closedBall c ρ := ball_subset_closedBall (ball_subset_ball (by linarith) hw4)
  have hA0 : 0 ≤ A := (hnn w hwρ).trans huw
  have hwe := H ha hLam hcont hu hnn hsuper w hw4
  have hle_enn : eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (ρ / s))) ≤
      ENNReal.ofReal (C * ρ ^ (n / p) * (A + ρ * F / lam)) := by
    refine hwe.trans ?_
    calc ENNReal.ofReal (C * ρ ^ (n / p)) *
          (ENNReal.ofReal (u w) + ENNReal.ofReal (ρ / lam) *
            eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c ρ)))
        ≤ ENNReal.ofReal (C * ρ ^ (n / p)) *
            (ENNReal.ofReal A + ENNReal.ofReal (ρ / lam) * ENNReal.ofReal F) := by gcongr
      _ = ENNReal.ofReal (C * ρ ^ (n / p) * (A + ρ * F / lam)) := by
          rw [← ENNReal.ofReal_mul (div_pos hρ hlam).le, ← ENNReal.ofReal_add hA0 (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have htoReal : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (ρ / s)))).toReal ≤
      C * ρ ^ (n / p) * (A + ρ * F / lam) :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_enn).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hscale : (s⁻¹ * ρ) ^ (-n / p) * ρ ^ (n / p) = s ^ (n / p) := by
    rw [inv_mul_eq_div, neg_div, Real.rpow_neg (div_pos hρ (by linarith)).le,
      Real.div_rpow hρ.le (by linarith), inv_div, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hρ _).ne']
  calc (s⁻¹ * ρ) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (s⁻¹ * ρ)))).toReal
      ≤ (s⁻¹ * ρ) ^ (-n / p) * (C * ρ ^ (n / p) * (A + ρ * F / lam)) := by
        rw [inv_mul_eq_div]
        gcongr
    _ = C * ((s⁻¹ * ρ) ^ (-n / p) * ρ ^ (n / p)) * (A + ρ * F / lam) := by ring
    _ = C * s ^ (n / p) * (A + ρ * F / lam) := by rw [hscale]

/-- **Propagation of the small-ball `Lᵖ` bound along a segment chain.** Given the small-ball
point-to-`Lᵖ` estimate `Hsmall` on balls of radius `σ R = (1 - θ) R / 2` inside `B(x₀, R)` and a
nonnegative `C²` supersolution `u` of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(x₀, R)`, stepping `N` times along
the segment from `y` to any `z ∈ closedBall x₀ (θ R)` bounds `(η₀ R)^(-n/p) ‖u‖_{Lᵖ(B(z, η₀ R))}`
by `((N + 1) M₁^N C₁) (u(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`, where `η₀ = (16 √n)⁻¹ (1 - θ) / 2`. -/
private theorem rpow_neg_mul_eLpNorm_ball_le_of_chain [Nonempty ι]
    {p C₁ κ θ lam Lam R : ℝ} {x₀ y z : EuclideanSpace ℝ ι}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u f : EuclideanSpace ℝ ι → ℝ}
    (hp : 0 < p) (hC₁ : 0 < C₁) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R)
    (ha : UniformlyEllipticOn (ball x₀ R) a lam Lam) (hLam : Lam ≤ κ * lam)
    (hu : ContDiffOn ℝ 2 u (ball x₀ R)) (hnn : ∀ x ∈ ball x₀ R, 0 ≤ u x)
    (hsuper : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x)
    (hf : MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R)))
    (Hsmall : ∀ ⦃lam Lam ρ A F : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄
      ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
      0 < ρ → 0 ≤ F →
      UniformlyEllipticOn (ball c ρ) a lam Lam → Lam ≤ κ * lam →
      ContinuousOn u (closedBall c ρ) → ContDiffOn ℝ 2 u (ball c ρ) →
      (∀ x ∈ closedBall c ρ, 0 ≤ u x) →
      (∀ x ∈ ball c ρ, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
      eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c ρ)) ≤
        ENNReal.ofReal F →
      (∃ w ∈ ball c ((16 * √(Fintype.card ι))⁻¹ * ρ), u w ≤ A) →
      ((16 * √(Fintype.card ι))⁻¹ * ρ) ^ (-(Fintype.card ι : ℝ) / p) *
        (eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (ball c ((16 * √(Fintype.card ι))⁻¹ * ρ)))).toReal ≤
      C₁ * (A + ρ * F / lam))
    (hy : y ∈ closedBall x₀ (θ * R)) (hz : z ∈ closedBall x₀ (θ * R)) :
    let n : ℝ := (Fintype.card ι : ℝ)
    let η₀ : ℝ := (16 * √n)⁻¹ * ((1 - θ) / 2)
    let K₀ : ℝ := 2 ^ (n / p) * (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹)
    let M₁ : ℝ := max 1 (C₁ * K₀)
    let N : ℕ := ⌈4 * θ / η₀⌉₊ + 1
    (η₀ * R) ^ (-n / p) *
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball z (η₀ * R)))).toReal ≤
    ((N : ℝ) + 1) * M₁ ^ N * C₁ *
      (u y + R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
        (volume.restrict (ball x₀ R))).toReal / lam) := by
  intro n η₀ K₀ M₁ N
  set δ₀ : ℝ := (16 * √n)⁻¹
  have hδ₀ : 0 < δ₀ := by positivity
  set σ : ℝ := (1 - θ) / 2
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hθσ : θ + σ < 1 := by simp only [σ]; linarith
  have hη₀ : 0 < η₀ := mul_pos hδ₀ hσ
  have hM₁ : 1 ≤ M₁ := le_max_left _ _
  have hNpos : 0 < N := Nat.succ_pos _
  have hlam : 0 < lam := ha.pos
  set F : ℝ := (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R))).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hfF : eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R)) =
      ENNReal.ofReal F := (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
  have hcball_sub {c : EuclideanSpace ℝ ι} (hc : c ∈ closedBall x₀ (θ * R)) :
      closedBall c (σ * R) ⊆ ball x₀ R := fun x hx ↦ by
    rw [mem_closedBall] at hx
    rw [mem_ball]
    calc dist x x₀ ≤ dist x c + dist c x₀ := dist_triangle x c x₀
      _ ≤ (θ + σ) * R := by linarith [mem_closedBall.1 hc]
      _ < 1 * R := by gcongr
      _ = R := one_mul R
  have hη_eq : δ₀ * (σ * R) = η₀ * R := by simp only [η₀, δ₀, σ]; ring
  have hδ1 : δ₀ ≤ 1 := by
    have hsq : 1 ≤ √n := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
    exact inv_le_one_of_one_le₀ (by linarith)
  have hησ : η₀ * R ≤ σ * R := by
    calc η₀ * R = δ₀ * (σ * R) := hη_eq.symm
      _ ≤ 1 * (σ * R) := by gcongr
      _ = σ * R := one_mul _
  have hsmall_at {c : EuclideanSpace ℝ ι} (hc : c ∈ closedBall x₀ (θ * R)) {A : ℝ}
      (hw : ∃ w ∈ ball c (η₀ * R), u w ≤ A) :
      (η₀ * R) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (η₀ * R)))).toReal ≤
      C₁ * (A + R * F / lam) := by
    have hsub := ball_subset_closedBall.trans (hcball_sub hc)
    have h := Hsmall (mul_pos hσ hR) hF (ha.mono_set hsub) hLam
      (hu.continuousOn.mono (hcball_sub hc)) (hu.mono hsub)
      (fun x hx ↦ hnn x (hcball_sub hc hx)) (fun x hx ↦ hsuper x (hsub hx))
      (hfF ▸ eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
      (by rwa [hη_eq])
    rw [hη_eq] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
    have hσR : σ * R ≤ R := mul_le_of_le_one_left hR.le (by simp only [σ]; linarith)
    have : σ * R * F / lam ≤ R * F / lam := by gcongr
    linarith
  -- One step along the chain: if `dist q q' < η₀ R / 2`, Chebyshev point selection on
  -- `B(q', η₀ R / 2) ⊆ B(q, η₀ R)` propagates the bound from `q` to `q'`.
  have hlink {q q' : EuclideanSpace ℝ ι} (hq : q ∈ closedBall x₀ (θ * R))
      (hq' : q' ∈ closedBall x₀ (θ * R)) (hdist : dist q q' < η₀ * R / 2) {B : ℝ}
      (hB : (η₀ * R) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q (η₀ * R)))).toReal ≤ B) :
      (η₀ * R) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q' (η₀ * R)))).toReal ≤
      M₁ * B + C₁ * (R * F / lam) := by
    have hB0 : 0 ≤ B := le_trans (by positivity) hB
    have hsub : ball q' (η₀ * R / 2) ⊆ ball q (η₀ * R) := fun x hx ↦ by
      rw [mem_ball] at hx ⊢
      linarith [dist_triangle x q' q, dist_comm q q']
    have huq_mem : MemLp u (ENNReal.ofReal p) (volume.restrict (ball q (η₀ * R))) :=
      (hu.continuousOn.mono (hcball_sub hq)).memLp_restrict_of_subset_isCompact
        (isCompact_closedBall q (σ * R)) measurableSet_ball
        ((ball_subset_ball hησ).trans ball_subset_closedBall) _
    obtain ⟨w, hw, huw⟩ := volume.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm hp
      (half_pos (mul_pos hη₀ hR)) (huq_mem.mono_measure (Measure.restrict_mono hsub le_rfl))
    have huw_le : u w ≤ K₀ * B := by
      rw [Real.norm_eq_abs, finrank_euclideanSpace] at huw
      have hmono : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q' (η₀ * R / 2)))).toReal ≤
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q (η₀ * R)))).toReal :=
        ENNReal.toReal_mono huq_mem.eLpNorm_ne_top
          (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
      have hrpow : (η₀ * R / 2) ^ (-(n / p)) = 2 ^ (n / p) * (η₀ * R) ^ (-n / p) := by
        rw [Real.div_rpow (mul_pos hη₀ hR).le zero_le_two, Real.rpow_neg zero_le_two,
          div_inv_eq_mul, ← neg_div, mul_comm]
      calc u w ≤ |u w| := le_abs_self _
        _ ≤ (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹) *
              ((η₀ * R / 2) ^ (-(n / p)) *
                (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q' (η₀ * R / 2)))).toReal) :=
            huw
        _ ≤ (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹) *
              (2 ^ (n / p) * ((η₀ * R) ^ (-n / p) *
                (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q (η₀ * R)))).toReal)) := by
            rw [hrpow, mul_assoc (2 ^ (n / p))]
            gcongr
        _ ≤ (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹) * (2 ^ (n / p) * B) := by
            gcongr
        _ = K₀ * B := by simp only [K₀]; ring
    have hw' : w ∈ ball q' (η₀ * R) :=
      ball_subset_ball (half_lt_self (mul_pos hη₀ hR)).le hw
    calc (η₀ * R) ^ (-n / p) *
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q' (η₀ * R)))).toReal
        ≤ C₁ * (K₀ * B + R * F / lam) := hsmall_at hq' ⟨w, hw', huw_le⟩
      _ = C₁ * K₀ * B + C₁ * (R * F / lam) := by ring
      _ ≤ M₁ * B + C₁ * (R * F / lam) := by
          have : C₁ * K₀ ≤ M₁ := le_max_right _ _
          nlinarith
  -- Walk `N` equal steps along `AffineMap.lineMap y z` inside `closedBall x₀ (θ R)`.
  have hy_nn : 0 ≤ u y := hnn y (closedBall_subset_ball (mul_lt_of_lt_one_left hR hθ1) hy)
  set pts : ℕ → EuclideanSpace ℝ ι := fun j ↦ AffineMap.lineMap y z ((j : ℝ) / N)
  have hpts_cb {j : ℕ} (hj : j ≤ N) : pts j ∈ closedBall x₀ (θ * R) :=
    (convex_closedBall x₀ (θ * R)).lineMap_mem hy hz
      ⟨by positivity, (div_le_one (Nat.cast_pos.2 hNpos)).2 (by exact_mod_cast hj)⟩
  have hpts_dist (j : ℕ) : dist (pts j) (pts (j + 1)) < η₀ * R / 2 := by
    have hdyz : dist y z ≤ 2 * θ * R := by
      linarith [mem_closedBall.1 hy, mem_closedBall.1 hz, dist_triangle y x₀ z, dist_comm x₀ z]
    have hNgt : 4 * θ / η₀ < N := by
      simp only [N, Nat.cast_add, Nat.cast_one]
      linarith [Nat.le_ceil (4 * θ / η₀)]
    rw [dist_lineMap_lineMap, Real.dist_eq]
    have hdiff : |(j : ℝ) / N - ((j + 1 : ℕ) : ℝ) / N| = (N : ℝ)⁻¹ := by
      rw [show (j : ℝ) / N - ((j + 1 : ℕ) : ℝ) / N = -(N : ℝ)⁻¹ by push_cast; field_simp; ring,
        abs_neg, abs_of_pos (inv_pos.2 (Nat.cast_pos.2 hNpos))]
    rw [hdiff]
    calc (N : ℝ)⁻¹ * dist y z ≤ (N : ℝ)⁻¹ * (2 * θ * R) := by gcongr
      _ < (4 * θ / η₀)⁻¹ * (2 * θ * R) := by gcongr
      _ = η₀ * R / 2 := by field_simp; ring
  suffices hind : ∀ j ≤ N,
      (η₀ * R) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball (pts j) (η₀ * R)))).toReal ≤
      ((j : ℝ) + 1) * M₁ ^ j * C₁ * (u y + R * F / lam) by
    have hN := hind N le_rfl
    have hptsN : pts N = z := by simp [pts, hNpos.ne']
    rwa [hptsN] at hN
  intro j hj
  induction j with
  | zero =>
    have h0 : pts 0 = y := by simp [pts]
    rw [h0]
    simpa using hsmall_at hy ⟨y, mem_ball_self (mul_pos hη₀ hR), le_rfl⟩
  | succ j ih =>
    have hj' : j ≤ N := Nat.le_of_succ_le hj
    refine (hlink (hpts_cb hj') (hpts_cb hj) (hpts_dist j) (ih hj')).trans ?_
    have hMpow : 1 ≤ M₁ ^ (j + 1) := one_le_pow₀ hM₁
    have hRHS : C₁ * (R * F / lam) ≤ 1 * M₁ ^ (j + 1) * C₁ * (u y + R * F / lam) := by
      calc C₁ * (R * F / lam) ≤ C₁ * (u y + R * F / lam) := by gcongr; linarith
        _ = 1 * (C₁ * (u y + R * F / lam)) := (one_mul _).symm
        _ ≤ M₁ ^ (j + 1) * (C₁ * (u y + R * F / lam)) :=
            mul_le_mul_of_nonneg_right hMpow (by positivity)
        _ = 1 * M₁ ^ (j + 1) * C₁ * (u y + R * F / lam) := by ring
    calc M₁ * (((j : ℝ) + 1) * M₁ ^ j * C₁ * (u y + R * F / lam)) + C₁ * (R * F / lam)
        ≤ M₁ * (((j : ℝ) + 1) * M₁ ^ j * C₁ * (u y + R * F / lam)) +
            1 * M₁ ^ (j + 1) * C₁ * (u y + R * F / lam) := add_le_add_right hRHS _
      _ = (((j + 1 : ℕ) : ℝ) + 1) * M₁ ^ (j + 1) * C₁ * (u y + R * F / lam) := by
          push_cast [pow_succ]
          ring

/-- **The weak Harnack inequality of Krylov and Safonov** (Gilbarg–Trudinger, Theorem 9.22;
Caffarelli–Cabré, Theorem 4.8). Let `κ` be given. There is an exponent `p > 0`, depending only on
the dimension `n` and on `κ`, such that for every `0 < θ < 1` there is a constant `C > 0`,
depending only on `n`, `κ` and `θ`, with the following property. Let `a` be uniformly elliptic on
`B(x₀, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` in `B(x₀, R)` with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there and `f⁺ ∈ Lⁿ(B(x₀, R))`. Then for every `y ∈ B(x₀, θ R)`,

`(θ R)^(-n/p) ‖u‖_{Lᵖ(B(x₀, θ R))} ≤ C (u(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le {κ : ℝ} :
    ∃ p : ℝ, 0 < p ∧ ∀ ⦃θ : ℝ⦄, 0 < θ → θ < 1 →
      ∃ C : ℝ, 0 < C ∧
        ∀ ⦃lam Lam R : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
          ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
          UniformlyEllipticOn (ball x₀ R) a lam Lam → Lam ≤ κ * lam →
          ContDiffOn ℝ 2 u (ball x₀ R) → (∀ x ∈ ball x₀ R, 0 ≤ u x) →
          (∀ x ∈ ball x₀ R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
          MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R)) →
          ∀ y ∈ ball x₀ (θ * R),
            (θ * R) ^ (-(Fintype.card ι : ℝ) / p) *
              (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))).toReal ≤
            C * (u y + R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
              (volume.restrict (ball x₀ R))).toReal / lam) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun θ hθ0 hθ1 ↦
      ⟨1, one_pos, fun lam Lam R x₀ a u f ha _ _ hnn _ _ y hy ↦ ?_⟩⟩
    have hθR : 0 < θ * R := pos_of_mem_ball hy
    have hR : 0 < R := (mul_pos_iff_of_pos_left hθ0).1 hθR
    have hlam : 0 < lam := ha.pos
    have huy : 0 ≤ u y := hnn y (ball_subset_ball (mul_le_of_le_one_left hR.le hθ1.le) hy)
    have hvol : volume (ball x₀ (θ * R)) ≤ 1 := by
      calc volume (ball x₀ (θ * R))
          ≤ volume (WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x₀) 1) :=
            measure_mono fun x _ ↦ by simp [Subsingleton.elim (WithLp.ofLp x) (WithLp.ofLp x₀)]
        _ = ENNReal.ofReal ((2 * 1) ^ Fintype.card ι) := by
            rw [(PiLp.volume_preserving_ofLp ι).measure_preimage
              measurableSet_ball.nullMeasurableSet, Real.volume_pi_ball _ one_pos]
        _ = 1 := by simp
    have hu_le : eLpNorm u (ENNReal.ofReal 1) (volume.restrict (ball x₀ (θ * R))) ≤
        ENNReal.ofReal (u y) := by
      have hmeas : AEStronglyMeasurable u (volume.restrict (ball x₀ (θ * R))) :=
        (continuous_of_discreteTopology : Continuous u).aestronglyMeasurable
      refine (eLpNorm_le_of_ae_bound (p := ENNReal.ofReal 1) hmeas (ae_of_all _ fun x ↦ by
        rw [Subsingleton.elim x y, Real.norm_of_nonneg huy])).trans ?_
      rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal zero_le_one, inv_one,
        ENNReal.rpow_one]
      calc volume (ball x₀ (θ * R)) * ENNReal.ofReal (u y) ≤ 1 * ENNReal.ofReal (u y) := by gcongr
        _ = ENNReal.ofReal (u y) := one_mul _
    have htoReal := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hu_le).trans_eq
      (ENNReal.toReal_ofReal huy)
    have hF : 0 ≤ R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
        (volume.restrict (ball x₀ R))).toReal / lam := by positivity
    simpa [Fintype.card_eq_zero] using htoReal.trans (le_add_of_nonneg_right hF)
  set κ' : ℝ := max κ 1
  have hκ' : 0 < κ' := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨p, C₁, hp, hC₁, Hsmall⟩ :=
    exists_rpow_neg_mul_eLpNorm_ball_le_of_exists_le_small (ι := ι) hκ'
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  set δ₀ : ℝ := (16 * √n)⁻¹
  have hδ₀ : 0 < δ₀ := by positivity
  refine ⟨p, hp, fun θ hθ0 hθ1 ↦ ?_⟩
  set σ : ℝ := (1 - θ) / 2
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hθσ : θ + σ < 1 := by simp only [σ]; linarith
  set η₀ : ℝ := δ₀ * σ
  have hη₀ : 0 < η₀ := mul_pos hδ₀ hσ
  -- Cover the compact unit-scale ball `closedBall 0 θ` by finitely many balls of radius `η₀`.
  obtain ⟨S, hScover⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ ι) θ).elim_finite_subcover
    (fun c : closedBall (0 : EuclideanSpace ℝ ι) θ ↦ ball (c : EuclideanSpace ℝ ι) η₀)
    (fun _ ↦ isOpen_ball)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self hη₀⟩)
  have hS_pos : 0 < (S.card : ℝ) := by
    have h0 : (0 : EuclideanSpace ℝ ι) ∈ ⋃ c ∈ S, ball (c : EuclideanSpace ℝ ι) η₀ :=
      hScover (mem_closedBall_self hθ0.le)
    obtain ⟨c, hcS, -⟩ := mem_iUnion₂.1 h0
    exact Nat.cast_pos.2 (Finset.card_pos.2 ⟨c, hcS⟩)
  -- Constants of the `N`-step ball chain along segments in `closedBall x₀ (θ R)`.
  set K₀ : ℝ := 2 ^ (n / p) * (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹)
  set M₁ : ℝ := max 1 (C₁ * K₀)
  have hM₁ : 1 ≤ M₁ := le_max_left _ _
  set N : ℕ := ⌈4 * θ / η₀⌉₊ + 1
  set C₂ : ℝ := ((N : ℝ) + 1) * M₁ ^ N * C₁
  have hC₂ : 0 < C₂ := by positivity
  refine ⟨(S.card : ℝ) ^ p⁻¹ * (η₀ / θ) ^ (n / p) * C₂, by positivity, ?_⟩
  intro lam Lam R x₀ a u f ha hLam hu hnn hsuper hf y hy
  have hθR : 0 < θ * R := pos_of_mem_ball hy
  have hR : 0 < R := pos_of_mem_ball ((ball_subset_ball (mul_le_of_le_one_left
    ((mul_pos_iff_of_pos_left hθ0).1 hθR).le hθ1.le)) hy)
  have hlam : 0 < lam := ha.pos
  have hLam' : Lam ≤ κ' * lam :=
    hLam.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le)
  set F : ℝ := (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R))).toReal
  have hy_cb : y ∈ closedBall x₀ (θ * R) := ball_subset_closedBall hy
  have hy_nn : 0 ≤ u y := hnn y (ball_subset_ball (mul_le_of_le_one_left hR.le hθ1.le) hy)
  have hδ1 : δ₀ ≤ 1 := by
    have hsq : 1 ≤ √n := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
    exact inv_le_one_of_one_le₀ (by linarith)
  have hησ : η₀ * R ≤ σ * R := by
    calc η₀ * R = δ₀ * (σ * R) := by simp only [η₀]; ring
      _ ≤ 1 * (σ * R) := by gcongr
      _ = σ * R := one_mul _
  -- Cover `B(x₀, θ R)` by the rescaled balls `B_c = B(x₀ + R • c, η₀ R)` for `c ∈ S` and sum
  -- the `p`-th powers of the `Lᵖ` seminorms via `eLpNorm_restrict_biUnion_finset_rpow_le`.
  set Bc : closedBall (0 : EuclideanSpace ℝ ι) θ → Set (EuclideanSpace ℝ ι) :=
    fun c ↦ ball (x₀ + R • (c : EuclideanSpace ℝ ι)) (η₀ * R)
  have hBc_cb (c : closedBall (0 : EuclideanSpace ℝ ι) θ) :
      x₀ + R • (c : EuclideanSpace ℝ ι) ∈ closedBall x₀ (θ * R) := by
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 c.property) hR.le
  have hcoverR : ball x₀ (θ * R) ⊆ ⋃ c ∈ S, Bc c := fun x hx ↦ by
    have hx0 : R⁻¹ • (x - x₀) ∈ closedBall (0 : EuclideanSpace ℝ ι) θ := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
      rw [mem_ball, dist_eq_norm] at hx
      exact (inv_mul_le_iff₀ hR).2 (by linarith)
    obtain ⟨c, hcS, hxc⟩ := mem_iUnion₂.1 (hScover hx0)
    refine mem_iUnion₂.2 ⟨c, hcS, ?_⟩
    rw [mem_ball, dist_eq_norm] at hxc ⊢
    have hrel : x - (x₀ + R • (c : EuclideanSpace ℝ ι)) =
        R • (R⁻¹ • (x - x₀) - (c : EuclideanSpace ℝ ι)) := by
      rw [smul_sub, smul_inv_smul₀ hR.ne']
      abel
    rw [hrel, norm_smul, Real.norm_of_nonneg hR.le, mul_comm]
    exact mul_lt_mul_of_pos_right hxc hR
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  set B_each : ℝ := (η₀ * R) ^ (n / p) * (C₂ * (u y + R * F / lam))
  have hB_each0 : 0 ≤ B_each := by positivity
  have hsum_le : eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ^ p ≤
      ENNReal.ofReal ((S.card : ℝ) * B_each ^ p) := by
    calc eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ^ p
        ≤ eLpNorm u (ENNReal.ofReal p) (volume.restrict (⋃ c ∈ S, Bc c)) ^ p :=
          ENNReal.rpow_le_rpow
            (eLpNorm_mono_measure _ (Measure.restrict_mono hcoverR le_rfl)) hp.le
      _ ≤ ∑ c ∈ S, eLpNorm u (ENNReal.ofReal p) (volume.restrict (Bc c)) ^ p := by
          simpa [ENNReal.toReal_ofReal hp.le] using
            eLpNorm_restrict_biUnion_finset_rpow_le (μ := volume) u hp0 ENNReal.ofReal_ne_top S Bc
      _ ≤ ∑ _c ∈ S, ENNReal.ofReal (B_each ^ p) := by
          refine Finset.sum_le_sum fun c _ ↦ ?_
          have hsub_c : closedBall (x₀ + R • (c : EuclideanSpace ℝ ι)) (σ * R) ⊆ ball x₀ R :=
            fun x hx ↦ by
              rw [mem_closedBall] at hx
              rw [mem_ball]
              calc dist x x₀ ≤ dist x (x₀ + R • (c : EuclideanSpace ℝ ι)) +
                      dist (x₀ + R • (c : EuclideanSpace ℝ ι)) x₀ := dist_triangle _ _ _
                _ ≤ (θ + σ) * R := by linarith [mem_closedBall.1 (hBc_cb c)]
                _ < 1 * R := by gcongr
                _ = R := one_mul R
          have hBc_mem : MemLp u (ENNReal.ofReal p) (volume.restrict (Bc c)) :=
            (hu.continuousOn.mono hsub_c).memLp_restrict_of_subset_isCompact
              (isCompact_closedBall _ (σ * R)) measurableSet_ball
              ((ball_subset_ball hησ).trans ball_subset_closedBall) _
          have hc_est := rpow_neg_mul_eLpNorm_ball_le_of_chain hp hC₁ hθ0 hθ1 hR ha hLam' hu hnn
            hsuper hf Hsmall hy_cb (hBc_cb c)
          have hle_real : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Bc c))).toReal ≤
              B_each := by
            calc (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Bc c))).toReal
                = (η₀ * R) ^ (n / p) * ((η₀ * R) ^ (-n / p) *
                    (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Bc c))).toReal) := by
                  rw [neg_div, Real.rpow_neg (mul_pos hη₀ hR).le]
                  field_simp
              _ ≤ B_each := by
                  simp only [Bc, B_each, C₂, M₁, K₀, N, η₀, δ₀, σ] at hc_est ⊢
                  gcongr
          rw [← ENNReal.ofReal_toReal hBc_mem.eLpNorm_ne_top,
            ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le]
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow ENNReal.toReal_nonneg hle_real hp.le)
      _ = ENNReal.ofReal ((S.card : ℝ) * B_each ^ p) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hnorm_enn : eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ≤
      ENNReal.ofReal ((S.card : ℝ) ^ p⁻¹ * B_each) := by
    calc eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))
        = (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ^ p) ^ p⁻¹ := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal ((S.card : ℝ) * B_each ^ p)) ^ p⁻¹ :=
          ENNReal.rpow_le_rpow hsum_le (inv_nonneg.2 hp.le)
      _ = ENNReal.ofReal ((S.card : ℝ) ^ p⁻¹ * B_each) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp.le),
            Real.mul_rpow hS_pos.le (Real.rpow_nonneg hB_each0 p), ← Real.rpow_mul hB_each0,
            mul_inv_cancel₀ hp.ne', Real.rpow_one]
  have hnorm_le : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))).toReal ≤
      (S.card : ℝ) ^ p⁻¹ * B_each :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm_enn).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  calc (θ * R) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))).toReal
      ≤ (θ * R) ^ (-n / p) * ((S.card : ℝ) ^ p⁻¹ * B_each) := by gcongr
    _ = (S.card : ℝ) ^ p⁻¹ * (η₀ / θ) ^ (n / p) * C₂ * (u y + R * F / lam) := by
        simp only [B_each]
        have hratio : (θ * R) ^ (-n / p) * (η₀ * R) ^ (n / p) = (η₀ / θ) ^ (n / p) := by
          rw [neg_div, Real.rpow_neg hθR.le, ← div_eq_inv_mul,
            ← Real.div_rpow (mul_pos hη₀ hR).le hθR.le, mul_div_mul_right _ _ hR.ne']
        calc (θ * R) ^ (-n / p) * ((S.card : ℝ) ^ p⁻¹ *
              ((η₀ * R) ^ (n / p) * (C₂ * (u y + R * F / lam))))
            = (S.card : ℝ) ^ p⁻¹ * ((θ * R) ^ (-n / p) * (η₀ * R) ^ (n / p)) *
                C₂ * (u y + R * F / lam) := by ring
          _ = _ := by rw [hratio]

end PDE

end TauCeti
