/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.Analysis.Convex.HarnackChain
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Basic.ENNReal.Real
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.LpSeminorm.PosPart
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean
import TauCeti.Topology.Order.OrderClosed

/-!
# The weak Harnack inequality of Krylov and Safonov

Let `a` be uniformly elliptic on a ball `B(x₀, R) ⊆ ℝⁿ`, `n ≥ 1`, with constants `λ ≤ Λ ≤ κ λ`,
and let `u ≥ 0` be a classical supersolution of the non-divergence-form equation,
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(x₀, R)`. For every `0 < θ < 1`, the **weak Harnack inequality** bounds a
small power mean of `u` on `B(x₀, θ R)` by the values of `u` there and the size of `f⁺`: there are
`p > 0` depending only on `n` and `κ`, and `C > 0` depending only on `n`, `κ`, and `θ`, with

`(θ R)^(-n / p) ‖u‖_{Lᵖ(B(x₀, θ R))} ≤ C (u(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`

for every `y ∈ B(x₀, θ R)`
(`TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`). Dividing by
`(θ R)^(n / p) ≈ |B(x₀, θ R)|^(1 / p)`, this says that the `Lᵖ` average of `u` over `B(x₀, θ R)` is
at most a multiple of `inf_{B(x₀, θ R)} u` plus the right-hand-side term. The coefficients need no
regularity, not even measurability, and need not be symmetric.

Together with the local maximum principle
(`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`), which bounds the supremum of a
subsolution by its `Lᵖ` norms for every `p > 0`, it gives the Harnack inequality of Krylov and
Safonov for nonnegative solutions. For the extension to `W^{2,n}` strong supersolutions, see
`TauCeti.Analysis.PDE.Regularity.KrylovSafonov.Sobolev`.

## The argument

Normalise by a level `m > 0` with `u(y) ≤ m` and `R ‖f⁺‖ ≤ ε₀ λ m`. Choose the dyadic scale `2ᵏ`
with `4 · 2ᵏ √n ≤ R < 8 · 2ᵏ √n`, and translate the dyadic cube of level `k` to be centred at `c`
(`TauCeti.PDE.exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul`). Its power decay,
applied to `u / m`, gives `|{u ≥ t} ∩ B(c, R / (16 √n))| ≤ C (t / m)^(-ε) (R / (4 √n))ⁿ` for all
`t > 0`: the point `y ∈ B(c, R / 4)` lies within `2 · 2ᵏ √n` of `c`, and the small ball lies in
the cube. The layer-cake bound `TauCeti.lintegral_rpow_le_of_measure_lt_le_rpow_mul` at the
exponent `p = ε / 2` turns this into `∫ uᵖ ≤ (1 + C) mᵖ (R / (4 √n))ⁿ` over the small ball, and
letting `m` decrease to `u(y) + R ‖f⁺‖ / (ε₀ λ)` gives the small-ball estimate on
`B(c, R / (16 √n))`.

To pass from `B(c, R / (16 √n))` to any concentric ball `B(x₀, θ R)` with `0 < θ < 1`, we chain
the small-ball estimate along segments inside `closedBall x₀ (θ R)` via
`Convex.le_pow_mul_add_mul_of_dist_le_mul` (using Chebyshev point selection
`MeasureTheory.Measure.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm` to pick a pointwise
bound inside each overlapping ball) and cover `closedBall x₀ (θ R)` by finitely many small balls
using `TauCeti.exists_finset_isCover_of_subset_closedBall`.

## Main declarations

* `TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`: **the weak
  Harnack inequality** for classical supersolutions on `B(x₀, θ R)` for arbitrary `0 < θ < 1`.

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
open scoped ENNReal NNReal

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
private theorem exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart {κ : ℝ} (hκ : 0 < κ) :
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

omit [DecidableEq ι] in
/-- For `c ∈ closedBall x₀ (θ R)` with `θ < 1` and `R > 0`, the closed ball of radius
`(1 - θ) / 2 * R` around `c` lies inside `B(x₀, R)`. -/
private theorem closedBall_half_sub_subset_ball {x₀ c : EuclideanSpace ℝ ι} {θ R : ℝ}
    (hθ1 : θ < 1) (hR : 0 < R) (hc : c ∈ closedBall x₀ (θ * R)) :
    closedBall c ((1 - θ) / 2 * R) ⊆ ball x₀ R :=
  closedBall_subset_ball' (by nlinarith [mem_closedBall.1 hc])

omit [DecidableEq ι] in
/-- A `C²` function on `B(x₀, R)` is in `Lᵖ` on each small ball `B(c, η₀ R)` centred in
`closedBall x₀ (θ R)`, where `η₀ = (16 √n)⁻¹ ((1 - θ) / 2)`. -/
private theorem memLp_smallBall_of_contDiffOn [Nonempty ι] {x₀ c : EuclideanSpace ℝ ι}
    {θ R p : ℝ} (hθ1 : θ < 1) (hR : 0 < R) (hc : c ∈ closedBall x₀ (θ * R))
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiffOn ℝ 2 u (ball x₀ R)) :
    MemLp u (ENNReal.ofReal p)
      (volume.restrict (ball c ((16 * √(Fintype.card ι))⁻¹ * ((1 - θ) / 2) * R))) := by
  have hsq : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have hδ1 : (16 * √(Fintype.card ι : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hσR : 0 ≤ (1 - θ) / 2 * R := mul_nonneg (by linarith) hR.le
  exact (hu.continuousOn.mono
      (closedBall_half_sub_subset_ball hθ1 hR hc)).memLp_restrict_of_subset_isCompact
    (isCompact_closedBall _ _) measurableSet_ball
    ((ball_subset_ball (by rw [mul_assoc]; exact mul_le_of_le_one_left hσR hδ1)).trans
      ball_subset_closedBall) _

/-- **Propagation of the small-ball `Lᵖ` bound along a segment chain.** Given the small-ball
point-to-`Lᵖ` estimate `Hsmall` on balls of radius `(1 - θ) R / 2` inside `B(x₀, R)` and a
nonnegative `C²` supersolution `u` of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(x₀, R)`, applying
`Convex.le_pow_mul_add_mul_of_dist_le_mul` along the segment from `z` to `y` in
`closedBall x₀ (θ R)` bounds `(η₀ R)^(-n/p) ‖u‖_{Lᵖ(B(z, η₀ R))}` by
`C₂ (u(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`, where `η₀ = (16 √n)⁻¹ (1 - θ) / 2` and `C₂ > 0` depends
only on `p, C₁, θ`, and the dimension. -/
private theorem exists_rpow_neg_mul_eLpNorm_ball_le_of_chain [Nonempty ι] {p C₁ κ θ : ℝ}
    (hp : 0 < p) (hC₁ : 0 < C₁) (hθ0 : 0 < θ) (hθ1 : θ < 1)
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
      C₁ * (A + ρ * F / lam)) :
    let n : ℝ := (Fintype.card ι : ℝ)
    let η₀ : ℝ := (16 * √n)⁻¹ * ((1 - θ) / 2)
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃x₀ y z : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        0 < R → UniformlyEllipticOn (ball x₀ R) a lam Lam → Lam ≤ κ * lam →
        ContDiffOn ℝ 2 u (ball x₀ R) → (∀ x ∈ ball x₀ R, 0 ≤ u x) →
        (∀ x ∈ ball x₀ R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R)) →
        y ∈ closedBall x₀ (θ * R) → z ∈ closedBall x₀ (θ * R) →
        (η₀ * R) ^ (-n / p) *
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball z (η₀ * R)))).toReal ≤
        C₂ * (u y + R * (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball x₀ R))).toReal / lam) := by
  intro n η₀
  set K₀ : ℝ := 2 ^ (n / p) * (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹)
  set M₁ : ℝ := max 1 (C₁ * K₀)
  set N : ℕ := ⌈8 * θ / η₀⌉₊
  refine ⟨((N : ℝ) + 1) * M₁ ^ N * C₁, by positivity, ?_⟩
  intro lam Lam R x₀ y z a u f hR ha hLam hu hnn hsuper hf hy hz
  set δ₀ : ℝ := (16 * √n)⁻¹
  set σ : ℝ := (1 - θ) / 2
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hη₀ : 0 < η₀ := by positivity
  have hη_eq : δ₀ * (σ * R) = η₀ * R := by simp only [η₀, δ₀, σ]; ring
  have hM₁ : 1 ≤ M₁ := le_max_left _ _
  have hlam : 0 < lam := ha.pos
  set F : ℝ := (eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R))).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hfF : eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball x₀ R)) =
      ENNReal.ofReal F := (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
  set g : EuclideanSpace ℝ ι → ℝ := fun q ↦ (η₀ * R) ^ (-n / p) *
    (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball q (η₀ * R)))).toReal
  have hsmall_at {c : EuclideanSpace ℝ ι} (hc : c ∈ closedBall x₀ (θ * R)) {A : ℝ}
      (hw : ∃ w ∈ ball c (η₀ * R), u w ≤ A) :
      g c ≤ C₁ * (A + R * F / lam) := by
    have hcb := closedBall_half_sub_subset_ball hθ1 hR hc
    have hsub := ball_subset_closedBall.trans hcb
    have h := Hsmall (mul_pos hσ hR) hF (ha.mono_set hsub) hLam
      (hu.continuousOn.mono hcb) (hu.mono hsub)
      (fun x hx ↦ hnn x (hcb hx)) (fun x hx ↦ hsuper x (hsub hx))
      (hfF ▸ eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
      (by rwa [hη_eq])
    rw [hη_eq] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
    have hσR : σ * R ≤ R := mul_le_of_le_one_left hR.le (by simp only [σ]; linarith)
    have : σ * R * F / lam ≤ R * F / lam := by gcongr
    linarith
  -- One step along the chain: if `dist q' q ≤ η₀ R / 4`, Chebyshev point selection on
  -- `B(q', η₀ R / 2) ⊆ B(q, η₀ R)` propagates the `Lᵖ` bound from `q` to `q'`.
  have hlink : ∀ q' ∈ closedBall x₀ (θ * R), ∀ q ∈ closedBall x₀ (θ * R),
      dist q' q ≤ η₀ * R / 4 → g q' ≤ M₁ * (g q + C₁ * (R * F / lam)) := by
    intro q' hq' q hq hdist
    have hsub : ball q' (η₀ * R / 2) ⊆ ball q (η₀ * R) := fun x hx ↦ by
      rw [mem_ball] at hx ⊢
      linarith [dist_triangle x q' q, mul_pos hη₀ hR]
    have huq_mem : MemLp u (ENNReal.ofReal p) (volume.restrict (ball q (η₀ * R))) :=
      memLp_smallBall_of_contDiffOn hθ1 hR hq hu
    obtain ⟨w, hw, huw⟩ := volume.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm hp
      (half_pos (mul_pos hη₀ hR)) (huq_mem.mono_measure (Measure.restrict_mono hsub le_rfl))
    have huw_le : u w ≤ K₀ * g q := by
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
        _ ≤ (volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) ^ (-p⁻¹) * (2 ^ (n / p) * g q) := by
            rw [hrpow, mul_assoc (2 ^ (n / p))]
            dsimp only [g]
            gcongr
        _ = K₀ * g q := by simp only [K₀]; ring
    have hw' : w ∈ ball q' (η₀ * R) :=
      ball_subset_ball (half_lt_self (mul_pos hη₀ hR)).le hw
    calc g q' ≤ C₁ * (K₀ * g q + R * F / lam) := hsmall_at hq' ⟨w, hw', huw_le⟩
      _ = C₁ * K₀ * g q + 1 * (C₁ * (R * F / lam)) := by ring
      _ ≤ M₁ * g q + M₁ * (C₁ * (R * F / lam)) := by
          have : 0 ≤ g q := by positivity
          have : C₁ * K₀ ≤ M₁ := le_max_right _ _
          gcongr
      _ = M₁ * (g q + C₁ * (R * F / lam)) := by ring
  -- Chain along the segment from `z` to `y` in `closedBall x₀ (θ R)`.
  have hzy : dist z y ≤ (N : ℝ) * (η₀ * R / 4) := by
    have h1 : dist z y ≤ 2 * θ * R := by
      linarith [mem_closedBall.1 hz, mem_closedBall.1 hy, dist_triangle z x₀ y, dist_comm x₀ y]
    have h2 : 2 * θ * R = (8 * θ / η₀) * (η₀ * R / 4) := by field_simp; ring
    exact h1.trans (h2 ▸ mul_le_mul_of_nonneg_right (Nat.le_ceil (8 * θ / η₀)) (by positivity))
  have hchain := (convex_closedBall x₀ (θ * R)).le_pow_mul_add_mul_of_dist_le_mul hM₁
    (by positivity) hlink N hz hy hzy
  have hy_nn : 0 ≤ u y := hnn y (closedBall_subset_ball (mul_lt_of_lt_one_left hR hθ1) hy)
  have hy_est : g y ≤ C₁ * (u y + R * F / lam) :=
    hsmall_at hy ⟨y, mem_ball_self (mul_pos hη₀ hR), le_rfl⟩
  have hK_le : C₁ * (R * F / lam) ≤ C₁ * (u y + R * F / lam) := by gcongr; linarith
  calc g z ≤ M₁ ^ N * (g y + (N : ℝ) * (C₁ * (R * F / lam))) := hchain
    _ ≤ M₁ ^ N * (C₁ * (u y + R * F / lam) + (N : ℝ) * (C₁ * (u y + R * F / lam))) := by
        gcongr
    _ = ((N : ℝ) + 1) * M₁ ^ N * C₁ * (u y + R * F / lam) := by ring

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
  have : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨p, hp, fun θ hθ0 hθ1 ↦ ?_⟩
  set η₀ : ℝ := (16 * √n)⁻¹ * ((1 - θ) / 2)
  have hη₀ : 0 < η₀ := by positivity
  obtain ⟨C₂, hC₂, Hchain⟩ := exists_rpow_neg_mul_eLpNorm_ball_le_of_chain hp hC₁ hθ0 hθ1 Hsmall
  set M₀ : ℝ := (1 + 4 * θ / η₀) ^ Fintype.card ι
  have hM₀ : 0 < M₀ := by positivity
  refine ⟨M₀ ^ p⁻¹ * (η₀ / θ) ^ (n / p) * C₂, by positivity, ?_⟩
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
  -- Cover `closedBall x₀ (θ R)` by at most `M₀` balls of radius `η₀ R / 2` centred in
  -- `closedBall x₀ (θ R)`, then pass to `B(c, η₀ R)` and sum the `p`-th powers.
  set ε : ℝ≥0 := ⟨η₀ * R / 2, by positivity⟩
  have hε0 : ε ≠ 0 := mt (congrArg NNReal.toReal) (half_pos (mul_pos hη₀ hR)).ne'
  obtain ⟨S, hSsub, hScov, hScard⟩ := exists_finset_isCover_of_subset_closedBall
    (r := ⟨θ * R, hθR.le⟩) hε0 (Subset.rfl : closedBall x₀ (θ * R) ⊆ _)
  have hS_le : (S.card : ℝ) ≤ M₀ := by
    refine hScard.trans_eq ?_
    rw [finrank_euclideanSpace]
    congr 1
    change 1 + 2 * (θ * R) / (η₀ * R / 2) = 1 + 4 * θ / η₀
    field_simp
    ring
  have hcoverR : ball x₀ (θ * R) ⊆ ⋃ c ∈ S, ball c (η₀ * R) :=
    ball_subset_closedBall.trans <| hScov.subset_iUnion_closedBall.trans <|
      iUnion₂_mono fun _ _ ↦ closedBall_subset_ball (half_lt_self (mul_pos hη₀ hR))
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  set B_each : ℝ := (η₀ * R) ^ (n / p) * (C₂ * (u y + R * F / lam))
  have hB_each0 : 0 ≤ B_each := by positivity
  have hsum_le : eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ^ p ≤
      ENNReal.ofReal ((S.card : ℝ) * B_each ^ p) := by
    calc eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ^ p
        ≤ eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (⋃ c ∈ S, ball c (η₀ * R))) ^ p :=
          ENNReal.rpow_le_rpow
            (eLpNorm_mono_measure _ (Measure.restrict_mono hcoverR le_rfl)) hp.le
      _ ≤ ∑ c ∈ S, eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (η₀ * R))) ^ p := by
          simpa [ENNReal.toReal_ofReal hp.le] using
            eLpNorm_restrict_biUnion_finset_rpow_le (μ := volume) u hp0 ENNReal.ofReal_ne_top S
              fun c ↦ ball c (η₀ * R)
      _ ≤ ∑ _c ∈ S, ENNReal.ofReal (B_each ^ p) := by
          refine Finset.sum_le_sum fun c hc ↦ ?_
          have hBc_mem : MemLp u (ENNReal.ofReal p) (volume.restrict (ball c (η₀ * R))) :=
            memLp_smallBall_of_contDiffOn hθ1 hR (hSsub hc) hu
          have hc_est := Hchain hR ha hLam' hu hnn hsuper hf hy_cb (hSsub hc)
          have hle_real :
              (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (η₀ * R)))).toReal ≤
                B_each := by
            calc (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (η₀ * R)))).toReal
                = (η₀ * R) ^ (n / p) * ((η₀ * R) ^ (-n / p) *
                    (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c (η₀ * R)))).toReal) := by
                  rw [neg_div, Real.rpow_neg (mul_pos hη₀ hR).le]
                  field_simp
              _ ≤ B_each := by
                  dsimp only [B_each]
                  gcongr
          rw [← ENNReal.ofReal_toReal hBc_mem.eLpNorm_ne_top,
            ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le]
          exact ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow ENNReal.toReal_nonneg hle_real hp.le)
      _ = ENNReal.ofReal ((S.card : ℝ) * B_each ^ p) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hnorm_enn : eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ≤
      ENNReal.ofReal (M₀ ^ p⁻¹ * B_each) := by
    calc eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))
        = (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R))) ^ p) ^ p⁻¹ := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal ((S.card : ℝ) * B_each ^ p)) ^ p⁻¹ :=
          ENNReal.rpow_le_rpow hsum_le (inv_nonneg.2 hp.le)
      _ ≤ (ENNReal.ofReal (M₀ * B_each ^ p)) ^ p⁻¹ := by
          gcongr
      _ = ENNReal.ofReal (M₀ ^ p⁻¹ * B_each) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp.le),
            Real.mul_rpow hM₀.le (Real.rpow_nonneg hB_each0 p), ← Real.rpow_mul hB_each0,
            mul_inv_cancel₀ hp.ne', Real.rpow_one]
  have hnorm_le : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))).toReal ≤
      M₀ ^ p⁻¹ * B_each :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm_enn).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  calc (θ * R) ^ (-n / p) *
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ (θ * R)))).toReal
      ≤ (θ * R) ^ (-n / p) * (M₀ ^ p⁻¹ * B_each) := by gcongr
    _ = M₀ ^ p⁻¹ * (η₀ / θ) ^ (n / p) * C₂ * (u y + R * F / lam) := by
        simp only [B_each]
        have hratio : (θ * R) ^ (-n / p) * (η₀ * R) ^ (n / p) = (η₀ / θ) ^ (n / p) := by
          rw [neg_div, Real.rpow_neg hθR.le, ← div_eq_inv_mul,
            ← Real.div_rpow (mul_pos hη₀ hR).le hθR.le, mul_div_mul_right _ _ hR.ne']
        calc (θ * R) ^ (-n / p) * (M₀ ^ p⁻¹ *
              ((η₀ * R) ^ (n / p) * (C₂ * (u y + R * F / lam))))
            = M₀ ^ p⁻¹ * ((θ * R) ^ (-n / p) * (η₀ * R) ^ (n / p)) *
                C₂ * (u y + R * F / lam) := by ring
          _ = _ := by rw [hratio]

end PDE

end TauCeti
