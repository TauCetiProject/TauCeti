/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp
import TauCeti.MeasureTheory.Function.LpSeminorm.PosPart
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# The weak Harnack and Harnack inequalities of Krylov and Safonov

Let the coefficient matrix `a` be uniformly elliptic on a ball in `ℝⁿ`, `n ≥ 1`, with constants
`λ ≤ Λ ≤ κ λ`. This file proves the **weak Harnack inequality** and the **Harnack inequality** of
Krylov and Safonov (Gilbarg–Trudinger, Theorem 9.22) for classical supersolutions and solutions of
second-order equations in non-divergence form without lower-order terms. No regularity, symmetry or
measurability of the coefficients is used.

* **Weak Harnack inequality.** There is an exponent `p > 0`, depending only on `n` and `κ`, such
  that for every `0 < θ < 1` there is a constant `C > 0`, depending only on `n`, `κ` and `θ`,
  with the following property: if `u ≥ 0` is `C²` in `B(x₀, R)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there
  and `f⁺ ∈ Lⁿ(B(x₀, R))`, then

  `(θ R)^(-n/p) ‖u‖_{Lᵖ(B(x₀, θ R))} ≤ C (u(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`

  for every `y ∈ B(x₀, θ R)`
  (`TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`).
* **Harnack inequality.** Combining the weak Harnack inequality at `θ = 3 / 4` on `B(x₀, 2 r)` with
  the local maximum principle (`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`) on the
  balls `B(x, r / 2) ⊆ B(x₀, 3 r / 2)` for `x ∈ B(x₀, r)` shows that if `u ≥ 0` is `C²` in
  `B(x₀, 2 r)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` (or more generally `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`) and
  `f ∈ Lⁿ(B(x₀, 2 r))`, then

  `u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)` for all `x, y ∈ B(x₀, r)`

  (`TauCeti.PDE.exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le`,
  `TauCeti.PDE.exists_le_mul_add_of_sum_mul_fderiv_fderiv_eq`), with `C > 0` depending only on `n`
  and `κ`.

## The argument for the weak Harnack inequality

1. **From a point bound to a small-ball `Lᵖ` bound.** On a closed ball `closedBall c ρ` inside
   `B(x₀, R)`, choose the dyadic level `k` with `4 · 2ᵏ √n ≤ ρ < 8 · 2ᵏ √n`
   (`TauCeti.exists_two_zpow_mul_sqrt_card_le_and_lt`) and translate `dyadicCube k 0` to share the
   centre `c`. With `δ₀ = (16 √n)⁻¹`, the ball `B(c, δ₀ ρ)` has radius below `2ᵏ / 2` and so lies
   in the translated cube (`TauCeti.ball_subset_preimage_ofLp_dyadicCube`). If `u ≤ A` somewhere in
   `B(c, δ₀ ρ)`, rescaling `u` by `A + ρ ‖f⁺‖_{Lⁿ} / (ε₀ λ) + ζ` puts it into the regime of the
   Krylov–Safonov power decay
   (`TauCeti.PDE.exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul`), and integrating
   the superlevel decay at exponent `p = ε / 2`
   (`MeasureTheory.Measure.eLpNorm_le_of_meas_lt_rpow_mul`) bounds
   `(δ₀ ρ)^(-n/p) ‖u‖_{Lᵖ(B(c, δ₀ ρ))}` by a multiple of `A + ρ ‖f⁺‖_{Lⁿ} / λ`.
2. **Propagation along a chain of balls.** Set `σ = (1 - θ) / 2` and `η₀ = δ₀ σ`, so that
   `closedBall c (σ R) ⊆ B(x₀, R)` for every `c ∈ closedBall x₀ (θ R)`. If `z, z'` in
   `closedBall x₀ (θ R)` satisfy `dist z z' < η₀ R / 2`, then `B(z', η₀ R / 2) ⊆ B(z, η₀ R)`, so an
   `Lᵖ` bound on `B(z, η₀ R)` forces a point in `B(z', η₀ R / 2)` where `u` is controlled
   (`MeasureTheory.Measure.exists_mem_ball_norm_le_rpow_neg_mul_toReal_eLpNorm`), and Step 1
   propagates the `Lᵖ` bound to `B(z', η₀ R)`. Walking a fixed number `⌈4 θ / η₀⌉₊ + 1` of equal
   steps along the segment from `y` to `z` transfers the bound from any `y ∈ closedBall x₀ (θ R)`
   to every `z ∈ closedBall x₀ (θ R)`.
3. **Finite covering.** Cover the compact unit-scale ball `closedBall 0 θ` once by finitely many
   balls of radius `η₀`, rescale the cover to `closedBall x₀ (θ R)`, and sum the `p`-th powers of
   the `Lᵖ` seminorms (`MeasureTheory.eLpNorm_restrict_biUnion_finset_rpow_le`).

## Main declarations

* `TauCeti.PDE.exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le`: **the weak
  Harnack inequality** for classical supersolutions.
* `TauCeti.PDE.exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le`: **the Harnack inequality** for
  classical functions satisfying `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_le_mul_add_of_sum_mul_fderiv_fderiv_eq`: **the Harnack inequality** for
  classical solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`.

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

open Metric MeasureTheory Module Set
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Small-ball `Lᵖ` bound from a point bound.** Let `δ₀ = (16 √n)⁻¹`. There are `p > 0` and
`C₁ > 0`, depending only on the dimension `n` and on `κ`, with the following property. Let `a` be
uniformly elliptic on `B(c, ρ)` with `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be continuous on
`closedBall c ρ` and `C²` in `B(c, ρ)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` there and
`‖f⁺‖_{Lⁿ(B(c, ρ))} ≤ F`, `F ≥ 0`. If `u ≤ A` at some point of `B(c, δ₀ ρ)`, then

`(δ₀ ρ)^(-n/p) ‖u‖_{Lᵖ(B(c, δ₀ ρ))} ≤ C₁ (A + ρ F / λ)`. -/
private theorem exists_rpow_neg_mul_eLpNorm_ball_le_of_exists_le {κ : ℝ} (hκ : 0 < κ) :
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
  obtain ⟨C₀, ε, ε₀, hC₀, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_comp_add_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hsq : 1 ≤ √n := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  set p : ℝ := ε / 2
  have hp : 0 < p := half_pos hε
  have hpε : p < ε := half_lt_self hε
  set K₁ : ℝ := 4 ^ (n / p) * (1 + C₀ * p / (ε - p)) ^ p⁻¹
  have hK₁ : 0 < K₁ := by
    have : 0 ≤ C₀ * p / (ε - p) := div_nonneg (by positivity) (sub_pos.2 hpε).le
    positivity
  refine ⟨p, K₁ * max 1 ε₀⁻¹, hp, by positivity, ?_⟩
  intro lam Lam ρ A F c a u f hρ hF ha hLam hcont hu hnn hsuper hf ⟨w, hw, huw⟩
  have hlam : 0 < lam := ha.pos
  set δ₀ : ℝ := (16 * √n)⁻¹
  have hδ₀ : 0 < δ₀ := by positivity
  set r₀ : ℝ := δ₀ * ρ
  have hr₀ : 0 < r₀ := mul_pos hδ₀ hρ
  have h4r₀ : 4 * r₀ = ρ / (4 * √n) := by
    simp only [r₀, δ₀]
    field_simp
    ring
  -- Pick `k : ℤ` with `4 · 2ᵏ √n ≤ ρ < 8 · 2ᵏ √n`, so `r₀ < 2ᵏ / 2` and `2ᵏ ≤ 4 r₀`.
  obtain ⟨k, hR4, hk4⟩ :=
    exists_two_zpow_mul_sqrt_card_le_and_lt (ι := ι) (r := ρ / 4) (by positivity)
  have h2k : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hR_le : 4 * 2 ^ k * √n ≤ ρ := by linarith
  have hk_le : (2 : ℝ) ^ k ≤ 4 * r₀ := by
    rw [h4r₀, le_div_iff₀ (by positivity)]
    linarith
  have hr₀_lt : r₀ < 2 ^ k / 2 := by
    calc r₀ = (16 * √n)⁻¹ * ρ := rfl
      _ < (16 * √n)⁻¹ * (8 * 2 ^ k * √n) := by gcongr; linarith
      _ = 2 ^ k / 2 := by field_simp; ring
  have hwρ : w ∈ closedBall c ρ :=
    ball_subset_closedBall (ball_subset_ball (lt_of_lt_of_le hr₀_lt (by nlinarith)).le hw)
  have hA0 : 0 ≤ A := (hnn w hwρ).trans huw
  -- Translate `dyadicCube k 0` to have centre `c`.
  set c₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ 2⁻¹ * 2 ^ k
  set d : EuclideanSpace ℝ ι := c - c₀
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' dyadicCube k 0
  have hQm : MeasurableSet Q := measurableSet_preimage_ofLp_dyadicCube k 0
  have hQvol : volume Q = ENNReal.ofReal ((2 ^ k) ^ Fintype.card ι) :=
    volume_preimage_ofLp_dyadicCube k 0
  have hc₀_eq : c₀ = WithLp.toLp 2 fun i : ι ↦ (((0 : ι → ℤ) i : ℝ) + 2⁻¹) * 2 ^ k := by
    simp [c₀]
  have hballQ : ball c₀ r₀ ⊆ Q :=
    (ball_subset_ball hr₀_lt.le).trans (hc₀_eq ▸ ball_subset_preimage_ofLp_dyadicCube k 0)
  have hQd : MapsTo (· + d) Q (closedBall c ρ) :=
    (hc₀_eq ▸ preimage_ofLp_dyadicCube_subset_ball k 0).trans
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by nlinarith))).trans
        (by simp [d] : closedBall c₀ ρ ⊆ (· + d) ⁻¹' closedBall c ρ))
  have hpre : (· + d) ⁻¹' ball c r₀ = ball c₀ r₀ := by simp [d]
  -- Rescale `u` by `s = A + ρ F / (ε₀ λ) + ζ` for arbitrary `ζ > 0`, then let `ζ → 0`.
  suffices hstep : r₀ ^ (-n / p) *
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c r₀))).toReal ≤
        K₁ * (A + ρ * F / (ε₀ * lam)) by
    refine hstep.trans ?_
    rw [mul_assoc K₁]
    gcongr K₁ * ?_
    have h1 : A ≤ max 1 ε₀⁻¹ * A := le_mul_of_one_le_left hA0 (le_max_left _ _)
    have h2 : ρ * F / (ε₀ * lam) ≤ max 1 ε₀⁻¹ * (ρ * F / lam) := by
      have : ρ * F / (ε₀ * lam) = ε₀⁻¹ * (ρ * F / lam) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    linarith
  refine le_of_forall_pos_le_add fun ζ hζ ↦ ?_
  set s : ℝ := A + ρ * F / (ε₀ * lam) + ζ / K₁
  have hs : 0 < s := by positivity
  set v : EuclideanSpace ℝ ι → ℝ := fun x ↦ s⁻¹ * u x
  set g : EuclideanSpace ℝ ι → ℝ := fun x ↦ s⁻¹ * f x
  have hgR : ENNReal.ofReal ρ * eLpNorm (fun x ↦ (g x)⁺) (Fintype.card ι)
      (volume.restrict (ball c ρ)) ≤ ENNReal.ofReal (ε₀ * lam) :=
    ofReal_mul_eLpNorm_posPart_inv_mul_le hρ.le hs hf <| by
      have hle : ρ * F / (ε₀ * lam) ≤ s := by
        simp only [s]
        linarith [div_pos hζ hK₁]
      rw [mul_comm (ε₀ * lam)]
      exact (div_le_iff₀ (by positivity)).1 hle
  have hw2k : w ∈ ball c (2 * 2 ^ k * √n) :=
    ball_subset_ball (hr₀_lt.le.trans (by nlinarith)) hw
  have hvw : v w ≤ 1 := by
    simp only [v]
    rw [inv_mul_le_iff₀ hs, mul_one]
    have h1 : 0 ≤ ρ * F / (ε₀ * lam) := by positivity
    have h2 : 0 < ζ / K₁ := div_pos hζ hK₁
    exact huw.trans (by simp only [s]; linarith)
  have hdec := H (u := v) (f := g) hR_le ha hLam (continuousOn_const.mul hcont)
    (contDiffOn_const.mul hu) (fun x hx ↦ mul_nonneg (by positivity) (hnn x hx))
    (fun x hx ↦ by
      simp only [v, g]
      rw [sum_mul_fderiv_fderiv_const_mul]
      exact mul_le_mul_of_nonneg_left (hsuper x hx) (by positivity))
    hgR ⟨w, hw2k, hvw⟩
  -- Integrate the superlevel bound on `Q` via `Measure.eLpNorm_le_of_meas_lt_rpow_mul`.
  have hvQ_meas : AEStronglyMeasurable (fun x ↦ v (x + d)) (volume.restrict Q) :=
    ((continuousOn_const.mul hcont).comp (continuous_id.add continuous_const).continuousOn
      hQd).aestronglyMeasurable hQm
  have hvQ_nn : 0 ≤ᵐ[volume.restrict Q] fun x ↦ v (x + d) :=
    (ae_restrict_mem hQm).mono fun x hx ↦ mul_nonneg (by positivity) (hnn _ (hQd hx))
  have hvQ_lp := (volume.restrict Q).eLpNorm_le_of_meas_lt_rpow_mul hvQ_meas hvQ_nn hp hpε
    (V := volume Q) (by rw [Measure.restrict_apply_univ]) fun t ht ↦ by
      rw [Measure.restrict_apply' hQm]
      refine (measure_mono fun x hx ↦ ?_).trans (hdec (zero_lt_one.trans ht))
      exact ⟨Set.mem_ofPred.2 (le_of_lt (Set.mem_ofPred.1 hx.1)), hx.2⟩
  -- Pull the `Lᵖ` bound from `Q` to `B(c₀, r₀)` and translate by `d` to `B(c, r₀)`.
  have hvd : eLpNorm (v ∘ (· + d)) (ENNReal.ofReal p) (volume.restrict (ball c₀ r₀)) =
      eLpNorm v (ENNReal.ofReal p) (volume.restrict (ball c r₀)) :=
    hpre ▸ (measurePreserving_add_right volume d).eLpNorm_comp_restrict_preimage
      (measurableEmbedding_addRight d) v _ _
  have hcp_nn : 0 ≤ C₀ * p / (ε - p) := div_nonneg (by positivity) (sub_pos.2 hpε).le
  have h1cp : (1 + ENNReal.ofReal (C₀ * p / (ε - p))) ^ p⁻¹ =
      ENNReal.ofReal ((1 + C₀ * p / (ε - p)) ^ p⁻¹) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hcp_nn,
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (inv_nonneg.2 hp.le)]
  have hv_le : eLpNorm v (ENNReal.ofReal p) (volume.restrict (ball c r₀)) ≤
      ENNReal.ofReal (K₁ * r₀ ^ (n / p)) := by
    calc eLpNorm v (ENNReal.ofReal p) (volume.restrict (ball c r₀))
        = eLpNorm (fun x ↦ v (x + d)) (ENNReal.ofReal p) (volume.restrict (ball c₀ r₀)) :=
          hvd.symm
      _ ≤ eLpNorm (fun x ↦ v (x + d)) (ENNReal.ofReal p) (volume.restrict Q) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hballQ le_rfl)
      _ ≤ ENNReal.ofReal ((1 + C₀ * p / (ε - p)) ^ p⁻¹) * volume Q ^ p⁻¹ := h1cp ▸ hvQ_lp
      _ ≤ ENNReal.ofReal ((1 + C₀ * p / (ε - p)) ^ p⁻¹) *
            ENNReal.ofReal (((4 * r₀) ^ Fintype.card ι) ^ p⁻¹) := by
          gcongr
          rw [hQvol, ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp.le)]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity)
            (pow_le_pow_left₀ h2k.le hk_le _) (inv_nonneg.2 hp.le))
      _ = ENNReal.ofReal (K₁ * r₀ ^ (n / p)) := by
          have hcpos : 0 ≤ (1 + C₀ * p / (ε - p)) ^ p⁻¹ := by positivity
          rw [← ENNReal.ofReal_mul hcpos]
          congr 1
          rw [← Real.rpow_natCast (4 * r₀), ← Real.rpow_mul (by positivity),
            Real.mul_rpow (by norm_num) hr₀.le, ← div_eq_mul_inv]
          simp only [K₁, n]
          ring
  have hvu : eLpNorm v (ENNReal.ofReal p) (volume.restrict (ball c r₀)) =
      ENNReal.ofReal s⁻¹ * eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c r₀)) := by
    have : v = s⁻¹ • u := rfl
    rw [this, eLpNorm_const_smul, Real.eNorm_eq_ofReal (by positivity)]
  rw [hvu] at hv_le
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv_le
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hu_le : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c r₀))).toReal ≤
      s * (K₁ * r₀ ^ (n / p)) := by
    rwa [inv_mul_le_iff₀ hs] at hreal
  calc r₀ ^ (-n / p) * (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c r₀))).toReal
      ≤ r₀ ^ (-n / p) * (s * (K₁ * r₀ ^ (n / p))) := by gcongr
    _ = K₁ * s := by
        rw [neg_div, Real.rpow_neg hr₀.le]
        field_simp
    _ = K₁ * (A + ρ * F / (ε₀ * lam)) + ζ := by
        simp only [s]
        field_simp

/-- **Propagation of the small-ball `Lᵖ` bound along a segment chain.** Given the small-ball
point-to-`Lᵖ` estimate `Hsmall` on balls of radius `σ R = (1 - θ) R / 2` inside `B(x₀, R)` and a
nonnegative `C²` supersolution `u` of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(x₀, R)`, stepping `N` times along
the segment from `y` to any `z ∈ closedBall x₀ (θ R)` bounds `(η₀ R)^(-n/p) ‖u‖_{Lᵖ(B(z, η₀ R))}`
by `((N + 1) M₁^N C₁) (u(y) + R ‖f⁺‖_{Lⁿ(B(x₀, R))} / λ)`, where `η₀ = (16 √n)⁻¹ (1 - θ) / 2`. -/
private theorem rpow_neg_mul_eLpNorm_ball_le_of_chain
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
    rw [mem_closedBall] at hc hx
    rw [mem_ball]
    calc dist x x₀ ≤ dist x c + dist c x₀ := dist_triangle x c x₀
      _ ≤ (θ + σ) * R := by linarith
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
  set κ' : ℝ := max κ 1
  have hκ' : 0 < κ' := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨p, C₁, hp, hC₁, Hsmall⟩ := exists_rpow_neg_mul_eLpNorm_ball_le_of_exists_le (ι := ι) hκ'
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
    exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 c.2) hR.le
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

/-- **The Harnack inequality of Krylov and Safonov** (Gilbarg–Trudinger, Theorem 9.22;
Caffarelli–Cabré, Corollary 4.9), for classical functions satisfying the two-sided inequality
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`. Let `κ` be given. There is a constant `C > 0`, depending only on the
dimension `n` and on `κ`, with the following property. Let `a` be uniformly elliptic on
`B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` in `B(x₀, 2 r)` with
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` there and `f ∈ Lⁿ(B(x₀, 2 r))`. Then for all `x, y ∈ B(x₀, r)`,

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le {κ : ℝ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContDiffOn ℝ 2 u (ball x₀ (2 * r)) → (∀ x ∈ ball x₀ (2 * r), 0 ≤ u x) →
        (∀ x ∈ ball x₀ (2 * r), |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
          u x ≤ C * (u y + r * (eLpNorm f (Fintype.card ι)
            (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨p, hp, HW'⟩ :=
    exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
  obtain ⟨C_W, hCW, HW⟩ := HW' (θ := 3 / 4) (by norm_num) (by norm_num)
  obtain ⟨C_M, hCM, HM⟩ := exists_le_mul_rpow_mul_eLpNorm_posPart_add (ι := ι) (κ := κ) hp
  set n : ℝ := (Fintype.card ι : ℝ)
  refine ⟨C_M * (2 * 3 ^ (n / p) * C_W + 1), by positivity, ?_⟩
  intro lam Lam r x₀ a u f ha hLam hu hnn heq hf x hx y hy
  have hr : 0 < r := pos_of_mem_ball hx
  have hlam : 0 < lam := ha.pos
  set F : ℝ := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  -- On `B(x₀, 2 r)` the function `f` is nonnegative (`0 ≤ |∑ ...| ≤ f`), so `f⁺ = f` and
  -- `(-f)⁻ = f`.
  have hf_nn : ∀ z ∈ ball x₀ (2 * r), 0 ≤ f z := fun z hz ↦ (abs_nonneg _).trans (heq z hz)
  have hf_pos : EqOn (fun z ↦ (f z)⁺) f (ball x₀ (2 * r)) :=
    fun z hz ↦ posPart_eq_self.2 (hf_nn z hz)
  have hnf_neg : EqOn (fun z ↦ (-f z)⁻) f (ball x₀ (2 * r)) := fun z hz ↦ by
    dsimp only
    rw [negPart_neg, posPart_eq_self.2 (hf_nn z hz)]
  -- Weak Harnack on `B(x₀, 3 r / 2) = B(x₀, (3 / 4) (2 r))` evaluated at `y ∈ B(x₀, r)`.
  have hy3 : y ∈ ball x₀ ((3 / 4 : ℝ) * (2 * r)) := ball_subset_ball (by linarith) hy
  have hf_pos_ae : (fun z ↦ (f z)⁺) =ᵐ[volume.restrict (ball x₀ (2 * r))] f :=
    (ae_restrict_mem measurableSet_ball).mono hf_pos
  have hw := HW ha hLam hu hnn (fun z hz ↦ (le_abs_self _).trans (heq z hz))
    (hf.ae_eq hf_pos_ae.symm) y hy3
  rw [eLpNorm_congr_ae hf_pos_ae] at hw
  -- Local maximum principle on `B(x, r / 2) ⊆ closedBall x (r / 2) ⊆ B(x₀, 3 r / 2)`.
  have hxcb : closedBall x (r / 2) ⊆ ball x₀ (2 * r) := fun z hz ↦ by
    rw [mem_closedBall] at hz
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle z x x₀]
  have hx3 : ball x (r / 2) ⊆ ball x₀ ((3 / 4 : ℝ) * (2 * r)) := fun z hz ↦ by
    rw [mem_ball] at hx hz ⊢
    linarith [dist_triangle z x x₀]
  have hx2 : ball x (r / 2) ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hxcb
  have hnf_ae : (fun z ↦ (-f z)⁻) =ᵐ[volume.restrict (ball x (r / 2))] f :=
    (ae_restrict_mem measurableSet_ball).mono fun z hz ↦ hnf_neg (hx2 hz)
  have hu_pos_ae : (fun z ↦ (u z)⁺) =ᵐ[volume.restrict (ball x (r / 2))] u :=
    (ae_restrict_mem measurableSet_ball).mono fun z hz ↦ posPart_eq_self.2 (hnn z (hx2 hz))
  have hm := HM (ha.mono_set hx2) hLam (hu.continuousOn.mono hxcb) (hu.mono hx2)
    (f := fun z ↦ -f z) (fun z hz ↦ neg_le.2 ((neg_le_abs _).trans (heq z (hx2 hz))))
    ((hf.mono_measure (Measure.restrict_mono hx2 le_rfl)).ae_eq hnf_ae.symm)
    x (mem_ball_self (by positivity))
  rw [eLpNorm_congr_ae hnf_ae, eLpNorm_congr_ae hu_pos_ae] at hm
  -- Compare `B(x, r / 2)` with `B(x₀, 3 r / 2)` and `B(x₀, 2 r)`.
  have hu3_mem : MemLp u (ENNReal.ofReal p) (volume.restrict (ball x₀ ((3 / 4 : ℝ) * (2 * r)))) :=
    (hu.continuousOn.mono (closedBall_subset_ball (by linarith))).memLp_restrict_of_subset_isCompact
      (isCompact_closedBall x₀ ((3 / 4 : ℝ) * (2 * r))) measurableSet_ball
      ball_subset_closedBall _
  have hu_mono : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x (r / 2)))).toReal ≤
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x₀ ((3 / 4 : ℝ) * (2 * r))))).toReal :=
    ENNReal.toReal_mono hu3_mem.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hx3 le_rfl))
  have hf_mono : (eLpNorm f (Fintype.card ι) (volume.restrict (ball x (r / 2)))).toReal ≤ F :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hx2 le_rfl))
  have hscale : (r / 2) ^ (-n / p) =
      3 ^ (n / p) * ((3 / 4 : ℝ) * (2 * r)) ^ (-n / p) := by
    have heq_r : (3 / 4 : ℝ) * (2 * r) = 3 * (r / 2) := by ring
    have h3 : (3 : ℝ) ^ (n / p) * 3 ^ (-n / p) = 1 := by
      rw [neg_div, Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
    rw [heq_r, Real.mul_rpow (by norm_num) (half_pos hr).le, ← mul_assoc, h3, one_mul]
  have hy_nn : 0 ≤ u y := hnn y (ball_subset_ball (by linarith) hy)
  calc u x ≤ C_M * ((r / 2) ^ (-n / p) *
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball x (r / 2)))).toReal +
          (r / 2) / lam *
            (eLpNorm f (Fintype.card ι) (volume.restrict (ball x (r / 2)))).toReal) := hm
    _ ≤ C_M * (3 ^ (n / p) * (((3 / 4 : ℝ) * (2 * r)) ^ (-n / p) *
          (eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (ball x₀ ((3 / 4 : ℝ) * (2 * r))))).toReal) +
          (r / 2) / lam * F) := by
        rw [hscale, mul_assoc (3 ^ (n / p))]
        gcongr
    _ ≤ C_M * (3 ^ (n / p) * (C_W * (u y + 2 * r * F / lam)) + (r / 2) / lam * F) := by gcongr
    _ ≤ C_M * (2 * 3 ^ (n / p) * C_W + 1) * (u y + r * F / lam) := by
        have hRF : 0 ≤ r * F / lam := by positivity
        have h3p : 0 < (3 : ℝ) ^ (n / p) := by positivity
        have hrew : (r / 2) / lam * F = 2⁻¹ * (r * F / lam) := by ring
        have hrew2 : 2 * r * F / lam = 2 * (r * F / lam) := by ring
        rw [hrew, hrew2]
        nlinarith [mul_nonneg (mul_pos h3p hCW).le hy_nn]

/-- **The Harnack inequality of Krylov and Safonov** (Gilbarg–Trudinger, Theorem 9.22), for
classical solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`. Let `κ` be given. There is a constant `C > 0`,
depending only on the dimension `n` and on `κ`, with the following property. Let `a` be uniformly
elliptic on `B(x₀, 2 r)` with constants `λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` in `B(x₀, 2 r)` with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` there and `f ∈ Lⁿ(B(x₀, 2 r))`. Then for all `x, y ∈ B(x₀, r)`,

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity or measurability, and need not be symmetric. -/
theorem exists_le_mul_add_of_sum_mul_fderiv_fderiv_eq {κ : ℝ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam → Lam ≤ κ * lam →
        ContDiffOn ℝ 2 u (ball x₀ (2 * r)) → (∀ x ∈ ball x₀ (2 * r), 0 ≤ u x) →
        (∀ x ∈ ball x₀ (2 * r), ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
          u x ≤ C * (u y + r * (eLpNorm f (Fintype.card ι)
            (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C, hC, H⟩ := exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
  refine ⟨C, hC, fun lam Lam r x₀ a u f ha hLam hu hnn heq hf x hx y hy ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H ha hLam hu hnn (fun z hz ↦ (heq z hz).symm ▸ (Real.norm_eq_abs _).ge) hf.norm x hx y hy

end PDE

end TauCeti
