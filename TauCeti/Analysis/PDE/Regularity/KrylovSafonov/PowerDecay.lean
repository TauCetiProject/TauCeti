/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.MeasureEstimate
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.KrylovSafonov
import Mathlib.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import TauCeti.Basic.ENNReal.Real
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# Power decay of the superlevel sets of a supersolution

Let `u ≥ 0` be a `C²` supersolution of a non-divergence-form equation
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` with a uniformly elliptic coefficient matrix, `λ ≤ Λ ≤ κ λ`, on a ball
`B(c, R) ⊆ ℝⁿ`, `n ≥ 1`, centred at the centre `c` of a dyadic cube `Q₀` of side `ℓ` and with
`R ≥ 4 ℓ √n`. If `u ≤ 1` somewhere in `B(c, 2 ℓ √n)` and the right-hand side is small,
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, then the superlevel sets of `u` in `Q₀` decay geometrically,

`|{u ≥ Mʲ⁺¹} ∩ Q₀| ≤ δʲ⁺¹ |Q₀|`

(`TauCeti.PDE.exists_volume_setOf_pow_le_inter_dyadicCube_le_pow_mul`), and so as a power of the
level,

`|{u ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`

(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`). The constants `M > 1`,
`0 < δ < 1`, `C`, `ε > 0` and `ε₀ > 0` depend only on the dimension and on `κ`. This is the `L^ε`
estimate of Krylov and Safonov: it says that a nonnegative supersolution which is at most `1`
somewhere is in weak `L^ε` on `Q₀`, with a bound independent of the solution, and it is the step
from the measure estimate to the weak Harnack inequality.

## The argument

The basic measure estimate (`TauCeti.PDE.exists_mul_volume_ball_le_volume_setOf_lt_inter_ball`),
applied on the ball of radius `4 ℓ √n` about the centre of a dyadic cube `Q` of side `ℓ` to the
rescaled function `u / s`, says: if `u ≤ s` somewhere within distance `2 ℓ √n` of the centre of
`Q`, then `u < M s` on a fixed fraction of the ball of radius `ℓ / 2` inside `Q`, so that
`|{u ≥ M s} ∩ Q| ≤ δ |Q|`. Every point of the parent of `Q` lies within distance `2 ℓ √n` of the
centre of `Q`. So if a dyadic subcube `Q` of `Q₀` meets `{u ≥ Mʲ⁺²}` in more than a `δ` fraction
of its volume, then `u > Mʲ⁺¹` on all of its parent. This is the hypothesis of the Krylov–Safonov
covering lemma for the sets `Aⱼ = {u ≥ Mʲ⁺¹} ∩ Q₀`, and its iteration
(`TauCeti.volume_le_pow_mul_volume_dyadicCube`) gives the geometric decay. The rescaling by `s ≥ 1`
only makes the right-hand side smaller, so the smallness of `f` is needed at the scale of `Q₀` only.

## Main declarations

* `TauCeti.PDE.exists_volume_setOf_pow_le_inter_dyadicCube_le_pow_mul`: geometric decay of the
  superlevel sets `{u ≥ Mʲ⁺¹}` in a dyadic cube.
* `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`: the power decay
  `|{u ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|`.

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

open Metric MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The measure estimate on a dyadic cube.** There are constants `M > 1`, `0 < δ < 1` and
`ε₀ > 0`, depending only on the dimension and on `κ`, with the following property. Let `Q` be a
dyadic cube of side `ℓ` with centre `c`, let `u ≥ 0` be a `C²` supersolution on a ball
`B(c₀, R₀) ⊇ B(c, 4 ℓ √n)` with `R₀ ‖f⁺‖_{Lⁿ} ≤ ε₀ λ`, and let `s ≥ 1`. If `u ≤ s` somewhere in
`B(c, 2 ℓ √n)`, then `|{u ≥ M s} ∩ Q| ≤ δ |Q|`. -/
private theorem exists_volume_setOf_mul_le_inter_dyadicCube_le {κ : ℝ} (hκ : 0 < κ) :
    ∃ M δ ε₀ : ℝ, 1 < M ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam s R₀ : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c₀ : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 1 ≤ s →
        4 * 2 ^ k * √(Fintype.card ι) +
          dist (WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k : EuclideanSpace ℝ ι) c₀ ≤ R₀ →
        UniformlyEllipticOn (ball c₀ R₀) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c₀ R₀) → ContDiffOn ℝ 2 u (ball c₀ R₀) →
        (∀ x ∈ closedBall c₀ R₀, 0 ≤ u x) →
        (∀ x ∈ ball c₀ R₀, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R₀ * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c₀ R₀)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball (WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k : EuclideanSpace ℝ ι)
          (2 * 2 ^ k * √(Fintype.card ι)), u x ≤ s) →
        volume ({y | M * s ≤ u (WithLp.toLp 2 y)} ∩ dyadicCube k m) ≤
          ENNReal.ofReal δ * volume (dyadicCube k m) := by
  set n := Fintype.card ι
  have hn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  obtain ⟨M, μ, ε₀, _, hμ, hε₀, H⟩ := exists_mul_volume_ball_le_volume_setOf_lt_inter_ball
    (ι := ι) hκ (θ := (8 * √(n : ℝ))⁻¹) (by positivity) (τ := 1 / 2) (by norm_num) (by norm_num)
  set ω₁ := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω₁ : 0 < ω₁ :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  set ω := μ * ω₁ / 2 ^ n
  have hω : 0 < ω := by positivity
  refine ⟨max M 2, (1 + ω)⁻¹, ε₀, lt_max_of_lt_right one_lt_two, by positivity,
    inv_lt_one_of_one_lt₀ (by linarith), hε₀, ?_⟩
  intro lam Lam s R₀ k m c₀ a u f hs hR₀ ha hLam hcont hu hnonneg hsuper hf hx
  set c : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k
  set R := 4 * 2 ^ k * √(n : ℝ)
  have hR : 0 < R := by positivity
  have hs0 : 0 < s := one_pos.trans_le hs
  have hRR₀ : R ≤ R₀ := le_of_add_le_of_nonneg_left hR₀ dist_nonneg
  have hball : ball c R ⊆ ball c₀ R₀ := ball_subset_ball' hR₀
  have hcball : closedBall c R ⊆ closedBall c₀ R₀ := closedBall_subset_closedBall' hR₀
  -- The measure estimate for `u / s` on `B(c, R)`, whose small ball has radius `2ᵏ / 2`.
  have hθR : (8 * √(n : ℝ))⁻¹ * R = 2 ^ k / 2 := by
    simp only [R]
    field_simp
    ring
  -- The middle ball of the measure estimate on `B(c, R)` is `B(c, 2 · 2ᵏ √n)`.
  have hτR : 1 / 2 * R = 2 * 2 ^ k * √(n : ℝ) := by
    simp only [R]
    ring
  obtain ⟨x₀, hx₀, hux₀⟩ := hx
  -- Dividing by `s ≥ 1` does not increase the `Lⁿ` norm of the positive part of `f`.
  have hfs : eLpNorm (fun x ↦ (s⁻¹ * f x)⁺) n (volume.restrict (ball c R)) ≤
      eLpNorm (fun x ↦ (f x)⁺) n (volume.restrict (ball c₀ R₀)) := by
    have h : (fun x ↦ (s⁻¹ * f x)⁺) = s⁻¹ • fun x ↦ (f x)⁺ := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, posPart_def, mul_max_of_nonneg _ _ (inv_pos.2 hs0).le,
        mul_zero]
    rw [h]
    refine eLpNorm_const_smul_le.trans (mul_le_of_le_one_of_le ?_
      (eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)))
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀ hs)
  have key := H (u := fun x ↦ s⁻¹ * u x) (f := fun x ↦ s⁻¹ * f x) hR (ha.mono_set hball) hLam
    (continuousOn_const.mul (hcont.mono hcball)) (contDiffOn_const.mul (hu.mono hball))
    (fun x hx ↦ mul_nonneg (by positivity) (hnonneg x (hcball (sphere_subset_closedBall hx))))
    (fun x hx ↦ by
      rw [sum_mul_fderiv_fderiv_const_mul]
      exact mul_le_mul_of_nonneg_left (hsuper x (hball hx)) (by positivity))
    (hf.trans' (mul_le_mul' (ENNReal.ofReal_le_ofReal hRR₀) hfs))
    ⟨x₀, by rwa [hτR], by rw [inv_mul_le_iff₀ hs0]; linarith⟩
  rw [hθR] at key
  -- `Y`, where `u < M s`, is an open subset of the ball of radius `2ᵏ / 2`, which lies in `Q`.
  set Y := ball c (2 ^ k / 2) ∩ (fun x ↦ s⁻¹ * u x) ⁻¹' Iio M
  have hYo : IsOpen Y := by
    refine ContinuousOn.isOpen_inter_preimage (f := fun x ↦ s⁻¹ * u x) ?_ isOpen_ball isOpen_Iio
    refine continuousOn_const.mul (hcont.mono (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall ?_).trans hcball)))
    have hn1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
    simp only [R]
    nlinarith [zpow_pos (two_pos : (0 : ℝ) < 2) k]
  have hY : ENNReal.ofReal (ω * (2 ^ k) ^ n) ≤ volume (WithLp.toLp 2 ⁻¹' Y) := by
    rw [(PiLp.volume_preserving_toLp ι).measure_preimage hYo.measurableSet.nullMeasurableSet]
    refine le_of_eq_of_le ?_ ((le_of_eq (by rw [inter_comm]; rfl)).trans' key)
    rw [Measure.addHaar_ball_of_pos _ _ (by positivity), finrank_euclideanSpace,
      ← ENNReal.ofReal_toReal (measure_ball_lt_top (μ := volume) (x := (0 : EuclideanSpace ℝ ι))
        (r := 1)).ne, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hμ.le]
    congr 1
    simp only [ω, ω₁, n, div_pow]
    field_simp
  -- `{u ≥ M s}` and `Y` are disjoint parts of `Q`.
  set X := {y | max M 2 * s ≤ u (WithLp.toLp 2 y)} ∩ dyadicCube k m
  have hXY : volume X + volume (WithLp.toLp 2 ⁻¹' Y) ≤ volume (dyadicCube k m) := by
    rw [← measure_union _ (hYo.measurableSet.preimage (PiLp.continuous_toLp 2 _).measurable)]
    · refine measure_mono (union_subset inter_subset_right fun y hy ↦ ?_)
      exact toLp_preimage_ball_subset_dyadicCube k m hy.1
    · refine disjoint_left.2 fun y hyX hyY ↦ ?_
      have h1 : s⁻¹ * u (WithLp.toLp 2 y) < M := hyY.2
      have h2 : max M 2 * s ≤ u (WithLp.toLp 2 y) := hyX.1
      rw [inv_mul_lt_iff₀ hs0] at h1
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left M 2) hs0.le]
  rw [volume_dyadicCube] at hXY ⊢
  exact le_ofReal_inv_add_mul_of_add_le (by positivity) hω.le hY hXY

/-- **Geometric decay of the superlevel sets of a supersolution** (Caffarelli–Cabré, Lemma 4.6,
for classical supersolutions of linear equations). Let `κ > 0`. There are constants `M > 1`,
`0 < δ < 1` and `ε₀ > 0`, depending only on the dimension and on `κ`, with the following
property. Let `Q₀` be a dyadic cube of level `k`, so of side `2ᵏ`, with centre `c`, and let
`R ≥ 4 · 2ᵏ √n`. Let the coefficient matrix `a` be uniformly elliptic on `B(c, R)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u` be continuous and nonnegative on `closedBall c R` and `C²` in
`B(c, R)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(c, R)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `u ≤ 1`
somewhere in `B(c, 2 · 2ᵏ √n)`, then `|{u ≥ Mʲ⁺¹} ∩ Q₀| ≤ δʲ⁺¹ |Q₀|` for every `j`. -/
theorem exists_volume_setOf_pow_le_inter_dyadicCube_le_pow_mul {κ : ℝ} (hκ : 0 < κ) :
    ∃ M δ ε₀ : ℝ, 1 < M ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) →
        4 * 2 ^ k * √(Fintype.card ι) ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), u x ≤ 1) →
        ∀ j : ℕ, volume ({x | M ^ (j + 1) ≤ u x} ∩ WithLp.ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal (δ ^ (j + 1)) *
            volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) := by
  obtain ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, H⟩ :=
    exists_volume_setOf_mul_le_inter_dyadicCube_le (ι := ι) hκ
  refine ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, ?_⟩
  intro lam Lam R k₀ m₀ c a u f hc hR ha hLam hcont hu hnonneg hsuper hf hx j
  subst hc
  set Q₀ := dyadicCube k₀ m₀
  have hQ₀ : Q₀ ⊆ WithLp.toLp 2 ⁻¹' closedBall (WithLp.toLp 2 fun i ↦
      ((m₀ i : ℝ) + 2⁻¹) * 2 ^ k₀) R := fun y hy ↦ by
    have h := dist_toLp_lt_of_mem_dyadicCube hy (centre_mem_dyadicCube k₀ m₀)
    rw [mem_preimage, mem_closedBall]
    nlinarith [zpow_pos (two_pos : (0 : ℝ) < 2) k₀, Real.sqrt_nonneg (Fintype.card ι)]
  -- The superlevel sets `Aⱼ = {u ≥ Mʲ⁺¹} ∩ Q₀`, in the coordinates of `ι → ℝ`.
  set A : ℕ → Set (ι → ℝ) := fun j ↦ {y | M ^ (j + 1) ≤ u (WithLp.toLp 2 y)} ∩ Q₀
  have hA : ∀ j, MeasurableSet (A j) := fun j ↦
    measurableSet_setOf_le_inter_dyadicCube isClosed_closedBall hcont hQ₀ _
  have hanti : Antitone A := fun i j hij ↦ inter_subset_inter_left _ fun y hy ↦
    (pow_le_pow_right₀ hM.le (by omega)).trans hy
  -- The measure estimate on `Q₀` itself starts the iteration.
  have hA0 : volume (A 0) ≤ ENNReal.ofReal δ * volume Q₀ := by
    have h := H (s := 1) le_rfl (by rw [dist_self, add_zero]; exact hR) ha hLam hcont hu hnonneg
      hsuper hf hx
    simpa [A] using h
  -- If a dyadic subcube of `Q₀` meets `A_(j+1)` in more than a `δ` fraction, then `u > Mʲ⁺¹` on
  -- its parent: otherwise the measure estimate on the subcube, at the scale `s = Mʲ⁺¹`, fails.
  have hB : ∀ (j : ℕ) (k : ℤ) (m m' : ι → ℤ), k < k₀ → dyadicCube k m ⊆ Q₀ →
      dyadicCube k m ⊆ dyadicCube (k + 1) m' →
      ENNReal.ofReal δ * volume (dyadicCube k m) < volume (A (j + 1) ∩ dyadicCube k m) →
      dyadicCube (k + 1) m' ⊆ A j := by
    intro j k m m' hk hQ hQP hlt
    have hPQ₀ : dyadicCube (k + 1) m' ⊆ Q₀ :=
      (dyadicCube_subset_or_disjoint (by omega : k + 1 ≤ k₀) m' m₀).resolve_right
        (not_disjoint_iff_nonempty_inter.2 ((dyadicCube_nonempty k m).mono (subset_inter hQP hQ)))
    by_contra hP
    obtain ⟨y, hyP, hyA⟩ := not_subset.1 hP
    have huy : u (WithLp.toLp 2 y) ≤ M ^ (j + 1) := (not_le.1 fun h ↦ hyA ⟨h, hPQ₀ hyP⟩).le
    -- `B(w, 4 · 2ᵏ √n) ⊆ B(c, 4 · 2^k₀ √n)` for the centre `w` of the subcube, and `y` lies in
    -- `B(w, 2 · 2ᵏ √n)`: these are the balls on which the measure estimate is applied.
    have hw := centre_mem_dyadicCube k m
    have h2k : (2 : ℝ) ^ (k + 1) ≤ 2 ^ k₀ := zpow_le_zpow_right₀ one_le_two (by omega)
    have hn := Real.sqrt_nonneg (Fintype.card ι)
    have h₀ := dist_toLp_lt_of_mem_dyadicCube (hQ hw) (centre_mem_dyadicCube k₀ m₀)
    have h₁ := dist_toLp_lt_of_mem_dyadicCube hyP (hQP hw)
    rw [zpow_add_one₀ two_ne_zero] at h2k h₁
    have hdist : 4 * 2 ^ k * √(Fintype.card ι) + dist (WithLp.toLp 2 fun i ↦
        ((m i : ℝ) + 2⁻¹) * 2 ^ k : EuclideanSpace ℝ ι) (WithLp.toLp 2 fun i ↦
          ((m₀ i : ℝ) + 2⁻¹) * 2 ^ k₀) ≤ 4 * 2 ^ k₀ * √(Fintype.card ι) := by
      nlinarith [mul_le_mul_of_nonneg_right h2k hn,
        mul_nonneg (zpow_pos (two_pos : (0 : ℝ) < 2) k₀).le hn]
    have hy : dist (WithLp.toLp 2 y : EuclideanSpace ℝ ι)
        (WithLp.toLp 2 fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) < 2 * 2 ^ k * √(Fintype.card ι) := by
      nlinarith [mul_le_mul_of_nonneg_right h2k hn]
    have hstep := H (s := M ^ (j + 1)) (one_le_pow₀ hM.le) (hdist.trans hR) ha hLam hcont hu
      hnonneg hsuper hf ⟨_, hy, huy⟩
    refine (hlt.trans_le ((measure_mono ?_).trans hstep)).false
    rintro x ⟨⟨hx, -⟩, hxQ⟩
    exact ⟨by rwa [← pow_succ'], hxQ⟩
  have hdecay := volume_le_pow_mul_volume_dyadicCube (fun j ↦ (hA j).nullMeasurableSet) hanti
    (ENNReal.ofReal_lt_one.2 hδ1) inter_subset_right hA0 hB j
  have hpre : {x | M ^ (j + 1) ≤ u x} ∩ WithLp.ofLp ⁻¹' Q₀ = WithLp.ofLp ⁻¹' A j := by
    ext x
    simp [A]
  rw [hpre, (PiLp.volume_preserving_ofLp ι).measure_preimage (hA j).nullMeasurableSet,
    (PiLp.volume_preserving_ofLp ι).measure_preimage
      (measurableSet_dyadicCube k₀ m₀).nullMeasurableSet, ENNReal.ofReal_pow hδ0.le]
  exact hdecay

/-- **Power decay of the superlevel sets of a supersolution**, the `L^ε` estimate of Krylov and
Safonov (Caffarelli–Cabré, Lemma 4.6, for classical supersolutions of linear equations). Let
`κ > 0`. There are constants `C > 0`, `ε > 0` and `ε₀ > 0`, depending only on the dimension and on
`κ`, with the following property. Let `Q₀` be a dyadic cube of level `k` with centre `c`, and let
`R ≥ 4 · 2ᵏ √n`. Let the coefficient matrix `a` be uniformly elliptic on `B(c, R)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u` be continuous and nonnegative on `closedBall c R` and `C²` in
`B(c, R)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(c, R)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `u ≤ 1`
somewhere in `B(c, 2 · 2ᵏ √n)`, then `|{u ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for every `t > 0`. -/
theorem exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul {κ : ℝ} (hκ : 0 < κ) :
    ∃ C ε ε₀ : ℝ, 0 < C ∧ 0 < ε ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) →
        4 * 2 ^ k * √(Fintype.card ι) ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)), u x ≤ 1) →
        ∀ ⦃t : ℝ⦄, 0 < t → volume ({x | t ≤ u x} ∩ WithLp.ofLp ⁻¹' dyadicCube k m) ≤
          ENNReal.ofReal (C * t ^ (-ε)) *
            volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) := by
  obtain ⟨M, δ, ε₀, hM, hδ0, hδ1, hε₀, H⟩ :=
    exists_volume_setOf_pow_le_inter_dyadicCube_le_pow_mul (ι := ι) hκ
  -- `ε = -log_M δ`, so that `M^(-ε) = δ`, and `C = δ⁻¹`.
  have hlog : Real.logb M δ < 0 := Real.logb_neg hM hδ0 hδ1
  have hMδ : M ^ Real.logb M δ = δ := Real.rpow_logb (by linarith) hM.ne' hδ0
  refine ⟨δ⁻¹, -Real.logb M δ, ε₀, inv_pos.2 hδ0, neg_pos.2 hlog, hε₀, ?_⟩
  intro lam Lam R k m c a u f hc hR ha hLam hcont hu hnonneg hsuper hf hx t ht
  -- With `N = ⌊log_M t⌋₊`, `t ≤ M^(N+1)`, so `δ^N = δ⁻¹ δ^(N+1) ≤ δ⁻¹ t^(-ε)`.
  set N := ⌊Real.logb M t⌋₊
  have htN : t ≤ M ^ (N + 1) := by
    have h := Nat.lt_floor_add_one (Real.logb M t)
    rw [Real.logb_lt_iff_lt_rpow hM ht] at h
    exact_mod_cast h.le
  have hδN : δ ^ N ≤ δ⁻¹ * t ^ (-(-Real.logb M δ)) := by
    rw [neg_neg]
    calc δ ^ N = δ⁻¹ * (M ^ Real.logb M δ) ^ (N + 1) := by
          rw [hMδ, pow_succ']
          field_simp
      _ ≤ δ⁻¹ * t ^ Real.logb M δ := by
          rw [Real.rpow_pow_comm (by linarith)]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht htN hlog.le)
            (inv_pos.2 hδ0).le
  -- The superlevel set of `t` lies in that of `M^N`.
  have hvol : volume ({x | t ≤ u x} ∩ WithLp.ofLp ⁻¹' dyadicCube k m) ≤
      ENNReal.ofReal (δ ^ N) *
        volume (WithLp.ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) := by
    cases hN : N with
    | zero =>
      rw [pow_zero, ENNReal.ofReal_one, one_mul]
      exact measure_mono inter_subset_right
    | succ j =>
      have hMt : M ^ (j + 1) ≤ t := by
        have hN0 : 0 < N := by rw [hN]; exact j.succ_pos
        have h : (N : ℝ) ≤ Real.logb M t :=
          Nat.floor_le (zero_le_one.trans (Nat.floor_pos.1 hN0))
        rw [Real.le_logb_iff_rpow_le hM ht, hN] at h
        exact_mod_cast h
      exact (measure_mono (inter_subset_inter_left _ (ofPred_subset_ofPred.2 fun _ hx ↦
        hMt.trans hx))).trans (H hc hR ha hLam hcont hu hnonneg hsuper hf hx j)
  exact hvol.trans (by gcongr)

end PDE

end TauCeti
