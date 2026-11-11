/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.PowerDecay
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube.Euclidean

/-!
# The weak Harnack inequality of Krylov and Safonov

Let `u ≥ 0` be a `C²` supersolution of a non-divergence-form equation
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` with a uniformly elliptic coefficient matrix, `λ ≤ Λ ≤ κ λ`, on a ball
`B(c, R) ⊆ ℝⁿ`, `n ≥ 1`, centred at the centre `c` of a dyadic cube `Q₀` of side `ℓ = 2ᵏ` and with
`R ≥ 4 ℓ √n`. The weak Harnack inequality bounds a small power mean of `u` over `Q₀` by the value
of `u` at any point of the larger ball `B(c, 2 ℓ √n)`, plus the right-hand side:

`‖u‖_{Lᵖ(Q₀)} ≤ C ℓ^(n / p) (u x + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)` for `x ∈ B(c, 2 ℓ √n)`

(`TauCeti.PDE.exists_eLpNorm_dyadicCube_le_mul_rpow_mul_add`). Since `|Q₀| = ℓⁿ`, the left-hand side
divided by `ℓ^(n / p)` is the power mean `(⨍_{Q₀} uᵖ)^(1 / p)`, so the estimate says that this mean
is controlled by the infimum of `u` over `B(c, 2 ℓ √n)`. Translating and choosing the dyadic scale
`ℓ ∈ [2 r, 4 r)` gives the same estimate on an arbitrary ball,
`‖u‖_{Lᵖ(B(c, r))} ≤ C r^(n / p) (u x + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)` for `x ∈ B(c, 4 √n r)` and
`R ≥ 16 √n r` (`TauCeti.PDE.exists_eLpNorm_ball_le_mul_rpow_mul_add`). The exponent `p > 0` and
the constant `C` depend only on the dimension and on `κ`; no regularity of `a` beyond the pointwise
bounds is used. Together with the local maximum principle for subsolutions, this is the estimate
behind the Harnack inequality and the interior Hölder estimate of Krylov and Safonov.

## The argument

The power decay of the superlevel sets
(`TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`) says that if `u ≤ 1` somewhere
in `B(c, 2 ℓ √n)` and `R ‖f⁺‖_{Lⁿ} ≤ ε₀ λ`, then `|{u ≥ t} ∩ Q₀| ≤ C t^(-ε) |Q₀|` for all `t > 0`.
Integrating this by the layer cake formula at the exponent `p = ε / 2`
(`MeasureTheory.Measure.lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_mul`) bounds `∫_{Q₀} uᵖ` by a
multiple of `|Q₀|`. The general case follows by applying this to `u / s` and `f / s` for every
`s > u x + R ‖f⁺‖_{Lⁿ} / (ε₀ λ)` and letting `s` decrease to that value.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_dyadicCube_le_mul_rpow_mul_add`: **the weak Harnack inequality** for
  classical supersolutions on a dyadic cube.
* `TauCeti.PDE.exists_eLpNorm_ball_le_mul_rpow_mul_add`: the weak Harnack inequality on an
  arbitrary ball `B(c, r)`, with the infimum taken over `B(c, 4 √n r)`.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Theorem 4.8 (a).
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.22.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open Metric MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The normalized weak Harnack inequality.** There are constants `K > 0`, `p > 0` and
`ε₀ > 0`, depending only on the dimension and on `κ`, with the following property. Under the
hypotheses of the power decay `TauCeti.PDE.exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul`,
in particular if `u ≤ 1` somewhere in `B(c, 2 · 2ᵏ √n)` and `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`, the
`Lᵖ` norm of `u` over the dyadic cube `Q₀` of level `k` is at most `K (2ᵏ)^(n / p)`. -/
private theorem exists_eLpNorm_dyadicCube_le_mul_rpow {κ : ℝ} (hκ : 0 < κ) :
    ∃ K p ε₀ : ℝ, 0 < K ∧ 0 < p ∧ 0 < ε₀ ∧
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
        eLpNorm u (ENNReal.ofReal p) (volume.restrict (WithLp.ofLp ⁻¹' dyadicCube k m)) ≤
          ENNReal.ofReal (K * (2 ^ k) ^ ((Fintype.card ι : ℝ) / p)) := by
  obtain ⟨C, ε, ε₀, hC, hε, hε₀, H⟩ :=
    exists_volume_setOf_le_inter_dyadicCube_le_rpow_mul (ι := ι) hκ
  -- Integrate the power decay at the exponent `p = ε / 2`.
  set p := ε / 2
  have hp : 0 < p := by positivity
  set K₀ := 1 + C * p / (ε - p)
  have hK₀ : 0 < K₀ := by
    have : 0 < ε - p := by simp only [p]; linarith
    positivity
  refine ⟨K₀ ^ (1 / p), p, ε₀, by positivity, hp, hε₀, ?_⟩
  intro lam Lam R k m c a u f hc hR ha hLam hcont hu hnonneg hsuper hf hx
  set n := Fintype.card ι
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' dyadicCube k m
  have hQm : MeasurableSet Q :=
    (measurableSet_dyadicCube k m).preimage (PiLp.continuous_ofLp 2 _).measurable
  have hQ : Q ⊆ closedBall c R := fun y hy ↦ by
    have h := dist_toLp_lt_of_mem_dyadicCube hy (centre_mem_dyadicCube k m)
    rw [WithLp.toLp_ofLp, ← hc] at h
    refine mem_closedBall.2 (h.le.trans (le_trans ?_ hR))
    nlinarith [mul_nonneg (zpow_pos (two_pos : (0 : ℝ) < 2) k).le (Real.sqrt_nonneg (n : ℝ))]
  have hum : AEStronglyMeasurable u (volume.restrict Q) :=
    (hcont.mono hQ).aestronglyMeasurable hQm
  have hvolQ : volume Q = ENNReal.ofReal ((2 ^ k) ^ n) := by
    rw [(PiLp.volume_preserving_ofLp ι).measure_preimage
      (measurableSet_dyadicCube k m).nullMeasurableSet, volume_dyadicCube]
  -- The superlevel sets of `‖u‖ₑ` in `Q` are those of `u`, since `u ≥ 0` there.
  have hlevel : ∀ t : ℝ, 1 < t → volume.restrict Q {y | ENNReal.ofReal t < ‖u y‖ₑ} ≤
      ENNReal.ofReal (C * t ^ (-ε)) * volume.restrict Q univ := by
    intro t ht
    have hsub : {y | ENNReal.ofReal t < ‖u y‖ₑ} ∩ Q ⊆ {y | t ≤ u y} ∩ Q := fun y hy ↦ by
      have h := hy.1
      rw [mem_ofPred_eq, Real.enorm_eq_ofReal (hnonneg y (hQ hy.2))] at h
      exact ⟨((ENNReal.ofReal_lt_ofReal_iff').1 h).1.le, hy.2⟩
    rw [Measure.restrict_apply' hQm, Measure.restrict_apply_univ]
    exact (measure_mono hsub).trans
      (H hc hR ha hLam hcont hu hnonneg hsuper hf hx (one_pos.trans ht))
  have hint := (volume.restrict Q).lintegral_rpow_le_of_meas_ofReal_lt_le_rpow_mul
    hum.enorm hp (by simp only [p]; linarith) hC.le hlevel
  rw [Measure.restrict_apply_univ, hvolQ] at hint
  -- Take the `p`-th root.
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hum,
    ENNReal.toReal_ofReal hp.le]
  calc (∫⁻ y in Q, ‖u y‖ₑ ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal K₀ * ENNReal.ofReal ((2 ^ k) ^ n)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = ENNReal.ofReal (K₀ ^ (1 / p) * (2 ^ k) ^ ((n : ℝ) / p)) := by
        have h2k : (0 : ℝ) ≤ 2 ^ k := (zpow_pos two_pos k).le
        rw [← ENNReal.ofReal_mul hK₀.le, ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by positivity), Real.mul_rpow hK₀.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul h2k, mul_one_div]

/-- **The weak Harnack inequality of Krylov and Safonov** for classical supersolutions
(Caffarelli–Cabré, Theorem 4.8 (a), and Gilbarg–Trudinger, Theorem 9.22, without lower-order
terms). Let `κ > 0`. There are constants `C > 0` and `p > 0`, depending only on the dimension and
on `κ`, with the following property. Let `Q₀` be a dyadic cube of level `k`, so of side `2ᵏ`, with
centre `c`, and let `R ≥ 4 · 2ᵏ √n`. Let the coefficient matrix `a` be uniformly elliptic on
`B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u` be continuous and nonnegative on
`closedBall c R` and `C²` in `B(c, R)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(c, R)` and
`f⁺ ∈ Lⁿ(B(c, R))`. Then for every `x ∈ B(c, 2 · 2ᵏ √n)`

`‖u‖_{Lᵖ(Q₀)} ≤ C (2ᵏ)^(n / p) (u x + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)`.

As `|Q₀| = (2ᵏ)ⁿ`, this bounds the power mean `(⨍_{Q₀} uᵖ)^(1 / p)` by
`C (inf_{B(c, 2 · 2ᵏ √n)} u + R ‖f⁺‖_{Lⁿ} / λ)`. -/
theorem exists_eLpNorm_dyadicCube_le_mul_rpow_mul_add {κ : ℝ} (hκ : 0 < κ) :
    ∃ C p : ℝ, 0 < C ∧ 0 < p ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃k : ℤ⦄ ⦃m : ι → ℤ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        c = WithLp.toLp 2 (fun i ↦ ((m i : ℝ) + 2⁻¹) * 2 ^ k) →
        4 * 2 ^ k * √(Fintype.card ι) ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) →
        ∀ x ∈ ball c (2 * 2 ^ k * √(Fintype.card ι)),
          eLpNorm u (ENNReal.ofReal p) (volume.restrict (WithLp.ofLp ⁻¹' dyadicCube k m)) ≤
            ENNReal.ofReal (C * (2 ^ k) ^ ((Fintype.card ι : ℝ) / p) *
              (u x + R / lam * (eLpNorm (fun y ↦ (f y)⁺) (Fintype.card ι)
                (volume.restrict (ball c R))).toReal)) := by
  obtain ⟨K, p, ε₀, hK, hp, hε₀, H⟩ := exists_eLpNorm_dyadicCube_le_mul_rpow (ι := ι) hκ
  refine ⟨K * max 1 ε₀⁻¹, p, by positivity, hp, ?_⟩
  intro lam Lam R k m c a u f hc hR ha hLam hcont hu hnonneg hsuper hfLp x hx
  set n := Fintype.card ι
  set L : ℝ := (2 ^ k) ^ ((n : ℝ) / p)
  have hL : 0 ≤ L := Real.rpow_nonneg (zpow_pos two_pos k).le _
  have hlam : 0 < lam := ha.pos
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  set F := (eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R))).toReal
  have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
  have hF : eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R)) = ENNReal.ofReal F :=
    (ENNReal.ofReal_toReal hfLp.eLpNorm_ne_top).symm
  have hxR : x ∈ closedBall c R := by
    refine ball_subset_closedBall (ball_subset_ball (le_trans ?_ hR) hx)
    nlinarith [mul_nonneg (zpow_pos (two_pos : (0 : ℝ) < 2) k).le (Real.sqrt_nonneg (n : ℝ))]
  have hux : 0 ≤ u x := hnonneg x hxR
  -- The estimate at every scale `s` at which `u / s` and `f / s` satisfy the normalization.
  have hscale : ∀ s : ℝ, 0 < s → u x ≤ s → R * F ≤ ε₀ * lam * s →
      eLpNorm u (ENNReal.ofReal p) (volume.restrict (WithLp.ofLp ⁻¹' dyadicCube k m)) ≤
        ENNReal.ofReal (K * L * s) := by
    intro s hs hus hRF
    have hf' : ENNReal.ofReal R * eLpNorm (fun y ↦ (s⁻¹ * f y)⁺) n
        (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) := by
      have h : (fun y ↦ (s⁻¹ * f y)⁺) = s⁻¹ • fun y ↦ (f y)⁺ := by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, posPart_def,
          mul_max_of_nonneg _ _ (inv_pos.2 hs).le, mul_zero]
      rw [h, eLpNorm_const_smul, hF, Real.enorm_eq_ofReal (inv_pos.2 hs).le,
        ← ENNReal.ofReal_mul (inv_pos.2 hs).le, ← ENNReal.ofReal_mul hR0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← mul_assoc, mul_comm R, mul_assoc, inv_mul_le_iff₀ hs]
      linarith
    have key := H (u := fun y ↦ s⁻¹ * u y) (f := fun y ↦ s⁻¹ * f y) hc hR ha hLam
      (continuousOn_const.mul hcont) (contDiffOn_const.mul hu)
      (fun y hy ↦ mul_nonneg (inv_pos.2 hs).le (hnonneg y hy))
      (fun y hy ↦ by
        rw [sum_mul_fderiv_fderiv_const_mul]
        exact mul_le_mul_of_nonneg_left (hsuper y hy) (inv_pos.2 hs).le)
      hf' ⟨x, hx, by rwa [inv_mul_le_one₀ hs]⟩
    have hu' : u = s • fun y ↦ s⁻¹ * u y := by
      funext y
      simp [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne']
    rw [hu', eLpNorm_const_smul, Real.enorm_eq_ofReal hs.le]
    calc ENNReal.ofReal s * eLpNorm (fun y ↦ s⁻¹ * u y) (ENNReal.ofReal p)
          (volume.restrict (WithLp.ofLp ⁻¹' dyadicCube k m))
        ≤ ENNReal.ofReal s * ENNReal.ofReal (K * L) := by gcongr
      _ = ENNReal.ofReal (K * L * s) := by
          rw [← ENNReal.ofReal_mul hs.le, mul_comm]
  -- Let `s` decrease to `u x + R F / (ε₀ λ)`.
  set T := u x + R * F / (ε₀ * lam)
  have hT : 0 ≤ T := by positivity
  have hlim : eLpNorm u (ENNReal.ofReal p) (volume.restrict (WithLp.ofLp ⁻¹' dyadicCube k m)) ≤
      ENNReal.ofReal (K * L * T) := by
    have htends : Tendsto (fun s ↦ ENNReal.ofReal (K * L * s)) (𝓝[>] T)
        (𝓝 (ENNReal.ofReal (K * L * T))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)).tendsto T).mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto htends (eventually_nhdsWithin_of_forall fun s (hs : T < s) ↦ ?_)
    have hRF : 0 ≤ R * F / (ε₀ * lam) := by positivity
    refine hscale s (hT.trans_lt hs) (by linarith) ?_
    rw [← div_le_iff₀' (by positivity)]
    linarith
  refine hlim.trans (ENNReal.ofReal_le_ofReal ?_)
  -- `T ≤ max 1 ε₀⁻¹ (u x + R F / λ)`.
  have hT' : T ≤ max 1 ε₀⁻¹ * (u x + R / lam * F) := by
    have h1 : u x ≤ max 1 ε₀⁻¹ * u x := le_mul_of_one_le_left hux (le_max_left _ _)
    have h2 : R * F / (ε₀ * lam) ≤ max 1 ε₀⁻¹ * (R / lam * F) := by
      rw [show R * F / (ε₀ * lam) = ε₀⁻¹ * (R / lam * F) by field_simp]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    simp only [T]
    linarith
  calc K * L * T ≤ K * L * (max 1 ε₀⁻¹ * (u x + R / lam * F)) :=
        mul_le_mul_of_nonneg_left hT' (by positivity)
    _ = K * max 1 ε₀⁻¹ * L * (u x + R / lam * F) := by ring


/-- **The weak Harnack inequality of Krylov and Safonov on balls** for classical supersolutions
(Gilbarg–Trudinger, Theorem 9.22, without lower-order terms). Let `κ > 0`. There are constants
`C > 0` and `p > 0`, depending only on the dimension and on `κ`, with the following property. Let
`R ≥ 16 √n r`. Let the coefficient matrix `a` be uniformly elliptic on `B(c, R)` with
constants `λ ≤ Λ ≤ κ λ`, and let `u` be continuous and nonnegative on `closedBall c R` and `C²` in
`B(c, R)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(c, R)` and `f⁺ ∈ Lⁿ(B(c, R))`. Then for every
`x ∈ B(c, 4 √n r)`

`‖u‖_{Lᵖ(B(c, r))} ≤ C r^(n / p) (u x + R ‖f⁺‖_{Lⁿ(B(c, R))} / λ)`.

So the power mean `(⨍_{B(c, r)} uᵖ)^(1 / p)` is at most a multiple of
`inf_{B(c, 4 √n r)} u + R ‖f⁺‖_{Lⁿ} / λ`. Unlike
`TauCeti.PDE.exists_eLpNorm_dyadicCube_le_mul_rpow_mul_add`, the statement is invariant under
translations and dilations. -/
theorem exists_eLpNorm_ball_le_mul_rpow_mul_add {κ : ℝ} (hκ : 0 < κ) :
    ∃ C p : ℝ, 0 < C ∧ 0 < p ∧
      ∀ ⦃lam Lam R r : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄
        ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄ ⦃u f : EuclideanSpace ℝ ι → ℝ⦄,
        16 * √(Fintype.card ι) * r ≤ R →
        UniformlyEllipticOn (ball c R) a lam Lam → Lam ≤ κ * lam →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        MemLp (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) →
        ∀ x ∈ ball c (4 * √(Fintype.card ι) * r),
          eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c r)) ≤
            ENNReal.ofReal (C * r ^ ((Fintype.card ι : ℝ) / p) *
              (u x + R / lam * (eLpNorm (fun y ↦ (f y)⁺) (Fintype.card ι)
                (volume.restrict (ball c R))).toReal)) := by
  obtain ⟨C, p, hC, hp, H⟩ := exists_eLpNorm_dyadicCube_le_mul_rpow_mul_add (ι := ι) hκ
  set n := Fintype.card ι
  refine ⟨C * 4 ^ ((n : ℝ) / p), p, by positivity, hp, ?_⟩
  intro lam Lam R r c a u f hR ha hLam hcont hu hnonneg hsuper hfLp x hx
  -- For `r ≤ 0` the ball `B(c, r)` is empty.
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hn1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- The dyadic scale `2ᵏ ∈ [2 r, 4 r)`.
  obtain ⟨j, hj₁, hj₂⟩ := exists_mem_Ioc_zpow (by positivity : 0 < 2 * r) one_lt_two
  set k : ℤ := j + 1
  have hk₁ : 2 * r ≤ 2 ^ k := hj₂
  have hk₂ : (2 : ℝ) ^ k < 4 * r := by
    rw [zpow_add_one₀ two_ne_zero]
    linarith
  -- Translate `c` to the centre `c₀` of the dyadic cube `Q₀` of level `k` at the origin.
  set c₀ : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i ↦ (((0 : ι → ℤ) i : ℝ) + 2⁻¹) * 2 ^ k
  set d := c - c₀
  have hcd : c₀ + d = c := add_sub_cancel c₀ c
  have hmaps : ∀ ρ, MapsTo (· + d) (ball c₀ ρ) (ball c ρ) := fun ρ y hy ↦ by
    rwa [mem_ball, ← hcd, dist_add_right]
  have hmapsC : ∀ ρ, MapsTo (· + d) (closedBall c₀ ρ) (closedBall c ρ) := fun ρ y hy ↦ by
    rwa [mem_closedBall, ← hcd, dist_add_right]
  have htr : ∀ (g : EuclideanSpace ℝ ι → ℝ) (ρ : ℝ) (q : ℝ≥0∞),
      AEStronglyMeasurable g (volume.restrict (ball c ρ)) →
      eLpNorm (fun y ↦ g (y + d)) q (volume.restrict (ball c₀ ρ)) =
        eLpNorm g q (volume.restrict (ball c ρ)) := by
    intro g ρ q hg
    have hmp := (measurePreserving_add_right volume d).restrict_preimage
      (measurableSet_ball (x := c) (ε := ρ))
    rw [preimage_add_right_ball, show c - d = c₀ from sub_sub_cancel c c₀] at hmp
    exact eLpNorm_comp_measurePreserving hg hmp
  have hrR : r ≤ R := by nlinarith
  have hum : AEStronglyMeasurable u (volume.restrict (ball c r)) :=
    (hcont.mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrR))).aestronglyMeasurable measurableSet_ball
  have hfR := htr (fun z ↦ (f z)⁺) R n hfLp.aestronglyMeasurable
  -- The weak Harnack inequality on `Q₀` for the translates.
  have key := H (c := c₀) (m := 0) (a := fun y ↦ a (y + d)) (u := fun y ↦ u (y + d))
    (f := fun y ↦ f (y + d)) rfl (by nlinarith) (ha.comp (hmaps R)) hLam
    (hcont.comp (continuous_id.add continuous_const).continuousOn (hmapsC R))
    (hu.comp (contDiff_id.add contDiff_const).contDiffOn (hmaps R))
    (fun y hy ↦ hnonneg _ (hmapsC R hy))
    (fun y hy ↦ by
      have h₁ : fderiv ℝ (fun z ↦ u (z + d)) = fun z ↦ fderiv ℝ u (z + d) :=
        funext fun z ↦ fderiv_comp_add_right d
      rw [h₁, fderiv_comp_add_right d]
      exact hsuper _ (hmaps R hy))
    (by rw [memLp_iff, hfR]; exact hfLp.eLpNorm_lt_top) (x - d)
    (by
      rw [mem_ball, ← dist_add_right (x - d) c₀ d, sub_add_cancel, hcd]
      refine (mem_ball.1 hx).trans_le ?_
      nlinarith)
  rw [sub_add_cancel, hfR] at key
  -- `B(c₀, r) ⊆ B(c₀, 2ᵏ / 2) ⊆ Q₀`.
  have hsub : ball c₀ r ⊆ WithLp.ofLp ⁻¹' dyadicCube k 0 := fun y hy ↦ by
    refine toLp_preimage_ball_subset_dyadicCube k 0 ?_
    rw [mem_preimage, WithLp.toLp_ofLp]
    exact ball_subset_ball (by linarith) hy
  rw [← htr u r _ hum]
  refine (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans
    (key.trans (ENNReal.ofReal_le_ofReal ?_))
  -- `(2ᵏ)^(n / p) ≤ (4 r)^(n / p)`.
  have hux : 0 ≤ u x := hnonneg x (ball_subset_closedBall (ball_subset_ball (by nlinarith) hx))
  have hX : 0 ≤ u x + R / lam * (eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R))).toReal :=
    add_nonneg hux (mul_nonneg (div_nonneg (by linarith) ha.pos.le) ENNReal.toReal_nonneg)
  have hpow : ((2 : ℝ) ^ k) ^ ((n : ℝ) / p) ≤ 4 ^ ((n : ℝ) / p) * r ^ ((n : ℝ) / p) := by
    rw [← Real.mul_rpow (by norm_num) hr.le]
    exact Real.rpow_le_rpow (zpow_pos two_pos k).le hk₂.le (by positivity)
  calc C * ((2 : ℝ) ^ k) ^ ((n : ℝ) / p) * (u x + R / lam *
        (eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R))).toReal)
      ≤ C * (4 ^ ((n : ℝ) / p) * r ^ ((n : ℝ) / p)) * (u x + R / lam *
          (eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R))).toReal) := by
        gcongr
    _ = C * 4 ^ ((n : ℝ) / p) * r ^ ((n : ℝ) / p) * (u x + R / lam *
          (eLpNorm (fun y ↦ (f y)⁺) n (volume.restrict (ball c R))).toReal) := by ring

end PDE

end TauCeti
