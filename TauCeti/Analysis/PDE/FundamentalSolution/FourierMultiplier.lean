/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.RieszTransform.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.Normed.Group.Bounded
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling

/-!
# Second derivatives of solutions of Poisson's equation as Riesz transforms

Let `E` be a finite-dimensional real inner product space of dimension `d`. On Schwartz functions,
`∂_v ∂_w = T_{m_{v,w}} ∘ Δ`, where `T_{m_{v,w}}` is the `L²` Fourier multiplier with symbol
`⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` (`SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM`),
and `T_{m_{v,w}} = -R_v R_w` for the Riesz transforms `R_v`
(`TauCeti.rieszTransform_compL_rieszTransform`).
The solutions of Poisson's equation `-Δu = f` that matter, the Newtonian potentials, are not
Schwartz functions: they decay like `‖x‖ ^ (2 - d)` for `d ≥ 3` and grow like `log ‖x‖` in the
plane. This file shows that the identity survives for every smooth solution that does not grow
too fast. If `f` has compact support, `Δu = -f`, and

`‖x‖ ^ (d/2 - 2) ‖u x‖ → 0` and `‖x‖ ^ (d/2 - 1) ‖Du x‖ → 0` as `x → ∞`,

then `T_{m_{v,w}} f = -D²u(v, w)` almost everywhere
(`TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg`), that is,

`D²u(v, w) = R_v R_w f`

(`TauCeti.coeFn_rieszTransform_rieszTransform_toLp_of_laplacian_eq_neg`). The Newtonian potentials
satisfy the growth conditions in every dimension: they decay for `d ≥ 3`, grow logarithmically for
`d = 2` and linearly for `d = 1`. Some growth condition is needed: adding the harmonic polynomial
`x₁ x₂` to `u` does not change `f`, but it changes `D²u(e₁, e₂)` by `1`.

## The argument

Truncate `u` by a cutoff `χ_R` equal to `1` on `ball 0 R` and to `0` off `closedBall 0 (2R)`, with
`‖Dχ_R‖ = O(1/R)` and `|Δχ_R| = O(1/R²)`
(`TauCeti.exists_forall_contDiff_cutoff_ball_norm_laplacian_le`). The truncation `χ_R u` is a
Schwartz function, and once `R` exceeds the support of `f`,

`Δ(χ_R u) + f = 2 Du(∇χ_R) + (Δχ_R) u`

vanishes off the annulus `R ≤ ‖x‖ ≤ 2R`. On the annulus it is `o(R ^ (-d/2))` by the growth
conditions, and the annulus has volume `O(R ^ d)`, so `Δ(χ_R u) → -f` in `L²`. Applying
`T_{m_{v,w}}` and passing to an almost everywhere convergent subsequence gives the identity, since
`χ_R u` agrees with `u` near each point once `R` is large.

## Main declarations

* `TauCeti.coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg`:
  `T_{m_{v,w}} f = -D²u(v, w)`.
* `TauCeti.coeFn_rieszTransform_rieszTransform_toLp_of_laplacian_eq_neg`: `R_v R_w f = D²u(v, w)`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace MeasureTheory Metric Module Set Topology
open scoped ContDiff Laplacian Gradient LineDeriv SchwartzMap

/-- A growth bound `‖x‖ ^ (-a) g x ≤ δ` beyond a radius `R' ≤ R` bounds `g` on the annulus
`R ≤ ‖x‖ ≤ 2R` by `δ 2 ^ |a| R ^ a`. -/
private theorem le_mul_two_rpow_abs_mul_rpow_of_rpow_neg_mul_le {E : Type*}
    [NormedAddCommGroup E] {g : E → ℝ} {R R' δ a : ℝ} (hR : 0 < R) (hR' : R' ≤ R)
    (hg0 : ∀ x, 0 ≤ g x) (hg : ∀ x : E, R' ≤ ‖x‖ → ‖x‖ ^ (-a) * g x ≤ δ) :
    ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 2 * R → g x ≤ δ * 2 ^ |a| * R ^ a := by
  intro x hx hx2
  have hx0 : 0 < ‖x‖ := hR.trans_le hx
  calc g x = ‖x‖ ^ a * (‖x‖ ^ (-a) * g x) := by
        rw [← mul_assoc, ← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero, one_mul]
    _ ≤ (2 ^ |a| * R ^ a) * δ :=
        mul_le_mul (rpow_le_two_rpow_abs_mul (by linarith) hx2) (hg x (hR'.trans hx))
          (mul_nonneg (by positivity) (hg0 x)) (by positivity)
    _ = δ * 2 ^ |a| * R ^ a := by ring

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] {u f : E → F}

variable [FiniteDimensional ℝ E]

/-- **The truncation error.** Let `Δu = -f` with `f` vanishing off `closedBall 0 R₀`, and let `χ`
be a cutoff equal to `1` on `ball 0 R` and to `0` off `closedBall 0 (2R)`, with `‖Dχ‖ ≤ C / R`
and `|Δχ| ≤ C / R²`, where `R₀ < R`. If `‖u‖ ≤ a` and `‖Du‖ ≤ b` on the annulus
`R ≤ ‖x‖ ≤ 2R`, then `Δ(χ u) + f = 2 Du(∇χ) + (Δχ) u` is bounded by `2 b C / R + a C / R²` there,
and it vanishes off the annulus. -/
private theorem norm_laplacian_smul_add_le (hu : ContDiff ℝ ∞ u) (hΔ : Δ u = -f)
    {R₀ R C a b : ℝ} (hf : ∀ y : E, R₀ < ‖y‖ → f y = 0) (hR₀ : R₀ < R) (hR : 0 < R)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ1 : ∀ x, ‖x‖ < R → χ =ᶠ[𝓝 x] fun _ => 1)
    (hχ0 : ∀ x, 2 * R < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0) (hχ' : ∀ x, ‖fderiv ℝ χ x‖ ≤ C / R)
    (hχ'' : ∀ x, ‖Δ χ x‖ ≤ C / R ^ 2) (hC : 0 ≤ C) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 2 * R → ‖u x‖ ≤ a)
    (hb : ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 2 * R → ‖fderiv ℝ u x‖ ≤ b) (x : E) :
    ‖Δ (fun y => χ y • u y) x + f x‖ ≤
      (closedBall (0 : E) (2 * R)).indicator (fun _ => 2 * (b * (C / R)) + C / R ^ 2 * a) x := by
  have hK : 0 ≤ 2 * (b * (C / R)) + C / R ^ 2 * a := by positivity
  by_cases hxR : ‖x‖ < R
  · -- Inside `ball 0 R` the truncation is `u` itself, and `Δu = -f`.
    have h : (fun y => χ y • u y) =ᶠ[𝓝 x] u := by
      filter_upwards [hχ1 x hxR] with y hy
      rw [hy, one_smul]
    rw [(laplacian_congr_nhds h).eq_of_nhds, hΔ, Pi.neg_apply, neg_add_cancel, norm_zero]
    exact indicator_nonneg (fun _ _ => hK) x
  by_cases hx2R : 2 * R < ‖x‖
  · -- Off `closedBall 0 (2R)` the truncation vanishes identically, and so does `f`.
    have h : (fun y => χ y • u y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [hχ0 x hx2R] with y hy
      rw [hy, zero_smul]
    rw [(laplacian_congr_nhds h).eq_of_nhds, laplacian_const, hf x (by linarith), add_zero,
      Pi.zero_apply, norm_zero]
    exact indicator_nonneg (fun _ _ => hK) x
  -- On the annulus, expand `Δ(χ u)` by the Leibniz rule; `f` vanishes there.
  push Not at hxR hx2R
  rw [indicator_of_mem (mem_closedBall_zero_iff.2 hx2R),
    (hχ.contDiffAt.of_le (by simp)).laplacian_fun_smul (hu.contDiffAt.of_le (by simp)), hΔ,
    Pi.neg_apply, hf x (by linarith), neg_zero, smul_zero, zero_add, add_zero]
  have hgrad : ‖∇ χ x‖ ≤ C / R := by
    rw [norm_gradient_eq_norm_fderiv]
    exact hχ' x
  calc ‖(2 : ℝ) • fderiv ℝ u x (∇ χ x) + Δ χ x • u x‖
      ≤ 2 * ‖fderiv ℝ u x (∇ χ x)‖ + ‖Δ χ x‖ * ‖u x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_two]
    _ ≤ 2 * (b * (C / R)) + C / R ^ 2 * a := by
        gcongr
        · exact (le_opNorm _ _).trans (mul_le_mul (hb x hxR hx2R) hgrad (norm_nonneg _) hb0)
        · exact hχ'' x
        · exact ha x hxR hx2R

variable [MeasurableSpace E] [BorelSpace E]

/-- The volume of `closedBall 0 (2R)` scales like `R ^ d`: its square root cancels `R ^ (-d/2)`. -/
private theorem rpow_neg_mul_measureReal_closedBall_rpow {R : ℝ} (hR : 0 < R) :
    R ^ (-((finrank ℝ E : ℝ) / 2)) * volume.real (closedBall (0 : E) (2 * R)) ^ (1 / 2 : ℝ) =
      2 ^ ((finrank ℝ E : ℝ) / 2) * volume.real (ball (0 : E) 1) ^ (1 / 2 : ℝ) := by
  set d : ℝ := (finrank ℝ E : ℝ)
  have hRd : R ^ (-(d / 2)) * R ^ (d / 2) = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  rw [Measure.addHaar_real_closedBall _ _ (by positivity),
    Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), Real.mul_rpow zero_le_two hR.le, mul_one_div]
  linear_combination (2 ^ (d / 2) * volume.real (ball (0 : E) 1) ^ (1 / 2 : ℝ)) * hRd

/-- **The `L²` truncation error.** Under the hypotheses of `norm_laplacian_smul_add_le`, the
`L²` norm of `Δ(χ u) + f` is at most the pointwise bound `2 b C / R + a C / R²` times the square
root of the volume of `closedBall 0 (2R)`. -/
private theorem norm_toLp_laplacian_add_le (hu : ContDiff ℝ ∞ u) (hΔ : Δ u = -f)
    (hf : MemLp f 2 volume) {R₀ R C a b : ℝ} (hf0 : ∀ y : E, R₀ < ‖y‖ → f y = 0) (hR₀ : R₀ < R)
    (hR : 0 < R) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ x, ‖x‖ < R → χ =ᶠ[𝓝 x] fun _ => 1) (hχ0 : ∀ x, 2 * R < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0)
    (hχ' : ∀ x, ‖fderiv ℝ χ x‖ ≤ C / R) (hχ'' : ∀ x, ‖Δ χ x‖ ≤ C / R ^ 2) (hC : 0 ≤ C)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 2 * R → ‖u x‖ ≤ a)
    (hb : ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 2 * R → ‖fderiv ℝ u x‖ ≤ b) :
    ‖(Δ ((hχc.smul_right (f' := u)).toSchwartzMap (hχ.smul hu))).toLp 2 + hf.toLp f‖ ≤
      (2 * (b * (C / R)) + C / R ^ 2 * a) *
        volume.real (closedBall (0 : E) (2 * R)) ^ (1 / 2 : ℝ) := by
  set c := 2 * (b * (C / R)) + C / R ^ 2 * a
  have hc0 : 0 ≤ c := by positivity
  set S := (hχc.smul_right (f' := u)).toSchwartzMap (hχ.smul hu)
  set I := indicatorConstLp 2 (measurableSet_closedBall (x := (0 : E)) (ε := 2 * R))
    (measure_closedBall_lt_top (μ := volume)).ne c
  refine (Lp.norm_le_norm_of_ae_le (g := I) ?_).trans_eq ?_
  · filter_upwards [Lp.coeFn_add ((Δ S).toLp 2) (hf.toLp f),
      SchwartzMap.coeFn_toLp (Δ S) 2 volume, hf.coeFn_toLp,
      indicatorConstLp_coeFn (p := 2) (μ := volume)
        (hs := measurableSet_closedBall (x := (0 : E)) (ε := 2 * R))
        (hμs := (measure_closedBall_lt_top (μ := volume)).ne) (c := c)] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.add_apply, h₂, h₃, h₄, SchwartzMap.laplacian_apply, norm_indicator_eq_indicator_norm,
      Real.norm_of_nonneg hc0]
    exact norm_laplacian_smul_add_le hu hΔ hf0 hR₀ hR hχ hχ1 hχ0 hχ' hχ'' hC ha0 hb0 ha hb x
  · rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, Real.norm_of_nonneg hc0,
      ENNReal.toReal_ofNat]

/-- With the growth bounds `a = δ 2 ^ |2 - d/2| R ^ (2 - d/2)` on `u` and
`b = δ 2 ^ |1 - d/2| R ^ (1 - d/2)` on `Du`, the `L²` bound of `norm_toLp_laplacian_add_le` is
`δ C (2 · 2 ^ |1 - d/2| + 2 ^ |2 - d/2|) 2 ^ (d/2) |B(0, 1)| ^ (1/2)`, independent of `R`. -/
private theorem truncation_bound_mul_measureReal_closedBall_rpow {R δ C : ℝ} (hR : 0 < R) :
    (2 * (δ * 2 ^ |1 - (finrank ℝ E : ℝ) / 2| * R ^ (1 - (finrank ℝ E : ℝ) / 2) * (C / R)) +
      C / R ^ 2 * (δ * 2 ^ |2 - (finrank ℝ E : ℝ) / 2| * R ^ (2 - (finrank ℝ E : ℝ) / 2))) *
        volume.real (closedBall (0 : E) (2 * R)) ^ (1 / 2 : ℝ) =
      δ * C * (2 * 2 ^ |1 - (finrank ℝ E : ℝ) / 2| + 2 ^ |2 - (finrank ℝ E : ℝ) / 2|) *
        (2 ^ ((finrank ℝ E : ℝ) / 2) * volume.real (ball (0 : E) 1) ^ (1 / 2 : ℝ)) := by
  set d : ℝ := (finrank ℝ E : ℝ)
  have h₁ : R ^ (1 - d / 2) = R ^ (-(d / 2)) * R := by
    rw [← Real.rpow_add_one hR.ne']
    ring_nf
  have h₂ : R ^ (2 - d / 2) = R ^ (-(d / 2)) * R ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    push_cast
    ring_nf
  have hc : 2 * (δ * 2 ^ |1 - d / 2| * R ^ (1 - d / 2) * (C / R)) +
      C / R ^ 2 * (δ * 2 ^ |2 - d / 2| * R ^ (2 - d / 2)) =
        δ * C * (2 * 2 ^ |1 - d / 2| + 2 ^ |2 - d / 2|) * R ^ (-(d / 2)) := by
    rw [h₁, h₂]
    field_simp
  rw [hc, mul_assoc, rpow_neg_mul_measureReal_closedBall_rpow hR]

/-- **Schwartz truncations of a solution of Poisson's equation.** If `Δu = -f` with `f` of compact
support and `u` satisfies the growth conditions, there are Schwartz functions `Sₘ` that agree with
`u` near every point of `ball 0 m` and whose Laplacians tend to `-f` in `L²`. They are `χ_R u` for
cutoffs `χ_R` at radii `R ≥ m`. -/
private theorem exists_schwartzMap_eventuallyEq_tendsto_toLp_laplacian_add
    (hu : ContDiff ℝ ∞ u) (hΔ : Δ u = -f) (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hu₀ : Tendsto (fun x => ‖x‖ ^ ((finrank ℝ E : ℝ) / 2 - 2) * ‖u x‖) (cocompact E) (𝓝 0))
    (hu₁ : Tendsto (fun x => ‖x‖ ^ ((finrank ℝ E : ℝ) / 2 - 1) * ‖fderiv ℝ u x‖) (cocompact E)
      (𝓝 0)) :
    ∃ S : ℕ → 𝓢(E, F), (∀ (m : ℕ) x, ‖x‖ < m → (S m : E → F) =ᶠ[𝓝 x] u) ∧
      Tendsto (fun m => (Δ (S m)).toLp 2 + hf.toLp f) atTop (𝓝 0) := by
  set d : ℝ := (finrank ℝ E : ℝ)
  obtain ⟨C, hC⟩ := exists_forall_contDiff_cutoff_ball_norm_laplacian_le (E := E)
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hf0 : ∀ y : E, R₀ < ‖y‖ → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => (mem_closedBall_zero_iff.1 (hR₀ h)).not_gt hy
  -- Cutoffs at radii `R m ≥ m` beyond the support of `f`.
  set R : ℕ → ℝ := fun m => max (max m 1) (R₀ + 1)
  have hR0 : ∀ m, 0 < R m := fun m => zero_lt_one.trans_le ((le_max_right _ _).trans
    (le_max_left _ _))
  have hRm : ∀ m : ℕ, (m : ℝ) ≤ R m := fun m => (le_max_left _ _).trans (le_max_left _ _)
  have hR₀R : ∀ m, R₀ < R m := fun m => (lt_add_one R₀).trans_le (le_max_right _ _)
  have hR : Tendsto R atTop atTop := tendsto_atTop_mono hRm tendsto_natCast_atTop_atTop
  choose χ hχ hχc hχ1 hχ0 hχ' hχ'' _ using fun m => hC (R m) (hR0 m)
  refine ⟨fun m => ((hχc m).smul_right (f' := u)).toSchwartzMap ((hχ m).smul hu),
    fun m x hx => ?_, ?_⟩
  · filter_upwards [hχ1 m x (hx.trans_le (hRm m))] with y hy
    simp [hy]
  -- Once the growth bounds hold with `δ` beyond `R m`, the `L²` error is at most `δ K`.
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hχ' 0 0)
    rwa [le_div_iff₀ (hR0 0), zero_mul] at this
  set K := C * (2 * 2 ^ |1 - d / 2| + 2 ^ |2 - d / 2|) *
    (2 ^ (d / 2) * volume.real (ball (0 : E) 1) ^ (1 / 2 : ℝ))
  have hK : 0 ≤ K := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (K + 1)
  have hδK : δ * K < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hδ : 0 < δ := div_pos hε (by linarith)
  rw [← Metric.cobounded_eq_cocompact, ← neg_sub] at hu₀ hu₁
  obtain ⟨R₁, hR₁⟩ := exists_forall_le_of_tendsto_cobounded hu₀ hδ
  obtain ⟨R₂, hR₂⟩ := exists_forall_le_of_tendsto_cobounded hu₁ hδ
  obtain ⟨N, hN⟩ := (hR.eventually (eventually_ge_atTop (max R₁ R₂))).exists_forall_of_atTop
  refine ⟨N, fun m hm => ?_⟩
  have hRm0 := hR0 m
  have hbound := norm_toLp_laplacian_add_le hu hΔ hf hf0 (hR₀R m) hRm0 (hχ m) (hχc m) (hχ1 m)
    (hχ0 m) (hχ' m) (hχ'' m) hC0 (by positivity) (by positivity)
    (le_mul_two_rpow_abs_mul_rpow_of_rpow_neg_mul_le hRm0 ((le_max_left _ _).trans (hN m hm))
      (fun x => norm_nonneg (u x)) hR₁)
    (le_mul_two_rpow_abs_mul_rpow_of_rpow_neg_mul_le hRm0 ((le_max_right _ _).trans (hN m hm))
      (fun x => norm_nonneg (fderiv ℝ u x)) hR₂)
  rw [dist_zero_right]
  refine hbound.trans_lt (lt_of_eq_of_lt ?_ hδK)
  rw [truncation_bound_mul_measureReal_closedBall_rpow hRm0]
  ring

variable [CompleteSpace F]

/-- **The Hessian multiplier on a solution of Poisson's equation.** Let `u` be smooth with
`Δu = -f`, where `f` has compact support, and suppose that `‖x‖ ^ (d/2 - 2) ‖u x‖` and
`‖x‖ ^ (d/2 - 1) ‖Du x‖` tend to zero at infinity, `d` the dimension. Then the Fourier multiplier
`T_{m_{v,w}}` with symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` sends `f` to `-D²u(v, w)`. Since `-Δu = f`, this
says that `T_{m_{v,w}} = ∂_v ∂_w Δ⁻¹` on `f`, with `Δ⁻¹ f = -u`. -/
theorem coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg
    (hu : ContDiff ℝ ∞ u) (hΔ : Δ u = -f) (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hu₀ : Tendsto (fun x => ‖x‖ ^ ((finrank ℝ E : ℝ) / 2 - 2) * ‖u x‖) (cocompact E) (𝓝 0))
    (hu₁ : Tendsto (fun x => ‖x‖ ^ ((finrank ℝ E : ℝ) / 2 - 1) * ‖fderiv ℝ u x‖) (cocompact E)
      (𝓝 0)) (v w : E) :
    Lp.fourierMultiplierCLM F (hessianSymbolLp v w) (hf.toLp f) =ᵐ[volume]
      fun x => -iteratedFDeriv ℝ 2 u x ![v, w] := by
  set T := Lp.fourierMultiplierCLM F (hessianSymbolLp v w)
  obtain ⟨S, hSu, hSlim⟩ :=
    exists_schwartzMap_eventuallyEq_tendsto_toLp_laplacian_add hu hΔ hf hc hu₀ hu₁
  -- `T (Δ Sₘ + f) - T f = ∂_v ∂_w Sₘ`, and `T (Δ Sₘ + f) → 0` in `L²`, so almost everywhere along
  -- a subsequence.
  have hT : ∀ m, T ((Δ (S m)).toLp 2 + hf.toLp f) - T (hf.toLp f) =
      (∂_{v} (∂_{w} (S m))).toLp 2 := fun m => by
    rw [map_add, add_sub_cancel_right]
    exact (SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM (S m) v w).symm
  have hlim : Tendsto (fun m => T ((Δ (S m)).toLp 2 + hf.toLp f)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (T.continuous.tendsto 0).comp hSlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hpt : ∀ᵐ x, ∀ m, T ((Δ (S m)).toLp 2 + hf.toLp f) x - T (hf.toLp f) x =
      ∂_{v} (∂_{w} (S m)) x := by
    rw [ae_all_iff]
    intro m
    filter_upwards [Lp.coeFn_sub (T ((Δ (S m)).toLp 2 + hf.toLp f)) (T (hf.toLp f)),
      SchwartzMap.coeFn_toLp (∂_{v} (∂_{w} (S m))) 2 volume] with x h₁ h₂
    rw [← Pi.sub_apply, ← h₁, hT m, h₂]
  filter_upwards [hae, hpt, Lp.coeFn_zero F 2 (volume : Measure E)] with x hx hx' h0
  rw [h0, Pi.zero_apply] at hx
  -- Once `‖x‖ < ns i`, `Sₘ` agrees with `u` near `x`, and so do their second derivatives.
  have hev : ∀ᶠ i in atTop, T ((Δ (S (ns i))).toLp 2 + hf.toLp f) x =
      T (hf.toLp f) x + iteratedFDeriv ℝ 2 u x ![v, w] := by
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt ‖x‖
    filter_upwards [hns.tendsto_atTop.eventually_ge_atTop m₀] with i hi
    have h : (fun y => fderiv ℝ (S (ns i)) y w) =ᶠ[𝓝 x] fun y => fderiv ℝ u y w :=
      ((hSu (ns i) x (hm₀.trans_le (by exact_mod_cast hi))).fderiv (𝕜 := ℝ)).mono fun y hy => by
        simp only [hy]
    have hw : (⇑(∂_{w} (S (ns i)) : 𝓢(E, F)) : E → F) = fun y => fderiv ℝ (S (ns i)) y w :=
      funext fun y => SchwartzMap.lineDerivOp_apply_eq_fderiv w (S (ns i)) y
    rw [← sub_eq_iff_eq_add', hx' (ns i), SchwartzMap.lineDerivOp_apply_eq_fderiv, hw,
      h.fderiv_eq, fderiv_clm_apply_const_apply
        ((hu.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x),
      iteratedFDeriv_two_apply]
    simp
  have h := tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun i hi => hi.symm)) hx
  exact eq_neg_of_add_eq_zero_left h

/-- **Second derivatives of a solution of Poisson's equation are Riesz transforms.** Let `u` be
smooth with `Δu = -f`, where `f` has compact support, and suppose that `‖x‖ ^ (d/2 - 2) ‖u x‖` and
`‖x‖ ^ (d/2 - 1) ‖Du x‖` tend to zero at infinity, `d` the dimension. Then
`D²u(v, w) = R_v R_w f` almost everywhere. -/
theorem coeFn_rieszTransform_rieszTransform_toLp_of_laplacian_eq_neg
    (hu : ContDiff ℝ ∞ u) (hΔ : Δ u = -f) (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hu₀ : Tendsto (fun x => ‖x‖ ^ ((finrank ℝ E : ℝ) / 2 - 2) * ‖u x‖) (cocompact E) (𝓝 0))
    (hu₁ : Tendsto (fun x => ‖x‖ ^ ((finrank ℝ E : ℝ) / 2 - 1) * ‖fderiv ℝ u x‖) (cocompact E)
      (𝓝 0)) (v w : E) :
    rieszTransform F v (rieszTransform F w (hf.toLp f)) =ᵐ[volume]
      fun x => iteratedFDeriv ℝ 2 u x ![v, w] := by
  rw [rieszTransform_rieszTransform_apply]
  filter_upwards [Lp.coeFn_neg (Lp.fourierMultiplierCLM F (hessianSymbolLp v w) (hf.toLp f)),
    coeFn_fourierMultiplierCLM_hessianSymbolLp_toLp_of_laplacian_eq_neg hu hΔ hf hc hu₀ hu₁ v w]
    with x h₁ h₂
  rw [h₁, Pi.neg_apply, h₂, neg_neg]

end TauCeti
