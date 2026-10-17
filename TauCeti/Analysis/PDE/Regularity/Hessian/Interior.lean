/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Localization
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.Wkp.Interpolation
import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# The interior Calderón–Zygmund estimate on balls

Let `0 < n` and `1 < p < ∞`. This file proves the interior `W^{2,p}` estimate on a ball for strong
solutions of a non-divergence-form equation whose coefficients have small oscillation
(`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_eq_of_abs_sub_le`).
There are `C` and `δ > 0`, depending only on `n` and `p`, with the following property. Let `A` be a
matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, write `B_ρ` for the ball `B(x₀, ρ)`, and let
`B_R ⊆ Ω`. If `|aᵢⱼ - Aᵢⱼ| ≤ δ λ` and `|aᵢⱼ| ≤ Λ` almost everywhere on `B_R`, then every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_R` satisfies, for `r < R`,

`(R - r)² ‖D²u‖_{Lᵖ(B_r)} ≤ C ((R² / λ) ‖f‖_{Lᵖ(B_R)} + (1 + Λ / λ)² ‖u‖_{Lᵖ(B_R)})`.

In contrast to the localized estimate
`TauCeti.PDE.exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le`, the right
side involves only `f` and `u`, not the gradient of `u`. When the coefficients are continuous, every
point of `Ω` is the centre of a ball on which their oscillation is below `δ λ`, so this is the
local estimate behind the interior `W^{2,p}` estimate for continuous coefficients.

## The argument

For `0 < s < t ≤ R`, a cutoff between `B_s` and `B_t` whose first and second derivatives are
bounded by `c / (t - s)` and `c / (t - s)²` (`TauCeti.exists_forall_contDiff_cutoff_closedBall`)
gives two inequalities:

* the localized estimate on `B_t` bounds `‖D²u‖_{B_s}` by `‖f‖_{B_R}`,
  `(t - s)⁻¹ ‖∇u‖_{B_t}` and `(t - s)⁻² ‖u‖_{B_R}`;
* the interpolation inequality in `W^{2,p}_0`
  (`TauCeti.Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule`), applied to the cutoff
  of `u`, bounds `‖∇u‖_{B_s}` by `ε ‖D²u‖_{B_t}` plus lower-order terms, for every `ε > 0`.

In terms of the weighted quantities `Φ₁ = sup (R - σ) ‖∇u‖_{B_σ}` and
`Φ₂ = sup (R - σ)² ‖D²u‖_{B_σ}` over `0 < σ < R`, which are finite because `u ∈ W^{2,p}(Ω)`,
applying both inequalities at `σ` and at `(σ + R) / 2`, with `ε` a small multiple of `R - σ`, gives
`Φ₂ ≤ C (R² ‖f‖ / λ + K (Φ₁ + ‖u‖))` and `Φ₁ ≤ θ (Φ₂ + Φ₁) + C_θ ‖u‖` with `θ` as small as needed.
Absorbing `Φ₁` bounds `Φ₂`, and `(R - r)² ‖D²u‖_{B_r} ≤ Φ₂`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.11 and its proof (the weighted interior seminorms), and Theorem 7.28 (interpolation).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace Metric Module
open scoped ENNReal NNReal InnerProductSpace Gradient ContDiff

section Interpolation

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Interpolation between concentric balls.** There is a universal constant `c` such that, for
`1 ≤ p < ∞`, every `u ∈ W^{2,p}(Ω)`, every pair of radii `0 < s < t` with `B(x₀, t) ⊆ Ω`, and every
`ε > 0`,

`‖∇u‖_{Lᵖ(B_s)} ≤ ε (‖D²u‖_{Lᵖ(B_t)} + c (t - s)⁻¹ ‖∇u‖_{Lᵖ(B_t)} + c (t - s)⁻² ‖u‖_{Lᵖ(B_t)})
  + (n² / ε) ‖u‖_{Lᵖ(B_t)}`, `n = dim E`.

This is the interpolation inequality applied to a cutoff of `u` between the two balls. -/
private theorem exists_lpNorm_gradient_ball_le (hp_top : p ≠ ⊤) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Omega : Opens E} (u : Wkp mu Omega p 2) {x₀ : E} {s t : ℝ}, 0 < s →
      s < t → ball x₀ t ⊆ Omega → ∀ {ε : ℝ}, 0 < ε →
        lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ s)) ≤
          ε * (lpNorm (Wkp.iteratedGradient 1 u) p (mu.restrict (ball x₀ t)) +
            c / (t - s) *
              lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ t)) +
            c / (t - s) ^ 2 * lpNorm (Wkp.value 2 u) p (mu.restrict (ball x₀ t))) +
          finrank ℝ E ^ 2 / ε * lpNorm (Wkp.value 2 u) p (mu.restrict (ball x₀ t)) := by
  obtain ⟨c, hc0, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := E)
  refine ⟨4 * c, by positivity, fun {Omega} u x₀ s t hs hst ht ε hε => ?_⟩
  set m := (s + t) / 2 with hm
  obtain ⟨η, hη, hηr, hη1, hηts, hηg, hηh⟩ := hcut x₀ hs.le (show s < m by linarith)
  set U : Opens E := ⟨ball x₀ t, isOpen_ball⟩
  have hU : U ≤ Omega := fun x hx => ht hx
  have hsU : ball x₀ s ⊆ U := ball_subset_ball hst.le
  set v := Wkp.restrictL hU 2 u with hv
  have hcpt : HasCompactSupport η :=
    (isCompact_closedBall x₀ m).of_isClosed_subset (isClosed_tsupport η) hηts
  have hηU : tsupport η ⊆ U := hηts.trans (closedBall_subset_ball (by linarith))
  obtain ⟨w, hw0, hwv⟩ := Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul hp_top hη hcpt hηU 2 v
  have hint := Wkp.norm_iteratedGradient_lowerOrder_le_of_mem_wkp0Submodule hp_top hw0 hε
  have hηabs : ∀ x, |η x| ≤ 1 := fun x =>
    abs_le.2 ⟨by linarith [(hηr ⟨x, rfl⟩).1], (hηr ⟨x, rfl⟩).2⟩
  -- The restriction `v` of `u` to `B_t` has the same value and weak derivatives there.
  have hvg : (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v) : E → E) =ᵐ[mu.restrict U]
      Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) := by
    rw [hv, Wkp.lowerOrder_restrictL]
    exact Wkp.iteratedGradient_restrictL_ae hU 0 (Wkp.lowerOrder 1 u)
  have hnv : ‖Wkp.value 2 v‖ = lpNorm (Wkp.value 2 u) p (mu.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Wkp.value_restrictL_ae hU 2 u), toReal_eLpNorm]
    rfl
  have hngv : ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ =
      lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae hvg, toReal_eLpNorm]
    rfl
  have hnHv : ‖Wkp.iteratedGradient 1 v‖ =
      lpNorm (Wkp.iteratedGradient 1 u) p (mu.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Wkp.iteratedGradient_restrictL_ae hU 1 u), toReal_eLpNorm]
    rfl
  -- On `B_s` the cutoff is one, so `∇w = ∇u` there.
  have hwg := Wkp.iteratedGradient_zero_ae_eq_of_value_ae_eq_mul (u := Wkp.lowerOrder 1 v)
    (w := Wkp.lowerOrder 1 w) hη (by simpa only [Wkp.value_succ] using hwv)
  have hgs : (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) : E → E) =ᵐ[mu.restrict (ball x₀ s)]
      Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsU hvg,
      ae_restrict_of_ae_restrict_of_subset hsU hwg, ae_restrict_mem measurableSet_ball]
      with x h1 h2 hx
    have hev : η =ᶠ[nhds x] fun _ => 1 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy =>
        hη1 (ball_subset_closedBall hy)
    rw [h2, hη1 (ball_subset_closedBall hx), hev.gradient_eq, gradient_fun_const, h1]
    simp
  have hstep1 : lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (mu.restrict (ball x₀ s)) ≤
      ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w)‖ := by
    rw [← toReal_eLpNorm, eLpNorm_congr_ae hgs, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsU le_rfl))
  -- The weak Hessian of `w = η v` is `η D²v` plus the Leibniz remainder.
  set M₁ := c / (m - s)
  set M₂ := c / (m - s) ^ 2
  have hM₁0 : 0 ≤ M₁ := div_nonneg hc0 (by linarith)
  have hM₂0 : 0 ≤ M₂ := div_nonneg hc0 (by positivity)
  have hD := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hη hwv
  have hηH : MemLp (fun x => η x • Wkp.iteratedGradient 1 v x) p (mu.restrict U) :=
    (hη.continuous.memLp_top_of_hasCompactSupport hcpt (mu.restrict U)).smul (Lp.memLp _)
  set TL := Wkp.iteratedGradient 1 w - hηH.toLp _ with hTL_def
  have hTL : ‖TL‖ ≤ 2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ +
      M₂ * ‖Wkp.value 2 v‖ := by
    refine TauCeti.Lp.norm_le_add_of_ae_norm_le (by positivity) hM₂0 ?_
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 w) (hηH.toLp _), hD,
      hηH.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, add_assoc, add_assoc, add_sub_cancel_left, ← add_assoc]
    refine (norm_leibnizRemainder_le η _ _ x).trans ?_
    gcongr
    · exact hηg x
    · exact hηh x
  have hηHn : ‖hηH.toLp _‖ ≤ ‖Wkp.iteratedGradient 1 v‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hηH.coeFn_toLp] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηabs x)
  have hstep2 : ‖Wkp.iteratedGradient 1 w‖ ≤ ‖Wkp.iteratedGradient 1 v‖ +
      (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ + M₂ * ‖Wkp.value 2 v‖) := by
    rw [show Wkp.iteratedGradient 1 w = hηH.toLp _ + TL by rw [hTL_def, add_sub_cancel]]
    exact (norm_add_le _ _).trans (add_le_add hηHn hTL)
  have hstep3 : ‖Wkp.value 2 w‖ ≤ ‖Wkp.value 2 v‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hwv] with x hx
    rw [hx, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηabs x)
  have hms : m - s = (t - s) / 2 := by rw [hm]; ring
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  have hm1 : 2 * M₁ = 4 * c / (t - s) := by
    simp only [M₁, hms]
    field_simp
    ring
  have hm2 : M₂ = 4 * c / (t - s) ^ 2 := by
    simp only [M₂, hms]
    field_simp
    ring
  rw [hm1, hm2, hngv, hnv, hnHv] at hstep2
  rw [hnv] at hstep3
  calc _ ≤ _ := hstep1
    _ ≤ _ := hint
    _ ≤ _ := by
        gcongr
        linarith

end Interpolation

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The localized estimate between concentric balls.** For `0 < s < t ≤ R`, applying the
localized Calderón–Zygmund estimate on `B_t` to a cutoff between `B_s` and `B_t` bounds `D²u` on
`B_s` by `f` and `u` on `B_R` and by `∇u` on `B_t`, with the explicit dependence on `t - s` coming
from the derivatives of the cutoff. -/
private theorem exists_lpNorm_iteratedGradient_ball_le_of_lt (hn : 0 < n) (hp : 1 < p)
    (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ},
      0 < lam → (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin n))} {x₀ : EuclideanSpace ℝ (Fin n)} {R : ℝ},
        ball x₀ R ⊆ Omega →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {ε Λ : ℝ},
        AEStronglyMeasurable a (volume.restrict (ball x₀ R)) → ε ≤ δ * lam →
        (∀ᵐ x, x ∈ ball x₀ R → ∀ i j, |a x i j - A i j| ≤ ε) → 0 ≤ Λ →
        (∀ᵐ x, x ∈ ball x₀ R → ∀ i j, |a x i j| ≤ Λ) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
        {f : EuclideanSpace ℝ (Fin n) → ℝ}, MemLp f p (volume.restrict (ball x₀ R)) →
        (∀ᵐ x ∂(volume.restrict (ball x₀ R)),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ = f x) →
      ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
        lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ s)) ≤
          C / lam * lpNorm f p (volume.restrict (ball x₀ R)) +
            (C / lam * n ^ 2 * Λ + 1) * (c / (t - s) *
              lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p
                (volume.restrict (ball x₀ t)) +
              c / (t - s) ^ 2 * lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R))) := by
  obtain ⟨C, δ, hδ, hloc⟩ :=
    exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le hn hp hp_top
  obtain ⟨c, hc0, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ (Fin n))
  refine ⟨C, δ, hδ, 4 * c, by positivity, fun {A lam} hlam hA {Omega x₀ R} hR {a ε Λ} ha hε
    haA hΛ haΛ u f hf heq s t hs hst htR => ?_⟩
  set m := (s + t) / 2 with hm
  obtain ⟨ζ, hζ, hζr, hζ1, hζts, hζg, hζh⟩ := hcut x₀ hs.le (show s < m by linarith)
  set U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨ball x₀ t, isOpen_ball⟩
  have hUR : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball x₀ R := ball_subset_ball htR
  have hU : U ≤ Omega := fun x hx => hR (hUR hx)
  have hsU : ball x₀ s ⊆ U := ball_subset_ball hst.le
  set v := Wkp.restrictL hU 2 u with hv
  have hcpt : HasCompactSupport ζ :=
    (isCompact_closedBall x₀ m).of_isClosed_subset (isClosed_tsupport ζ) hζts
  have hζU : tsupport ζ ⊆ U := hζts.trans (closedBall_subset_ball (by linarith))
  have hζabs : ∀ x, |ζ x| ≤ 1 := fun x =>
    abs_le.2 ⟨by linarith [(hζr ⟨x, rfl⟩).1], (hζr ⟨x, rfl⟩).2⟩
  have hft : MemLp f p (volume.restrict U) := hf.mono_measure (Measure.restrict_mono hUR le_rfl)
  -- The localized estimate for the restriction `v` of `u` to `B_t`.
  have hveq : ∀ᵐ x ∂(volume.restrict (U : Set (EuclideanSpace ℝ (Fin n)))),
      ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 v x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ = hft.toLp f x := by
    filter_upwards [Wkp.iteratedGradient_restrictL_ae hU 1 u, hft.coeFn_toLp,
      ae_restrict_of_ae_restrict_of_subset hUR heq] with x h1 h2 h3
    rw [h1, h2, h3]
  have key := hloc hlam hA hζ hcpt hζU hζg hζh (ha.mono_measure (Measure.restrict_mono hUR le_rfl))
    hε (haA.mono fun x hx hxζ => hx (hUR (hζU hxζ))) hΛ
    (haΛ.mono fun x hx hxζ => hx (hUR (hζU hxζ))) v (hft.toLp f) hveq
  -- Compare each term of the localized estimate with the norms on balls.
  have hζH : MemLp (fun x => ζ x • Wkp.iteratedGradient 1 v x) p (volume.restrict U) :=
    (hζ.continuous.memLp_top_of_hasCompactSupport hcpt _).smul (Lp.memLp _)
  have hlow : lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ s)) ≤
      lpNorm (fun x => ζ x • Wkp.iteratedGradient 1 v x) p (volume.restrict U) := by
    have hae : (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict
        (ball x₀ s)] fun x => ζ x • Wkp.iteratedGradient 1 v x := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsU
        (Wkp.iteratedGradient_restrictL_ae hU 1 u), ae_restrict_mem measurableSet_ball]
        with x h1 hx
      rw [hζ1 (ball_subset_closedBall hx), h1, Pi.one_apply, one_smul]
    rw [← toReal_eLpNorm, eLpNorm_congr_ae hae]
    exact ENNReal.toReal_mono hζH.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsU le_rfl))
  have hfb : lpNorm (fun x => ζ x * hft.toLp f x) p (volume.restrict U) ≤
      lpNorm f p (volume.restrict (ball x₀ R)) := by
    refine ENNReal.toReal_mono hf.eLpNorm_ne_top ((eLpNorm_mono_ae
      (hζ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) ?_).trans
      (eLpNorm_mono_measure _ (Measure.restrict_mono hUR le_rfl)))
    filter_upwards [hft.coeFn_toLp] with x hx
    rw [Pi.mul_apply, hx, norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hζabs x)
  have hng : ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 v)‖ =
      lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (volume.restrict (ball x₀ t)) := by
    rw [Lp.norm_def, hv, Wkp.lowerOrder_restrictL,
      eLpNorm_congr_ae (Wkp.iteratedGradient_restrictL_ae hU 0 (Wkp.lowerOrder 1 u)),
      toReal_eLpNorm]
    rfl
  have hnv : ‖Wkp.value 2 v‖ ≤ lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R)) := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Wkp.value_restrictL_ae hU 2 u)]
    exact ENNReal.toReal_mono
      ((Lp.memLp (Wkp.value 2 u)).mono_measure (Measure.restrict_mono hR le_rfl)).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hUR le_rfl))
  have hms : m - s = (t - s) / 2 := by rw [hm]; ring
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  have hm1 : 2 * (c / (m - s)) = 4 * c / (t - s) := by
    rw [hms]
    field_simp
    ring
  have hm2 : c / (m - s) ^ 2 = 4 * c / (t - s) ^ 2 := by
    rw [hms]
    field_simp
    ring
  rw [hm1, hm2, hng] at key
  calc _ ≤ _ := hlow
    _ ≤ _ := key
    _ ≤ _ := by gcongr

/-- Where the coefficients are bounded, the right side of `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` lies in `Lᵖ`. -/
private theorem memLp_of_ae_sum_mul_inner_eq {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSm : MeasurableSet S) (hS : S ⊆ Omega)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
    {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {Λ : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict S)) (haΛ : ∀ᵐ x, x ∈ S → ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (heq : ∀ᵐ x ∂(volume.restrict S),
      ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ = f x) :
    MemLp f p (volume.restrict S) := by
  have hH : MemLp (Wkp.iteratedGradient 1 u) p (volume.restrict S) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hS le_rfl)
  have hmeas : AEStronglyMeasurable (fun x => ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ)
      (volume.restrict S) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable ha).mul
          (((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i 1)).continuous
            |>.comp_aestronglyMeasurable hH.aestronglyMeasurable).inner aestronglyMeasurable_const)
  refine (hH.of_le_mul (c := n ^ 2 * Λ) hmeas ?_).ae_eq heq
  filter_upwards [(ae_restrict_iff' hSm).2 haΛ] with x hx
  rw [← Matrix.contraction_apply, Real.norm_eq_abs]
  exact Matrix.abs_contraction_le hx _

/-- The arithmetic of the absorption. If `θ (16 K c_A + 4 c_B + 1) = 1` and the weighted
suprema satisfy `Φ₂ ≤ P + 4 K c_A (Φ₁ + z)` and
`Φ₁ ≤ 2 θ Φ₂ + 2 θ c_B Φ₁ + (2 θ c_B + 2 N / θ) z`, then `Φ₁` can be absorbed and `Φ₂` is bounded
by `P` and `z` alone. -/
private theorem le_two_mul_add_mul_sq_mul_of_le_of_le {Φ₁ Φ₂ P z K cA cB N θ : ℝ}
    (hΦ₁0 : 0 ≤ Φ₁) (hz0 : 0 ≤ z) (hP0 : 0 ≤ P) (hK1 : 1 ≤ K) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hN : 0 ≤ N) (hθ0 : 0 < θ) (hθ : θ * (16 * K * cA + 4 * cB + 1) = 1)
    (hΦ₂ : Φ₂ ≤ P + 4 * K * cA * (Φ₁ + z))
    (hΦ₁ : Φ₁ ≤ 2 * θ * Φ₂ + 2 * θ * cB * Φ₁ + (2 * θ * cB + 2 * N / θ) * z) :
    Φ₂ ≤ 2 * P + (8 * cA + 256 * cA ^ 2 * N + 16 * cA * N * (4 * cB + 1)) * K ^ 2 * z := by
  have hNθ : N / θ = N * (16 * K * cA + 4 * cB + 1) := by
    rw [div_eq_iff hθ0.ne']
    linear_combination (-N) * hθ
  have hα : θ * (16 * K * cA + 4 * cB) ≤ 1 := by nlinarith
  have h2θ : 2 * θ * Φ₂ ≤ 2 * θ * (P + 4 * K * cA * (Φ₁ + z)) :=
    mul_le_mul_of_nonneg_left hΦ₂ (by positivity)
  have hαΦ := mul_le_mul_of_nonneg_right hα hΦ₁0
  have hαz := mul_le_mul_of_nonneg_right hα hz0
  have hΦ₁' : Φ₁ ≤ 4 * θ * P + z + 4 * (N / θ) * z := by
    rw [mul_div_assoc] at hΦ₁
    linarith
  rw [hNθ] at hΦ₁'
  have h16 : 16 * K * cA * θ ≤ 1 := by nlinarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left hΦ₁' (by positivity : (0 : ℝ) ≤ 4 * K * cA)
  have h5 := mul_le_mul_of_nonneg_right h16 hP0
  have h6 := mul_le_mul_of_nonneg_right hKK
    (by positivity : (0 : ℝ) ≤ (8 * cA + 16 * cA * N * (4 * cB + 1)) * z)
  nlinarith

/-- **Absorption over concentric balls.** Let `0 < r < R`, and let `k`, `h`, `y` be nonnegative
functions of the radius, thought of as the norms of `D²u`, `∇u` and `u` on `B_σ`, with `k` and
`h` bounded on `(0, R)` by their values at `R` and `y ≤ z` there. Suppose that for `0 < s < t ≤ R`

`k(s) ≤ a₀ + K (c_A (t - s)⁻¹ h(t) + c_A (t - s)⁻² z)` and
`h(s) ≤ η (k(t) + c_B (t - s)⁻¹ h(t) + c_B (t - s)⁻² y(t)) + (N / η) y(t)` for all `η > 0`.

Then `(R - r)² k(r)` is bounded by `R² a₀` and `z` alone. The proof absorbs the weighted suprema
`sup (R - σ) h(σ)` and `sup (R - σ)² k(σ)` over `0 < σ < R`, applying both inequalities at `σ` and
the midpoint `(σ + R) / 2`. -/
private theorem sq_mul_le_of_forall_le {R z a₀ K cA cB N : ℝ} {k h y : ℝ → ℝ} (hR0 : 0 < R)
    (hz0 : 0 ≤ z) (ha₀ : 0 ≤ a₀) (hK1 : 1 ≤ K) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hN : 0 ≤ N)
    (hk0 : ∀ σ, 0 ≤ k σ) (hh0 : ∀ σ, 0 ≤ h σ) (hkR : ∀ σ ∈ Set.Ioo 0 R, k σ ≤ k R)
    (hhR : ∀ σ ∈ Set.Ioo 0 R, h σ ≤ h R) (hyz : ∀ σ ∈ Set.Ioo 0 R, y σ ≤ z)
    (hA : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
      k s ≤ a₀ + K * (cA / (t - s) * h t + cA / (t - s) ^ 2 * z))
    (hB : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R → ∀ {η : ℝ}, 0 < η →
      h s ≤ η * (k t + cB / (t - s) * h t + cB / (t - s) ^ 2 * y t) + N / η * y t)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    (R - r) ^ 2 * k r ≤
      2 * (R ^ 2 * a₀) + (8 * cA + 256 * cA ^ 2 * N + 16 * cA * N * (4 * cB + 1)) * K ^ 2 * z := by
  -- The weighted suprema `Φ₁ = sup (R - σ) h(σ)` and `Φ₂ = sup (R - σ)² k(σ)` over `0 < σ < R`.
  set I := Set.Ioo (0 : ℝ) R
  have hI : R / 2 ∈ I := ⟨by positivity, by linarith⟩
  have hbdd₁ : BddAbove ((fun σ => (R - σ) * h σ) '' I) := ⟨R * h R, by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mul_le_mul (by linarith [hσ.1]) (hhR σ hσ) (hh0 σ) hR0.le⟩
  have hbdd₂ : BddAbove ((fun σ => (R - σ) ^ 2 * k σ) '' I) := ⟨R ^ 2 * k R, by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mul_le_mul (pow_le_pow_left₀ (by linarith [hσ.2]) (by linarith [hσ.1]) 2)
      (hkR σ hσ) (hk0 σ) (by positivity)⟩
  set Φ₁ := sSup ((fun σ => (R - σ) * h σ) '' I)
  set Φ₂ := sSup ((fun σ => (R - σ) ^ 2 * k σ) '' I)
  have hle₁ : ∀ σ ∈ I, (R - σ) * h σ ≤ Φ₁ := fun σ hσ => le_csSup hbdd₁ ⟨σ, hσ, rfl⟩
  have hle₂ : ∀ σ ∈ I, (R - σ) ^ 2 * k σ ≤ Φ₂ := fun σ hσ => le_csSup hbdd₂ ⟨σ, hσ, rfl⟩
  have hΦ₁0 : 0 ≤ Φ₁ := (mul_nonneg (by linarith) (hh0 _)).trans (hle₁ _ hI)
  have hmid : ∀ σ ∈ I, (σ + R) / 2 ∈ I ∧ σ < (σ + R) / 2 := fun σ hσ =>
    ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, by linarith [hσ.2]⟩
  -- Step (A) at `σ` and the midpoint `σ' = (σ + R) / 2` bounds `Φ₂` by `Φ₁`.
  have hΦ₂ : Φ₂ ≤ R ^ 2 * a₀ + 4 * K * cA * (Φ₁ + z) := by
    refine csSup_le ⟨_, Set.mem_image_of_mem _ hI⟩ ?_
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨hσ', hσσ'⟩ := hmid σ hσ
    set d := (R - σ) / 2 with hd
    have hd0 : 0 < d := by linarith [hσ.2]
    have hstep := hA hσ.1 hσσ' hσ'.2.le
    have h1 := hle₁ _ hσ'
    rw [show (σ + R) / 2 - σ = d by rw [hd]; ring] at hstep
    rw [show R - (σ + R) / 2 = d by rw [hd]; ring] at h1
    have hRσ : R - σ = 2 * d := by rw [hd]; ring
    calc (R - σ) ^ 2 * k σ
        ≤ (R - σ) ^ 2 * (a₀ + K * (cA / d * h ((σ + R) / 2) + cA / d ^ 2 * z)) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
      _ = (R - σ) ^ 2 * a₀ + 4 * K * cA * (d * h ((σ + R) / 2)) +
            4 * K * cA * z := by
          rw [hRσ]
          field_simp
          ring
      _ ≤ R ^ 2 * a₀ + 4 * K * cA * Φ₁ + 4 * K * cA * z := by
          gcongr
          · linarith [hσ.2]
          · linarith [hσ.1]
      _ = _ := by ring
  -- Step (B) with `η = θ (R - σ) / 2` bounds `Φ₁` by a small multiple of `Φ₂` and of itself.
  set θ := 1 / (16 * K * cA + 4 * cB + 1) with hθ
  have hθ0 : 0 < θ := by positivity
  have hΦ₁ : Φ₁ ≤ 2 * θ * Φ₂ + 2 * θ * cB * Φ₁ + (2 * θ * cB + 2 * N / θ) * z := by
    refine csSup_le ⟨_, Set.mem_image_of_mem _ hI⟩ ?_
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨hσ', hσσ'⟩ := hmid σ hσ
    set d := (R - σ) / 2 with hd
    have hd0 : 0 < d := by linarith [hσ.2]
    have hstep := hB hσ.1 hσσ' hσ'.2.le (η := θ * d) (by positivity)
    have h1 := hle₁ _ hσ'
    have h2 := hle₂ _ hσ'
    rw [show (σ + R) / 2 - σ = d by rw [hd]; ring] at hstep
    rw [show R - (σ + R) / 2 = d by rw [hd]; ring] at h1 h2
    have hyz' : y ((σ + R) / 2) ≤ z := hyz _ hσ'
    have hRσ : R - σ = 2 * d := by rw [hd]; ring
    calc (R - σ) * h σ
        ≤ (R - σ) * (θ * d * (k ((σ + R) / 2) + cB / d * h ((σ + R) / 2) +
            cB / d ^ 2 * y ((σ + R) / 2)) + N / (θ * d) * y ((σ + R) / 2)) :=
          mul_le_mul_of_nonneg_left hstep (by linarith [hσ.2])
      _ = 2 * θ * (d ^ 2 * k ((σ + R) / 2)) + 2 * θ * cB * (d * h ((σ + R) / 2)) +
            (2 * θ * cB + 2 * N / θ) * y ((σ + R) / 2) := by
          rw [hRσ]
          field_simp
          ring
      _ ≤ _ := by gcongr
  -- Absorbing `Φ₁`, then bounding `Φ₂`.
  have hθeq : θ * (16 * K * cA + 4 * cB + 1) = 1 := by
    rw [hθ]
    exact one_div_mul_cancel (by positivity)
  exact (hle₂ r ⟨hr, hrR⟩).trans
    (le_two_mul_add_mul_sq_mul_of_le_of_le hΦ₁0 hz0 (by positivity) hK1 hcA hcB hN hθ0 hθeq hΦ₂ hΦ₁)

/-- **The interior Calderón–Zygmund estimate on balls for coefficients of small oscillation.**
Let `0 < n` and `1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `n` and `p`,
with the following property. Let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `Ω` be
open, and let `B_ρ` denote the ball `B(x₀, ρ)`. Let `r < R` with `B_R ⊆ Ω`, and let `a` be a
measurable matrix-valued coefficient with `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε` and `|aᵢⱼ(x)| ≤ Λ` for almost
every `x ∈ B_R`, where `ε ≤ δ λ` and `0 ≤ Λ`. Then every `u ∈ W^{2,p}(Ω)` with
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_R` satisfies

`(R - r)² ‖D²u‖_{Lᵖ(B_r)} ≤ C ((R² / λ) ‖f‖_{Lᵖ(B_R)} + (1 + Λ / λ)² ‖u‖_{Lᵖ(B_R)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No boundary condition on `u`
and no regularity of `a` beyond the oscillation bound are assumed, and `f` is not assumed to be in
`Lᵖ`: the equation and the coefficient bound force it. Unlike
`TauCeti.PDE.exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le`, the right
side does not involve the gradient of `u`. -/
theorem exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_eq_of_abs_sub_le (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin n))} {x₀ : EuclideanSpace ℝ (Fin n)} {r R : ℝ},
        r < R → ball x₀ R ⊆ Omega →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {ε Λ : ℝ},
        AEStronglyMeasurable a (volume.restrict (ball x₀ R)) → ε ≤ δ * lam →
        (∀ᵐ x, x ∈ ball x₀ R → ∀ i j, |a x i j - A i j| ≤ ε) → 0 ≤ Λ →
        (∀ᵐ x, x ∈ ball x₀ R → ∀ i j, |a x i j| ≤ Λ) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
        (f : EuclideanSpace ℝ (Fin n) → ℝ),
        (∀ᵐ x ∂(volume.restrict (ball x₀ R)),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ = f x) →
        (R - r) ^ 2 * lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ r)) ≤
          C * (R ^ 2 / lam * lpNorm f p (volume.restrict (ball x₀ R)) +
            (1 + Λ / lam) ^ 2 * lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R))) := by
  obtain ⟨C, δ, hδ, cA, hcA, hstepA⟩ := exists_lpNorm_iteratedGradient_ball_le_of_lt hn hp hp_top
  obtain ⟨cB, hcB, hstepB⟩ :=
    exists_lpNorm_gradient_ball_le (E := EuclideanSpace ℝ (Fin n)) (mu := volume) hp_top
  set C₂ : ℝ := 8 * cA + 256 * cA ^ 2 * n ^ 2 + 16 * cA * n ^ 2 * (4 * cB + 1)
  refine ⟨Real.toNNReal (2 * C + C₂ * (C * n ^ 2 + 1) ^ 2), δ, hδ, fun {A lam} hlam hA
    {Omega x₀ r R} hrR hR {a ε Λ} ha hε haA hΛ haΛ u f heq => ?_⟩
  set F := lpNorm f p (volume.restrict (ball x₀ R))
  set z := lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R))
  set K := C / lam * n ^ 2 * Λ + 1 with hK
  have hF0 : 0 ≤ F := lpNorm_nonneg
  have hz0 : 0 ≤ z := lpNorm_nonneg
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hCfin : ((2 * C + C₂ * (C * n ^ 2 + 1) ^ 2).toNNReal : ℝ) =
      2 * C + C₂ * (C * n ^ 2 + 1) ^ 2 := Real.coe_toNNReal _ (by positivity)
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, Measure.restrict_empty, lpNorm_measure_zero, mul_zero, hCfin]
    positivity
  have hR0 : 0 < R := hr.trans hrR
  have hf := memLp_of_ae_sum_mul_inner_eq measurableSet_ball hR u ha haΛ heq
  -- The norms of `D²u`, `∇u` and `u` on the ball `B_σ`, nondecreasing in `σ ≤ R`.
  set k : ℝ → ℝ := fun σ => lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ σ))
  set h : ℝ → ℝ := fun σ =>
    lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p (volume.restrict (ball x₀ σ))
  set y : ℝ → ℝ := fun σ => lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ σ))
  have hmono : ∀ {G : Type} [NormedAddCommGroup G]
      (g : Lp G p (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n))))) {σ : ℝ}, σ ≤ R →
      lpNorm g p (volume.restrict (ball x₀ σ)) ≤ lpNorm g p (volume.restrict (ball x₀ R)) :=
    fun g σ hσ => ENNReal.toReal_mono
      ((Lp.memLp g).mono_measure (Measure.restrict_mono hR le_rfl)).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball hσ) le_rfl))
  -- The two steps between concentric balls, in this notation.
  have hA' : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
      k s ≤ C / lam * F + K * (cA / (t - s) * h t + cA / (t - s) ^ 2 * z) :=
    fun hs hst htR => hstepA hlam hA hR ha hε haA hΛ haΛ u hf heq hs hst htR
  have hB' : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R → ∀ {η : ℝ}, 0 < η →
      h s ≤ η * (k t + cB / (t - s) * h t + cB / (t - s) ^ 2 * y t) + n ^ 2 / η * y t :=
    fun {s t} hs hst htR {η} hη => by
      simpa only [finrank_euclideanSpace_fin] using
        hstepB u hs hst ((ball_subset_ball htR).trans hR) hη
  have hK1 : 1 ≤ K := le_add_of_nonneg_left (by positivity)
  have hΦ := sq_mul_le_of_forall_le (k := k) (h := h) (y := y) hR0 hz0
    (by positivity : 0 ≤ C / lam * F) hK1 hcA hcB (by positivity : (0 : ℝ) ≤ n ^ 2)
    (fun _ => lpNorm_nonneg) (fun _ => lpNorm_nonneg)
    (fun σ hσ => hmono (Wkp.iteratedGradient 1 u) hσ.2.le)
    (fun σ hσ => hmono (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) hσ.2.le)
    (fun σ hσ => hmono (Wkp.value 2 u) hσ.2.le) hA' hB' hr hrR
  -- The constants: `K ≤ (C n² + 1) (1 + Λ / λ)`.
  have hKle : K ^ 2 ≤ (C * n ^ 2 + 1) ^ 2 * (1 + Λ / lam) ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have hK' : K = C * n ^ 2 * (Λ / lam) + 1 := by rw [hK]; ring
    have h1 : 0 ≤ C * (n : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ Λ / lam := div_nonneg hΛ hlam.le
    rw [hK']
    nlinarith
  set X := R ^ 2 / lam * F with hX
  set Y := (1 + Λ / lam) ^ 2 * z with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  calc (R - r) ^ 2 * k r ≤ 2 * (R ^ 2 * (C / lam * F)) + C₂ * K ^ 2 * z := hΦ
    _ ≤ 2 * C * X + C₂ * (C * n ^ 2 + 1) ^ 2 * Y := by
        have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKle hz0) hC₂0
        rw [show R ^ 2 * (C / lam * F) = C * X by rw [hX]; ring, hY]
        linarith
    _ ≤ _ := by
        rw [hCfin, show (2 * C + C₂ * (C * n ^ 2 + 1) ^ 2) * (X + Y) =
          2 * C * X + C₂ * (C * n ^ 2 + 1) ^ 2 * Y + (2 * C * Y + C₂ * (C * n ^ 2 + 1) ^ 2 * X)
          by ring]
        have : 0 ≤ 2 * C * Y + C₂ * (C * n ^ 2 + 1) ^ 2 * X :=
          add_nonneg (mul_nonneg (mul_nonneg zero_le_two C.2) hY0)
            (mul_nonneg (mul_nonneg hC₂0 (sq_nonneg _)) hX0)
        linarith

end PDE

end TauCeti
