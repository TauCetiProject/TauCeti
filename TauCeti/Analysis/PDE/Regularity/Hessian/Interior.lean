/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Localization
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.SpecificLimits.Absorption
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
* the interpolation inequality between concentric balls
  (`TauCeti.Wkp.exists_lpNorm_gradient_ball_le`) bounds `‖∇u‖_{B_s}` by `ε ‖D²u‖_{B_t}` plus
  lower-order terms, for every `ε > 0`.

In terms of the weighted quantities `Φ₁ = sup (R - σ) ‖∇u‖_{B_σ}` and
`Φ₂ = sup (R - σ)² ‖D²u‖_{B_σ}` over `0 < σ < R`, which are finite because `u ∈ W^{2,p}(Ω)`,
applying both inequalities at `σ` and at `(σ + R) / 2`, with `ε` a small multiple of `R - σ`, gives
`Φ₂ ≤ C (R² ‖f‖ / λ + K (Φ₁ + ‖u‖))` and `Φ₁ ≤ θ (Φ₂ + Φ₁) + C_θ ‖u‖` with `θ` as small as needed.
Absorbing `Φ₁` bounds `Φ₂`, and `(R - r)² ‖D²u‖_{B_r} ≤ Φ₂`; this real-variable step is
`TauCeti.sq_mul_le_of_forall_le`.

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
    Wkp.exists_lpNorm_gradient_ball_le (E := EuclideanSpace ℝ (Fin n)) (mu := volume) hp_top
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
