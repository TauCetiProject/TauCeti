/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Hölder continuity near solutions of the homogeneous equation (De Giorgi)

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, and let `b` be a measurable drift with `‖b‖ ≤ β`. De Giorgi's theorem with a
right-hand side or with lower-order terms is reduced, one ball at a time, to the homogeneous
equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0`: on every ball `B(x, ρ)` of radius at most `R`, a weak
solution `u` lies within `ρ^γ A` of a weak solution of the homogeneous equation on that ball, for
some `γ > 0`. This file proves De Giorgi's estimates under this hypothesis alone, whatever
supplies it.

Comparing the essential oscillation of `u` on concentric balls with that of the homogeneous
solution gives

`osc_{B(x₀, s)} u ≤ C₀ (s/ρ)^α₀ osc_{B(x₀, ρ)} u + K ρ^γ A`,

and the iteration lemma `TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` turns
this into a power law with exponent `min γ (α₀/2)`. The precise representative then converts the
power law into a Hölder bound, as for the homogeneous equation. The error is small on small balls
exactly because `γ > 0`.

The drift is not invariant under dilations, so the constants depend on a bound `σ` for `βR/λ`,
through the oscillation decay `TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_sub_drift` and
local boundedness with lower-order terms
`TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder` of the
homogeneous equation. The estimates without a drift are the case `b = 0`, `σ = 0`.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le_drift`: local boundedness of a function
  within `W` of a solution of the homogeneous equation,
  `|u| ≤ D (R^(-n/2) ‖u‖_{L²(B_R)} + W)` on `B_{R/2}`.
* `exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le_drift`: one step of oscillation
  decay, comparing the essential oscillations of such a function on two concentric balls.
* `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le_drift`: the interior
  oscillation estimate for a function within `ρ^γ A` of a homogeneous solution on every ball
  `B(x₀, ρ)`, `ρ ≤ R`.
* `exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le_drift`: the Hölder
  continuity of the precise representative of such a function.
* `exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le`,
  `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le` and
  `exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le`: the same without a drift.
  One step of oscillation decay without a drift is
  `exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le_drift` at `b = 0`, `σ = 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.22 and 8.24, and Lemma 8.23.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter III, Lemma 2.1.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

namespace PDE

/-- **Local boundedness near a solution of the homogeneous equation with a drift.** Let `n ≥ 1`
be the dimension and fix a bound `σ` for `βR/λ`. There is `D > 0`, depending only on `λ`, `Λ`,
`σ`, `n` and the normalization of `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` be measurable with `‖b‖ ≤ β` on `Ω`, let
`B(x₀, R) ⊆ Ω` with `βR ≤ σλ`, and let `u ∈ H¹(Ω)` lie within `W` of a weak solution `h ∈ H¹(B)`
of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` on `B = B(x₀, R)`, that is `|u - h| ≤ W`
almost everywhere on `B`. Then almost everywhere on `B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + W)`.

For `W = 0` this is
`TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`. -/
theorem exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le_drift [Nonempty ι] {lam Lam : ℝ}
    (σ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {beta : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R W : ℝ} {g : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ v : W1p0 mu ⟨ball x₀ R, isOpen_ball⟩ 2,
        energyFormH1 a b 0 g (v : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2) = 0) →
      (∀ᵐ x ∂mu.restrict (ball x₀ R), |W1p.value u x - W1p.value g x| ≤ W) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → beta * R ≤ σ * lam →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          W) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨D₁, hD₁, hbound⟩ :=
    exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam)
  set D₀ := D₁ * (1 + σ ^ 2) ^ Fintype.card ι
  set ω := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  refine ⟨max (√2 * D₀) (√2 * D₀ * √ω + 1), lt_max_of_lt_left (by positivity), ?_⟩
  intro Omega a b beta u x₀ R W g h ha hb hb_bound hg hug hR hball hβR
  have hW : 0 ≤ W := nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₀ hR).ne' hug
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ (hball (mem_ball_self hR)))
  -- De Giorgi's bound for the homogeneous solution `g` on `B(x₀, R/2)`, with `(βR/λ)² ≤ σ²`.
  have hgbound : ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value g x| ≤
      D₀ * R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu) := by
    filter_upwards [hbound (Omega := ⟨ball x₀ R, isOpen_ball⟩) (c := 0) (gamma := 0)
      (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
      (hb.mono_measure (Measure.restrict_mono hball le_rfl)) aestronglyMeasurable_const
      (fun x hx => hb_bound x (hball hx)) (fun _ _ => by simp) (fun _ _ => le_rfl) hg
      (subset_refl _)] with x hx
    refine hx.trans ?_
    simp only [D₀]
    gcongr ?_ * _ * _
    exact mul_le_mul_of_nonneg_left
      (Real.one_add_div_sq_pow_le _ (mul_nonneg hbeta hR.le) h.pos hβR) hD₁.le
  -- `‖g‖_{L²(B)} ≤ √2 ‖u‖_{L²(B)} + √2 W |B|^(1/2)`.
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hsqrt := TauCeti.MeasureTheory.sqrt_integral_sq_le_of_ae_abs_sub_le
    (((Lp.memLp (W1p.value u)).integrable_sq).mono_measure (Measure.restrict_mono hball le_rfl))
    hug
  rw [measureReal_restrict_apply_univ, Measure.sqrt_addHaar_real_ball mu x₀ hR,
    finrank_euclideanSpace] at hsqrt
  -- Combine: `|u| ≤ |g| + W`.
  have hR' : R ^ (-n / 2) * R ^ (n / 2) = 1 := by
    rw [← Real.rpow_add hR, neg_div, neg_add_cancel, Real.rpow_zero]
  filter_upwards [hgbound, ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (half_le_self hR.le)) hug] with x hx hxu
  set Q := R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  calc |W1p.value u x| ≤ |W1p.value g x| + |W1p.value u x - W1p.value g x| := by
        simpa using abs_add_le (W1p.value g x) (W1p.value u x - W1p.value g x)
    _ ≤ D₀ * R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu) + W := add_le_add hx hxu
    _ ≤ D₀ * R ^ (-n / 2) * (√2 * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          √2 * W * (R ^ (n / 2) * √ω)) + W := by gcongr
    _ = √2 * D₀ * Q + (√2 * D₀ * √ω + 1) * W := by
        linear_combination (√2 * D₀ * W * √ω) * hR'
    _ ≤ max (√2 * D₀) (√2 * D₀ * √ω + 1) * Q + max (√2 * D₀) (√2 * D₀ * √ω + 1) * W := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = _ := by ring

/-- **Local boundedness near a solution of the homogeneous equation.** Let `n ≥ 1` be the
dimension. There is `D > 0`, depending only on `λ`, `Λ`, `n` and the normalization of `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let `B(x₀, R) ⊆ Ω`, and let `u ∈ H¹(Ω)` lie within `W` of a weak solution `h ∈ H¹(B)` of
the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` on `B = B(x₀, R)`, that is `|u - h| ≤ W` almost
everywhere on `B`. Then almost everywhere on `B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + W)`.

This is the case `b = 0` of `TauCeti.PDE.exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le_drift`;
for `W = 0` it is `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le [Nonempty ι] {lam Lam : ℝ} :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R W : ℝ} {g : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu ⟨ball x₀ R, isOpen_ball⟩ 2,
        energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2) = 0) →
      (∀ᵐ x ∂mu.restrict (ball x₀ R), |W1p.value u x - W1p.value g x| ≤ W) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          W) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le_drift (mu := mu) (lam := lam) (Lam := Lam) 0
  exact ⟨D, hD, fun h ha hg hug hR hball => hmain (beta := 0) h ha aestronglyMeasurable_const
    (fun _ _ => by simp) hg hug hR hball (by simp)⟩

/-- **One step of oscillation decay near a solution of the homogeneous equation with a drift.**
Let `n ≥ 1` be the dimension and fix a bound `σ` for `βρ/λ`. There are `α ∈ (0, 1]` and
`C, K > 0`, depending only on `λ`, `Λ`, `σ`, `n` and the normalization of `mu`, such that the
following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b`
be measurable with `‖b‖ ≤ β` on `Ω`, let `B(x₀, ρ) ⊆ Ω` with `βρ ≤ σλ`, and let `u ∈ H¹(Ω)` be
essentially bounded on `B(x₀, ρ)` and lie within `W` of a weak solution `h ∈ H¹(B(x₀, ρ))` of the
homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` there. If `0 < s ≤ ρ`, then the essential
oscillations `osc_s` and `osc_ρ` of `u` on `B(x₀, s)` and `B(x₀, ρ)` satisfy

`osc_s ≤ C (s/ρ)^α osc_ρ + K W`.

For `W = 0` this is the oscillation decay
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_sub_drift` of the homogeneous equation. -/
theorem exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le_drift [Nonempty ι]
    {lam Lam : ℝ} (σ : ℝ) :
    ∃ α C K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {beta : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {ρ s M W : ℝ} {g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        energyFormH1 a b 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤ W) →
      0 < s → s ≤ ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → beta * ρ ≤ σ * lam →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M) →
      essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)) -
          essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)) ≤
        C * (s / ρ) ^ α *
            (essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ)) -
              essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))) +
          K * W := by
  obtain ⟨α₀, C₀, hα₀, hα₀1, hC₀, hpow⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_sub_drift (mu := mu) (lam := lam) (Lam := Lam) σ
  refine ⟨α₀, C₀, 2 * C₀ + 2, hα₀, hα₀1, hC₀, by positivity, ?_⟩
  intro Omega a b beta u x₀ ρ s M W g h ha hb hb_bound hg hug hs hsρ hball hβρ hM
  have hρ : 0 < ρ := hs.trans_le hsρ
  have hW0 : 0 ≤ W := nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₀ hρ).ne' hug
  have : (ae (mu.restrict (ball x₀ s))).NeBot :=
    ae_restrict_neBot.2 (measure_ball_pos mu x₀ hs).ne'
  set m := essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))
  set m₁ := essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))
  -- `g` lies in `[m - W, m₁ + W]` on `B(x₀, ρ)`.
  have hgI : ∀ᵐ x ∂mu.restrict (ball x₀ ρ), W1p.value g x ∈ Icc (m - W) (m₁ + W) := by
    filter_upwards [ae_le_essSup (isBoundedUnder_of_eventually_le (a := M)
        (hM.mono fun _ hx => (abs_le.1 hx).2)),
      ae_essInf_le (isBoundedUnder_of_eventually_ge (a := -M)
        (hM.mono fun _ hx => (abs_le.1 hx).1)), hug] with x hx₁ hx₂ hxg
    rw [abs_le] at hxg
    exact ⟨by linarith only [hx₂, hxg.2], by linarith only [hx₁, hxg.1]⟩
  obtain ⟨m', hm'⟩ := hpow (Omega := ⟨ball x₀ ρ, isOpen_ball⟩) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    (hb.mono_measure (Measure.restrict_mono hball le_rfl)) (fun x hx => hb_bound x (hball hx))
    hg hs hsρ (subset_refl _) hβρ hgI
  -- Hence `u` lies in an interval of length `C₀ (s/ρ)^α₀ (m₁ - m + 2W) + 2W` on `B(x₀, s)`.
  have hosc := essSup_sub_essInf_le (f := (W1p.value u : EuclideanSpace ℝ ι → ℝ))
    (ν := mu.restrict (ball x₀ s)) (m := m' - W)
    (L := C₀ * (s / ρ) ^ α₀ * (m₁ + W - (m - W)) + 2 * W) <| by
    filter_upwards [hm', ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hsρ) hug]
      with x hx hxg
    rw [abs_le] at hxg
    exact ⟨by linarith only [hx.1, hxg.1], by linarith only [hx.2, hxg.2]⟩
  have hsρ1 : C₀ * (s / ρ) ^ α₀ ≤ C₀ :=
    mul_le_of_le_one_right hC₀.le
      (Real.rpow_le_one (by positivity) ((div_le_one hρ).2 hsρ) hα₀.le)
  calc _ ≤ C₀ * (s / ρ) ^ α₀ * (m₁ + W - (m - W)) + 2 * W := hosc
    _ = C₀ * (s / ρ) ^ α₀ * (m₁ - m) + (2 * (C₀ * (s / ρ) ^ α₀) + 2) * W := by ring
    _ ≤ C₀ * (s / ρ) ^ α₀ * (m₁ - m) + (2 * C₀ + 2) * W := by gcongr

/-- **De Giorgi's interior oscillation estimate near solutions of the homogeneous equation with
a drift.** Let `n ≥ 1` be the dimension, let `γ > 0`, and fix a bound `σ` for `βR/λ`. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `σ`, `n`, `γ` and the normalization of
`mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, let `b` be measurable with `‖b‖ ≤ β` on `Ω`, let `B(x₀, R) ⊆ Ω` with `βR ≤ σλ`,
and let `u ∈ H¹(Ω)` lie within `ρ^γ A` of a weak solution of the homogeneous equation
`-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` on `B(x₀, ρ)`, for every `0 < ρ ≤ R`. If `0 < s ≤ R/2`, then almost
everywhere on `B(x₀, s)` the function `u` takes values in an interval of length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^γ A)`.

For `A = 0` this is the form of
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral_drift`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le_drift [Nonempty ι]
    {lam Lam γ : ℝ} (hγ : 0 < γ) (σ : ℝ) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {beta : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R s A : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a b 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤ ρ ^ γ * A) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * R ≤ σ * lam →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ γ * A)) := by
  obtain ⟨α₀, C₀, K, hα₀, hα₀1, hC₀, hK, hosc⟩ :=
    exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le_drift (mu := mu) (lam := lam)
      (Lam := Lam) σ
  obtain ⟨D, hD, hloc⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le_drift (mu := mu) (lam := lam) (Lam := Lam) σ
  obtain ⟨β, C, hβ, hβα, hC, hiter⟩ := exists_le_mul_rpow_of_essOsc_step hα₀ hC₀.le hK.le hD.le hγ
  refine ⟨β, C, hβ, hβα.le.trans hα₀1, hC, ?_⟩
  intro Omega a b beta u x₀ R s A h ha hb hb_bound happrox hs hsR hball hβR
  have hR : 0 < R := by linarith only [hs, hsR]
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ (hball (mem_ball_self hR)))
  obtain ⟨g₀, hg₀, hug₀⟩ := happrox R hR le_rfl
  have hA : 0 ≤ A := (mul_nonneg_iff_of_pos_left (Real.rpow_pos_of_pos hR γ)).1
    (nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₀ hR).ne' hug₀)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) :=
    ⟨_, rfl⟩
  -- Local boundedness: `|u| ≤ M₀` on `B(x₀, R/2)`.
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = D * (Q + R ^ γ * A) := ⟨_, rfl⟩
  have hM : ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤ M₀ := by
    filter_upwards [hloc h ha hb hb_bound hg₀ hug₀ hR hball hβR] with x hx
    exact hx.trans_eq (by rw [hM₀def, hQdef])
  -- The essential oscillation `φ ρ` of `u` on `B(x₀, ρ)`.
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ → ℝ, φ = fun ρ => essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ)
      (mu.restrict (ball x₀ ρ)) - essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ)
        (mu.restrict (ball x₀ ρ)) := ⟨_, rfl⟩
  have hMρ : ∀ ρ, ρ ≤ R / 2 → ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M₀ :=
    fun ρ hρ => ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρ) hM
  obtain ⟨hφ0, hmono, hφR₁⟩ := essSup_sub_essInf_nonneg_monotoneOn_ball (mu := mu) x₀
    (φ := φ) (fun ρ => by rw [hφdef]) (half_pos hR) hM
  -- One comparison step: `φ s ≤ C₀ (s/ρ)^α₀ φ ρ + K ρ^γ A` for `s ≤ ρ ≤ R / 2`.
  have hstep : ∀ s ρ, 0 < s → s ≤ ρ → ρ ≤ R / 2 →
      φ s ≤ C₀ * (s / ρ) ^ α₀ * φ ρ + K * ρ ^ γ * A := by
    intro s ρ hs hsρ hρR₁
    have hρR : ρ ≤ R := hρR₁.trans (half_le_self hR.le)
    obtain ⟨g, hg, hug⟩ := happrox ρ (hs.trans_le hsρ) hρR
    rw [hφdef, mul_assoc K]
    exact hosc h ha hb hb_bound hg hug hs hsρ ((ball_subset_ball hρR).trans hball)
      ((mul_le_mul_of_nonneg_left hρR hbeta).trans hβR) (hMρ ρ hρR₁)
  have hφs := hiter hs hsR (by rw [hQdef]; positivity) hA hmono hφ0 (hM₀def ▸ hφR₁) hstep
  obtain ⟨hb₁, hb₂⟩ :=
    isBoundedUnder_le_abs.mp (isBoundedUnder_of_eventually_le (hMρ s hsR))
  rw [← hQdef]
  rw [hφdef] at hφs
  refine ⟨essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)), ?_⟩
  filter_upwards [ae_le_essSup hb₁, ae_essInf_le hb₂] with x hx₁ hx₂
  exact ⟨hx₂, by linarith only [hφs, hx₁]⟩

/-- **De Giorgi's interior oscillation estimate near solutions of the homogeneous equation.** Let
`n ≥ 1` be the dimension and let `γ > 0`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `n`, `γ` and the normalization of `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `B(x₀, R) ⊆ Ω`, and let
`u ∈ H¹(Ω)` lie within `ρ^γ A` of a weak solution of the homogeneous equation on `B(x₀, ρ)`, for
every `0 < ρ ≤ R`. If `0 < s ≤ R/2`, then almost everywhere on `B(x₀, s)` the function `u` takes
values in an interval of length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^γ A)`.

This is the case `b = 0` of
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le_drift`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le [Nonempty ι]
    {lam Lam γ : ℝ} (hγ : 0 < γ) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R s A : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤ ρ ^ γ * A) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ γ * A)) := by
  obtain ⟨α, C, hα, hα1, hC, hmain⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le_drift (mu := mu)
      (lam := lam) (Lam := Lam) hγ 0
  exact ⟨α, C, hα, hα1, hC, fun h ha happrox hs hsR hball => hmain (beta := 0) h ha
    aestronglyMeasurable_const (fun _ _ => by simp) happrox hs hsR hball (by simp)⟩

/-- **Hölder continuity near solutions of the homogeneous equation with a drift.** Let `n ≥ 1` be
the dimension, let `γ > 0`, and fix a bound `σ` for `βR/λ`. There are `α ∈ (0, 1]` and `C > 0`,
depending only on `λ`, `Λ`, `σ`, `n`, `γ` and the normalization of the additive Haar measure `mu`,
such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let `b` be measurable with `‖b‖ ≤ β` on `Ω`, let the closed `R`-thickening of a set `K` lie
in `Ω` with `βR ≤ σλ`, and let `u ∈ H¹(Ω)` lie within `ρ^γ A` of a weak solution of the
homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` on `B(x, ρ)`, for every `x ∈ K` and every
`0 < ρ ≤ R`. Then the precise representative of `u` is Hölder continuous on `K` with exponent `α`
and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + R^γ A)`.

This is the common form of De Giorgi's theorem for equations with lower-order terms and a
right-hand side: splitting off the right-hand side on each ball supplies the hypothesis, with `γ`
the Morrey gain of the datum and `A` a multiple of its norm. -/
theorem exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le_drift [Nonempty ι]
    {lam Lam γ : ℝ} (hγ : 0 < γ) (σ : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {beta : ℝ} {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R A : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ K, ∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x ρ, isOpen_ball⟩ 2,
          energyFormH1 a b 0 g (v : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ y ∂mu.restrict (ball x ρ), |W1p.value u y - W1p.value g y| ≤ ρ ^ γ * A) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → beta * R ≤ σ * lam →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            R ^ γ * A)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C₀, hα, hα1, hC₀, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le_drift (mu := mu)
      (lam := lam) (Lam := Lam) hγ σ
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le_drift (mu := mu) (lam := lam) (Lam := Lam) σ
  lift α to ℝ≥0 using hα.le
  refine ⟨α, max C₀ (4 * D), NNReal.coe_pos.1 hα, NNReal.coe_le_one.1 hα1,
    lt_max_of_lt_left hC₀, ?_⟩
  intro Omega a b beta u K R A h ha hb hb_bound happrox hR hRK hβR
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₁, hx₁⟩
  · exact holderOnWith_empty _ _ _
  have hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (self_subset_cthickening K).trans hRK
  -- Every ball of radius `R` centred in `K` lies in `Ω`.
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  have hA : 0 ≤ A := by
    obtain ⟨g, -, hug⟩ := happrox x₁ hx₁ R hR le_rfl
    exact (mul_nonneg_iff_of_pos_left (Real.rpow_pos_of_pos hR γ)).1
      (nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₁ hR).ne' hug)
  -- The scaled norms of `u` and of the datum on such a ball are at most `N`, their values on `Ω`.
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N =
      R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) + R ^ γ * A :=
    ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hN : ∀ x ∈ K, R ^ (-(Fintype.card ι : ℝ) / 2) *
      √(∫ y in ball x R, W1p.value u y ^ 2 ∂mu) + R ^ γ * A ≤ N := fun x hx => by
    rw [hNdef]
    gcongr
    · exact ae_of_all _ fun y => sq_nonneg _
    · exact (Lp.memLp (W1p.value u)).integrable_sq
    · exact hball x hx
  have hint : ∀ x ∈ K, IntegrableAtFilter (W1p.value u) (𝓝 x) mu := fun x hx =>
    W1p.integrableAtFilter_value_of_mem u (hKΩ hx)
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (C : ℝ) = C₀ * N / R ^ (α : ℝ) / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, (M : ℝ) = D * N := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = R / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  refine (holderOnWith_preciseRepresentative (C := C) (M := M) (ρ := ρ)
    (NNReal.coe_pos.1 hα) (NNReal.coe_pos.1 (hρ ▸ half_pos hR)) hint
    (fun x hx s hs hsR => ?_) (fun x hx => ?_)).mono_const ?_
  · -- Oscillation: `u` lies in an interval of length `L ≤ 2 C s^α` on `B(x, s)`.
    rw [hρ] at hsR
    obtain ⟨m', hm'⟩ := hosc h ha hb hb_bound (happrox x hx) hs hsR (hball x hx) hβR
    have hL := Real.mul_rpow_div_mul_le_two_mul (α := (α : ℝ)) hC₀.le hs.le hR (hN x hx) hC
    refine ⟨m' + C * s ^ (α : ℝ), ?_⟩
    filter_upwards [hm'] with y hy
    rw [Real.closedBall_eq_Icc]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · -- Boundedness: `|u| ≤ D N` on `B(x, R/2)`, by local boundedness.
    rw [hρ]
    obtain ⟨g, hg, hug⟩ := happrox x hx R hR le_rfl
    filter_upwards [hbound h ha hb hb_bound hg hug hR (hball x hx) hβR] with y hy
    rw [Real.norm_eq_abs, hM]
    exact hy.trans (mul_le_mul_of_nonneg_left (hN x hx) hD.le)
  · -- The constant: `2 C = C₀ N R^(-α)` and `2 M / ρ^α = 2^(1+α) D N R^(-α) ≤ 4 D N R^(-α)`.
    rw [← hNdef]
    exact NNReal.max_two_mul_le_toNNReal hα1 hR hC₀.le hD.le hN0 hC hM hρ

/-- **Hölder continuity near solutions of the homogeneous equation.** Let `n ≥ 1` be the dimension
and let `γ > 0`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `γ` and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let the closed `R`-thickening of a
set `K` lie in `Ω`, and let `u ∈ H¹(Ω)` lie within `ρ^γ A` of a weak solution of the homogeneous
equation `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` on `B(x, ρ)`, for every `x ∈ K` and every `0 < ρ ≤ R`. Then the precise
representative of `u` is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + R^γ A)`.

This is the case `b = 0` of
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le_drift`, the common
form of De Giorgi's theorem for equations with a right-hand side. -/
theorem exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le [Nonempty ι]
    {lam Lam γ : ℝ} (hγ : 0 < γ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)} {R A : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ x ∈ K, ∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ y ∂mu.restrict (ball x ρ), |W1p.value u y - W1p.value g y| ≤ ρ ^ γ * A) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            R ^ γ * A)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C, hα, hα1, hC, hmain⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le_drift (mu := mu)
      (lam := lam) (Lam := Lam) hγ 0
  exact ⟨α, C, hα, hα1, hC, fun h ha happrox hR hRK => hmain (beta := 0) h ha
    aestronglyMeasurable_const (fun _ _ => by simp) happrox hR hRK (by simp)⟩

end PDE

end TauCeti
