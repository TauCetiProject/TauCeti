/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.LowerOrder
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.MeasureTheory.Function.EssSup

/-!
# Hölder continuity of weak solutions with lower-order terms (De Giorgi)

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, with constants
`0 < λ ≤ Λ`, let `b` be a measurable drift with `‖b‖ ≤ β` and let `c` be a measurable mass
coefficient with `|c| ≤ γ` on `Ω`. This file extends De Giorgi's theorem
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative` to weak solutions `u ∈ H¹(Ω)` of the
full divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0` in `Ω`,

that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with drift `b`
and mass `c`. The drift is not invariant under dilations, so the constants depend on a bound `σ`
for `βR/λ`. The mass term enters the Hölder constant only through the dimensionless quantity
`γR²/λ`, and the Hölder exponent does not depend on `γ`: it depends only on `λ`, `Λ`, `σ`, the
dimension and the normalization of the Haar measure.

* For a solution with `|u| ≤ M` on the balls `B(x, R)`, `x ∈ K`, and `c` of either sign, the
  precise representative of `u` is `α`-Hölder on `K` with constant
  `C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + γ R² M / λ)`
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_lowerOrder_of_ae_abs_le`).
* For `c ≥ 0`, De Giorgi's local boundedness supplies `M`, and the constant becomes
  `C R^(-α) (1 + γR²/λ) R^(-n/2) ‖u‖_{L²(Ω)}`
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_lowerOrder`). In particular the precise
  representative is continuous on `Ω` (`TauCeti.PDE.continuousOn_preciseRepresentative_lowerOrder`).

Without a drift, `b = 0` and `σ = 0`; without a mass term, `c = 0` and `γ = 0`, which is
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_drift`.

## The argument

The mass term is moved to the right-hand side: `u` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = f` with `f = -c u`
(`TauCeti.PDE.energyFormH1_eq_energyFormH1_zero_add_setIntegral`). On a ball `B(x, ρ)` on which
`|u| ≤ M` and `2βρ ≤ λ`, the datum satisfies `|f| ≤ γ M`, and splitting it off on the ball
(`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le`) leaves a solution of
`-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` within `K ρ² γ M / λ` of `u`. The smallness `2βρ ≤ λ` makes the
energy form of the drift operator coercive on `H¹₀(B(x, ρ))`, which is what Stampacchia's bound on
the ball needs; it holds on the balls of radius at most `R / (2σ + 1)`. On those balls the Hölder
theorem near solutions of the homogeneous equation
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le_drift`) applies
with the Morrey gain `2`, and passing from the radius `R / (2σ + 1)` back to `R` costs a factor
depending only on `σ` and the dimension. The sign condition `c ≥ 0` is used only through local
boundedness
(`TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder_of_nonneg`),
which bounds `|u|` on `B(x, R/2)` by `D (1 + σ²)ⁿ R^(-n/2) ‖u‖_{L²(B(x, R))}`.

## Main declarations

* `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_lowerOrder`: on a ball on which
  `|u| ≤ M` and `2βρ ≤ λ`, a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0` lies within
  `K ρ² γ M / λ` of a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0`.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_lowerOrder_of_ae_abs_le`: Hölder
  continuity of bounded weak solutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, for `c` of either
  sign.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_lowerOrder`: **De Giorgi's theorem with
  lower-order terms**, for `c ≥ 0`.
* `TauCeti.PDE.continuousOn_preciseRepresentative_lowerOrder`: continuity of weak solutions, for
  `c ≥ 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.17, 8.22 and 8.24.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- A weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0` with bounded `c` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = -c u`: the mass term moves to the right-hand side by
`TauCeti.PDE.energyFormH1_eq_energyFormH1_zero_add_setIntegral`. -/
private theorem energyFormH1_zero_mass_eq_setIntegral_neg_mul
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    {u : W1p mu Omega 2}
    (hab : MemLp (fun x => energyIntegrand (a x) (b x) 0) ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0)
    (v : W1p0 mu Omega 2) :
    energyFormH1 a b 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, -(c x * W1p.value u x) * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have h := hu v
  rw [energyFormH1_eq_energyFormH1_zero_add_setIntegral hab hc] at h
  simp only [neg_mul, integral_neg]
  linarith

/-- **Splitting off a mass term on a ball.** Let `n ≥ 1` be the dimension. There is `K > 0`,
depending only on `n` and the normalization of `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be measurable with
`‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0` with `|u| ≤ M` almost everywhere on `B = B(x₀, ρ) ⊆ Ω`, where
`2βρ ≤ λ`. Then there is a weak solution `h ∈ H¹(B)` of the homogeneous equation
`-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` with

`|u - h| ≤ K ρ² γ M / λ` almost everywhere on `B`.

The datum `-c u`, bounded by `γ M` on `B`, is split off by
`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le`. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_lowerOrder [Nonempty ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → 2 * beta * ρ ≤ lam →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a b 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ 2 * (gamma * M) / lam := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le (mu := mu)
  refine ⟨K, hK, ?_⟩
  intro Omega a b c lam Lam beta gamma u x₀ ρ M h ha hb hc hb_bound hc_bound hu hρ hball hsmall
    hM
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ (hball (mem_ball_self hρ)))
  -- The mass term moves to the right-hand side `f = -c u`, with `|f| ≤ γ M` on the ball.
  have hab := memLp_energyIntegrand_of_bounds (c := 0) (gamma := 0) h.upper_nonneg ha hb
    aestronglyMeasurable_const (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound
    (fun _ _ => by simp)
  have hcLp : MemLp c ⊤ (mu.restrict Omega) := memLp_top_of_bound hc gamma
    ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx => hc_bound x hx)
  have hfmeas : AEStronglyMeasurable (fun x => -(c x * W1p.value u x))
      (mu.restrict (ball x₀ ρ)) :=
    ((hc.mul (Lp.aestronglyMeasurable (W1p.value u))).neg).mono_measure
      (Measure.restrict_mono hball le_rfl)
  refine hsplit h ha hb hb_bound hfmeas ?_
    (energyFormH1_zero_mass_eq_setIntegral_neg_mul (by simpa using hab) hcLp hu) hρ hball hsmall
  filter_upwards [hM, ae_restrict_mem measurableSet_ball] with x hx hxB
  rw [Real.norm_eq_abs, abs_neg, abs_mul]
  exact mul_le_mul ((Real.norm_eq_abs _).symm.trans_le (hc_bound x (hball hxB))) hx
    (abs_nonneg _) hgamma

/-- Shrinking the radius from `R` to `R / N`, `N ≥ 1`, in the constant of the Hölder estimate: for
`α ≤ 1`, `n ≥ 0` and nonnegative `C, Q, K₀, P`,

`C (R/N)^(-α) ((R/N)^(-n/2) Q + (R/N)² K₀ P)
  ≤ C N^(1 + n/2) max 1 K₀ R^(-α) (R^(-n/2) Q + R² P)`. -/
private theorem mul_div_rpow_mul_add_le {C N R Q K₀ P n : ℝ} {α : ℝ≥0} (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hR : 0 < R) (hn : 0 ≤ n) (hQ : 0 ≤ Q) (hK₀ : 0 ≤ K₀)
    (hP : 0 ≤ P) :
    C * (R / N) ^ (-(α : ℝ)) * ((R / N) ^ (-n / 2) * Q + (R / N) ^ (2 : ℝ) * (K₀ * P)) ≤
      C * N ^ (1 + n / 2) * max 1 K₀ * R ^ (-(α : ℝ)) * (R ^ (-n / 2) * Q + R ^ 2 * P) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hRα := Real.div_rpow_neg_le_mul_rpow_neg (α := α) (by exact_mod_cast hα1) hN hR.le
  have hRn : (R / N) ^ (-n / 2) = N ^ (n / 2) * R ^ (-n / 2) := by
    rw [neg_div, Real.div_rpow_eq_rpow_neg_mul_rpow hR.le hN0, neg_neg]
  have hR2 : (R / N) ^ (2 : ℝ) ≤ R ^ 2 := by
    rw [Real.rpow_two]
    gcongr
    exact div_le_self hR.le hN
  have hNn : 1 ≤ N ^ (n / 2) := Real.one_le_rpow hN (by positivity)
  have hm1 : 1 ≤ max 1 K₀ := le_max_left _ _
  set Q' := R ^ (-n / 2) * Q
  have : 0 ≤ Q' := by positivity
  -- The inner sum is at most `N^(n/2) max 1 K₀ (Q' + R² P)`.
  have hinner : (R / N) ^ (-n / 2) * Q + (R / N) ^ (2 : ℝ) * (K₀ * P) ≤
      N ^ (n / 2) * max 1 K₀ * (Q' + R ^ 2 * P) := by
    rw [hRn, mul_assoc, mul_add]
    refine add_le_add ?_ ?_
    · calc N ^ (n / 2) * Q' = N ^ (n / 2) * (1 * Q') := by rw [one_mul]
        _ ≤ N ^ (n / 2) * (max 1 K₀ * Q') := by gcongr
        _ = _ := by ring
    · calc (R / N) ^ (2 : ℝ) * (K₀ * P) ≤ R ^ 2 * (max 1 K₀ * P) := by
            gcongr
            exact le_max_right _ _
        _ = 1 * (max 1 K₀ * (R ^ 2 * P)) := by ring
        _ ≤ N ^ (n / 2) * (max 1 K₀ * (R ^ 2 * P)) := by gcongr
        _ = _ := by ring
  have hNpow : N ^ (1 + n / 2) = N * N ^ (n / 2) := by
    rw [Real.rpow_add hN0, Real.rpow_one]
  calc C * (R / N) ^ (-(α : ℝ)) * ((R / N) ^ (-n / 2) * Q + (R / N) ^ (2 : ℝ) * (K₀ * P))
      ≤ C * (N * R ^ (-(α : ℝ))) * (N ^ (n / 2) * max 1 K₀ * (Q' + R ^ 2 * P)) := by
        gcongr
    _ = _ := by rw [hNpow]; ring

/-- **De Giorgi's theorem for bounded solutions with lower-order terms.** Let `n` be the
dimension, and fix a bound `σ` for `βR/λ`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `σ`, the dimension and the normalization of the additive Haar measure `mu`, such that
the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`,
let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, `c` of either sign, and let
`u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, that is `a(u, v) = 0` for
every `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with drift `b` and mass `c`. If the closed
`R`-thickening of a set `K` lies in `Ω`, `βR ≤ σλ` and `|u| ≤ M` almost everywhere on every ball
`B(x, R)`, `x ∈ K`, then the precise representative of `u` is Hölder continuous on `K` with
exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + γ R² M / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). Neither `α` nor `C` depends on `γ`. -/
theorem exists_holderOnWith_preciseRepresentative_lowerOrder_of_ae_abs_le (σ : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → beta * R ≤ σ * lam →
      (∀ x ∈ K, ∀ᵐ y ∂mu.restrict (ball x R), |W1p.value u y| ≤ M) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            gamma * R ^ 2 * M / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, zero_lt_one, le_rfl, zero_lt_one, ?_⟩
    intros
    exact Set.subsingleton_of_subsingleton.holderOnWith _ _ _
  obtain ⟨K₀, hK₀, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_lowerOrder (mu := mu)
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le_drift (mu := mu)
      (lam := lam) (Lam := Lam) (γ := 2) two_pos (1 / 2)
  -- On the balls of radius at most `R / N`, `N = 2 max σ 0 + 1`, the drift is small: `2βρ ≤ λ`.
  set N : ℝ := 2 * max σ 0 + 1
  have hN : 1 ≤ N := by have := le_max_right σ 0; simp only [N]; linarith
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  set n : ℝ := (Fintype.card ι : ℝ)
  refine ⟨α, C * N ^ (1 + n / 2) * max 1 K₀, hα, hα1,
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hN0 _)) (lt_max_of_lt_left one_pos), ?_⟩
  intro Omega a b c beta gamma u K R M h ha hb hc hb_bound hc_bound hu hR hRK hβR hM
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₁, hx₁⟩
  · exact holderOnWith_empty _ _ _
  have hlam : 0 < lam := h.pos
  have hx₁Ω : x₁ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hRK (self_subset_cthickening K hx₁)
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₁ hx₁Ω)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₁ hx₁Ω)
  have hM0 : 0 ≤ M := nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₁ hR).ne' (hM x₁ hx₁)
  have hR₁R : R / N ≤ R := div_le_self hR.le hN
  have hβR₁ : 2 * beta * (R / N) ≤ lam := by
    rw [← mul_div_assoc, div_le_iff₀ hN0]
    have := hβR.trans (mul_le_mul_of_nonneg_right (le_max_left σ 0) hlam.le)
    simp only [N]
    linarith
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  -- On every ball `B(x, ρ)`, `x ∈ K`, `ρ ≤ R / N`, the datum `-c u` is bounded by `γ M`.
  refine (hhol (A := K₀ * (gamma * M / lam)) h ha hb hb_bound (fun x hx ρ hρ hρR => ?_)
    (div_pos hR hN0) ((cthickening_mono hR₁R K).trans hRK) (by linarith)).mono_const ?_
  · have hρR' : ρ ≤ R := hρR.trans hR₁R
    obtain ⟨g, hg, hug⟩ := hsplit h ha hb hc hb_bound hc_bound hu hρ
      ((ball_subset_ball hρR').trans (hball x hx))
      ((mul_le_mul_of_nonneg_left hρR (by positivity)).trans hβR₁)
      (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR') (hM x hx))
    exact ⟨g, hg, hug.mono fun _ hy => hy.trans_eq (by rw [Real.rpow_two]; ring)⟩
  · refine Real.toNNReal_le_toNNReal ((mul_div_rpow_mul_add_le hα1 hC.le hN hR (by positivity)
      (by positivity) hK₀.le (by positivity : 0 ≤ gamma * M / lam)).trans_eq ?_)
    ring

/-- The constant of
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_lowerOrder_of_ae_abs_le` at the radius
`R / 2`, with the bound `M = D R^(-n/2) N` from local boundedness, is at most
`2 C₁ max (2^(n/2)) D R^(-α) (1 + γR²/λ) R^(-n/2) N`: here `(R/2)^(-α) ≤ 2 R^(-α)`,
`(R/2)^(-n/2) = 2^(n/2) R^(-n/2)` and `γ (R/2)² M / λ = (D/4) (γR²/λ) R^(-n/2) N`. -/
private theorem mul_half_rpow_mul_add_le {C₁ D R N gamma lam n : ℝ} {α : ℝ≥0} (hα1 : α ≤ 1)
    (hC₁ : 0 ≤ C₁) (hD : 0 ≤ D) (hR : 0 < R) (hN : 0 ≤ N) (hgamma : 0 ≤ gamma)
    (hlam : 0 < lam) :
    C₁ * (R / 2) ^ (-(α : ℝ)) * ((R / 2) ^ (-n / 2) * N +
        gamma * (R / 2) ^ 2 * (D * (R ^ (-n / 2) * N)) / lam) ≤
      2 * C₁ * max (2 ^ (n / 2)) D * R ^ (-(α : ℝ)) * (1 + gamma * R ^ 2 / lam) *
        (R ^ (-n / 2) * N) := by
  have hRα := Real.div_rpow_neg_le_mul_rpow_neg (α := α) (by exact_mod_cast hα1) one_le_two hR.le
  have hRn : (R / 2) ^ (-n / 2) = 2 ^ (n / 2) * R ^ (-n / 2) := by
    rw [neg_div, Real.div_rpow_eq_rpow_neg_mul_rpow hR.le two_pos, neg_neg]
  set Q := R ^ (-n / 2) * N
  have hQ : 0 ≤ Q := by positivity
  set T := gamma * R ^ 2 / lam
  have hT : 0 ≤ T := by positivity
  have hinner : (R / 2) ^ (-n / 2) * N + gamma * (R / 2) ^ 2 * (D * Q) / lam ≤
      max (2 ^ (n / 2)) D * ((1 + T) * Q) := by
    have hmass : gamma * (R / 2) ^ 2 * (D * Q) / lam = D / 4 * (T * Q) := by
      simp only [T]
      ring
    rw [hRn, hmass, mul_assoc, add_mul, one_mul, mul_add]
    refine add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ) ?_
    calc D / 4 * (T * Q) ≤ D * (T * Q) := by
          have := mul_nonneg hT hQ
          nlinarith
      _ ≤ max (2 ^ (n / 2)) D * (T * Q) := by gcongr; exact le_max_right _ _
  calc C₁ * (R / 2) ^ (-(α : ℝ)) * ((R / 2) ^ (-n / 2) * N + gamma * (R / 2) ^ 2 * (D * Q) / lam)
      ≤ C₁ * (2 * R ^ (-(α : ℝ))) * (max (2 ^ (n / 2)) D * ((1 + T) * Q)) := by
        gcongr
    _ = _ := by ring

/-- **De Giorgi's theorem with lower-order terms.** Let `n` be the dimension, and fix a bound `σ`
for `βR/λ`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `σ`, the dimension
and the normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be measurable with
`‖b‖ ≤ β` and `0 ≤ c ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, where `a(·, ·)` is
the energy form with drift `b` and mass `c`. If the closed `R`-thickening of a set `K` lies in `Ω`
and `βR ≤ σλ`, then the precise representative of `u` is Hölder continuous on `K` with exponent
`α` and constant

`C R^(-α) (1 + γR²/λ) R^(-n/2) ‖u‖_{L²(Ω)}`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). The sign condition enters only through De Giorgi's
local boundedness theorem; for bounded solutions and `c` of either sign, see
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_lowerOrder_of_ae_abs_le`. -/
theorem exists_holderOnWith_preciseRepresentative_lowerOrder (σ : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → beta * R ≤ σ * lam →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (1 + gamma * R ^ 2 / lam) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) *
            √(∫ y in Omega, W1p.value u y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, zero_lt_one, le_rfl, zero_lt_one, ?_⟩
    intros
    exact Set.subsingleton_of_subsingleton.holderOnWith _ _ _
  obtain ⟨α, C₁, hα, hα1, hC₁, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_lowerOrder_of_ae_abs_le (mu := mu) (lam := lam)
      (Lam := Lam) σ
  obtain ⟨D₀, hD₀, hbound⟩ :=
    exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder_of_nonneg (mu := mu)
      (lam := lam) (Lam := Lam)
  set n : ℝ := (Fintype.card ι : ℝ)
  set D := D₀ * (1 + σ ^ 2) ^ Fintype.card ι
  refine ⟨α, 2 * C₁ * max (2 ^ (n / 2)) D, hα, hα1, by positivity, ?_⟩
  intro Omega a b c beta gamma u K R h ha hb hc hb_bound hc_bound hc_nonneg hu hR hRK hβR
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₁, hx₁⟩
  · exact holderOnWith_empty _ _ _
  have hlam : 0 < lam := h.pos
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  have hx₁Ω : x₁ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hball x₁ hx₁ (mem_ball_self hR)
  have hbeta : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₁ hx₁Ω)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₁ hx₁Ω)
  set N := √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
  -- Local boundedness: `|u| ≤ M = D R^(-n/2) ‖u‖_{L²(Ω)}` on `B(x, R/2)` for `x ∈ K`, since
  -- `(βR/λ)² ≤ σ²`.
  set M := D * (R ^ (-n / 2) * N)
  have hM : ∀ x ∈ K, ∀ᵐ y ∂mu.restrict (ball x (R / 2)), |W1p.value u y| ≤ M := fun x hx => by
    filter_upwards [hbound h ha hb hc hb_bound hc_bound hc_nonneg hu (hball x hx)] with y hy
    refine hy.trans ?_
    rw [mul_assoc]
    simp only [M, D]
    gcongr _ * ?_ * (_ * ?_)
    · exact Real.one_add_div_sq_pow_le _ (mul_nonneg hbeta hR.le) hlam hβR
    · exact Real.sqrt_le_sqrt (setIntegral_mono_set (Lp.memLp (W1p.value u)).integrable_sq
        (ae_of_all _ fun y => sq_nonneg _) (hball x hx).eventuallySubset)
  have hRK' : cthickening (R / 2) K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (cthickening_mono (half_le_self hR.le) K).trans hRK
  have hβR' : beta * (R / 2) ≤ σ * lam :=
    (mul_le_mul_of_nonneg_left (half_le_self hR.le) hbeta).trans hβR
  exact (hhol h ha hb hc hb_bound hc_bound hu (half_pos hR) hRK' hβR' hM).mono_const
    (Real.toNNReal_le_toNNReal (mul_half_rpow_mul_add_le hα1 hC₁.le (by positivity) hR
      (by positivity) hgamma hlam))

/-- **Continuity of weak solutions with lower-order terms.** Let `n` be the dimension. Let `a` be
measurable and uniformly elliptic on `Ω`, let `b` be measurable and bounded, let `c` be measurable
and bounded with `c ≥ 0` on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u = 0`. Then the precise representative of `u`, which agrees with `u`
almost everywhere on `Ω`, is continuous on `Ω`. -/
theorem continuousOn_preciseRepresentative_lowerOrder
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ}
    {u : W1p mu Omega 2}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) = 0) :
    ContinuousOn (preciseRepresentative mu (W1p.value u)) Omega := by
  intro x hx
  obtain ⟨ε, hε, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  have hε2 : 0 < ε / 2 := half_pos hε
  have hK : cthickening (ε / 2) (closedBall x (ε / 2)) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := by
    rw [cthickening_closedBall hε2.le hε2.le, add_halves]
    exact hsub
  -- The drift bound `σ = β (ε/2) / λ` of the ball.
  obtain ⟨α, _C, hα, -, -, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_lowerOrder (mu := mu) (lam := lam) (Lam := Lam)
      (beta * (ε / 2) / lam)
  exact (((hhol h ha hb hc hb_bound hc_bound hc_nonneg hu hε2 hK
    (div_mul_cancel₀ _ h.pos.ne').ge).continuousOn hα).continuousAt
      (closedBall_mem_nhds x hε2)).continuousWithinAt

end PDE

end TauCeti
