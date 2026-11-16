/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness.LowerOrder
import TauCeti.MeasureTheory.Function.EssSup

/-!
# Hölder continuity of weak solutions with a mass term (De Giorgi)

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, with constants
`0 < λ ≤ Λ`, and let `c` be a measurable mass coefficient with `|c| ≤ γ` on `Ω`. This file extends
De Giorgi's theorem `TauCeti.PDE.exists_holderOnWith_preciseRepresentative` to weak solutions
`u ∈ H¹(Ω)` of

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0` in `Ω`,

that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with mass `c` and
no drift. The mass term enters the Hölder constant only through the dimensionless quantity
`γR²/λ`, and the Hölder exponent does not depend on `γ` at all: it depends only on `λ`, `Λ`, the
dimension and the normalization of the Haar measure, as for `c = 0`.

* For a solution with `|u| ≤ M` on the balls `B(x, R)`, `x ∈ K`, and `c` of either sign, the
  precise representative of `u` is `α`-Hölder on `K` with constant
  `C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + γ R² M / λ)`
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_mass_of_ae_abs_le`).
* For `c ≥ 0`, De Giorgi's local boundedness supplies `M`, and the constant becomes
  `C R^(-α) (1 + γR²/λ) R^(-n/2) ‖u‖_{L²(Ω)}`
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_mass`). In particular the precise
  representative is continuous on `Ω` (`TauCeti.PDE.continuousOn_preciseRepresentative_mass`).

## The argument

The mass term is moved to the right-hand side: `u` is a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with
`f = -c u` (`TauCeti.PDE.energyFormH1_principal_eq_setIntegral_sub`). On a ball `B(x, ρ)` on
which `|u| ≤ M`, the datum satisfies `|f| ≤ γ M`, so its `Lʳ(B(x, ρ))` norm is at most
`γ M |B(x, ρ)|^(1/r)` for every `r`. Splitting it off on the ball
(`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le`, which is
`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le` with `r = n + 1`) leaves a
solution of the homogeneous equation within `K ρ^(2 - n/r) γ M |B(x, ρ)|^(1/r) / λ`, which is a
multiple of `ρ² γ M / λ`, of `u`. The Morrey gain is therefore `2` whatever `r` is, and the
Hölder theorem near solutions of the homogeneous equation
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_forall_exists_ae_abs_sub_le`) applies
with the gain `2`. The sign condition `c ≥ 0` is used only through local boundedness
(`TauCeti.PDE.exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder`), which
bounds `|u|` on `B(x, R/2)` by `D R^(-n/2) ‖u‖_{L²(B(x, R))}`.

## Main declarations

* `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_mass`: on a ball on which
  `|u| ≤ M`, a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0` lies within `K ρ² γ M / λ` of a weak
  solution of the homogeneous equation.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_mass_of_ae_abs_le`: Hölder continuity of
  bounded weak solutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0`, for `c` of either sign.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_mass`: **De Giorgi's theorem with a mass
  term**, for `c ≥ 0`.
* `TauCeti.PDE.continuousOn_preciseRepresentative_mass`: continuity of weak solutions, for
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
/-- A weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0` with bounded `c` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = -c u`: the case of `TauCeti.PDE.energyFormH1_principal_eq_setIntegral_sub` with no
drift and no right-hand side. -/
private theorem energyFormH1_zero_zero_eq_setIntegral_neg_mul {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega))
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 c u (v : W1p mu Omega 2) = 0)
    (v : W1p0 mu Omega 2) :
    energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, -(c x * W1p.value u x) * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  -- The right-hand side is `0 ∈ L²`, whose representative vanishes almost everywhere.
  have hzero : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 c u (v : W1p mu Omega 2) =
      ∫ x in Omega, (0 : Lp ℝ 2 (mu.restrict Omega)) x * W1p.value (v : W1p mu Omega 2) x ∂mu :=
    fun v => (hu v).trans (integral_eq_zero_of_ae ((Lp.coeFn_zero ℝ 2 _).mono fun x hx => by
      rw [Pi.zero_apply] at hx
      rw [hx, zero_mul, Pi.zero_apply])).symm
  rw [energyFormH1_principal_eq_setIntegral_sub hcoeff MemLp.zero hc hzero v]
  refine integral_congr_ae ((Lp.coeFn_zero ℝ 2 _).mono fun x hx => ?_)
  rw [Pi.zero_apply] at hx
  dsimp only
  rw [hx]
  simp

/-- **Splitting off a mass term on a ball.** Let `n ≥ 1` be the dimension. There is `K > 0`,
depending only on `n` and the normalization of `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `c` be measurable with
`|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0` with
`|u| ≤ M` almost everywhere on `B = B(x₀, ρ) ⊆ Ω`. Then there is a weak solution `h ∈ H¹(B)` of
the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K ρ² γ M / λ` almost everywhere on `B`.

The datum `-c u`, bounded by `γ M` on `B`, is split off by
`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le`. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_mass [Nonempty ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {c : EuclideanSpace ℝ ι → ℝ}
      {gamma : ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 c u (v : W1p mu Omega 2) = 0) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ 2 * (gamma * M) / lam := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le (mu := mu)
  refine ⟨K, hK, ?_⟩
  intro Omega a lam Lam c gamma u x₀ ρ M h ha hc hc_bound hu hρ hball hM
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ (hball (mem_ball_self hρ)))
  -- The mass term moves to the right-hand side `f = -c u`, with `|f| ≤ γ M` on the ball.
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h.upper_nonneg ha aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  have hcLp : MemLp c ⊤ (mu.restrict Omega) := memLp_top_of_bound hc gamma
    ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx => hc_bound x hx)
  have hfmeas : AEStronglyMeasurable (fun x => -(c x * W1p.value u x))
      (mu.restrict (ball x₀ ρ)) :=
    ((hc.mul (Lp.aestronglyMeasurable (W1p.value u))).neg).mono_measure
      (Measure.restrict_mono hball le_rfl)
  refine hsplit h ha hfmeas ?_ (energyFormH1_zero_zero_eq_setIntegral_neg_mul hcoeff hcLp hu) hρ
    hball
  filter_upwards [hM, ae_restrict_mem measurableSet_ball] with x hx hxB
  rw [Real.norm_eq_abs, abs_neg, abs_mul]
  exact mul_le_mul ((Real.norm_eq_abs _).symm.trans_le (hc_bound x (hball hxB))) hx
    (abs_nonneg _) hgamma

/-- **De Giorgi's theorem for bounded solutions with a mass term.** Let `n` be the dimension.
There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `c` be measurable with
`|c| ≤ γ` on `Ω`, of either sign, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the
energy form with mass `c` and no drift. If the closed `R`-thickening of a set `K` lies in `Ω`
and `|u| ≤ M` almost everywhere on every ball `B(x, R)`, `x ∈ K`, then the precise
representative of `u` is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + γ R² M / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). Neither `α` nor `C` depends on `γ`. -/
theorem exists_holderOnWith_preciseRepresentative_mass_of_ae_abs_le :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {gamma : ℝ}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R M : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 c u (v : W1p mu Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ x ∈ K, ∀ᵐ y ∂mu.restrict (ball x R), |W1p.value u y| ≤ M) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            gamma * R ^ 2 * M / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, zero_lt_one, le_rfl, zero_lt_one, ?_⟩
    intros
    exact Set.subsingleton_of_subsingleton.holderOnWith _ _ _
  obtain ⟨K₀, hK₀, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_mass (mu := mu)
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_exists_ae_abs_sub_le (mu := mu)
      (lam := lam) (Lam := Lam) (γ := 2) two_pos hK₀.le
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Omega a c gamma u K R M h ha hc hc_bound hu hR hRK hM
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₁, hx₁⟩
  · exact holderOnWith_empty _ _ _
  have hx₁Ω : x₁ ∈ (Omega : Set (EuclideanSpace ℝ ι)) := hRK (self_subset_cthickening K hx₁)
  have hgamma : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₁ hx₁Ω)
  have hM0 : 0 ≤ M := nonneg_of_ae_restrict_abs_le (measure_ball_pos mu x₁ hR).ne' (hM x₁ hx₁)
  -- On every ball `B(x, ρ)`, `x ∈ K`, `ρ ≤ R`, the datum `-c u` is bounded by `γ M`.
  refine (hhol (N := fun _ => gamma * M) h ha (fun x hx ρ hρ hρR hballρ => ?_)
    (fun _ _ => le_rfl) (mul_nonneg hgamma hM0) hR hRK).mono_const
    (Real.toNNReal_le_toNNReal (le_of_eq (by rw [Real.rpow_two]; ring)))
  exact hsplit h ha hc hc_bound hu hρ hballρ
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR) (hM x hx)) |>.imp fun _ hg =>
      ⟨hg.1, hg.2.mono fun _ hy => hy.trans_eq (by rw [Real.rpow_two])⟩

/-- The constant of `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_mass_of_ae_abs_le` at
the radius `R / 2`, with the bound `M = D R^(-n/2) N` from local boundedness, is at most
`2 C₁ max (2^(n/2)) D R^(-α) (1 + γR²/λ) R^(-n/2) N`: here `(R/2)^(-α) ≤ 2 R^(-α)`,
`(R/2)^(-n/2) = 2^(n/2) R^(-n/2)` and `γ (R/2)² M / λ = (D/4) (γR²/λ) R^(-n/2) N`. -/
private theorem mul_half_rpow_mul_add_le {C₁ D R N gamma lam n : ℝ} {α : ℝ≥0} (hα1 : α ≤ 1)
    (hC₁ : 0 ≤ C₁) (hD : 0 ≤ D) (hR : 0 < R) (hN : 0 ≤ N) (hgamma : 0 ≤ gamma)
    (hlam : 0 < lam) :
    C₁ * (R / 2) ^ (-(α : ℝ)) * ((R / 2) ^ (-n / 2) * N +
        gamma * (R / 2) ^ 2 * (D * (R ^ (-n / 2) * N)) / lam) ≤
      2 * C₁ * max (2 ^ (n / 2)) D * R ^ (-(α : ℝ)) * (1 + gamma * R ^ 2 / lam) *
        (R ^ (-n / 2) * N) := by
  have hRα : (R / 2) ^ (-(α : ℝ)) ≤ 2 * R ^ (-(α : ℝ)) := by
    rw [Real.div_rpow hR.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]
    gcongr
    calc (2 : ℝ) ^ (α : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by exact_mod_cast hα1)
      _ = 2 := Real.rpow_one 2
  have hRn : (R / 2) ^ (-n / 2) = 2 ^ (n / 2) * R ^ (-n / 2) := by
    rw [Real.div_rpow hR.le zero_le_two, neg_div, Real.rpow_neg zero_le_two, div_inv_eq_mul,
      mul_comm]
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

/-- **De Giorgi's theorem with a mass term.** Let `n` be the dimension. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, let `c` be measurable with `0 ≤ c ≤ γ` on `Ω`, and let
`u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0`, that is `a(u, v) = 0` for every
`v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with mass `c` and no drift. If the closed
`R`-thickening of a set `K` lies in `Ω`, then the precise representative of `u` is Hölder
continuous on `K` with exponent `α` and constant

`C R^(-α) (1 + γR²/λ) R^(-n/2) ‖u‖_{L²(Ω)}`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). The sign condition enters only through De Giorgi's
local boundedness theorem; for bounded solutions and `c` of either sign, see
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_mass_of_ae_abs_le`. -/
theorem exists_holderOnWith_preciseRepresentative_mass :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {c : EuclideanSpace ℝ ι → ℝ} {gamma : ℝ}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 c u (v : W1p mu Omega 2) = 0) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (1 + gamma * R ^ 2 / lam) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) *
            √(∫ y in Omega, W1p.value u y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, zero_lt_one, le_rfl, zero_lt_one, ?_⟩
    intros
    exact Set.subsingleton_of_subsingleton.holderOnWith _ _ _
  obtain ⟨α, C₁, hα, hα1, hC₁, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_mass_of_ae_abs_le (mu := mu) (lam := lam)
      (Lam := Lam)
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_pow_mul_rpow_mul_sqrt_setIntegral_lowerOrder (mu := mu)
      (lam := lam) (Lam := Lam)
  set n : ℝ := (Fintype.card ι : ℝ)
  refine ⟨α, 2 * C₁ * max (2 ^ (n / 2)) D, hα, hα1, by positivity, ?_⟩
  intro Omega a c gamma u K R h ha hc hc_bound hc_nonneg hu hR hRK
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₁, hx₁⟩
  · exact holderOnWith_empty _ _ _
  have hlam : 0 < lam := h.pos
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  have hgamma : 0 ≤ gamma :=
    (norm_nonneg _).trans (hc_bound x₁ (hball x₁ hx₁ (mem_ball_self hR)))
  set N := √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
  -- Local boundedness: `|u| ≤ M = D R^(-n/2) ‖u‖_{L²(Ω)}` on `B(x, R/2)` for `x ∈ K`.
  set M := D * (R ^ (-n / 2) * N)
  have hM : ∀ x ∈ K, ∀ᵐ y ∂mu.restrict (ball x (R / 2)), |W1p.value u y| ≤ M := fun x hx => by
    filter_upwards [hbound (b := 0) (beta := 0) h ha aestronglyMeasurable_const hc
      (fun _ _ => by simp) hc_bound hc_nonneg (by simpa using hu) (hball x hx)] with y hy
    have h1 : (1 + ((0 : ℝ) * R / lam) ^ 2) ^ Fintype.card ι = 1 := by simp
    refine hy.trans ?_
    rw [h1, mul_one, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (setIntegral_mono_set (Lp.memLp (W1p.value u)).integrable_sq
        (ae_of_all _ fun y => sq_nonneg _) (hball x hx).eventuallySubset)) (by positivity)) hD.le
  have hRK' : cthickening (R / 2) K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (cthickening_mono (half_le_self hR.le) K).trans hRK
  exact (hhol h ha hc hc_bound hu (half_pos hR) hRK' hM).mono_const
    (Real.toNNReal_le_toNNReal (mul_half_rpow_mul_add_le hα1 hC₁.le hD.le hR (by positivity)
      hgamma hlam))

/-- **Continuity of weak solutions with a mass term.** Let `n` be the dimension. Let `a` be
measurable and uniformly elliptic on `Ω`, let `c` be measurable and bounded with `c ≥ 0` on `Ω`,
and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = 0`. Then the precise
representative of `u`, which agrees with `u` almost everywhere on `Ω`, is continuous on `Ω`. -/
theorem continuousOn_preciseRepresentative_mass
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {c : EuclideanSpace ℝ ι → ℝ} {gamma : ℝ} {u : W1p mu Omega 2}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 c u (v : W1p mu Omega 2) = 0) :
    ContinuousOn (preciseRepresentative mu (W1p.value u)) Omega := by
  obtain ⟨α, _C, hα, -, -, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_mass (mu := mu) (lam := lam) (Lam := Lam)
  intro x hx
  obtain ⟨ε, hε, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  have hε2 : 0 < ε / 2 := half_pos hε
  have hK : cthickening (ε / 2) (closedBall x (ε / 2)) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := by
    rw [cthickening_closedBall hε2.le hε2.le, add_halves]
    exact hsub
  exact (((hhol h ha hc hc_bound hc_nonneg hu hε2 hK).continuousOn
    hα).continuousAt (closedBall_mem_nhds x hε2)).continuousWithinAt

end PDE

end TauCeti
