/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
public import TauCeti.Analysis.PDE.Regularity.NearSolution
import TauCeti.Algebra.Order.Ring.MaxOneMul
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Hölder continuity of weak solutions with a right-hand side

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`. This file extends De Giorgi's theorem
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative` from `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` to weak solutions
`u ∈ H¹(Ω)` of an equation with a right-hand side, in three forms:

* `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ Lʳ`, `r > 1` and `r > n/2`, that is `a(u, v) = ∫_Ω f v` for every
  `v ∈ H¹₀(Ω)`;
* `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with `F ∈ L^q(Ω; ℝⁿ)`, `q > 2` and `q > n`, that is
  `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`;
* `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with both data, that is `a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every
  `v ∈ H¹₀(Ω)`.

Such a solution is locally bounded and has a locally Hölder continuous representative, with an
exponent depending only on `λ`, `Λ`, `n`, the exponent of the datum and the normalization of the
Haar measure, and with constants controlled by `‖u‖_{L²}` and the norm of the datum divided by `λ`.
The datum enters with the Morrey gain `2 - n/r`, respectively `1 - n/q`, of its exponent; with both
data, each enters with its own gain. No regularity of the coefficients beyond measurability is
assumed.

The right-hand side is split off one ball at a time. On `B = B(x₀, ρ) ⊆ Ω`, the Dirichlet problem
`-∂ᵢ(aⁱʲ ∂ⱼw) = f` (or `= ∂ᵢFⁱ`) in `B`, `w ∈ H¹₀(B)`, has a solution, and Stampacchia's bounds
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_drift` (at `b = 0`) and
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence` give
`|w| ≤ C ρ^γ ‖f‖_{Lʳ(B)} / λ` with `γ = 2 - n/r` (or `|w| ≤ C ρ^γ ‖F‖_{L^q(B)} / λ` with
`γ = 1 - n/q`). The difference `h = u - w` solves the homogeneous equation on `B`, so De Giorgi's
local boundedness and oscillation decay apply to it. With both data, the solution `w` with datum
`f` is split off first, and `u - w` is a solution with datum `∂ᵢFⁱ` alone.

Everything after the splitting depends only on the outcome: on every ball `B(x, ρ)` of radius at
most `R`, `u` lies within `ρ^γ A` of a solution of the homogeneous equation, for some `γ > 0`.
De Giorgi's estimates under this hypothesis alone are in
`TauCeti.Analysis.PDE.Regularity.NearSolution`. The error is small on small balls exactly because
`γ > 0`, which is where the conditions `r > n/2` and `q > n` enter.

Applied on small balls, the `Lʳ` form gives continuity of weak solutions whose right-hand side is
only locally in `Lʳ`, tested against test functions; this is the form in which semilinear
equations, whose right-hand side depends on the solution, are met. On a general
finite-dimensional inner product space the Laplacian case follows by orthonormal coordinates.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_holderOnWith_preciseRepresentative_of_forall_exists_ae_abs_sub_le`: Hölder continuity
  of the precise representative of a function within `K₀ ρ^γ N(B(x, ρ)) / λ` of a homogeneous
  solution, as supplied by a splitting lemma for a datum with norm `N`.
* `exists_forall_energyFormH1_eq_ae_abs_le_divergence`: the Dirichlet problem with datum `∂ᵢFⁱ`
  on an open set of finite measure has a weak solution in `H¹₀` bounded by Stampacchia's estimate.
* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le` and
  `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence`: on a ball, a weak solution with
  right-hand side `f` (or `∂ᵢFⁱ`) is a weak solution of the homogeneous equation up to an error
  bounded by `K ρ^(2 - n/r) ‖f‖_{Lʳ} / λ` (or `K ρ^(1 - n/q) ‖F‖_{L^q} / λ`).
* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_drift`: the same for
  `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = f` and the homogeneous equation with the drift `b`, on balls with
  `2βρ ≤ λ`.
* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le`: the same, with or without a
  drift, for a right-hand side bounded by `B` on the ball, with error `K ρ² B / λ`.
* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_add_divergence`: the same for the datum
  `f + ∂ᵢFⁱ`, with error `K (ρ^(2 - n/r) ‖f‖_{Lʳ} + ρ^(1 - n/q) ‖F‖_{L^q}) / λ`.
* `exists_ae_abs_value_le_mul_add_of_memLp` and
  `exists_ae_abs_value_le_mul_add_of_memLp_divergence`: local boundedness,
  `|u| ≤ D (R^(-n/2) ‖u‖_{L²(B_R)} + R^(2 - n/r) ‖f‖_{Lʳ(B_R)} / λ)` on `B_{R/2}`, and its
  counterpart with `R^(1 - n/q) ‖F‖_{L^q(B_R)} / λ`.
* `exists_ae_abs_value_le_mul_add_of_memLp_add_divergence`: local boundedness for the datum
  `f + ∂ᵢFⁱ`, with both terms.
* `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp_add_divergence`: De Giorgi's interior
  oscillation estimate for the datum `f + ∂ᵢFⁱ`, with the same two terms.
* `exists_holderOnWith_preciseRepresentative_of_memLp` and
  `exists_holderOnWith_preciseRepresentative_of_memLp_divergence`: **De Giorgi's theorem with a
  right-hand side**, the Hölder continuity of the precise representative.
* `exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence`: De Giorgi's theorem for
  the datum `f + ∂ᵢFⁱ`, with the constant
  `C R^(-α) (R^(-n/2) ‖u‖_{L²} + (R^(2 - n/r) ‖f‖_{Lʳ} + R^(1 - n/q) ‖F‖_{L^q}) / λ)`.
* `continuousOn_preciseRepresentative_of_forall_memLp`: for a weak solution with a right-hand
  side in `Lʳ` on compact subsets of `Ω`, `r ≥ 2` and `r > n/2`, the precise representative is
  continuous on `Ω`.
* `exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq`: the same for Poisson's equation
  `-Δu = f` on an open subset of a finite-dimensional real inner product space.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.17, 8.22 and 8.24, and Lemma 8.23.
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

/-! ### Splitting off a datum on balls -/

/-- The common last step of splitting off a right-hand side on a ball `B = B(x₀, ρ) ⊆ Ω`: if
`w ∈ H¹₀(B)` has the same energy form as `u|_B` against `H¹₀(B)` and `|w| ≤ T`, then
`h = u|_B - w` solves the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` on `B` and
`|u - h| ≤ T`. -/
private theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_abs_le
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {lam Lam beta : ℝ}
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ T : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hB : (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega)
    (w : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2)
    (hw : ∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
      energyFormH1 a b 0 (W1p.restrictL hB u) (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) =
        energyFormH1 a b 0 (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2)
          (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2))
    (hwbound : ∀ᵐ x ∂mu.restrict (ball x₀ ρ),
      |W1p.value (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) x| ≤ T) :
    ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
      (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        energyFormH1 a b 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
      ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤ T := by
  have hBell : UniformlyEllipticOn (ball x₀ ρ) a lam Lam := h.mono_set hB
  have hcoeff := memLp_energyIntegrand_of_bounds (c := 0) (gamma := 0)
    hBell.upper_nonneg (ha.mono_measure (Measure.restrict_mono hB le_rfl))
    (hb.mono_measure (Measure.restrict_mono hB le_rfl)) aestronglyMeasurable_const
    (fun _x hx eta xi => hBell.upper_bound hx eta xi) (fun x hx => hb_bound x (hB hx))
    (fun _ _ => by simp)
  refine ⟨W1p.restrictL hB u - (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2), fun v => ?_, ?_⟩
  · rw [energyFormH1_sub_left hcoeff, hw v, sub_self]
  filter_upwards [hwbound,
    W1p.value_sub_ae (W1p.restrictL hB u) (w : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2),
    W1p.value_restrictL_ae hB u] with x hx hxs hxr
  rwa [hxs, Pi.sub_apply, hxr, sub_sub_cancel]

/-- Local boundedness for a function within `K R^γ N / λ` of a solution of the homogeneous
equation on `B(x₀, R)`, as supplied by a splitting lemma: the form of
`TauCeti.PDE.exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le` with the splitting constant `K`
absorbed into `D`. -/
private theorem exists_ae_abs_value_le_mul_add_of_exists_ae_abs_sub_le [Nonempty ι]
    {lam Lam : ℝ} (K : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R γ N : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∃ g : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ R, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ R), |W1p.value u x - W1p.value g x| ≤
          K * R ^ γ * N / lam) →
      0 ≤ N → 0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ γ * N / lam) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam) (Lam := Lam)
  refine ⟨D * max 1 K, by positivity, ?_⟩
  intro Omega a u x₀ R γ N h ha hsplit hN hR hball
  have hlam := h.pos
  obtain ⟨g, hg, hug⟩ := hsplit
  filter_upwards [hbound h ha hg hug hR hball] with x hx
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := R ^ γ * N / lam
  have hmax := add_mul_le_max_one_mul_add (c := K) (by positivity : 0 ≤ Q)
    (div_nonneg (mul_nonneg (Real.rpow_nonneg hR.le γ) hN) hlam.le : 0 ≤ P)
  calc |W1p.value u x| ≤ D * (Q + K * P) := hx.trans_eq (by simp only [P]; ring)
    _ ≤ D * (max 1 K * (Q + P)) := by gcongr
    _ = _ := by ring

/-- Hölder continuity for a function within `K₀ ρ^γ N(B(x, ρ)) / λ` of a solution of the
homogeneous equation on every ball `B(x, ρ) ⊆ Ω` with `x ∈ K` and `ρ ≤ R`, as supplied by a
splitting lemma, where the norm `N` of the datum on a set is at most its norm `N(Ω)` on `Ω`: the
form of `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le` with
`A = K₀ N(Ω) / λ` and the splitting constant `K₀` absorbed into `C`. -/
theorem exists_holderOnWith_preciseRepresentative_of_forall_exists_ae_abs_sub_le
    [Nonempty ι] {lam Lam γ K₀ : ℝ} (hγ : 0 < γ) (hK₀ : 0 ≤ K₀) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)} {R : ℝ} {N : Set (EuclideanSpace ℝ ι) → ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ x ∈ K, ∀ ρ, 0 < ρ → ρ ≤ R → ball x ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∃ g : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2,
          (∀ v : W1p0 mu ⟨ball x ρ, isOpen_ball⟩ 2,
            energyFormH1 a 0 0 g (v : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2) = 0) ∧
          ∀ᵐ y ∂mu.restrict (ball x ρ), |W1p.value u y - W1p.value g y| ≤
            K₀ * ρ ^ γ * N (ball x ρ) / lam) →
      (∀ s ⊆ (Omega : Set (EuclideanSpace ℝ ι)), N s ≤ N Omega) → 0 ≤ N Omega →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            R ^ γ * N Omega / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) hγ
  refine ⟨α, C * max 1 K₀, hα, hα1, by positivity, ?_⟩
  intro Omega a u K R N h ha hsplit hmono hN hR hRK
  have hlam := h.pos
  -- On every ball `B(x, ρ)`, `x ∈ K`, `ρ ≤ R`, the splitting error is at most
  -- `ρ^γ K₀ N(Ω) / λ`.
  refine (hhol (A := K₀ * N Omega / lam) h ha (fun x hx ρ hρ hρR => ?_) hR hRK).mono_const ?_
  · have hballρ : ball x ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (ball_subset_ball hρR).trans
      ((ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK))
    obtain ⟨g, hg, hug⟩ := hsplit x hx ρ hρ hρR hballρ
    refine ⟨g, hg, hug.mono fun y hy => hy.trans ?_⟩
    calc K₀ * ρ ^ γ * N (ball x ρ) / lam ≤ K₀ * ρ ^ γ * N Omega / lam := by
          gcongr
          exact hmono _ hballρ
      _ = _ := by ring
  · -- `C (Q + K₀ P) ≤ C max 1 K₀ (Q + P)`.
    refine Real.toNNReal_le_toNNReal ?_
    set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
    set P := R ^ γ * N Omega / lam
    have hmax := add_mul_le_max_one_mul_add (c := K₀) (by positivity : 0 ≤ Q)
      (div_nonneg (mul_nonneg (Real.rpow_nonneg hR.le γ) hN) hlam.le : 0 ≤ P)
    calc C * R ^ (-(α : ℝ)) * (Q + R ^ γ * (K₀ * N Omega / lam)) =
          C * R ^ (-(α : ℝ)) * (Q + K₀ * P) := by simp only [P]; ring
      _ ≤ C * R ^ (-(α : ℝ)) * (max 1 K₀ * (Q + P)) := by gcongr
      _ = _ := by ring

/-! ### A right-hand side in `Lʳ` -/

/-- **Splitting off the right-hand side on a ball, with a drift.** Let `n ≥ 1` be the dimension
and let `r > 1` with `r > n/2`. There is `K > 0`, depending only on `n`, `r` and the normalization
of `mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, let `b` be measurable with `‖b‖ ≤ β` on `Ω`, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = f`, that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with
`f ∈ Lʳ(B(x₀, ρ))`, `B(x₀, ρ) ⊆ Ω` and `2βρ ≤ λ`. Then on `B = B(x₀, ρ)` there is a weak solution
`h ∈ H¹(B)` of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` with

`|u - h| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` almost everywhere on `B`.

This transfers estimates for the homogeneous equation to equations with a right-hand side. The
smallness `2βρ ≤ λ` is that of Stampacchia's bound with a drift on the ball,
`TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_ae_abs_le_drift`. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_drift [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {lam Lam beta : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      MemLp f r (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → 2 * beta * ρ ≤ lam →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a b 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  obtain ⟨K, hK, hsolve⟩ :=
    exists_forall_energyFormH1_eq_setIntegral_ae_abs_le_drift (mu := mu) hr hrn
  refine ⟨K, hK, ?_⟩
  intro Omega a b lam Lam beta f u x₀ ρ h ha hb hb_bound hf hu hρ hball hsmall
  have hB : (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega := hball
  -- The weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) + bⁱ ∂ᵢw = f` on `B`, and its bound;
  -- `u|_B - w` is the homogeneous part.
  obtain ⟨w, hw, hwbound⟩ :=
    hsolve (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl))
      (hb.mono_measure (Measure.restrict_mono hball le_rfl)) (fun x hx => hb_bound x (hball hx))
      hsmall hf hρ
  exact exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_abs_le h ha hb hb_bound hB w
    (fun v => (energyFormH1_restrictL_eq_setIntegral hB hu v).trans (hw v).symm) hwbound

/-- **Splitting off the right-hand side on a ball.** Let `n ≥ 1` be the dimension and let `r > 1`
with `r > n/2`. There is `K > 0`, depending only on `n`, `r` and the normalization of `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with `f ∈ Lʳ(B(x₀, ρ))` and `B(x₀, ρ) ⊆ Ω`. Then on
`B = B(x₀, ρ)` there is a weak solution `h ∈ H¹(B)` of the homogeneous equation
`-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` almost everywhere on `B`.

This is the case `b = 0` of `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_drift`.
-/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le [Nonempty ι] {r : ℝ≥0} (hr : 1 < r)
    (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := by
  obtain ⟨K, hK, hmain⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_drift (mu := mu) hr hrn
  exact ⟨K, hK, fun h ha hf hu hρ hball => hmain (beta := 0) h ha aestronglyMeasurable_const
    (fun _ _ => by simp) hf hu hρ hball (by simpa using h.pos.le)⟩

/-- **Splitting off a bounded right-hand side on a ball.** Let `n ≥ 1` be the dimension. There is
`K > 0`, depending only on `n` and the normalization of `mu`, such that the following holds. Let
`a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` be measurable with
`‖b‖ ≤ β` on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = f`, that is
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with `f` measurable and `|f| ≤ B` almost everywhere
on `B(x₀, ρ) ⊆ Ω`, where `2βρ ≤ λ`. Then on `B(x₀, ρ)` there is a weak solution
`h ∈ H¹(B(x₀, ρ))` of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) + bⁱ ∂ᵢh = 0` with

`|u - h| ≤ K ρ² B / λ` almost everywhere on `B(x₀, ρ)`.

This is `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_drift` with the exponent
`r = n + 1`: since `f` is bounded, the Morrey gain is `2` whatever `r` is. Without a drift, `b = 0`
and `β = 0`, the condition `2βρ ≤ λ` holds on every ball. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_norm_le [Nonempty ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {lam Lam beta : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {ρ B : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      AEStronglyMeasurable b (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      AEStronglyMeasurable f (mu.restrict (ball x₀ ρ)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), ‖f x‖ ≤ B) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) → 2 * beta * ρ ≤ lam →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a b 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ 2 * B / lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  set r : ℝ≥0 := (Fintype.card ι : ℝ≥0) + 1
  have hr' : (r : ℝ) = n + 1 := by simp [r, n]
  have hr : 1 < r := by
    rw [← NNReal.coe_lt_coe, hr', NNReal.coe_one]
    linarith only [hn]
  have hrn : n < 2 * r := by rw [hr']; linarith only [hn]
  obtain ⟨K₀, hK₀, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_drift (mu := mu) hr hrn
  set ω := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := measureReal_ball_pos _ _ one_pos
  refine ⟨K₀ * ω ^ (r : ℝ)⁻¹, mul_pos hK₀ (Real.rpow_pos_of_pos hω _), ?_⟩
  intro Omega a b lam Lam beta f u x₀ ρ B h ha hb hb_bound hf hfB hu hρ hball hsmall
  have hlam : 0 < lam := h.pos
  have : IsFiniteMeasure (mu.restrict (ball x₀ ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨g, hg, hug⟩ := hsplit h ha hb hb_bound (MemLp.of_bound hf _ hfB) hu hρ hball hsmall
  refine ⟨g, hg, hug.mono fun x hx => hx.trans ?_⟩
  -- The scale-invariant `Lʳ` bound on the ball, with `ρ^(2 - n/r) = ρ² ρ^(-n/r)`.
  have hnorm := Measure.rpow_neg_mul_toReal_eLpNorm_ball_le_of_ae_norm_le mu (p := r) hρ hf hfB
  rw [finrank_euclideanSpace, ENNReal.ofReal_coe_nnreal, one_div] at hnorm
  have hpow : ρ ^ (2 - n / r) = ρ ^ 2 * ρ ^ (-(n / r)) := by
    rw [← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ]
    push_cast
    ring_nf
  calc K₀ * ρ ^ (2 - n / r) * (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam
      = K₀ * ρ ^ 2 * (ρ ^ (-(n / r)) * (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal) / lam := by
        rw [hpow]; ring
    _ ≤ K₀ * ρ ^ 2 * (ω ^ (r : ℝ)⁻¹ * B) / lam := by gcongr
    _ = K₀ * ω ^ (r : ℝ)⁻¹ * ρ ^ 2 * B / lam := by ring

/-- **Local boundedness of weak solutions with a right-hand side.** Let `n ≥ 1` be the dimension
and let `r > 1` with `r > n/2`. There is `D > 0`, depending only on `λ`, `Λ`, `n`, `r` and the
normalization of `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ Lʳ(B(x₀, R))`. If `B(x₀, R) ⊆ Ω`, then almost everywhere on
`B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} / λ)`.

For `f = 0` this is `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_abs_value_le_mul_add_of_memLp [Nonempty ι] {lam Lam : ℝ} {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam) := by
  obtain ⟨K, -, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  obtain ⟨D, hD, hbound⟩ := exists_ae_abs_value_le_mul_add_of_exists_ae_abs_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) K
  exact ⟨D, hD, fun h ha hf hu hR hball =>
    hbound h ha (hsplit h ha hf hu hR hball) ENNReal.toReal_nonneg hR hball⟩

/-- **De Giorgi's theorem with a right-hand side.** Let `n ≥ 1` be the dimension and let `r > 1`
with `r > n/2`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `r` and the
normalization of the additive Haar measure `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ Lʳ(Ω)`, and let
`u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`. If the closed `R`-thickening of a set `K` lies in `Ω`, then the precise
representative of `u` is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + R^(2 - n/r) ‖f‖_{Lʳ(Ω)} / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). No regularity of the coefficients beyond
measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_of_memLp [Nonempty ι] {lam Lam : ℝ}
    {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            R ^ (2 - (Fintype.card ι : ℝ) / r) *
              (eLpNorm f r (mu.restrict Omega)).toReal / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast zero_lt_one.trans hr
  obtain ⟨K₀, hK₀, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_exists_ae_abs_sub_le (mu := mu)
      (lam := lam) (Lam := Lam) (γ := 2 - (Fintype.card ι : ℝ) / r)
      (sub_pos.2 ((div_lt_iff₀ hr0).2 (by linarith only [hrn]))) hK₀.le
  refine ⟨α, C, hα, hα1, hC, fun {Omega a f u K R} h ha hf hu hR hRK => ?_⟩
  exact hhol (N := fun s => (eLpNorm f r (mu.restrict s)).toReal) h ha
    (fun _ _ ρ hρ _ hballρ =>
      hsplit h ha (hf.mono_measure (Measure.restrict_mono hballρ le_rfl)) hu hρ hballρ)
    (fun s hs => ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl)))
    ENNReal.toReal_nonneg hR hRK

/-! ### A right-hand side in divergence form -/

/-- **Solving the Dirichlet problem with a divergence datum, with Stampacchia's bound.** Let
`n ≥ 1` be the dimension and let `q > 2` with `q > n`. There is `C > 0`, depending only on `n`,
`q` and the normalization of `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on an open set `D` of finite measure with constants `λ, Λ`, and let
`F ∈ L^q(D; ℝⁿ)`. Then `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ` has a weak solution `w ∈ H¹₀(D)`, that is
`a(w, v) = -∫_D ⟪F, ∇v⟫` for every `v ∈ H¹₀(D)`, with

`|w| ≤ C ‖F‖_{L^q(D)} / λ · |D|^(1/n - 1/q)` almost everywhere on `D`.

The solution is given by Lax–Milgram,
`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_of_measure_ne_top`, applied to
the functional `TauCeti.PDE.divergenceForcing F`, and the bound is
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`. -/
theorem exists_forall_energyFormH1_eq_ae_abs_le_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, mu D ≠ ∞ →
      UniformlyEllipticOn (D : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict D) → MemLp F q (mu.restrict D) →
      ∃ w : W1p0 mu D 2, (∀ v : W1p0 mu D 2,
        energyFormH1 a 0 0 (w : W1p mu D 2) (v : W1p mu D 2) =
          -∫ x in D, ⟪F x, W1p.gradient (v : W1p mu D 2) x⟫ ∂mu) ∧
        ∀ᵐ x ∂mu.restrict D, |W1p.value (w : W1p mu D 2) x| ≤
          C * (eLpNorm F q (mu.restrict D)).toReal / lam *
            mu.real D ^ ((Fintype.card ι : ℝ)⁻¹ - (q : ℝ)⁻¹) := by
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  refine ⟨C, hC, fun {D a lam Lam F} hD h ha hF => ?_⟩
  have : IsFiniteMeasure (mu.restrict (D : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hD
  -- The weak solution exists since `F ∈ L²(D)`.
  have hF2 : MemLp F 2 (mu.restrict D) :=
    hF.mono_exponent (by exact_mod_cast (show ((2 : ℝ≥0) : ℝ) ≤ q by exact_mod_cast hq.le))
  obtain ⟨w, hw⟩ := h.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top ha hD hF2
  exact ⟨w, hw, hstamp (c := 0) (gamma := 0) hD h ha
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hF hw⟩

/-- **Splitting off a right-hand side in divergence form on a ball.** Let `n ≥ 1` be the
dimension and let `q > 2` with `q > n`. There is `K > 0`, depending only on `n`, `q` and the
normalization of `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, that is `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`, with
`F ∈ L^q(B(x₀, ρ); ℝⁿ)` and `B(x₀, ρ) ⊆ Ω`. Then on `B = B(x₀, ρ)` there is a weak solution
`h ∈ H¹(B)` of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K ρ^(1 - n/q) ‖F‖_{L^q(B)} / λ` almost everywhere on `B`.

The difference `u - h` is the solution in `H¹₀(B)` of the Dirichlet problem on `B` with datum
`∂ᵢFⁱ`, the functional `TauCeti.PDE.divergenceForcing F`, bounded by Stampacchia's estimate
`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_divergence`. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence [Nonempty ι] {q : ℝ≥0}
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam := by
  set n : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_divergence (mu := mu) hq hqn
  set e : ℝ := n⁻¹ - (q : ℝ)⁻¹
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e,
    mul_pos hC (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos) _), ?_⟩
  intro Omega a lam Lam F u x₀ ρ h ha hF hu hρ hball
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (B : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hBfin
  have hBell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hball
  have hBmeas : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono hball le_rfl)
  have hF2 : MemLp F 2 (mu.restrict B) :=
    hF.mono_exponent (by exact_mod_cast (show ((2 : ℝ≥0) : ℝ) ≤ q by exact_mod_cast hq.le))
  -- The weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) = ∂ᵢFⁱ` on `B`, and its bound; `u|_B - w` is
  -- the homogeneous part.
  obtain ⟨w, hw⟩ :=
    hBell.exists_forall_energyFormH1_eq_divergence_of_measure_ne_top hBmeas hBfin hF2
  -- `|B|^e = ρ^(n e) |B(0, 1)|^e`, with `n e = 1 - n/q`.
  have hmeas : mu.real (ball x₀ ρ) ^ e =
      ρ ^ (1 - n / q) * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e := by
    rw [Measure.addHaar_real_ball_rpow _ _ hρ, finrank_euclideanSpace]
    congr 2
    simp only [e, n]
    field_simp
  exact exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_of_ae_abs_le (beta := 0) h ha
    aestronglyMeasurable_const (fun _ _ => by simp) hB w
    (fun v => (energyFormH1_restrictL_eq_neg_setIntegral_inner hB hu v).trans (hw v).symm)
    ((hstamp (Omega := B) (c := 0) (gamma := 0) hBfin hBell hBmeas aestronglyMeasurable_const
      (fun _ _ => by simp) (fun _ _ => le_rfl) hF hw).mono
      fun x hx => hx.trans_eq (by simp only [B, Opens.coe_mk]; rw [hmeas]; ring))

/-- **Local boundedness of weak solutions with a right-hand side in divergence form.** Let
`n ≥ 1` be the dimension and let `q > 2` with `q > n`. There is `D > 0`, depending only on `λ`,
`Λ`, `n`, `q` and the normalization of `mu`, such that the following holds. Let `a` be measurable
and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with `F ∈ L^q(B(x₀, R); ℝⁿ)`. If `B(x₀, R) ⊆ Ω`, then almost everywhere on
`B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^(1 - n/q) ‖F‖_{L^q(B(x₀, R))} / λ)`. -/
theorem exists_ae_abs_value_le_mul_add_of_memLp_divergence [Nonempty ι] {lam Lam : ℝ}
    {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ (1 - (Fintype.card ι : ℝ) / q) *
            (eLpNorm F q (mu.restrict (ball x₀ R))).toReal / lam) := by
  obtain ⟨K, -, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence (mu := mu) hq hqn
  obtain ⟨D, hD, hbound⟩ := exists_ae_abs_value_le_mul_add_of_exists_ae_abs_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) K
  exact ⟨D, hD, fun h ha hF hu hR hball =>
    hbound h ha (hsplit h ha hF hu hR hball) ENNReal.toReal_nonneg hR hball⟩

/-- **De Giorgi's theorem with a right-hand side in divergence form.** Let `n ≥ 1` be the
dimension and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `n`, `q` and the normalization of the additive Haar measure `mu`, such that the
following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let
`F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, that is
`a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. If the closed `R`-thickening of a set `K` lies
in `Ω`, then the precise representative of `u` is Hölder continuous on `K` with exponent `α` and
constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + R^(1 - n/q) ‖F‖_{L^q(Ω)} / λ)`.

The precise representative agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). No regularity of the coefficients beyond
measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_of_memLp_divergence [Nonempty ι]
    {lam Lam : ℝ} {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu Omega 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict Omega)).toReal / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  have hq0 : (0 : ℝ) < q := two_pos.trans hq
  obtain ⟨K₀, hK₀, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence (mu := mu) hq hqn
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_exists_ae_abs_sub_le (mu := mu)
      (lam := lam) (Lam := Lam) (γ := 1 - (Fintype.card ι : ℝ) / q)
      (sub_pos.2 ((div_lt_one hq0).2 hqn)) hK₀.le
  refine ⟨α, C, hα, hα1, hC, fun {Omega a F u K R} h ha hF hu hR hRK => ?_⟩
  exact hhol (N := fun s => (eLpNorm F q (mu.restrict s)).toReal) h ha
    (fun _ _ ρ hρ _ hballρ =>
      hsplit h ha (hF.mono_measure (Measure.restrict_mono hballρ le_rfl)) hu hρ hballρ)
    (fun s hs => ENNReal.toReal_mono hF.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl)))
    ENNReal.toReal_nonneg hR hRK

/-! ### A right-hand side `f + ∂ᵢFⁱ` -/

/-- **Splitting off a right-hand side `f + ∂ᵢFⁱ` on a ball.** Let `n ≥ 1` be the dimension, let
`r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There is `K > 0`, depending only on `n`,
`r`, `q` and the normalization of `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is `a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`, with
`f ∈ Lʳ(B(x₀, ρ))`, `F ∈ L^q(B(x₀, ρ); ℝⁿ)` and `B(x₀, ρ) ⊆ Ω`. Then on `B = B(x₀, ρ)` there is a
weak solution `h ∈ H¹(B)` of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K (ρ^(2 - n/r) ‖f‖_{Lʳ(B)} + ρ^(1 - n/q) ‖F‖_{L^q(B)}) / λ` almost everywhere on `B`.

Each datum contributes the error of its own splitting,
`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le` and
`TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence`. -/
theorem exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_add_divergence [Nonempty ι]
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ ρ)) → MemLp F q (mu.restrict (ball x₀ ρ)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ h : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 h (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value h x| ≤
          K * (ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
              (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal +
            ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal) / lam := by
  obtain ⟨K₁, -, hsplit₁⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  obtain ⟨K₂, hK₂, hsplit₂⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_divergence (mu := mu) hq hqn
  have hrn' : (Fintype.card ι : ℝ) * (2 - r) < 2 * r := by
    have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
    nlinarith [mul_pos (Nat.cast_pos.2 Fintype.card_pos : (0 : ℝ) < Fintype.card ι)
      (sub_pos.2 hr1)]
  refine ⟨max K₁ K₂, lt_max_of_lt_right hK₂, ?_⟩
  intro Omega a lam Lam f F u x₀ ρ h ha hf hF hu hρ hball
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have hBell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hball
  have hBmeas : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono hball le_rfl)
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hBell.upper_nonneg hBmeas aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hBell.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  -- The solution `w₁ ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw₁) = f` on `B` carries the datum `f`, and
  -- `u|_B - w₁` solves `-∂ᵢ(aⁱʲ ∂ⱼ·) = ∂ᵢFⁱ` on `B`; split each of them off.
  obtain ⟨w₁, hw₁, -⟩ :=
    hBell.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp (c := 0) (gamma := 0) hBmeas
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hBfin hr hrn' hf
  obtain ⟨h₁, hh₁, hb₁⟩ := hsplit₁ hBell hBmeas hf hw₁ hρ subset_rfl
  obtain ⟨h₂, hh₂, hb₂⟩ := hsplit₂ (u := W1p.restrictL hB u - (w₁ : W1p mu B 2)) hBell hBmeas hF
    (fun v => by
      have e := energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_inner hB hu v
      have e₁ := hw₁ v
      rw [energyFormH1_sub_left hcoeff, e]
      linarith) hρ subset_rfl
  -- `h₁ + h₂` is the homogeneous part of `u` on `B`.
  refine ⟨h₁ + h₂, fun v => by rw [energyFormH1_add_left hcoeff, hh₁ v, hh₂ v, add_zero], ?_⟩
  filter_upwards [hb₁, hb₂, W1p.value_add_ae h₁ h₂,
    W1p.value_sub_ae (W1p.restrictL hB u) (w₁ : W1p mu B 2), W1p.value_restrictL_ae hB u]
    with x hx₁ hx₂ hxa hxs hxr
  rw [hxs, Pi.sub_apply, hxr] at hx₂
  rw [hxa, Pi.add_apply]
  have hlam := h.pos
  calc |W1p.value u x - (W1p.value h₁ x + W1p.value h₂ x)|
      ≤ |W1p.value (w₁ : W1p mu B 2) x - W1p.value h₁ x| +
          |W1p.value u x - W1p.value (w₁ : W1p mu B 2) x - W1p.value h₂ x| :=
        (abs_add_le _ _).trans_eq' (by ring_nf)
    _ ≤ max K₁ K₂ * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam +
        max K₁ K₂ * ρ ^ (1 - (Fintype.card ι : ℝ) / q) *
          (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal / lam := by
        grw [hx₁, hx₂]
        gcongr
        exacts [le_max_left _ _, le_max_right _ _]
    _ = _ := by ring

/-- **Local boundedness of weak solutions with a right-hand side `f + ∂ᵢFⁱ`.** Let `n ≥ 1` be the
dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There is `D > 0`, depending
only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of `mu`, such that the following holds. Let
`a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with `f ∈ Lʳ(B(x₀, R))` and
`F ∈ L^q(B(x₀, R); ℝⁿ)`. If `B(x₀, R) ⊆ Ω`, then almost everywhere on `B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + (R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} +
  R^(1 - n/q) ‖F‖_{L^q(B(x₀, R))}) / λ)`. -/
theorem exists_ae_abs_value_le_mul_add_of_memLp_add_divergence [Nonempty ι] {lam Lam : ℝ}
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) → MemLp F q (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam) := by
  obtain ⟨K, -, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_add_divergence (mu := mu) hr hrn hq hqn
  obtain ⟨D, hD, hbound⟩ := exists_ae_abs_value_le_mul_add_of_exists_ae_abs_sub_le (mu := mu)
    (lam := lam) (Lam := Lam) K
  refine ⟨D, hD, fun {Omega a f F u x₀ R} h ha hf hF hu hR hball => ?_⟩
  -- The splitting error is `K R^0 N / λ` for the combined norm `N` of the data.
  obtain ⟨g, hg, hug⟩ := hsplit h ha hf hF hu hR hball
  refine (hbound (γ := 0) (N := R ^ (2 - (Fintype.card ι : ℝ) / r) *
      (eLpNorm f r (mu.restrict (ball x₀ R))).toReal + R ^ (1 - (Fintype.card ι : ℝ) / q) *
      (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) h ha
    ⟨g, hg, hug.mono fun x hx => hx.trans_eq ?_⟩ (by positivity) hR hball).mono
    fun x hx => hx.trans_eq ?_
  · rw [Real.rpow_zero, mul_one]
  · rw [Real.rpow_zero, one_mul]

omit [DecidableEq ι] in
/-- The smaller Morrey gain `min (2 - n/r) (1 - n/q)` of `f ∈ Lʳ` and `F ∈ L^q` is positive. -/
private theorem min_sub_div_pos {r q : ℝ≥0} (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hqn : (Fintype.card ι : ℝ) < q) :
    0 < min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q) := by
  have hr0 : (0 : ℝ) < r := by linarith only [hrn, (Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card ι)]
  have hq0 : (0 : ℝ) < q := (Nat.cast_nonneg _).trans_lt hqn
  exact lt_min (sub_pos.2 ((div_lt_iff₀ hr0).2 (by linarith only [hrn])))
    (sub_pos.2 ((div_lt_one hq0).2 hqn))

/-- The splitting `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_add_divergence`
on every ball `B(x₀, ρ)` with `ρ ≤ R` inside a set `S` carrying `f` and `F`, bounded through the
norms of `f` and `F` on `S` and the power `ρ^γ` of the smaller Morrey gain
`γ = min (2 - n/r) (1 - n/q)`: the comparison hypothesis of
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le` and
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le`. -/
private theorem exists_forall_exists_ae_abs_sub_le_of_memLp_add_divergence [Nonempty ι]
    {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) (hq : 2 < (q : ℝ))
    (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ} {S : Set (EuclideanSpace ℝ ι)},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict S) → MemLp F q (mu.restrict S) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      ball x₀ R ⊆ S → S ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤
          ρ ^ min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q) *
            (K * (R ^ (2 - (Fintype.card ι : ℝ) / r -
                  min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) *
                (eLpNorm f r (mu.restrict S)).toReal +
              R ^ (1 - (Fintype.card ι : ℝ) / q -
                  min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) *
                (eLpNorm F q (mu.restrict S)).toReal) / lam) := by
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le_add_divergence (mu := mu) hr hrn hq hqn
  refine ⟨K, hK, fun {Omega a lam Lam f F u x₀ R S} h ha hf hF hu hball hS ρ hρ hρR => ?_⟩
  have hρS : ball x₀ ρ ⊆ S := (ball_subset_ball hρR).trans hball
  obtain ⟨g, hg, hug⟩ := hsplit h ha (hf.mono_measure (Measure.restrict_mono hρS le_rfl))
    (hF.mono_measure (Measure.restrict_mono hρS le_rfl)) hu hρ (hρS.trans hS)
  refine ⟨g, hg, ?_⟩
  have hfρ : (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal ≤
      (eLpNorm f r (mu.restrict S)).toReal :=
    lpNorm_mono_measure hf (Measure.restrict_mono hρS le_rfl)
  have hFρ : (eLpNorm F q (mu.restrict (ball x₀ ρ))).toReal ≤
      (eLpNorm F q (mu.restrict S)).toReal :=
    lpNorm_mono_measure hF (Measure.restrict_mono hρS le_rfl)
  -- `ρ^δ ≤ R^(δ - γ) ρ^γ` for both gains `δ ≥ γ`.
  set γ := min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)
  have hpow : ∀ δ, γ ≤ δ → ρ ^ δ ≤ R ^ (δ - γ) * ρ ^ γ := fun δ hδ =>
    calc ρ ^ δ = ρ ^ (δ - γ) * ρ ^ γ := by rw [← Real.rpow_add hρ, sub_add_cancel]
      _ ≤ R ^ (δ - γ) * ρ ^ γ := by gcongr
  have h₁ := hpow _ (min_le_left _ _)
  have h₂ := hpow _ (min_le_right _ _)
  have := h.pos
  have hR : 0 < R := hρ.trans_le hρR
  filter_upwards [hug] with x hx
  refine hx.trans ?_
  calc _ ≤ K * (R ^ (2 - (Fintype.card ι : ℝ) / r - γ) * ρ ^ γ *
          (eLpNorm f r (mu.restrict S)).toReal + R ^ (1 - (Fintype.card ι : ℝ) / q - γ) *
            ρ ^ γ * (eLpNorm F q (mu.restrict S)).toReal) / lam := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
/-- The bound of `TauCeti.PDE.exists_forall_exists_ae_abs_sub_le_of_memLp_add_divergence` at
`ρ = R`: the factors `R^(δ - γ)` recombine with `R^γ` into the Morrey gains. -/
private theorem rpow_min_mul_eq {r q : ℝ≥0} {K R lam A₁ A₂ : ℝ} (hR : 0 < R) :
    R ^ min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q) *
      (K * (R ^ (2 - (Fintype.card ι : ℝ) / r -
            min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) * A₁ +
          R ^ (1 - (Fintype.card ι : ℝ) / q -
            min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)) * A₂) / lam) =
    K * ((R ^ (2 - (Fintype.card ι : ℝ) / r) * A₁ +
      R ^ (1 - (Fintype.card ι : ℝ) / q) * A₂) / lam) := by
  set γ := min (2 - (Fintype.card ι : ℝ) / r) (1 - (Fintype.card ι : ℝ) / q)
  have hpow : ∀ δ, R ^ (δ - γ) * R ^ γ = R ^ δ := fun δ => by
    rw [← Real.rpow_add hR, sub_add_cancel]
  calc _ = K * (R ^ (2 - (Fintype.card ι : ℝ) / r - γ) * R ^ γ * A₁ +
        R ^ (1 - (Fintype.card ι : ℝ) / q - γ) * R ^ γ * A₂) / lam := by ring
    _ = _ := by rw [hpow, hpow]; ring

/-- **De Giorgi's interior oscillation estimate with a right-hand side `f + ∂ᵢFⁱ`.** Let `n ≥ 1`
be the dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of
`mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with
`f ∈ Lʳ(B(x₀, R))` and `F ∈ L^q(B(x₀, R); ℝⁿ)`. If `B(x₀, R) ⊆ Ω` and `0 < s ≤ R/2`, then
almost everywhere on `B(x₀, s)` the function `u` takes values in an interval of length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} +`
`(R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} + R^(1 - n/q) ‖F‖_{L^q(B(x₀, R))}) / λ)`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp_add_divergence [Nonempty ι]
    {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R s : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) → MemLp F q (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
            R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam)) := by
  obtain ⟨K, -, hcmp⟩ :=
    exists_forall_exists_ae_abs_sub_le_of_memLp_add_divergence (mu := mu) hr hrn hq hqn
  obtain ⟨α, C, hα, hα1, hC, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) (min_sub_div_pos hrn hqn)
  refine ⟨α, C * max 1 K, hα, hα1, by positivity, ?_⟩
  intro Omega a f F u x₀ R s h ha hf hF hu hs hsR hball
  have hR : 0 < R := by linarith only [hs, hsR]
  obtain ⟨m', hm'⟩ := hosc h ha (hcmp h ha hf hF hu subset_rfl hball) hs hsR hball
  refine ⟨m', ?_⟩
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal +
    R ^ (1 - (Fintype.card ι : ℝ) / q) * (eLpNorm F q (mu.restrict (ball x₀ R))).toReal) / lam
  have hlen : C * (s / R) ^ α * (Q + K * P) ≤ C * max 1 K * (s / R) ^ α * (Q + P) :=
    (mul_le_mul_of_nonneg_left (add_mul_le_max_one_mul_add (by positivity)
      (by have := h.pos; positivity)) (by positivity)).trans_eq (by ring)
  filter_upwards [hm'] with x hx
  rw [rpow_min_mul_eq hR] at hx
  exact ⟨hx.1, hx.2.trans (by linarith only [hlen])⟩

/-- **De Giorgi's theorem with a right-hand side `f + ∂ᵢFⁱ`.** Let `n ≥ 1` be the dimension, let
`r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and `C > 0`,
depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of the additive Haar measure `mu`,
such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let `f ∈ Lʳ(Ω)` and `F ∈ L^q(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is `a(u, v) = ∫_Ω f v - ∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. If
the closed `R`-thickening of a set `K` lies in `Ω`, then the precise representative of `u` is
Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + (R^(2 - n/r) ‖f‖_{Lʳ(Ω)} + R^(1 - n/q) ‖F‖_{L^q(Ω)}) / λ)`.

Each datum enters with its own Morrey gain, `2 - n/r` and `1 - n/q`. The precise representative
agrees with `u` almost everywhere on `Ω`
(`TauCeti.W1p.ae_eq_preciseRepresentative`). No regularity of the coefficients beyond
measurability is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence [Nonempty ι]
    {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) → MemLp F q (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
          ∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫ ∂mu) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            (R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal +
              R ^ (1 - (Fintype.card ι : ℝ) / q) *
                (eLpNorm F q (mu.restrict Omega)).toReal) / lam)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨Ks, -, hcmp⟩ :=
    exists_forall_exists_ae_abs_sub_le_of_memLp_add_divergence (mu := mu) hr hrn hq hqn
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) (min_sub_div_pos hrn hqn)
  refine ⟨α, C * max 1 Ks, hα, hα1, by positivity, ?_⟩
  intro Omega a f F u K R h ha hf hF hu hR hRK
  refine (hhol h ha (fun x hx => hcmp h ha hf hF hu
    ((ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK))
    subset_rfl) hR hRK).mono_const (Real.toNNReal_le_toNNReal ?_)
  rw [rpow_min_mul_eq hR]
  exact (mul_le_mul_of_nonneg_left (add_mul_le_max_one_mul_add (by positivity)
    (by have := h.pos; positivity)) (by positivity)).trans_eq (by ring)

/-! ### Continuity for a locally integrable right-hand side -/

open scoped Distributions

/-- **Continuity of weak solutions with a locally integrable right-hand side.** Let `n ≥ 1` be the
dimension and let `r ≥ 2` with `r > n/2`. Let `a` be measurable and uniformly elliptic on `Ω`, and
let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f` against test functions, `a(u, φ) = ∫_Ω f φ`, where `f`
lies in `Lʳ` on every compact subset of `Ω`. Then the precise representative of `u`, which agrees
with `u` almost everywhere on `Ω` (`TauCeti.W1p.ae_eq_preciseRepresentative`), is continuous on
`Ω`.

No integrability of `f` on all of `Ω` is assumed. On each ball `B` whose closure lies in `Ω`, the
equation holds against all of `H¹₀(B)` (`TauCeti.PDE.forall_energyFormH1_restrictL_eq_setIntegral`,
which uses `f ∈ L²(B)`), and De Giorgi's theorem with a right-hand side,
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`, makes the restriction of `u`
Hölder continuous on the concentric ball of half the radius. -/
theorem continuousOn_preciseRepresentative_of_forall_memLp [Nonempty ι] {lam Lam : ℝ}
    {r : ℝ≥0} (hr : 2 ≤ r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hf : ∀ K, IsCompact K → K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      MemLp f r (mu.restrict K))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu) :
    ContinuousOn (preciseRepresentative mu (W1p.value u)) Omega := by
  obtain ⟨α, C, hα, -, -, hhol⟩ := exists_holderOnWith_preciseRepresentative_of_memLp
    (mu := mu) (lam := lam) (Lam := Lam) (lt_of_lt_of_le one_lt_two hr) hrn
  intro x hx
  -- Work on a ball `B = B(x, ε)` whose closure lies in `Ω`.
  obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  let B : Opens (EuclideanSpace ℝ ι) := ⟨ball x ε, isOpen_ball⟩
  have hBΩ : B ≤ Omega := ball_subset_closedBall.trans hεΩ
  have : IsFiniteMeasure (mu.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfB : MemLp f r (mu.restrict B) := (hf _ (isCompact_closedBall x ε) hεΩ).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hB : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hBΩ
  have haB : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono hBΩ le_rfl)
  have huB := forall_energyFormH1_restrictL_eq_setIntegral hBΩ
    (memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0) hB.upper_nonneg
      haB aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hy eta xi => hB.upper_bound hy eta xi) (fun _ _ => by simp) (fun _ _ => by simp))
    hu (hfB.mono_exponent (by exact_mod_cast hr))
  -- De Giorgi's theorem on `B`, on the closed ball of radius `ε / 2`.
  have hK : cthickening (ε / 4) (closedBall x (ε / 2)) ⊆ (B : Set (EuclideanSpace ℝ ι)) := by
    rw [cthickening_closedBall (by positivity) (by positivity)]
    exact closedBall_subset_ball (by linarith)
  have hcont : ContinuousAt (preciseRepresentative mu (W1p.value (W1p.restrictL hBΩ u))) x :=
    ((hhol hB haB hfB huB (by positivity) hK).continuousOn hα).continuousAt
      (closedBall_mem_nhds x (by positivity))
  -- Near `x`, the precise representatives of `u` and of its restriction to `B` agree.
  have heq : preciseRepresentative mu (W1p.value (W1p.restrictL hBΩ u)) =ᶠ[𝓝 x]
      preciseRepresentative mu (W1p.value u) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with y hy
    exact preciseRepresentative_congr_ae_nhds (isOpen_ball.mem_nhds hy)
      (W1p.value_restrictL_ae hBΩ u)
  exact (hcont.congr heq).continuousWithinAt

open InnerProductSpace in
open scoped Gradient InnerProductSpace in
/-- **Continuity of weak solutions of Poisson's equation.** Let `E` be a real inner product space
of finite dimension `n ≥ 1` with its volume, and let `r ≥ 2` with `r > n/2`. If `u ∈ H¹(Ω)` solves
`-Δu = f` weakly, `∫_Ω ⟪∇u, ∇φ⟫ = ∫_Ω f φ` for every test function `φ` on `Ω`, where `f` lies in
`Lʳ` on every compact subset of `Ω`, then `u` agrees almost everywhere on `Ω` with a function that
is continuous on `Ω`.

This is the case `a = 1` of `TauCeti.PDE.continuousOn_preciseRepresentative_of_forall_memLp`,
transported to `E` through the coordinates of an orthonormal basis. -/
theorem exists_continuousOn_ae_eq_of_forall_integral_inner_gradient_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] {r : ℝ≥0} (hr : 2 ≤ r) (hrn : (finrank ℝ E : ℝ) < 2 * r)
    {Omega : Opens E} {f : E → ℝ} {u : W1p volume Omega 2}
    (hf : ∀ K, IsCompact K → K ⊆ (Omega : Set E) → MemLp f r (volume.restrict K))
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x in Omega, ⟪W1p.gradient u x, ∇ (φ : E → ℝ) x⟫_ℝ = ∫ x in Omega, f x * φ x) :
    ∃ g : E → ℝ, ContinuousOn g Omega ∧ W1p.value u =ᵐ[volume.restrict Omega] g := by
  set n := finrank ℝ E
  have : Nonempty (Fin n) := ⟨⟨0, Module.finrank_pos⟩⟩
  -- Orthonormal coordinates `e : E ≃ ℝⁿ`, with inverse `g`, and `Ω' = e(Ω)`.
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ E).repr
  let g : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] E := e.symm.toAffineIsometryEquiv
  have heg : ∀ x, g (e x) = x := fun x => by simp [g]
  let Ω' : Opens (EuclideanSpace ℝ (Fin n)) := ⟨g ⁻¹' Omega, Omega.isOpen.preimage g.continuous⟩
  have hΩ : (Omega : Set E) = e ⁻¹' Ω' := by ext x; simp [Ω', heg]
  have hg : MeasurePreserving g volume volume := by
    simpa [g] using e.symm.measurePreserving
  set u' := W1p.compAffineIsometryEquivL g (U := Ω') rfl u
  have hf' : ∀ K, IsCompact K → K ⊆ (Ω' : Set (EuclideanSpace ℝ (Fin n))) →
      MemLp (f ∘ g) r (volume.restrict K) := fun _ hK hKΩ =>
    g.toHomeomorph.memLp_comp_restrict_of_forall_isCompact hg hf hK hKΩ
  have hu' : ∀ φ' : 𝓓(Ω', ℝ), energyFormH1 (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) 0 0 u'
      (W1p.ofTestFunctionₗ volume Ω' 2 φ') = ∫ y in Ω', (f ∘ g) y * φ' y := by
    -- The weak equation on `Ω'` is the one on `Ω` read in the coordinates `g`.
    intro φ'
    rw [energyFormH1_one_zero_zero_eq_inner, L2.inner_def]
    refine (integral_congr_ae ?_).trans
      (W1p.setIntegral_inner_gradient_compAffineIsometryEquivL_eq_setIntegral_mul e.symm rfl u hu
        φ')
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Ω') 2 φ'] with y hφy
    rw [W1p.gradient_ofTestFunctionₗ, hφy]
  have hw := continuousOn_preciseRepresentative_of_forall_memLp (mu := volume)
    (a := fun _ => 1) (f := f ∘ g) (u := u') hr (by simpa [n] using hrn)
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const hf' hu'
  set w := preciseRepresentative volume (W1p.value u' : EuclideanSpace ℝ (Fin n) → ℝ)
  have huw : W1p.value u' =ᵐ[volume.restrict Ω'] w := W1p.ae_eq_preciseRepresentative u'
  refine ⟨w ∘ e, hw.comp e.continuous.continuousOn fun x hx => by rwa [hΩ] at hx, ?_⟩
  -- Pull the identity `u ∘ g = w` on `Ω'` back along `e`.
  have hres : MeasurePreserving e (volume.restrict Omega) (volume.restrict Ω') := by
    rw [hΩ]
    exact e.measurePreserving.restrict_preimage Ω'.isOpen.measurableSet
  filter_upwards [hres.quasiMeasurePreserving.ae_eq_comp
    ((W1p.value_compAffineIsometryEquivL_ae g (U := Ω') rfl u).symm.trans huw)] with x hx
  simpa [heg] using hx

end PDE

end TauCeti
