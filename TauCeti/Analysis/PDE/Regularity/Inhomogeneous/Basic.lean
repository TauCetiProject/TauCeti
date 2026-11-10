/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Hölder continuity of weak solutions with a right-hand side

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, and let `f ∈ Lʳ` with `r > 1` and `r > n/2`. This file extends De Giorgi's theorem
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative` from `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` to weak solutions
`u ∈ H¹(Ω)` of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`.

Such a solution is locally bounded and has a locally Hölder continuous representative, with an
exponent depending only on `λ`, `Λ`, `n`, `r` and the normalization of the Haar measure, and with
constants controlled by `‖u‖_{L²}` and `‖f‖_{Lʳ}/λ`. No regularity of the coefficients beyond
measurability is assumed.

## Comparison with solutions of the homogeneous equation

The estimates are first proved for any `u ∈ H¹(Ω)` that is uniformly close to weak solutions of
the homogeneous equation on balls: if on every ball `B(x₀, ρ)` with `ρ ≤ R` there is a weak
solution `h ∈ H¹(B(x₀, ρ))` of `-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with `|u - h| ≤ E ρ^γ` almost everywhere, for
some `γ > 0`, then De Giorgi's local boundedness and oscillation decay for `h` transfer to `u`.
Comparing the essential oscillation of `u` on concentric balls with that of `h` gives

`osc_{B(x₀, s)} u ≤ C₀ (s/ρ)^α₀ osc_{B(x₀, ρ)} u + K E ρ^γ`,

and the iteration lemma `TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` turns
this into a power law with exponent `min γ (α₀/2)`. The precise representative then converts the
power law into a Hölder bound, as for the homogeneous equation. The right-hand side enters only
through the comparison, so the same results serve every kind of data for which the comparison is
available, such as data in divergence form
(`TauCeti/Analysis/PDE/Regularity/Inhomogeneous/Divergence.lean`).

## A right-hand side in `Lʳ`

On `B = B(x₀, ρ) ⊆ Ω`, the Dirichlet problem `-∂ᵢ(aⁱʲ ∂ⱼw) = f` in `B`, `w ∈ H¹₀(B)`, has a
solution
(`TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp`),
and Stampacchia's bound `TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow` gives
`|w| ≤ C ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ`. The difference `h = u - w` solves the homogeneous equation
on `B`, which is the comparison above with `γ = 2 - n/r`. The error `w` is small on small balls
exactly because `2 - n/r > 0`.

## Main declarations

All in the namespace `TauCeti.PDE`.

* `exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le`: local boundedness of a function within `W`
  of a weak solution of the homogeneous equation on a ball.
* `exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le`: one step of oscillation
  decay, comparing the essential oscillations of such a function on two concentric balls.
* `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le` and
  `exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le`: the interior oscillation
  estimate and the Hölder continuity of the precise representative, for a function within
  `E ρ^γ` of a weak solution of the homogeneous equation on every ball of radius `ρ ≤ R`.
* `exists_forall_energyFormH1_eq_zero_ae_abs_sub_le`: on a ball, a weak solution with right-hand
  side `f` is a weak solution of the homogeneous equation up to an error bounded by
  `K ρ^(2 - n/r) ‖f‖_{Lʳ} / λ`.
* `exists_ae_abs_value_le_mul_add_of_memLp`: local boundedness,
  `|u| ≤ D (R^(-n/2) ‖u‖_{L²(B_R)} + R^(2 - n/r) ‖f‖_{Lʳ(B_R)} / λ)` on `B_{R/2}`.
* `exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp`: the interior oscillation estimate.
* `exists_holderOnWith_preciseRepresentative_of_memLp`: **De Giorgi's theorem with a right-hand
  side**, the Hölder continuity of the precise representative.

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
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

namespace PDE

/-! ### Comparison with solutions of the homogeneous equation -/

/-- **Local boundedness by comparison.** Let `n ≥ 1` be the dimension. There is `D > 0`,
depending only on `λ`, `Λ`, `n` and the normalization of `mu`, such that the following holds.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let
`B(x₀, R) ⊆ Ω`. If `u ∈ H¹(Ω)` is within `W` of a weak solution `g ∈ H¹(B(x₀, R))` of the
homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼg) = 0`, that is `|u - g| ≤ W` almost everywhere on
`B(x₀, R)`, then almost everywhere on `B(x₀, R/2)`

`|u| ≤ D (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + W)`.

For `W = 0` this is `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le [Nonempty ι] {lam Lam : ℝ} :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R W : ℝ} {g : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ v : W1p0 mu ⟨ball x₀ R, isOpen_ball⟩ 2,
        energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ R, isOpen_ball⟩ 2) = 0) →
      (∀ᵐ x ∂mu.restrict (ball x₀ R), |W1p.value u x - W1p.value g x| ≤ W) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)), |W1p.value u x| ≤
        D * (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          W) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨D₀, hD₀, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
  set ω := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := Metric.measureReal_ball_pos mu 0 one_pos
  refine ⟨max (√2 * D₀) (√2 * D₀ * √ω + 1), lt_max_of_lt_left (by positivity), ?_⟩
  intro Omega a u x₀ R W g h ha hR hball hg hug
  have hW : 0 ≤ W := by
    have : (ae (mu.restrict (ball x₀ R))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos mu x₀ hR).ne'
    obtain ⟨x, hx⟩ := hug.exists
    exact (abs_nonneg _).trans hx
  -- De Giorgi's bound for `g` on `B(x₀, R/2)`.
  have hgbound := hbound (Omega := ⟨ball x₀ R, isOpen_ball⟩) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl)) hg hR (subset_refl _)
  -- `∫_B g² ≤ 2 ∫_B u² + 2 W² |B|`, since `g² ≤ 2 u² + 2 (u - g)²`.
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hu2 : Integrable (fun x => W1p.value u x ^ 2) (mu.restrict (ball x₀ R)) :=
    ((Lp.memLp (W1p.value u)).integrable_sq).mono_measure (Measure.restrict_mono hball le_rfl)
  have hg2 : ∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu ≤
      2 * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu + 2 * W ^ 2 * mu.real (ball x₀ R) := by
    have hrhs : ∫ x in ball x₀ R, (2 * W1p.value u x ^ 2 + 2 * W ^ 2) ∂mu =
        2 * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu + 2 * W ^ 2 * mu.real (ball x₀ R) := by
      rw [integral_add (hu2.const_mul 2) (integrable_const _), integral_const_mul, integral_const,
        smul_eq_mul, measureReal_restrict_apply_univ]
      ring
    rw [← hrhs]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      ((hu2.const_mul 2).add (integrable_const _)) ?_
    filter_upwards [hug] with x hx
    have habs : |W1p.value u x - W1p.value g x| ^ 2 ≤ W ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hx 2
    rw [sq_abs] at habs
    nlinarith [sq_nonneg (W1p.value u x + (W1p.value u x - W1p.value g x))]
  have hsqrt : √(∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu) ≤
      √2 * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) + √2 * W * √ω * R ^ (n / 2) := by
    have hball_meas : mu.real (ball x₀ R) = R ^ n * ω := by
      rw [Measure.addHaar_real_ball_of_pos _ _ hR, finrank_euclideanSpace, ← Real.rpow_natCast]
    have hRn : √(R ^ n * ω) = R ^ (n / 2) * √ω := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
      ring_nf
    calc √(∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu)
        ≤ √(2 * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu + 2 * W ^ 2 * mu.real (ball x₀ R)) :=
          Real.sqrt_le_sqrt hg2
      _ ≤ √(2 * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
            √(2 * W ^ 2 * mu.real (ball x₀ R)) := by
          have hA : 0 ≤ 2 * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu :=
            mul_nonneg zero_le_two (integral_nonneg fun _ => sq_nonneg _)
          have hB : 0 ≤ 2 * W ^ 2 * mu.real (ball x₀ R) := by positivity
          refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
          nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sqrt_nonneg (2 * W ^ 2 *
            mu.real (ball x₀ R)), Real.sqrt_nonneg (2 * ∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)]
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num), hball_meas, Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by norm_num), Real.sqrt_sq hW, hRn]
        ring
  -- Combine: `|u| ≤ |g| + W`.
  have hR' : R ^ (-n / 2) * R ^ (n / 2) = 1 := by
    rw [← Real.rpow_add hR, neg_div, neg_add_cancel, Real.rpow_zero]
  filter_upwards [hgbound, ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (half_le_self hR.le)) hug] with x hx hxu
  set Q := R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  have hQ : 0 ≤ Q := by positivity
  calc |W1p.value u x| ≤ |W1p.value g x| + |W1p.value u x - W1p.value g x| := by
        simpa using abs_add_le (W1p.value g x) (W1p.value u x - W1p.value g x)
    _ ≤ D₀ * R ^ (-n / 2) * √(∫ x in ball x₀ R, W1p.value g x ^ 2 ∂mu) + W := add_le_add hx hxu
    _ ≤ D₀ * R ^ (-n / 2) * (√2 * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          √2 * W * √ω * R ^ (n / 2)) + W := by gcongr
    _ = √2 * D₀ * Q + (√2 * D₀ * √ω + 1) * W := by
        linear_combination (√2 * D₀ * W * √ω) * hR'
    _ ≤ max (√2 * D₀) (√2 * D₀ * √ω + 1) * Q + max (√2 * D₀) (√2 * D₀ * √ω + 1) * W := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = _ := by ring

/-- **One step of oscillation decay by comparison.** Let `n ≥ 1` be the dimension. There are
`α ∈ (0, 1]` and `C, K > 0`, depending only on `λ`, `Λ`, `n` and the normalization of `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let `B(x₀, ρ) ⊆ Ω` and `0 < s ≤ ρ`, and let `u ∈ H¹(Ω)` be essentially bounded on
`B(x₀, ρ)`. If `|u - g| ≤ W` almost everywhere on `B(x₀, ρ)` for a weak solution
`g ∈ H¹(B(x₀, ρ))` of the homogeneous equation `-∂ᵢ(aⁱʲ ∂ⱼg) = 0`, then the essential
oscillations `osc_s` and `osc_ρ` of `u` on `B(x₀, s)` and `B(x₀, ρ)` satisfy

`osc_s ≤ C (s/ρ)^α osc_ρ + K W`.

For `W = 0` this is the oscillation decay `TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_sub`
of the homogeneous equation. -/
theorem exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le [Nonempty ι]
    {lam Lam : ℝ} :
    ∃ α C K : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {ρ s M W : ℝ} {g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      0 < s → s ≤ ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M) →
      (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) →
      (∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤ W) →
      essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)) -
          essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)) ≤
        C * (s / ρ) ^ α *
            (essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ)) -
              essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ ρ))) +
          K * W := by
  obtain ⟨α₀, C₀, hα₀, hα₀1, hC₀, hpow⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_sub (mu := mu) (lam := lam) (Lam := Lam)
  refine ⟨α₀, C₀, 2 * C₀ + 2, hα₀, hα₀1, hC₀, by positivity, ?_⟩
  intro Omega a u x₀ ρ s M W g h ha hs hsρ hball hM hg hug
  have hρ : 0 < ρ := hs.trans_le hsρ
  have : (ae (mu.restrict (ball x₀ s))).NeBot :=
    ae_restrict_neBot.2 (measure_ball_pos mu x₀ hs).ne'
  have hW0 : 0 ≤ W := by
    have : (ae (mu.restrict (ball x₀ ρ))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos mu x₀ hρ).ne'
    obtain ⟨x, hx⟩ := hug.exists
    exact (abs_nonneg _).trans hx
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
    (ha.mono_measure (Measure.restrict_mono hball le_rfl)) hg hs hsρ (subset_refl _) hgI
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
  have hC₀s : 0 ≤ C₀ * (s / ρ) ^ α₀ := by positivity
  calc _ ≤ C₀ * (s / ρ) ^ α₀ * (m₁ + W - (m - W)) + 2 * W := hosc
    _ = C₀ * (s / ρ) ^ α₀ * (m₁ - m) + (2 * (C₀ * (s / ρ) ^ α₀) + 2) * W := by ring
    _ ≤ C₀ * (s / ρ) ^ α₀ * (m₁ - m) + (2 * C₀ + 2) * W := by gcongr

/-- **De Giorgi's interior oscillation estimate by comparison.** Let `n ≥ 1` be the dimension and
let `γ > 0`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `γ` and the
normalization of `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `λ, Λ`, let `B(x₀, R) ⊆ Ω` and `0 < s ≤ R/2`, and let
`u ∈ H¹(Ω)`. Suppose that on every ball `B(x₀, ρ)` with `0 < ρ ≤ R` there is a weak solution
`g ∈ H¹(B(x₀, ρ))` of `-∂ᵢ(aⁱʲ ∂ⱼg) = 0` with `|u - g| ≤ E ρ^γ` almost everywhere on
`B(x₀, ρ)`. Then almost everywhere on `B(x₀, s)` the function `u` takes values in an interval of
length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + E R^γ)`.

The exponent `α` is at most `γ`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le [Nonempty ι]
    {lam Lam γ : ℝ} (hγ : 0 < γ) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι}
      {R s E : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤ E * ρ ^ γ) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          E * R ^ γ)) := by
  obtain ⟨α₀, C₀, K, hα₀, hα₀1, hC₀, hK, hosc⟩ :=
    exists_essSup_sub_essInf_le_mul_rpow_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam)
  obtain ⟨D, hD, hloc⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam) (Lam := Lam)
  -- The Hölder exponent `β = min γ (α₀/2) < α₀`.
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min γ (α₀ / 2) := ⟨_, rfl⟩
  have hβ : 0 < β := hβdef ▸ lt_min hγ (half_pos hα₀)
  have hβγ : β ≤ γ := hβdef ▸ min_le_left _ _
  have hβα : β < α₀ := hβdef ▸ (min_le_right _ _).trans_lt (half_lt_self hα₀)
  obtain ⟨ε₀, C₁, hε₀, hC₁, hiter⟩ :=
    exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hC₀.le hβα hβα
  refine ⟨β, C₁ * 2 ^ β * (2 * D + K), hβ, hβα.le.trans hα₀1, by positivity, ?_⟩
  intro Omega a u x₀ R s E h ha hcmp hs hsR hball
  have hR : 0 < R := by linarith only [hs, hsR]
  obtain ⟨R₁, hR₁def⟩ : ∃ R₁ : ℝ, R₁ = R / 2 := ⟨_, rfl⟩
  rw [← hR₁def] at hsR
  have hR₁ : 0 < R₁ := hR₁def ▸ half_pos hR
  have hR₁R : R₁ ≤ R := hR₁def ▸ half_le_self hR.le
  -- The comparison on `B(x₀, R)`, which also shows `E ≥ 0`.
  obtain ⟨gR, hgR, hugR⟩ := hcmp R hR le_rfl
  have hE : 0 ≤ E := by
    have : (ae (mu.restrict (ball x₀ R))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos mu x₀ hR).ne'
    obtain ⟨x, hx⟩ := hugR.exists
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hR γ)).1 ((abs_nonneg _).trans hx)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) :=
    ⟨_, rfl⟩
  have hQ : 0 ≤ Q := by rw [hQdef]; positivity
  -- Local boundedness: `|u| ≤ M₀` on `B(x₀, R₁)`.
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = D * (Q + E * R ^ γ) := ⟨_, rfl⟩
  have hM : ∀ᵐ x ∂mu.restrict (ball x₀ R₁), |W1p.value u x| ≤ M₀ := by
    filter_upwards [hR₁def ▸ hloc h ha hR hball hgR hugR] with x hx
    rwa [hM₀def, hQdef]
  clear hloc
  -- The essential oscillation `φ ρ` of `u` on `B(x₀, ρ)`: nonnegative and monotone for
  -- `ρ ≤ R₁`, where `u` is essentially bounded.
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ → ℝ, φ = fun ρ => essSup (W1p.value u : EuclideanSpace ℝ ι → ℝ)
      (mu.restrict (ball x₀ ρ)) - essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ)
        (mu.restrict (ball x₀ ρ)) := ⟨_, rfl⟩
  have hne : ∀ ρ, 0 < ρ → (ae (mu.restrict (ball x₀ ρ))).NeBot := fun ρ hρ =>
    ae_restrict_neBot.2 (measure_ball_pos mu x₀ hρ).ne'
  have hMρ : ∀ ρ, ρ ≤ R₁ → ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x| ≤ M₀ :=
    fun ρ hρ => ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρ) hM
  have hbdd₁ : ∀ ρ, ρ ≤ R₁ → IsBoundedUnder (· ≤ ·) (ae (mu.restrict (ball x₀ ρ)))
      (W1p.value u : EuclideanSpace ℝ ι → ℝ) := fun ρ hρ =>
    isBoundedUnder_of_eventually_le (a := M₀) ((hMρ ρ hρ).mono fun _ hx => (abs_le.1 hx).2)
  have hbdd₂ : ∀ ρ, ρ ≤ R₁ → IsBoundedUnder (· ≥ ·) (ae (mu.restrict (ball x₀ ρ)))
      (W1p.value u : EuclideanSpace ℝ ι → ℝ) := fun ρ hρ =>
    isBoundedUnder_of_eventually_ge (a := -M₀) ((hMρ ρ hρ).mono fun _ hx => (abs_le.1 hx).1)
  have hφ0 : ∀ ρ ∈ Ioc 0 R₁, 0 ≤ φ ρ := fun ρ hρ => by
    have := hne ρ hρ.1
    rw [hφdef]
    exact sub_nonneg.2 (liminf_le_limsup (hbdd₁ ρ hρ.2) (hbdd₂ ρ hρ.2))
  have hmono : MonotoneOn φ (Ioc 0 R₁) := fun ρ hρ ρ' hρ' hρρ' => by
    have := hne ρ hρ.1
    rw [hφdef]
    exact essSup_sub_essInf_mono_measure (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (ball_subset_ball hρρ') le_rfl)) (hbdd₁ ρ' hρ'.2) (hbdd₂ ρ' hρ'.2)
  -- One comparison step: `φ s ≤ C₀ (s/ρ)^α₀ φ ρ + B ρ^β` for `s ≤ ρ ≤ R₁`.
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = K * E * R₁ ^ (γ - β) := ⟨_, rfl⟩
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hstep : ∀ s ρ, 0 < s → s ≤ ρ → ρ ≤ R₁ →
      φ s ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + B * ρ ^ β := by
    intro s ρ hs hsρ hρR₁
    have hρ : 0 < ρ := hs.trans_le hsρ
    have hρR : ball x₀ ρ ⊆ ball x₀ R := ball_subset_ball (hρR₁.trans hR₁R)
    obtain ⟨g, hg, hug⟩ := hcmp ρ hρ (hρR₁.trans hR₁R)
    have hργ : ρ ^ γ ≤ R₁ ^ (γ - β) * ρ ^ β := by
      calc ρ ^ γ = ρ ^ (γ - β) * ρ ^ β := by rw [← Real.rpow_add hρ, sub_add_cancel]
        _ ≤ R₁ ^ (γ - β) * ρ ^ β := by gcongr
    have hoscρ : φ s ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + K * (E * ρ ^ γ) := by
      simpa only [hφdef, add_zero] using
        hosc h ha hs hsρ (hρR.trans hball) (hMρ ρ hρR₁) hg hug
    calc φ s ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + K * (E * ρ ^ γ) := hoscρ
      _ ≤ C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + K * (E * (R₁ ^ (γ - β) * ρ ^ β)) := by gcongr
      _ = C₀ * ((s / ρ) ^ α₀ + 0) * φ ρ + B * ρ ^ β := by rw [hBdef]; ring
  clear hosc
  -- Iterate, and bound the oscillation on `B(x₀, R₁)` by local boundedness.
  have hfin := hiter hB hε₀.le hmono hφ0 hstep s R₁ hs hsR le_rfl
  have hφR₁ : φ R₁ ≤ 2 * M₀ := by
    have := hne R₁ hR₁
    rw [hφdef]
    refine essSup_sub_essInf_le (m := -M₀) ?_
    filter_upwards [hM] with x hx
    rw [abs_le] at hx
    exact ⟨hx.1, by linarith only [hx.2]⟩
  have hsβ : B * s ^ β = K * E * R₁ ^ γ * (s / R₁) ^ β := by
    rw [hBdef, Real.div_rpow hs.le hR₁.le, Real.rpow_sub hR₁]
    field_simp
  have hR₁γ : R₁ ^ γ ≤ R ^ γ := Real.rpow_le_rpow hR₁.le hR₁R hγ.le
  have hsR₁ : (s / R₁) ^ β = 2 ^ β * (s / R) ^ β := by
    rw [← Real.mul_rpow (by norm_num) (by positivity), hR₁def]
    congr 1
    field_simp
  have hM₀ : 0 ≤ M₀ := by rw [hM₀def]; positivity
  have hφs : φ s ≤ C₁ * 2 ^ β * (2 * D + K) * (s / R) ^ β * (Q + E * R ^ γ) :=
  calc φ s ≤ C₁ * ((s / R₁) ^ β * φ R₁ + B * s ^ β) := hfin
    _ ≤ C₁ * ((s / R₁) ^ β * (2 * M₀) + K * E * R ^ γ * (s / R₁) ^ β) := by
        rw [hsβ]
        gcongr
    _ = C₁ * 2 ^ β * (s / R) ^ β * (2 * D * (Q + E * R ^ γ) + K * (E * R ^ γ)) := by
        rw [hsR₁, hM₀def]
        ring
    _ ≤ C₁ * 2 ^ β * (s / R) ^ β * ((2 * D + K) * (Q + E * R ^ γ)) := by
        gcongr
        nlinarith only [mul_nonneg hK.le hQ]
    _ = _ := by ring
  refine ⟨essInf (W1p.value u : EuclideanSpace ℝ ι → ℝ) (mu.restrict (ball x₀ s)), ?_⟩
  filter_upwards [ae_le_essSup (hbdd₁ s hsR), ae_essInf_le (hbdd₂ s hsR)] with x hx₁ hx₂
  refine ⟨hx₂, ?_⟩
  rw [← hQdef]
  rw [hφdef] at hφs
  linarith only [hφs, hx₁]

/-- **Hölder continuity by comparison.** Let `n ≥ 1` be the dimension and let `γ > 0`. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `γ` and the normalization of `mu`,
such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, let the closed `R`-thickening of a set `K` lie in `Ω`, and let `u ∈ H¹(Ω)`. Suppose that
on every ball `B(x, ρ)` with `x ∈ K` and `0 < ρ ≤ R` there is a weak solution
`g ∈ H¹(B(x, ρ))` of `-∂ᵢ(aⁱʲ ∂ⱼg) = 0` with `|u - g| ≤ E ρ^γ` almost everywhere on `B(x, ρ)`.
Then the precise representative of `u` is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖u‖_{L²(Ω)} + E R^γ)`.

The exponent `α` is at most `γ`. -/
theorem exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le [Nonempty ι]
    {lam Lam γ : ℝ} (hγ : 0 < γ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {K : Set (EuclideanSpace ℝ ι)} {R E : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      0 < R → cthickening R K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ x ∈ K, ∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ y ∂mu.restrict (ball x ρ), |W1p.value u y - W1p.value g y| ≤ E * ρ ^ γ) →
        HolderOnWith (C * R ^ (-(α : ℝ)) *
          (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) +
            E * R ^ γ)).toNNReal α
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨α, C₀, hα, hα1, hC₀, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le (mu := mu)
      (lam := lam) (Lam := Lam) hγ
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam) (Lam := Lam)
  lift α to ℝ≥0 using hα.le
  refine ⟨α, max C₀ (4 * D), NNReal.coe_pos.1 hα, NNReal.coe_le_one.1 hα1,
    lt_max_of_lt_left hC₀, ?_⟩
  intro Omega a u K R E h ha hR hRK hcmp
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₁, hx₁⟩
  · exact holderOnWith_empty _ _ _
  have hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := (self_subset_cthickening K).trans hRK
  -- Every ball of radius `R` centred in `K` lies in `Ω`.
  have hball : ∀ x ∈ K, ball x R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    (ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK)
  -- `E ≥ 0`, from the comparison on a ball centred in `K`.
  have hE : 0 ≤ E := by
    obtain ⟨g, -, hug⟩ := hcmp x₁ hx₁ R hR le_rfl
    have : (ae (mu.restrict (ball x₁ R))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos mu x₁ hR).ne'
    obtain ⟨y, hy⟩ := hug.exists
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hR γ)).1 ((abs_nonneg _).trans hy)
  -- The scaled norm of `u` on such a ball, plus `E R^γ`, is at most `N`.
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N =
      R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu) + E * R ^ γ :=
    ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hN : ∀ x ∈ K, R ^ (-(Fintype.card ι : ℝ) / 2) *
      √(∫ y in ball x R, W1p.value u y ^ 2 ∂mu) + E * R ^ γ ≤ N := fun x hx => by
    rw [hNdef]
    gcongr
    · exact ae_of_all _ fun y => sq_nonneg _
    · exact (Lp.memLp (W1p.value u)).integrable_sq
    · exact hball x hx
  have hint : ∀ x ∈ K, IntegrableAtFilter (W1p.value u) (𝓝 x) mu := fun x hx => by
    simpa [nhdsWithin_eq_nhds.2 (Omega.isOpen.mem_nhds (hKΩ hx))] using
      (W1p.hasWeakFDerivOn u).locallyIntegrableOn x (hKΩ hx)
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, (C : ℝ) = C₀ * N / R ^ (α : ℝ) / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0, (M : ℝ) = D * N := ⟨⟨_, by positivity⟩, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = R / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  refine (holderOnWith_preciseRepresentative (C := C) (M := M) (ρ := ρ)
    (NNReal.coe_pos.1 hα) (NNReal.coe_pos.1 (hρ ▸ half_pos hR)) hint
    (fun x hx s hs hsR => ?_) (fun x hx => ?_)).mono_const ?_
  · -- Oscillation: `u` lies in an interval of length `L ≤ 2 C s^α` on `B(x, s)`.
    rw [hρ] at hsR
    obtain ⟨m', hm'⟩ := hosc h ha (hcmp x hx) hs hsR (hball x hx)
    have hL := Real.mul_rpow_div_mul_le_two_mul (α := (α : ℝ)) hC₀.le hs.le hR (hN x hx) hC
    refine ⟨m' + C * s ^ (α : ℝ), ?_⟩
    filter_upwards [hm'] with y hy
    rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hy.1, hy.2]
  · -- Boundedness: `|u| ≤ D N` on `B(x, R/2)`, by local boundedness.
    rw [hρ]
    obtain ⟨g, hg, hug⟩ := hcmp x hx R hR le_rfl
    filter_upwards [hbound h ha hR (hball x hx) hg hug] with y hy
    rw [Real.norm_eq_abs, hM]
    exact hy.trans (mul_le_mul_of_nonneg_left (hN x hx) hD.le)
  · -- The constant: `2 C = C₀ N R^(-α)` and `2 M / ρ^α = 2^(1+α) D N R^(-α) ≤ 4 D N R^(-α)`.
    rw [← hNdef]
    exact NNReal.max_two_mul_le_toNNReal hα1 hR hC₀.le (by positivity) (by positivity) hC hM hρ

/-! ### A right-hand side in `Lʳ`: splitting off the right-hand side on a ball -/

/-- **Splitting off the right-hand side on a ball.** Let `n ≥ 1` be the dimension and let `r > 1`
with `r > n/2`. There is `K > 0`, depending only on `n`, `r` and the normalization of `mu`, such
that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`λ, Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with `f ∈ Lʳ(B(x₀, ρ))` and `B(x₀, ρ) ⊆ Ω`. Then on
`B = B(x₀, ρ)` there is a weak solution `h ∈ H¹(B)` of the homogeneous equation
`-∂ᵢ(aⁱʲ ∂ⱼh) = 0` with

`|u - h| ≤ K ρ^(2 - n/r) ‖f‖_{Lʳ(B)} / λ` almost everywhere on `B`.

This transfers estimates for the homogeneous equation to equations with a right-hand side. -/
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
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨C, hC, hstamp⟩ := exists_ae_abs_value_le_mul_div_mul_rpow (mu := mu) hr hrn
  have hrn' : n * (2 - r) < 2 * r := by
    have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
    nlinarith [mul_pos hn (sub_pos.2 hr1)]
  set e : ℝ := 2 / n - (r : ℝ)⁻¹
  refine ⟨C * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e,
    mul_pos hC (Real.rpow_pos_of_pos (measureReal_ball_pos _ _ one_pos) _), ?_⟩
  intro Omega a lam Lam f u x₀ ρ h ha hf hu hρ hball
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hBfin : mu B ≠ ∞ := measure_ball_lt_top.ne
  have hBell : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) a lam Lam := h.mono_set hball
  have hBmeas : AEStronglyMeasurable a (mu.restrict B) :=
    ha.mono_measure (Measure.restrict_mono hball le_rfl)
  -- The weak solution `w ∈ H¹₀(B)` of `-∂ᵢ(aⁱʲ ∂ⱼw) = f` on `B`, and its bound.
  obtain ⟨w, hw, -⟩ :=
    hBell.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp (c := 0) (gamma := 0) hBmeas
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hBfin hr hrn' hf
  have hwbound := hstamp (Omega := B) (c := 0) (gamma := 0) hBfin hBell hBmeas
    aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => le_rfl) hf hw
  -- The homogeneous part `h = u|_B - w`.
  have huB := energyFormH1_restrictL_eq_setIntegral hB hu
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    hBell.upper_nonneg hBmeas aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hBell.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  refine ⟨W1p.restrictL hB u - (w : W1p mu B 2), fun v => ?_, ?_⟩
  · rw [energyFormH1_sub_left hcoeff, huB v, hw v, sub_self]
  -- `mu(B)^e = ρ^(2 - n/r) mu(B(0, 1))^e`.
  have hmeas : mu.real (ball x₀ ρ) ^ e =
      ρ ^ (2 - n / r) * mu.real (ball (0 : EuclideanSpace ℝ ι) 1) ^ e := by
    rw [Measure.addHaar_real_ball_of_pos _ _ hρ, finrank_euclideanSpace,
      Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    congr 2
    simp only [e, n]
    field_simp
  filter_upwards [hwbound, W1p.value_sub_ae (W1p.restrictL hB u) (w : W1p mu B 2),
    W1p.value_restrictL_ae hB u] with x hx hxs hxr
  rw [hxs, Pi.sub_apply, hxr, sub_sub_cancel]
  refine hx.trans_eq ?_
  simp only [B, Opens.coe_mk, hmeas]
  ring

/-! ### Local boundedness -/

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
  obtain ⟨K, hK, hsplit⟩ :=
    exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_add_of_ae_abs_sub_le (mu := mu) (lam := lam) (Lam := Lam)
  refine ⟨D * max 1 K, by positivity, ?_⟩
  intro Omega a f u x₀ R h ha hf hu hR hball
  obtain ⟨g, hg, hug⟩ := hsplit h ha hf hu hR hball
  filter_upwards [hbound h ha hR hball hg hug] with x hx
  refine hx.trans ?_
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := R ^ (2 - (Fintype.card ι : ℝ) / r) *
    (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  have hKP : K * R ^ (2 - (Fintype.card ι : ℝ) / r) *
      (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam = K * P := by
    simp only [P]
    ring
  rw [hKP, mul_assoc]
  gcongr
  nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left 1 K)) hQ,
    mul_nonneg (sub_nonneg.2 (le_max_right 1 K)) hP]

/-! ### Oscillation decay -/

/-- The splitting `TauCeti.PDE.exists_forall_energyFormH1_eq_zero_ae_abs_sub_le` on every ball
`B(x₀, ρ)` with `ρ ≤ R` inside a set `S` carrying `f`, bounded through the norm of `f` on `S`.
This is the comparison hypothesis of the estimates above, with `γ = 2 - n/r`. -/
private theorem exists_forall_exists_ae_abs_sub_le_of_memLp [Nonempty ι] {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R : ℝ} {S : Set (EuclideanSpace ℝ ι)},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict S) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ball x₀ R ⊆ S → S ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ ρ, 0 < ρ → ρ ≤ R → ∃ g : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
        (∀ v : W1p0 mu ⟨ball x₀ ρ, isOpen_ball⟩ 2,
          energyFormH1 a 0 0 g (v : W1p mu ⟨ball x₀ ρ, isOpen_ball⟩ 2) = 0) ∧
        ∀ᵐ x ∂mu.restrict (ball x₀ ρ), |W1p.value u x - W1p.value g x| ≤
          K * (eLpNorm f r (mu.restrict S)).toReal / lam *
            ρ ^ (2 - (Fintype.card ι : ℝ) / r) := by
  obtain ⟨K, hK, hsplit⟩ := exists_forall_energyFormH1_eq_zero_ae_abs_sub_le (mu := mu) hr hrn
  refine ⟨K, hK, fun {Omega a lam Lam f u x₀ R S} h ha hf hu hball hS ρ hρ hρR => ?_⟩
  have hρS : ball x₀ ρ ⊆ S := (ball_subset_ball hρR).trans hball
  obtain ⟨g, hg, hug⟩ := hsplit h ha (hf.mono_measure (Measure.restrict_mono hρS le_rfl)) hu hρ
    (hρS.trans hS)
  refine ⟨g, hg, ?_⟩
  have hfρ : (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal ≤
      (eLpNorm f r (mu.restrict S)).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hρS le_rfl))
  have := h.pos
  filter_upwards [hug] with x hx
  calc _ ≤ K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) *
        (eLpNorm f r (mu.restrict (ball x₀ ρ))).toReal / lam := hx
    _ ≤ K * ρ ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict S)).toReal / lam := by
        gcongr
    _ = _ := by ring

/-- **De Giorgi's interior oscillation estimate with a right-hand side.** Let `n ≥ 1` be the
dimension and let `r > 1` with `r > n/2`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `n`, `r` and the normalization of `mu`, such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `f ∈ Lʳ(B(x₀, R))`. If `B(x₀, R) ⊆ Ω` and `0 < s ≤ R/2`,
then almost everywhere on `B(x₀, s)` the function `u` takes values in an interval of length

`C (s / R)^α (R^(-n/2) ‖u‖_{L²(B(x₀, R))} + R^(2 - n/r) ‖f‖_{Lʳ(B(x₀, R))} / λ)`.

For `f = 0` this is the form of
`TauCeti.PDE.exists_ae_value_mem_Icc_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral`. -/
theorem exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_memLp [Nonempty ι] {lam Lam : ℝ}
    {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R s : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict (ball x₀ R)) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < s → s ≤ R / 2 → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∃ m' : ℝ, ∀ᵐ x ∂mu.restrict (ball x₀ s), W1p.value u x ∈ Icc m' (m' + C * (s / R) ^ α *
        (R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu) +
          R ^ (2 - (Fintype.card ι : ℝ) / r) *
            (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam)) := by
  have hγ : 0 < 2 - (Fintype.card ι : ℝ) / r := by
    rw [sub_pos, div_lt_iff₀ (by exact_mod_cast zero_lt_one.trans hr)]
    linarith only [hrn]
  obtain ⟨K, hK, hcmp⟩ := exists_forall_exists_ae_abs_sub_le_of_memLp (mu := mu) hr hrn
  obtain ⟨α, C, hα, hα1, hC, hosc⟩ :=
    exists_ae_value_mem_Icc_add_mul_rpow_mul_add_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) hγ
  refine ⟨α, C * max 1 K, hα, hα1, by positivity, ?_⟩
  intro Omega a f u x₀ R s h ha hf hu hs hsR hball
  have hR : 0 < R := by linarith only [hs, hsR]
  obtain ⟨m', hm'⟩ := hosc h ha (hcmp h ha hf hu subset_rfl hball) hs hsR hball
  refine ⟨m', ?_⟩
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ x in ball x₀ R, W1p.value u x ^ 2 ∂mu)
  set P := R ^ (2 - (Fintype.card ι : ℝ) / r) *
    (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  have hKP : K * (eLpNorm f r (mu.restrict (ball x₀ R))).toReal / lam *
      R ^ (2 - (Fintype.card ι : ℝ) / r) = K * P := by
    simp only [P]
    ring
  have hlen : C * (s / R) ^ α * (Q + K * P) ≤ C * max 1 K * (s / R) ^ α * (Q + P) :=
    calc C * (s / R) ^ α * (Q + K * P) ≤ C * (s / R) ^ α * (max 1 K * (Q + P)) := by
          gcongr
          nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left 1 K)) hQ,
            mul_nonneg (sub_nonneg.2 (le_max_right 1 K)) hP]
      _ = _ := by ring
  filter_upwards [hm'] with x hx
  rw [hKP] at hx
  exact ⟨hx.1, hx.2.trans (by linarith only [hlen])⟩

/-! ### Hölder continuity -/

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
  have hγ : 0 < 2 - (Fintype.card ι : ℝ) / r := by
    rw [sub_pos, div_lt_iff₀ (by exact_mod_cast zero_lt_one.trans hr)]
    linarith only [hrn]
  obtain ⟨Ks, hKs, hcmp⟩ := exists_forall_exists_ae_abs_sub_le_of_memLp (mu := mu) hr hrn
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_forall_ae_abs_sub_le (mu := mu) (lam := lam)
      (Lam := Lam) hγ
  refine ⟨α, C * max 1 Ks, hα, hα1, by positivity, ?_⟩
  intro Omega a f u K R h ha hf hu hR hRK
  refine (hhol h ha hR hRK fun x hx => hcmp h ha hf hu
    ((ball_subset_thickening hx R).trans ((thickening_subset_cthickening R K).trans hRK))
    subset_rfl).mono_const (Real.toNNReal_le_toNNReal ?_)
  set Q := R ^ (-(Fintype.card ι : ℝ) / 2) * √(∫ y in Omega, W1p.value u y ^ 2 ∂mu)
  set P := R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm f r (mu.restrict Omega)).toReal / lam
  have hQ : 0 ≤ Q := by positivity
  have hP : 0 ≤ P := by have := h.pos; positivity
  have hKP : Ks * (eLpNorm f r (mu.restrict Omega)).toReal / lam *
      R ^ (2 - (Fintype.card ι : ℝ) / r) = Ks * P := by
    simp only [P]
    ring
  rw [hKP]
  calc C * R ^ (-(α : ℝ)) * (Q + Ks * P) ≤ C * R ^ (-(α : ℝ)) * (max 1 Ks * (Q + P)) := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left 1 Ks)) hQ,
          mul_nonneg (sub_nonneg.2 (le_max_right 1 Ks)) hP]
    _ = _ := by ring

end PDE

end TauCeti
