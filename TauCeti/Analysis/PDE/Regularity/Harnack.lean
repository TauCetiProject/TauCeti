/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Crossover
public import TauCeti.Analysis.PDE.Regularity.ReverseHolder
public import TauCeti.Analysis.PDE.Regularity.Supersolution.Lp
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Moser's weak Harnack inequality and the Harnack inequality

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`. This file
proves, in dimension `n ≥ 3`, the two Harnack inequalities of Moser for the divergence-form
equation `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`, with no regularity of the coefficients beyond measurability.

* The **weak Harnack inequality**: if `u ∈ H¹(Ω)` is a weak supersolution, `a(u, v) ≥ 0` for
  every nonnegative `v ∈ H¹₀(Ω)`, and `u ≥ 0` almost everywhere, then for every exponent
  `0 < s < n/(n - 2)` and every ball with `B(x₀, 12√n r) ⊆ Ω`,

  `(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`,

  that is, the `L^s` average of `u` is controlled by its essential infimum.
* The **Harnack inequality**: if `u` is a weak solution, `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`,
  and `u ≥ 0` almost everywhere, then on every ball with `B(x₀, 24√n r) ⊆ Ω`,

  `u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

  that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`.

In both, `C` depends only on `λ`, `Λ`, the dimension, the normalization of the Haar measure and,
for the weak Harnack inequality, the exponent `s`. It does not depend on `u` or on the ball, so the
estimates are scale invariant.

The weak Harnack inequality is first proved for supersolutions with `u ≥ ε > 0`, with a constant
independent of `ε`, as in Moser's proof. On `B = B(x₀, 2r)`, at an exponent
`p₀ ≤ 2` proportional to `λ/Λ`, it combines

* the lower bound from negative powers, `u⁻¹ ≤ D |B|^{-1/p₀} ‖u⁻¹‖_{L^{p₀}(B)}` on `B(x₀, r)`
  (`TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow`), with
* the crossover estimate `⨍_B u^{p₀} · ⨍_B u^{-p₀} ≤ K`, from the John–Nirenberg inequality for
  `log u` (`TauCeti.PDE.exists_setAverage_rpow_mul_setAverage_rpow_neg_le`).

Together they bound `(⨍_B u^{p₀})^{1/p₀}` by `C u(x)` for almost every `x ∈ B(x₀, r)`, in every
dimension `n ≥ 1`. Moser's iteration for small positive powers
(`TauCeti.PDE.exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv`) then raises the
exponent from `p₀` to any `s < n/(n - 2)`. A nonnegative supersolution is reduced to this case by
applying it to `u + δ` on the bounded ball `B(x₀, 12√n r)`, where constants lie in `H¹`, and
letting `δ → 0`. The Harnack inequality combines the weak Harnack
inequality at `s = 1` with the local boundedness of subsolutions in `L¹`
(`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow`).

The restriction `n ≥ 3` is inherited from Moser's iteration, which uses the Sobolev inequality of
`W^{1,2}_0(Ω)` with exponent `2n/(n - 2)`; it is expressed, as there, by an exponent `2*` with
`1/2* + 1/n = 1/2`. Only the passage from `p₀` to larger exponents needs it.

## Main declarations

* `TauCeti.PDE.exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value`: the weak Harnack inequality
  at a small exponent `p₀`, in every dimension, for supersolutions bounded below by `ε > 0`.
* `TauCeti.PDE.exists_ae_setAverage_rpow_rpow_inv_le_mul_value`: Moser's weak Harnack
  inequality for nonnegative supersolutions, for every exponent `0 < s < n/(n - 2)`.
* `TauCeti.PDE.exists_ae_ae_value_le_mul_value`: Moser's Harnack inequality for nonnegative
  solutions.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.17, 8.18 and 8.20.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- **Moser's weak Harnack inequality at a small exponent.** Let `n ≥ 1` be the dimension. There
are an exponent `p₀ ∈ (0, 2]` and a constant `C > 0`, depending only on `λ`, `Λ`, the dimension
and the normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`,
with `u ≥ ε` almost everywhere for some `ε > 0`. Then on every ball with `B(x₀, 12√n r) ⊆ Ω`,

`(⨍_{B(x₀, 2r)} u^{p₀})^{1/p₀} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`.

The exponent `p₀` is proportional to `λ/Λ`. The constant does not depend on `u`, `ε` or the
ball. -/
theorem exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value [Nonempty ι] :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      ball x₀ (12 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ ≤ C * W1p.value u x := by
  -- Without `0 < λ ≤ Λ` there is no uniformly elliptic `a`, and any constants work.
  by_cases hlL : 0 < lam ∧ lam ≤ Lam
  swap
  · exact ⟨1, one_pos, one_le_two, 1, one_pos, fun h _ _ _ _ => absurd ⟨h.pos, h.le⟩ hlL⟩
  -- The exponent `p₀` at which the crossover estimate applies.
  obtain ⟨c, hc, K, hcross⟩ := exists_setAverage_rpow_mul_setAverage_rpow_neg_le (ι := ι)
  set p₀ := min (c * (lam / Lam)) 2
  have hp₀ : 0 < p₀ := lt_min (mul_pos hc (div_pos hlL.1 (hlL.1.trans_le hlL.2))) two_pos
  have hp₀c : |p₀| ≤ c * (lam / Lam) := (abs_of_pos hp₀).trans_le (min_le_left _ _)
  obtain ⟨D, hD, hlower⟩ := exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow
    (mu := mu) (lam := lam) (Lam := Lam) hp₀ (min_le_right _ _)
  set n : ℝ := (Fintype.card ι : ℝ)
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  set K' := max K 1
  have hK' : 0 < K' := lt_max_of_lt_right one_pos
  refine ⟨p₀, hp₀, min_le_right _ _, K' ^ p₀⁻¹ * D * V ^ p₀⁻¹, by positivity, ?_⟩
  intro Omega a u ε x₀ r h ha hu hε hεu hball
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √n := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have h2r : 0 < 2 * r := by positivity
  have hρΩ : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hpos : ∀ᵐ y ∂mu.restrict (ball x₀ (2 * r)), 0 < W1p.value u y :=
    (ae_restrict_of_ae_restrict_of_subset hρΩ hεu).mono fun y hy => hε.trans_le hy
  set Ap := ⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu
  set An := ⨍ y in ball x₀ (2 * r), W1p.value u y ^ (-p₀) ∂mu
  have hAp : 0 ≤ Ap := average_nonneg_of_ae (hpos.mono fun y hy => (Real.rpow_pos_of_pos hy _).le)
  have hAn : 0 ≤ An := average_nonneg_of_ae (hpos.mono fun y hy => (Real.rpow_pos_of_pos hy _).le)
  -- The crossover estimate `⨍_B u^{p₀} · ⨍_B u^{-p₀} ≤ K` on `B = B(x₀, 2r)`.
  have hcross' : Ap * An ≤ K' := (hcross mu h ha hu hε hεu (x₀ := x₀) (r := 2 * r)
    ((ball_subset_ball (by nlinarith)).trans hball) hp₀c).trans (le_max_left K 1)
  -- The lower bound `u⁻¹ ≤ D (2r)^{-n/p₀} (∫_B u^{-p₀})^{1/p₀}` on `B(x₀, r)`, in averaged form.
  have hint : ∫ y in ball x₀ (2 * r), (W1p.value u y)⁻¹ ^ p₀ ∂mu = (2 * r) ^ n * V * An := by
    have hvol : mu.real (ball x₀ (2 * r)) = (2 * r) ^ n * V := by
      rw [Measure.addHaar_real_ball_of_pos mu x₀ h2r, finrank_euclideanSpace,
        ← Real.rpow_natCast]
    rw [← hvol, ← smul_eq_mul (mu.real _) An, measure_smul_setAverage _ measure_ball_lt_top.ne]
    exact integral_congr_ae (hpos.mono fun y hy => by
      simp only [Real.rpow_neg hy.le, Real.inv_rpow hy.le])
  have h1 := hlower h ha hu hε hεu h2r hρΩ
  rw [mul_div_cancel_left₀ r two_ne_zero, hint, Real.mul_rpow (by positivity) hAn,
    Real.mul_rpow (by positivity) hV.le, ← Real.rpow_mul h2r.le] at h1
  filter_upwards [h1, ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hpos]
    with x hx hux
  have hone : 1 ≤ D * V ^ p₀⁻¹ * An ^ p₀⁻¹ * W1p.value u x := by
    have e : D * (2 * r) ^ (-n / p₀) * ((2 * r) ^ (n * p₀⁻¹) * V ^ p₀⁻¹ * An ^ p₀⁻¹) =
        D * V ^ p₀⁻¹ * An ^ p₀⁻¹ := by
      rw [neg_div, Real.rpow_neg h2r.le, div_eq_mul_inv n p₀]
      field_simp
    rw [e] at hx
    rw [← inv_mul_cancel₀ hux.ne']
    exact mul_le_mul_of_nonneg_right hx hux.le
  -- Multiply the crossover estimate by the lower bound.
  calc Ap ^ p₀⁻¹ ≤ Ap ^ p₀⁻¹ * (D * V ^ p₀⁻¹ * An ^ p₀⁻¹ * W1p.value u x) :=
        le_mul_of_one_le_right (by positivity) hone
    _ = (Ap * An) ^ p₀⁻¹ * (D * V ^ p₀⁻¹ * W1p.value u x) := by
        rw [Real.mul_rpow hAp hAn]
        ring
    _ ≤ K' ^ p₀⁻¹ * (D * V ^ p₀⁻¹ * W1p.value u x) := by gcongr
    _ = K' ^ p₀⁻¹ * D * V ^ p₀⁻¹ * W1p.value u x := by ring

/-- Moser's weak Harnack inequality for supersolutions bounded below by a positive constant `ε`,
with a constant independent of `ε`. -/
private theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹)
    {s : ℝ} (hs : 0 < s) (hsχ : s < pstar.toReal / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {ε : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < ε → (∀ᵐ x ∂mu.restrict Omega, ε ≤ W1p.value u x) →
      ball x₀ (12 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  have := Fintype.card_pos_iff.1 <| Nat.pos_of_ne_zero <| ne_zero_of_inv_add_inv_eq_inv hexp
  obtain ⟨p₀, hp₀, hp₀2, C₁, hC₁, hsmall⟩ :=
    exists_pos_ae_setAverage_rpow_rpow_inv_le_mul_value (mu := mu) (lam := lam) (Lam := Lam)
  obtain ⟨D, hD, hiter⟩ := exists_setAverage_rpow_rpow_inv_le_mul_setAverage_rpow_rpow_inv
    (mu := mu) (lam := lam) (Lam := Lam) hpstar hexp hp₀ hp₀2 hs hsχ
  refine ⟨D * C₁, by positivity, ?_⟩
  intro Omega a u ε x₀ r h ha hu hε hεu hball
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Moser's iteration passes from `L^{p₀}` on `B(x₀, 2r)` to `L^s` on `B(x₀, r)`.
  have hiter' := hiter h ha hu hε hεu (x₀ := x₀) (R := 2 * r)
    ((ball_subset_ball (by nlinarith)).trans hball)
  rw [mul_div_cancel_left₀ r two_ne_zero] at hiter'
  filter_upwards [hsmall h ha hu hε hεu hball] with x hx
  calc (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹
      ≤ D * (⨍ y in ball x₀ (2 * r), W1p.value u y ^ p₀ ∂mu) ^ p₀⁻¹ := hiter'
    _ ≤ D * (C₁ * W1p.value u x) := by gcongr
    _ = D * C₁ * W1p.value u x := by ring

/-- **Moser's weak Harnack inequality.** Let `2*` be the Sobolev exponent of `W^{1,2}` in
dimension `n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). For every exponent
`0 < s < 2*/2 = n/(n - 2)` there is `C > 0`, depending only on `λ`, `Λ`, `s`, the dimension and
the normalization of the additive Haar measure `mu`, with the following property. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a
nonnegative weak supersolution of `-∂ⱼ(aⁱʲ ∂ᵢu) ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`. Then on every ball with `B(x₀, 12√n r) ⊆ Ω`,

`(⨍_{B(x₀, r)} u^s)^{1/s} ≤ C u(x)` for almost every `x ∈ B(x₀, r)`.

The constant does not depend on `u` or the ball. The proof applies the estimate for supersolutions
bounded below by `δ > 0` to `u + δ` on the bounded ball `B(x₀, 12√n r)` and lets `δ → 0`. -/
theorem exists_ae_setAverage_rpow_rpow_inv_le_mul_value {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹)
    {s : ℝ} (hs : 0 < s) (hsχ : s < pstar.toReal / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (12 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ r),
        (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤ C * W1p.value u x := by
  have := Fintype.card_pos_iff.1 <| Nat.pos_of_ne_zero <| ne_zero_of_inv_add_inv_eq_inv hexp
  obtain ⟨C, hC, hpos⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value_of_pos (mu := mu)
    (lam := lam) (Lam := Lam) hpstar hexp hs hsχ
  refine ⟨C, hC, ?_⟩
  intro Omega a u x₀ r h ha hu hu0 hball
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) := Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  -- Work on the bounded open ball `U = B(x₀, 12√n r)`, where constants lie in `H¹(U)`.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ (12 * √(Fintype.card ι) * r), isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hrU : ball x₀ r ⊆ (U : Set (EuclideanSpace ℝ ι)) := ball_subset_ball (by nlinarith)
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hone : HasWeakFDerivOn mu U (Lp.const 2 (mu.restrict U) (1 : ℝ))
      fun x => innerSL ℝ ((0 : Lp (EuclideanSpace ℝ ι) 2 (mu.restrict U)) x) := by
    have hconst : HasWeakFDerivOn mu U (fun _ : EuclideanSpace ℝ ι => (1 : ℝ)) 0 :=
      hasWeakFDerivOn_iff.2 fun _ => hasWeakLineDerivOn_const 1
    refine (hconst.congr_ae
      (Lp.coeFn_const 2 _ (1 : ℝ)).symm).congr_ae_deriv ?_
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ ι) 2 (mu.restrict U)] with x hx
    rw [hx, Pi.zero_apply, Pi.zero_apply, map_zero]
  set one : W1p mu U 2 := W1p.mk _ _ hone
  have hu0r : ∀ᵐ y ∂mu.restrict (ball x₀ r), 0 ≤ W1p.value u y :=
    ae_restrict_of_ae_restrict_of_subset (hrU.trans hball) hu0
  have hmeas : AEStronglyMeasurable (W1p.value u) (mu.restrict (ball x₀ r)) :=
    (Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono (hrU.trans hball) le_rfl)
  -- For each `δ = 1/(k + 1)`, the estimate for the positive supersolution `u + δ` on `U`.
  have hδ : ∀ k : ℕ, ∀ᵐ x ∂mu.restrict (ball x₀ r),
      (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹ ≤
        C * (W1p.value u x + 1 / ((k : ℝ) + 1)) := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ0 : 0 < δ := Nat.one_div_pos_of_nat
    set w := W1p.restrictL hU u + δ • one
    have hwv : ∀ᵐ y ∂mu.restrict U, W1p.value w y = W1p.value u y + δ := by
      have hw : W1p.value w =
          W1p.value (W1p.restrictL hU u) + δ • Lp.const 2 (mu.restrict U) (1 : ℝ) := by
        rw [← W1p.valueL_apply, map_add, map_smul, W1p.valueL_apply, W1p.valueL_apply,
          W1p.value_mk]
      filter_upwards [W1p.value_restrictL_ae hU u,
        Lp.coeFn_add (W1p.value (W1p.restrictL hU u)) (δ • Lp.const 2 (mu.restrict U) (1 : ℝ)),
        Lp.coeFn_smul δ (Lp.const 2 (mu.restrict U) (1 : ℝ)),
        Lp.coeFn_const 2 (mu.restrict U) (1 : ℝ)] with y h1 h2 h3 h4
      rw [hw, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h1, Function.const_apply, smul_eq_mul,
        mul_one]
    have hwg : W1p.gradient w = W1p.gradient (W1p.restrictL hU u) := by
      rw [← W1p.gradientL_apply, map_add, map_smul, W1p.gradientL_apply, W1p.gradientL_apply,
        W1p.gradient_mk, smul_zero, add_zero]
    -- `u + δ` is a weak supersolution on `U`, since `a(u|_U, v) ≥ 0` and `∇(u + δ) = ∇u`.
    have hw : ∀ v : W1p0 mu U 2, (∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) →
        0 ≤ energyFormH1 a 0 0 w (v : W1p mu U 2) := by
      intro v hv
      have hneg := energyFormH1_restrictL_nonpos (b := 0) (c := 0) hU (u := (-1 : ℝ) • u)
        (fun v hv => by rw [energyFormH1_smul_left]; linarith [hu v hv]) v hv
      rw [map_smul, energyFormH1_smul_left] at hneg
      have heq : energyFormH1 a 0 0 w (v : W1p mu U 2) =
          energyFormH1 a 0 0 (W1p.restrictL hU u) (v : W1p mu U 2) := by
        simp [energyFormH1_def, hwg, driftForm_apply, massForm_apply]
      linarith
    have hδw : ∀ᵐ y ∂mu.restrict U, δ ≤ W1p.value w y := by
      filter_upwards [hwv, ae_restrict_of_ae_restrict_of_subset hball hu0] with y h1 h2
      rw [h1]
      linarith
    have hH := hpos (h.mono_set hball) (ha.mono_measure (Measure.restrict_mono hball le_rfl)) hw
      hδ0 hδw (x₀ := x₀) (r := r) subset_rfl
    have hwvr := ae_restrict_of_ae_restrict_of_subset hrU hwv
    rw [setAverage_eq, integral_congr_ae (hwvr.mono fun y hy => by rw [hy])] at hH
    rw [setAverage_eq]
    -- The average of `u^s` is at most that of `(u + δ)^s`.
    have hmono : (mu.real (ball x₀ r))⁻¹ • ∫ y in ball x₀ r, W1p.value u y ^ s ∂mu ≤
        (mu.real (ball x₀ r))⁻¹ • ∫ y in ball x₀ r, (W1p.value u y + δ) ^ s ∂mu := by
      by_cases hint : IntegrableOn (fun y => W1p.value u y ^ s) (ball x₀ r) mu
      · have hint' : IntegrableOn (fun y => (W1p.value u y + δ) ^ s) (ball x₀ r) mu := by
          refine Integrable.mono' ((hint.add (integrable_const (δ ^ s))).const_mul (2 ^ s))
            ((hmeas.aemeasurable.add_const δ).pow_const s).aestronglyMeasurable ?_
          filter_upwards [hu0r] with y hy
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
          have hys := Real.rpow_nonneg hy s
          have hδs := Real.rpow_nonneg hδ0.le s
          rcases le_total (W1p.value u y) δ with hyδ | hyδ
          · calc (W1p.value u y + δ) ^ s ≤ (2 * δ) ^ s := by gcongr; linarith
              _ = 2 ^ s * δ ^ s := Real.mul_rpow zero_le_two hδ0.le
              _ ≤ 2 ^ s * (W1p.value u y ^ s + δ ^ s) := by gcongr; linarith
          · calc (W1p.value u y + δ) ^ s ≤ (2 * W1p.value u y) ^ s := by gcongr; linarith
              _ = 2 ^ s * W1p.value u y ^ s := Real.mul_rpow zero_le_two hy
              _ ≤ 2 ^ s * (W1p.value u y ^ s + δ ^ s) := by gcongr; linarith
        refine smul_le_smul_of_nonneg_left (integral_mono_ae hint hint' ?_) (by positivity)
        filter_upwards [hu0r] with y hy
        exact Real.rpow_le_rpow hy (by linarith) hs.le
      · rw [integral_undef hint, smul_zero]
        exact smul_nonneg (by positivity)
          (integral_nonneg_of_ae (hu0r.mono fun y hy => Real.rpow_nonneg (by linarith) _))
    filter_upwards [hH, hwvr] with x hx hwx
    rw [hwx] at hx
    refine (Real.rpow_le_rpow ?_ hmono (inv_nonneg.2 hs.le)).trans hx
    exact smul_nonneg (by positivity)
      (integral_nonneg_of_ae (hu0r.mono fun y hy => Real.rpow_nonneg hy _))
  -- Let `δ → 0`.
  filter_upwards [ae_all_iff.2 hδ, hu0r] with x hx hx0
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hε hC)
  calc (⨍ y in ball x₀ r, W1p.value u y ^ s ∂mu) ^ s⁻¹
      ≤ C * (W1p.value u x + 1 / ((k : ℝ) + 1)) := hx k
    _ < C * W1p.value u x + ε := by
        rw [mul_add]
        have := mul_lt_mul_of_pos_left hk hC
        rw [mul_div_cancel₀ ε hC.ne'] at this
        linarith

/-- **Moser's Harnack inequality.** Let `2*` be the Sobolev exponent of `W^{1,2}` in dimension
`n`, so that `1/2* + 1/n = 1/2` and `2* < ∞` (this forces `n ≥ 3`). There is `C > 0`, depending
only on `λ`, `Λ`, the dimension and the normalization of the additive Haar measure `mu`, with the
following property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`,
and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = 0`, that is `a(u, v) = 0` for every
`v ∈ H¹₀(Ω)`, with `u ≥ 0` almost everywhere. Then on every ball with `B(x₀, 24√n r) ⊆ Ω`,

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. The constant does not depend on `u`
or the ball. -/
theorem exists_ae_ae_value_le_mul_value {pstar : ℝ≥0∞}
    (hpstar : pstar ≠ (∞ : ℝ≥0∞)) (hexp : pstar⁻¹ + (Fintype.card ι : ℝ≥0∞)⁻¹ = 2⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {r : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value u x) →
      ball x₀ (24 * √(Fintype.card ι) * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ r), ∀ᵐ y ∂mu.restrict (ball x₀ r),
        W1p.value u y ≤ C * W1p.value u x := by
  have := Fintype.card_pos_iff.1 <| Nat.pos_of_ne_zero <| ne_zero_of_inv_add_inv_eq_inv hexp
  -- The weak Harnack inequality at `s = 1`, and local boundedness in `L¹`.
  obtain ⟨C₁, hC₁, hweak⟩ := exists_ae_setAverage_rpow_rpow_inv_le_mul_value (mu := mu)
    (lam := lam) (Lam := Lam) hpstar hexp one_pos
    (one_lt_toReal_div_two_and_div_mul_eq hpstar hexp).1
  obtain ⟨D, hD, hbdd⟩ := exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow (mu := mu)
    (lam := lam) (Lam := Lam) one_pos one_le_two
  set V := mu.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hV : 0 < V := measureReal_ball_pos mu 0 one_pos
  refine ⟨D * V * C₁, by positivity, ?_⟩
  intro Omega a u x₀ r h ha hu hu0 hball
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hsqrt : 1 ≤ √(Fintype.card ι : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have h2Ω : ball x₀ (2 * r) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ball_subset_ball (by nlinarith)).trans hball
  have hw := hweak h ha (fun v _ => (hu v).ge) hu0 (x₀ := x₀) (r := 2 * r)
    ((ball_subset_ball (by nlinarith)).trans hball)
  have hb := hbdd (k := 0) h ha (fun v _ => (hu v).le) h2Ω
  rw [mul_div_cancel_left₀ r two_ne_zero] at hb
  -- On `B(x₀, 2r)` the positive part of `u` is `u`, so `u ≤ D (2r)^{-n} ∫_{B(x₀, 2r)} u`.
  have hmax : ∫ y in ball x₀ (2 * r), max (W1p.value u y - 0) 0 ^ (1 : ℝ) ∂mu =
      ∫ y in ball x₀ (2 * r), W1p.value u y ∂mu :=
    integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset h2Ω hu0).mono fun y hy => by
      simp [max_eq_left hy])
  have hvol : mu.real (ball x₀ (2 * r)) = (2 * r) ^ Fintype.card ι * V := by
    rw [Measure.addHaar_real_ball_of_pos mu x₀ (by positivity), finrank_euclideanSpace]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hw]
    with x hx
  filter_upwards [hb] with y hy
  rw [hmax, inv_one, Real.rpow_one, zero_add] at hy
  simp only [Real.rpow_one, inv_one] at hx
  rw [setAverage_eq, smul_eq_mul, hvol, inv_mul_le_iff₀ (by positivity)] at hx
  calc W1p.value u y
      ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ) / 1) * ∫ y in ball x₀ (2 * r), W1p.value u y ∂mu := hy
    _ ≤ D * (2 * r) ^ (-(Fintype.card ι : ℝ) / 1) * ((2 * r) ^ Fintype.card ι * V *
          (C₁ * W1p.value u x)) := by gcongr
    _ = D * V * C₁ * W1p.value u x := by
        rw [div_one, Real.rpow_neg (by positivity), Real.rpow_natCast]
        field_simp

end PDE

end TauCeti
