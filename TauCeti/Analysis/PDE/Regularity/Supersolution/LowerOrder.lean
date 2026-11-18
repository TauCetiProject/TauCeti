/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Power
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Moser's lower bound for positive supersolutions with lower-order terms

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants `0 < λ ≤ Λ`, and
let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ`. Let `u ∈ H¹(Ω)` be a weak
supersolution of the full divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` in `Ω`,

meaning `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, where `a(·, ·)` is the energy form with
drift `b` and mass coefficient `c`, and suppose `u ≥ m` almost everywhere for a constant `m > 0`.
This file proves **Moser's lower bound from negative powers**: for every `p > 0` and every
`σ ≥ 0` there is a constant `D`, depending only on `λ`, `Λ`, `p`, `σ`, the dimension and the
normalization of the Haar measure, such that on every ball `B(x₀, R) ⊆ Ω` with
`βR ≤ σλ` and `γR² ≤ σλ`,

`u⁻¹ ≤ D R^{-n/p} (∫_{B(x₀, R)} u⁻ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`

(`TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`). Since
`|B(x₀, R)|` is proportional to `Rⁿ`, this bounds `ess inf_{B(x₀, R/2)} u` from below by a
multiple of the mean `(⨍_{B(x₀, R)} u⁻ᵖ)^{-1/p}`. The constant does not depend on `m`, on the
centre or on `R`, and no sign condition on `c` is needed. The lower-order terms enter only through
the dimensionless quantities `βR/λ` and `γR²/λ`, which is why they must be bounded. This is the
negative-power half of Moser's weak Harnack inequality: the crossover estimate passes from it to
small positive powers.

## The argument

This is Moser's iteration with negative exponents (Gilbarg–Trudinger, the proof of
Theorem 8.18). For `P > 0` the power `w = u^{-P/2} = (u⁻¹)^{P/2}` satisfies the Caccioppoli
inequality for powers with lower-order terms
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow_lowerOrder`)
at the exponent `-P`, whose constants stay bounded as `P` grows except for a factor `P γ / λ` in the
mass term. A cutoff and the Sobolev inequality of `W^{1,2}_0(B(x₀, R))` at an exponent `2χ`,
`χ > 1` (`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`), give the reverse
Hölder step on concentric balls `B(x₀, r) ⊂ B(x₀, ρ) ⊆ B(x₀, R)`:

`‖u⁻¹‖_{L^{χP}(B(x₀, r))} ≤ (C R^{1 - nδ} A)^{2/P} ‖u⁻¹‖_{L^P(B(x₀, ρ))}`,
`A = (1 + Λ/λ)/(ρ - r) + β/λ + √(Pγ/λ)`,

with `δ = (χ - 1)/(2χ)`. Along the exponents `Pₖ = P χᵏ` and the radii `R/2 + R/2^{k+1}` the
factors multiply to a bound `F R^{n/Pₖ - n/P}` with `F` independent of `k`, because the logarithms
of the step constants grow at most linearly in `k` while the exponents `2/Pₖ` decay geometrically.
Letting `k → ∞` bounds `u⁻¹` on `B(x₀, R/2)`, since the essential supremum is at most the limit
inferior of the `Lᵖ` norms (`TauCeti.ae_enorm_le_of_tendsto_of_eLpNorm_le`).

## Main declarations

* `TauCeti.PDE.exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder`: Moser's lower
  bound from negative powers for positive supersolutions with lower-order terms.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6, the proof of Theorem 8.18.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Gradient NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The arithmetic of the gradient bound in the reverse Hölder step. If `g² ≤ 2 X + 2 Y`, where
`X` is bounded by the Caccioppoli inequality for the power `-P` with lower-order terms, and the
cutoff and zeroth-order integrals satisfy `Y ≤ G² I` and `Z ≤ I`, then
`g ≤ (2 (1 + Λ/λ) G + 2 (β/λ + √(Pγ/λ))) √I`. -/
private theorem le_mul_sqrt_of_sq_le_lowerOrder {g X Y Z I G P lam Lam beta gamma : ℝ}
    (hg : 0 ≤ g) (hlam : 0 < lam) (hLam : 0 ≤ Lam) (hP : 0 < P) (hβ : 0 ≤ beta)
    (hγ : 0 ≤ gamma) (hG : 0 ≤ G) (hI : 0 ≤ I) (hY0 : 0 ≤ Y) (hZ0 : 0 ≤ Z) (hY : Y ≤ G ^ 2 * I)
    (hZ : Z ≤ I)
    (hX : X ≤ (P / ((1 + P) * lam)) ^ 2 *
      (2 * Lam ^ 2 * Y + (beta ^ 2 + (1 + P) * lam * gamma) * Z))
    (hg2 : g ^ 2 ≤ 2 * X + 2 * Y) :
    g ≤ (2 * (1 + Lam / lam) * G + 2 * (beta / lam + √(P * gamma / lam))) * √I := by
  set κ := P / ((1 + P) * lam)
  set L := Lam / lam
  set B := beta / lam
  set Q := √(P * gamma / lam)
  have : 0 ≤ κ := by positivity
  -- `κ λ (1 + P) = P`, so `κ ≤ λ⁻¹` and `κ² (1 + P) λ γ = κ P γ ≤ P γ / λ`.
  have hκP : κ * ((1 + P) * lam) = P := div_mul_cancel₀ P (by positivity)
  have hκlam : κ * lam ≤ 1 := by nlinarith
  have hκL : κ * Lam ≤ L := by
    rw [le_div_iff₀ hlam]
    nlinarith
  have hκB : κ * beta ≤ B := by
    rw [le_div_iff₀ hlam]
    nlinarith
  have hQ : Q ^ 2 = P * gamma / lam := Real.sq_sqrt (by positivity)
  have hκγ : κ ^ 2 * ((1 + P) * lam * gamma) ≤ Q ^ 2 := by
    rw [hQ, le_div_iff₀ hlam,
      show κ ^ 2 * ((1 + P) * lam * gamma) * lam = κ * ((1 + P) * lam) * (κ * lam) * gamma by ring,
      hκP]
    nlinarith [mul_nonneg hP.le hγ]
  have hL0 : 0 ≤ L := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hXb : X ≤ (2 * L ^ 2 * G ^ 2 + (B ^ 2 + Q ^ 2)) * I := by
    calc X ≤ 2 * (κ * Lam) ^ 2 * Y + ((κ * beta) ^ 2 + κ ^ 2 * ((1 + P) * lam * gamma)) * Z := by
          nlinarith
      _ ≤ 2 * L ^ 2 * (G ^ 2 * I) + (B ^ 2 + Q ^ 2) * I := by
          gcongr
      _ = _ := by ring
  have hsq : g ^ 2 ≤ ((2 * (1 + L) * G + 2 * (B + Q)) * √I) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hI]
    nlinarith [mul_nonneg (mul_nonneg hL0 (sq_nonneg G)) hI, mul_nonneg (sq_nonneg G) hI,
      mul_nonneg (mul_nonneg hB0 hQ0) hI, mul_nonneg (mul_nonneg hL0 hG) hI,
      mul_nonneg (mul_nonneg (mul_nonneg hG hB0) hL0) hI, mul_nonneg (mul_nonneg hG hB0) hI,
      mul_nonneg (mul_nonneg hG hQ0) hI, mul_nonneg (mul_nonneg (mul_nonneg hG hQ0) hL0) hI]
  exact (pow_le_pow_iff_left₀ hg (by positivity) two_ne_zero).1 hsq

/-- The gradient bound of the reverse Hölder step. Let `u ≥ m > 0` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `‖b‖ ≤ β` and `|c| ≤ γ`, let `w ∈ H¹(Ω)` have value
`u^{-P/2}` for some `P > 0`, and let `ψ` be a smooth cutoff with values in `[0, 1]`, gradient at
most `G` and support in a set `B ⊆ Ω`. Then
`‖∇(ψ w)‖₂ ≤ (2 (1 + Λ/λ) G + 2 (β/λ + √(Pγ/λ))) (∫_B w²)^{1/2}`. -/
private theorem norm_gradient_contDiffSMul_le_lowerOrder {mu : Measure (EuclideanSpace ℝ ι)}
    [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) (hβ : 0 ≤ beta)
    (hγ : 0 ≤ gamma) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    {m : ℝ} (hm : 0 < m) (hmu : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) {P : ℝ} (hP : 0 < P)
    {w : W1p mu Omega 2}
    (hwv : W1p.value w =ᵐ[mu.restrict Omega] fun x => W1p.value u x ^ (-P / 2))
    {B : Set (EuclideanSpace ℝ ι)} (hB : B ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψr : range ψ ⊆ Icc 0 1)
    (hcpt : HasCompactSupport ψ) (hψB : tsupport ψ ⊆ B) {G : ℝ} (hψg : ∀ x, ‖∇ ψ x‖ ≤ G)
    {M : ℝ} (hM : 0 ≤ M) (hψM : ∀ x ∈ Omega, |ψ x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M) :
    ‖W1p.gradient (W1p.contDiffSMul ψ hψ hM hψM hgradM w)‖ ≤
      (2 * (1 + Lam / lam) * G + 2 * (beta / lam + √(P * gamma / lam))) *
        √(∫ x in B, W1p.value w x ^ 2 ∂mu) := by
  -- The Caccioppoli inequality for the power `-P`, and the bounds of its two integrals.
  have hcacc := h.setIntegral_sq_mul_norm_gradient_sq_le_of_ae_eq_rpow_lowerOrder ha hb hc
    hb_bound hc_bound hu hm hmu (by linarith : -P < 1) hwv hψ hcpt (hψB.trans hB)
  rw [abs_neg, abs_of_pos hP, sub_neg_eq_add] at hcacc
  have hwI := (Lp.memLp (W1p.value w)).integrable_sq
  have hY := W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hψg hψB hwI
    (Filter.Eventually.of_forall fun x => le_rfl)
  have hZ := W1p.setIntegral_sq_mul_value_sq_le w (fun x => by
      obtain ⟨h0, h1⟩ := hψr (mem_range_self x)
      nlinarith) hψB hwI (Filter.Eventually.of_forall fun x => le_rfl)
  rw [inter_eq_right.2 hB] at hY hZ
  exact le_mul_sqrt_of_sq_le_lowerOrder (norm_nonneg _) h.pos h.upper_nonneg hP hβ hγ
    ((norm_nonneg _).trans (hψg 0)) (integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => by positivity) (integral_nonneg fun x => by positivity) hY hZ hcacc
    (W1p.norm_gradient_contDiffSMul_sq_le hψ hM hψM hgradM w)

/-- **Moser's reverse Hölder step for negative powers, with lower-order terms.** There is a
constant `C ≥ 0`, depending only on the dimension, with the following property. Suppose that
`W^{1,2}_0(Ω)` satisfies the Sobolev inequality `‖v‖_q ≤ S ‖∇v‖₂`, and let `u ≥ m > 0` be a weak
supersolution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0` with `‖b‖ ≤ β` and `|c| ≤ γ`. Then for every
`P > 0` and all concentric balls `B(x₀, r) ⊂ B(x₀, ρ) ⊆ Ω`,

`‖u^{-P/2}‖_{L^q(B(x₀, r))} ≤ S C ((1 + Λ/λ)/(ρ - r) + β/λ + √(Pγ/λ)) ‖u^{-P/2}‖_{L²(B(x₀, ρ))}`. -/
private theorem exists_eLpNorm_rpow_neg_le_mul_eLpNorm_rpow_neg_lowerOrder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
      {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
      {lam Lam beta gamma : ℝ} {q : ℝ≥0∞} {S : ℝ} {u : W1p mu Omega 2} {m P : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ ENNReal.ofReal S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) → 0 < P →
      0 < r → r < ρ → ball x₀ ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (fun x => W1p.value u x ^ (-P / 2)) q (mu.restrict (ball x₀ r)) ≤
        ENNReal.ofReal S *
          ENNReal.ofReal (C * ((1 + Lam / lam) / (ρ - r) + beta / lam + √(P * gamma / lam))) *
          eLpNorm (fun x => W1p.value u x ^ (-P / 2)) 2 (mu.restrict (ball x₀ ρ)) := by
  obtain ⟨c₀, hc₀, hcut⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  refine ⟨4 * c₀ + 2, by positivity, ?_⟩
  intro mu _ Omega a b c lam Lam beta gamma q S u m P x₀ r ρ h ha hb hc hb_bound hc_bound hS hu hm
    hmu hP hr hrρ hball
  have hβ : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ (hball (mem_ball_self (hr.trans hrρ))))
  have hγ : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ (hball (mem_ball_self (hr.trans hrρ))))
  -- A cutoff equal to `1` on `B(x₀, r)`, supported in `closedBall x₀ ρ'` with `ρ' = (r + ρ)/2`.
  set ρ' := (r + ρ) / 2
  obtain ⟨ψ, hψ, hψr, hψ1, hψts, hψg, -⟩ := hcut x₀ hr.le (by simp only [ρ']; linarith : r < ρ')
  have hρ'B : closedBall x₀ ρ' ⊆ ball x₀ ρ := closedBall_subset_ball (by simp only [ρ']; linarith)
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ρ').of_isClosed_subset (isClosed_tsupport ψ) hψts
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- The power `w = u^{-P/2}` and the product `z = ψ w ∈ H¹₀(Ω)`, with its gradient bound.
  obtain ⟨w, hwv, -⟩ := W1p.exists_value_gradient_ae_eq_rpow (by simp) hm
    (by linarith : -P / 2 ≤ 1) hmu
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hz : z ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM' hgradM' hcpt
      ((hψts.trans hρ'B).trans hball) w
  have hgradz := norm_gradient_contDiffSMul_le_lowerOrder h ha hb hc hb_bound hc_bound hβ hγ hu hm
    hmu hP hwv hball hψ hψr hcpt (hψts.trans hρ'B) hψg hM hψM' hgradM'
  -- The norms of `u^{-P/2}` on the two balls, through `w` and `z`.
  have hwB : eLpNorm (fun x => W1p.value u x ^ (-P / 2)) 2 (mu.restrict (ball x₀ ρ)) =
      ENNReal.ofReal √(∫ x in ball x₀ ρ, W1p.value w x ^ 2 ∂mu) := by
    rw [← eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hball hwv),
      ((Lp.memLp (W1p.value w)).mono_measure
        (Measure.restrict_mono hball le_rfl)).eLpNorm_two_eq_ofReal_sqrt_integral]
    simp only [Real.norm_eq_abs, sq_abs]
  have hzr := W1p.eLpNorm_le_eLpNorm_value_contDiffSMul hψ hM hψM' hgradM' hwv
    ((ball_subset_ball hrρ.le).trans hball) measurableSet_ball
    (hψ1.mono ball_subset_closedBall) q
  have h1 : 0 ≤ (1 + Lam / lam) / (ρ - r) := by
    have := h.upper_nonneg; have := h.pos; have := sub_pos.2 hrρ; positivity
  have h2 : 0 ≤ beta / lam + √(P * gamma / lam) := by have := h.pos; positivity
  have h12 : 0 ≤ (4 * c₀ + 2) * ((1 + Lam / lam) / (ρ - r) + beta / lam + √(P * gamma / lam)) :=
    mul_nonneg (by positivity) (by linarith)
  calc eLpNorm (fun x => W1p.value u x ^ (-P / 2)) q (mu.restrict (ball x₀ r))
      ≤ ENNReal.ofReal S * ‖W1p.gradient z‖ₑ := hzr.trans (hS z hz)
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal ((4 * c₀ + 2) * ((1 + Lam / lam) / (ρ - r) +
          beta / lam + √(P * gamma / lam)) * √(∫ x in ball x₀ ρ, W1p.value w x ^ 2 ∂mu)) := by
        rw [← ofReal_norm]
        gcongr
        refine hgradz.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
        rw [show 2 * (1 + Lam / lam) * (c₀ / (ρ' - r)) = 4 * c₀ * ((1 + Lam / lam) / (ρ - r)) by
          rw [show ρ' - r = (ρ - r) / 2 by simp only [ρ']; ring]; field_simp; ring]
        nlinarith
    _ = _ := by rw [hwB, mul_assoc (ENNReal.ofReal S), ← ENNReal.ofReal_mul h12]

/-- The step constants of Moser's iteration multiply to a bound independent of the number of
steps: for `E ≥ 0`, `P > 0` and `χ > 1`, the products `∏_{j < k} (E (2χ)^j)^{2/(P χ^j)}` are
bounded in `k`, since the exponents `2/(P χ^j)` decay geometrically while the logarithms of the
bases grow at most linearly in `j`. -/
private theorem exists_prod_rpow_le {E P χ : ℝ} (hE : 0 ≤ E) (hP : 0 < P) (hχ : 1 < χ) :
    ∃ F : ℝ, 0 < F ∧
      ∀ k : ℕ, ∏ j ∈ Finset.range k, (E * (2 * χ) ^ j) ^ (2 / (P * χ ^ j)) ≤ F := by
  set E' := max E 1
  set r := χ⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hχ
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  -- The exponents are `2/P · rʲ`, and their sums with weights `1` and `j` are bounded.
  have ha : ∀ j : ℕ, 2 / (P * χ ^ j) = 2 / P * r ^ j := fun j => by
    simp only [r, inv_pow]
    field_simp
  have hs1 : Summable fun j : ℕ => 2 / P * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hs2 : Summable fun j : ℕ => (j : ℝ) * (2 / P * r ^ j) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 1 hrn).mul_left (2 / P)
    refine this.congr fun j => ?_
    ring
  refine ⟨E' ^ (∑' j : ℕ, 2 / P * r ^ j) * (2 * χ) ^ (∑' j : ℕ, (j : ℝ) * (2 / P * r ^ j)),
    by positivity, fun k => ?_⟩
  have hE' : 1 ≤ E' := le_max_right _ _
  have hb : 1 ≤ 2 * χ := by linarith
  calc ∏ j ∈ Finset.range k, (E * (2 * χ) ^ j) ^ (2 / (P * χ ^ j))
      ≤ ∏ j ∈ Finset.range k, (E' * (2 * χ) ^ j) ^ (2 / (P * χ ^ j)) := by
        gcongr with j
        exact le_max_left _ _
    _ = E' ^ (∑ j ∈ Finset.range k, 2 / P * r ^ j) *
          (2 * χ) ^ (∑ j ∈ Finset.range k, (j : ℝ) * (2 / P * r ^ j)) := by
        rw [Real.rpow_sum_of_pos (by positivity), Real.rpow_sum_of_pos (by positivity),
          ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
          ha]
    _ ≤ _ := by
        gcongr
        · exact hs1.sum_le_tsum _ fun j _ => by positivity
        · exact hs2.sum_le_tsum _ fun j _ => by positivity

/-- The step constant of the `k`-th step of the iteration, between the radii `R/2 + R/2^{k+1}`
and `R/2 + R/2^{k+2}` at the exponent `P χᵏ`: when `βR ≤ σλ` and `γR² ≤ σλ`,
`C R^{1-e} A ≤ C E₀ (2χ)ᵏ R^{-e}` with `E₀ = 4 (1 + L) + σ + √(Pσ)`, where
`A = (1 + L)/(R/2^{k+2}) + β/λ + √(Pχᵏγ/λ)`. -/
private theorem mul_rpow_sub_mul_le_mul_pow_mul_rpow_neg {C L beta gamma lam σ P χ R e : ℝ}
    (k : ℕ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hlam : 0 < lam) (hR : 0 < R) (hχ : 1 ≤ χ) (hP : 0 < P)
    (hσ : 0 ≤ σ) (hγ : 0 ≤ gamma) (hβR : beta * R ≤ σ * lam) (hγR : gamma * R ^ 2 ≤ σ * lam) :
    C * R ^ (1 - e) * ((1 + L) / (R / 2 ^ (k + 2)) + beta / lam + √(P * χ ^ k * gamma / lam)) ≤
      C * (4 * (1 + L) + σ + √(P * σ)) * (2 * χ) ^ k * R ^ (-e) := by
  have h2k : (2 : ℝ) ^ k ≤ (2 * χ) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) k
  have hχk : χ ^ k ≤ (2 * χ) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
  have h1k : (1 : ℝ) ≤ χ ^ k := one_le_pow₀ hχ
  have h1 : (1 + L) / (R / 2 ^ (k + 2)) ≤ 4 * (1 + L) * (2 * χ) ^ k / R := by
    rw [div_div_eq_mul_div, pow_add]
    gcongr ?_ / R
    nlinarith
  have h2 : beta / lam ≤ σ * (2 * χ) ^ k / R := by
    rw [div_le_div_iff₀ hlam hR]
    nlinarith [mul_le_mul_of_nonneg_left (h1k.trans hχk) (mul_nonneg hσ hlam.le)]
  have h3 : √(P * χ ^ k * gamma / lam) ≤ √(P * σ) * (2 * χ) ^ k / R := by
    rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, Real.sq_sqrt (by positivity),
      div_le_div_iff₀ hlam (by positivity)]
    have hχk2 : χ ^ k ≤ ((2 * χ) ^ k) ^ 2 :=
      hχk.trans (le_self_pow₀ (h1k.trans hχk) two_ne_zero)
    have : 0 ≤ P * gamma := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hγR (by positivity : 0 ≤ P * χ ^ k),
      mul_le_mul_of_nonneg_left hχk2 (by positivity : 0 ≤ P * σ * lam)]
  calc _ ≤ C * R ^ (1 - e) * (4 * (1 + L) * (2 * χ) ^ k / R + σ * (2 * χ) ^ k / R +
          √(P * σ) * (2 * χ) ^ k / R) := by gcongr
    _ = _ := by
        rw [Real.rpow_sub hR, Real.rpow_one, Real.rpow_neg hR.le]
        field_simp

section Iteration

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure] {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- On a ball `B ⊆ Ω` on which `u ≥ m > 0`, the function `u⁻¹` lies in `L^p(B)`, and its `L^p`
norm is `(∫_B u⁻ᵖ)^{1/p}`. -/
private theorem memLp_inv_and_toReal_eLpNorm_inv_eq {Omega : Opens (EuclideanSpace ℝ ι)}
    {u : W1p mu Omega 2} {m p : ℝ} (hm : 0 < m)
    (hmu : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) (hp : 0 < p) {x₀ : EuclideanSpace ℝ ι}
    {R : ℝ} (hball : ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    MemLp (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal p) (mu.restrict (ball x₀ R)) ∧
      (eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal p) (mu.restrict (ball x₀ R))).toReal =
        (∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu) ^ p⁻¹ := by
  have hmR : ∀ᵐ x ∂mu.restrict (ball x₀ R), m ≤ W1p.value u x :=
    ae_restrict_of_ae_restrict_of_subset hball hmu
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- `u⁻¹` is bounded by `1/m` on `B(x₀, R)`.
  have hmem : MemLp (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal p) (mu.restrict (ball x₀ R)) := by
    refine MemLp.of_bound (((Lp.aestronglyMeasurable (W1p.value u)).aemeasurable.inv
      ).aestronglyMeasurable.mono_measure (Measure.restrict_mono hball le_rfl)) m⁻¹ ?_
    filter_upwards [hmR] with x hx
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hm.trans_le hx)]
    exact inv_anti₀ hm hx
  refine ⟨hmem, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hp.le]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hmR] with x hx
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos (hm.trans_le hx)]

omit [DecidableEq ι] in
/-- On a set `s ⊆ Ω` on which `u ≥ m > 0`, the `Lᵗ` norm of `u^{-P/2}` is the `(P/2)`-th power of
the `L^{tP/2}` norm of `u⁻¹`. -/
private theorem eLpNorm_rpow_neg_eq_eLpNorm_inv_rpow {Omega : Opens (EuclideanSpace ℝ ι)}
    {u : W1p mu Omega 2} {m P : ℝ} (hm : 0 < m)
    (hmu : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) (hP : 0 < P)
    {s : Set (EuclideanSpace ℝ ι)} (hs : s ⊆ Omega) (t : ℝ≥0∞) :
    eLpNorm (fun x => W1p.value u x ^ (-P / 2)) t (mu.restrict s) =
      eLpNorm (fun x => (W1p.value u x)⁻¹) (t * ENNReal.ofReal (P / 2)) (mu.restrict s) ^
        (P / 2) := by
  rw [← eLpNorm_norm_rpow (fun x => (W1p.value u x)⁻¹)
    (((Lp.aestronglyMeasurable (W1p.value u)).aemeasurable.inv).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hs le_rfl)) (by positivity)]
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hmu] with x hx
  have hux : 0 < W1p.value u x := hm.trans_le hx
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hux, Real.inv_rpow hux.le, ← Real.rpow_neg hux.le,
    neg_div]

omit [DecidableEq ι] in
/-- The exponents of one step of the iteration. On sets `s, t ⊆ Ω` on which `u ≥ m > 0`, a bound
`‖u^{-P/2}‖_{L^{2χ}(s)} ≤ B ‖u^{-P/2}‖_{L²(t)}` with `B ≥ 0` is the bound
`‖u⁻¹‖_{L^{χP}(s)} ≤ B^{2/P} ‖u⁻¹‖_{L^P(t)}`. -/
private theorem eLpNorm_inv_le_ofReal_rpow_mul_of_eLpNorm_rpow_neg_le
    {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {m P χ B : ℝ} {q : ℝ≥0}
    (hq : (q : ℝ) = 2 * χ) (hm : 0 < m) (hmu : ∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x)
    (hP : 0 < P) (hB : 0 ≤ B) {s t : Set (EuclideanSpace ℝ ι)} (hs : s ⊆ Omega) (ht : t ⊆ Omega)
    (h : eLpNorm (fun x => W1p.value u x ^ (-P / 2)) q (mu.restrict s) ≤
      ENNReal.ofReal B * eLpNorm (fun x => W1p.value u x ^ (-P / 2)) 2 (mu.restrict t)) :
    eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal (χ * P)) (mu.restrict s) ≤
      ENNReal.ofReal (B ^ (2 / P)) *
        eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal P) (mu.restrict t) := by
  have hq' : (q : ℝ≥0∞) * ENNReal.ofReal (P / 2) = ENNReal.ofReal (χ * P) := by
    rw [← ENNReal.ofReal_coe_nnreal, hq, ← ENNReal.ofReal_mul (by rw [← hq]; exact q.2)]
    ring_nf
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (P / 2) = ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
    ring_nf
  rw [eLpNorm_rpow_neg_eq_eLpNorm_inv_rpow hm hmu hP hs,
    eLpNorm_rpow_neg_eq_eLpNorm_inv_rpow hm hmu hP ht, hq', h2] at h
  -- Raise both sides to the power `2/P`.
  have h2P : 0 ≤ 2 / P := by positivity
  have hpow := ENNReal.rpow_le_rpow h h2P
  rwa [ENNReal.mul_rpow_of_nonneg _ _ h2P, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg hB h2P,
    show P / 2 * (2 / P) = 1 by field_simp, ENNReal.rpow_one, ENNReal.rpow_one] at hpow

/-- One step of Moser's iteration with negative exponents inside a ball `B(x₀, R) ⊆ Ω`, with the
Sobolev inequality of `W^{1,2}_0(B(x₀, R))`. Let `χ > 1` with `(n - 2) χ < n`, and
`δ = (χ - 1)/(2χ)`. There is `C ≥ 0`, depending only on `χ`, the dimension and the normalization of
`mu`, such that for every `P > 0` and all concentric balls `B(x₀, r) ⊂ B(x₀, ρ) ⊆ B(x₀, R) ⊆ Ω`,

`‖u⁻¹‖_{L^{χP}(B(x₀, r))} ≤ (C R^{1 - nδ} A)^{2/P} ‖u⁻¹‖_{L^P(B(x₀, ρ))}`, where
`A = (1 + Λ/λ)/(ρ - r) + β/λ + √(Pγ/λ)`. -/
private theorem exists_eLpNorm_inv_le_ofReal_rpow_mul_eLpNorm_inv_of_ball_subset [Nonempty ι]
    {χ : ℝ} (hχ : 1 < χ) (hχn : ((Fintype.card ι : ℝ) - 2) * χ < Fintype.card ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {m P : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {r ρ R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) → 0 < P →
      0 < r → r < ρ → ρ ≤ R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal (χ * P)) (mu.restrict (ball x₀ r)) ≤
        ENNReal.ofReal ((C * R ^ (1 - Fintype.card ι * ((χ - 1) / (2 * χ))) *
          ((1 + Lam / lam) / (ρ - r) + beta / lam + √(P * gamma / lam))) ^ (2 / P)) *
          eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal P) (mu.restrict (ball x₀ ρ)) := by
  obtain ⟨C₀, hC₀, hstep⟩ := exists_eLpNorm_rpow_neg_le_mul_eLpNorm_rpow_neg_lowerOrder (ι := ι)
  have hδn : (χ - 1) / (2 * χ) < (Fintype.card ι : ℝ)⁻¹ := by
    rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ (Nat.cast_pos.2 Fintype.card_pos)]
    linarith
  -- The Sobolev inequality of `W^{1,2}_0(B(x₀, R))` at the exponent `q = 2χ`, with
  -- `1/2 - 1/q = (χ - 1)/(2χ)`, has the constant `K R^{1 - nδ}`.
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = 2 * χ := ⟨⟨2 * χ, by positivity⟩, rfl⟩
  obtain ⟨K, hK, hsob⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball (mu := mu)
      (p := 2) ENNReal.ofNat_ne_top (q := q)
      (by exact_mod_cast (show (2 : ℝ) ≤ q by rw [hq]; linarith))
      (δ := (χ - 1) / (2 * χ)) (by rw [ENNReal.toReal_ofNat, hq]; field_simp)
      (by rwa [finrank_euclideanSpace])
  simp only [finrank_euclideanSpace] at hsob
  refine ⟨K * C₀, by positivity, ?_⟩
  intro Omega a b c beta gamma u m P x₀ r ρ R h ha hb hc hb_bound hc_bound hu hm hmu hP hr hrρ hρR
    hball
  have hR : 0 < R := hr.trans (hrρ.trans_le hρR)
  -- Work with the restriction of `u` to `U = B(x₀, R)`, where the Sobolev inequality holds.
  set U : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ R, isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hwv : ∀ᵐ y ∂mu.restrict U, W1p.value (W1p.restrictL hU u) y = W1p.value u y :=
    W1p.value_restrictL_ae hU u
  have hmw : ∀ᵐ y ∂mu.restrict U, m ≤ W1p.value (W1p.restrictL hU u) y :=
    (hwv.and (ae_restrict_of_ae_restrict_of_subset hball hmu)).mono fun y hy => hy.1 ▸ hy.2
  have hUsub : ∀ {s : ℝ}, s ≤ R → ball x₀ s ⊆ (U : Set (EuclideanSpace ℝ ι)) :=
    fun hs => ball_subset_ball hs
  have hone := hstep mu (Omega := U) (u := W1p.restrictL hU u) (h.mono_set hball)
    (ha.mono_measure (Measure.restrict_mono hball le_rfl))
    (hb.mono_measure (Measure.restrict_mono hball le_rfl))
    (hc.mono_measure (Measure.restrict_mono hball le_rfl))
    (fun x hx => hb_bound x (hball hx)) (fun x hx => hc_bound x (hball hx)) (hsob hR rfl)
    (energyFormH1_restrictL_nonneg hU hu) hm hmw hP hr hrρ (hUsub hρR)
  -- On balls inside `U`, the restriction and `u` agree.
  have hwu : ∀ {t : ℝ≥0∞} {s : ℝ}, s ≤ R →
      eLpNorm (fun y => (W1p.value (W1p.restrictL hU u) y)⁻¹) t (mu.restrict (ball x₀ s)) =
        eLpNorm (fun y => (W1p.value u y)⁻¹) t (mu.restrict (ball x₀ s)) := fun hs =>
    eLpNorm_congr_ae ((ae_restrict_of_ae_restrict_of_subset (hUsub hs) hwv).mono
      fun y hy => by simp only [hy])
  have hA : 0 ≤ (1 + Lam / lam) / (ρ - r) + beta / lam + √(P * gamma / lam) := by
    have := (norm_nonneg _).trans (hb_bound x₀ (hball (mem_ball_self hR)))
    have := h.upper_nonneg; have := h.pos; have := sub_pos.2 hrρ
    positivity
  rw [← ENNReal.ofReal_mul (by positivity)] at hone
  have hpow := eLpNorm_inv_le_ofReal_rpow_mul_of_eLpNorm_rpow_neg_le hq hm hmw hP (by positivity)
    (hUsub (hrρ.le.trans hρR)) (hUsub hρR) hone
  rw [hwu (hrρ.le.trans hρR), hwu hρR] at hpow
  convert hpow using 4
  ring

/-- Iterating `exists_eLpNorm_inv_le_ofReal_rpow_mul_eLpNorm_inv_of_ball_subset` along the
exponents `P χᵏ` and the radii `R/2 + R/2^{k+1}`, on a ball with `βR ≤ σλ` and `γR² ≤ σλ`, bounds
the `L^{Pχᵏ}` norm of `u⁻¹` on the `k`-th ball by `∏_{j < k} (E (2χ)ʲ)^{2/(Pχʲ)} R^{n/(Pχᵏ) - n/P}`
times its `L^P` norm on `B(x₀, R)`, with `E` depending only on `λ`, `Λ`, `χ`, `P`, `σ`, the
dimension and the normalization of `mu`. The powers of `R` telescope. -/
private theorem exists_eLpNorm_inv_iterate_le [Nonempty ι] {χ : ℝ} (hχ : 1 < χ)
    (hχn : ((Fintype.card ι : ℝ) - 2) * χ < Fintype.card ι) {P σ : ℝ} (hP : 0 < P)
    (hσ : 0 ≤ σ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {m : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * R ≤ σ * lam → gamma * R ^ 2 ≤ σ * lam → ∀ k : ℕ,
        eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal (P * χ ^ k))
            (mu.restrict (ball x₀ (R / 2 + R / 2 ^ (k + 1)))) ≤
          ENNReal.ofReal ((∏ j ∈ Finset.range k, (E * (2 * χ) ^ j) ^ (2 / (P * χ ^ j))) *
            R ^ ((Fintype.card ι : ℝ) / (P * χ ^ k) - (Fintype.card ι : ℝ) / P)) *
          eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal P) (mu.restrict (ball x₀ R)) := by
  obtain ⟨C, hC, hstep⟩ := exists_eLpNorm_inv_le_ofReal_rpow_mul_eLpNorm_inv_of_ball_subset
    (mu := mu) (lam := lam) (Lam := Lam) hχ hχn
  refine ⟨C * (4 * (1 + |Lam / lam|) + σ + √(P * σ)), by positivity, ?_⟩
  intro Omega a b c beta gamma u m x₀ R h ha hb hc hb_bound hc_bound hu hm hmu hR hball hβR hγR
  have hlam := h.pos
  have hLam := h.upper_nonneg
  rw [abs_of_nonneg (div_nonneg hLam hlam.le)]
  have hβ : 0 ≤ beta := (norm_nonneg _).trans (hb_bound x₀ (hball (mem_ball_self hR)))
  have hγ : 0 ≤ gamma := (norm_nonneg _).trans (hc_bound x₀ (hball (mem_ball_self hR)))
  set n : ℝ := (Fintype.card ι : ℝ)
  set δ : ℝ := (χ - 1) / (2 * χ)
  set E := C * (4 * (1 + Lam / lam) + σ + √(P * σ))
  intro k
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, pow_zero, mul_one, sub_self, Real.rpow_zero,
      ENNReal.ofReal_one, one_mul, zero_add, pow_one, add_halves, le_refl]
  | succ k ih =>
    have hgap : R / 2 + R / 2 ^ (k + 1) - (R / 2 + R / 2 ^ (k + 1 + 1)) = R / 2 ^ (k + 2) := by
      field_simp
      ring
    have hone := hstep h ha hb hc hb_bound hc_bound hu hm hmu (by positivity : 0 < P * χ ^ k)
      (r := R / 2 + R / 2 ^ (k + 1 + 1)) (ρ := R / 2 + R / 2 ^ (k + 1)) (by positivity)
      (by gcongr <;> norm_num) (by
        have : R / 2 ^ (k + 1) ≤ R / 2 := div_le_div_of_nonneg_left hR.le two_pos
          (le_self_pow₀ one_le_two (Nat.succ_ne_zero k))
        linarith) hball
    rw [hgap, show χ * (P * χ ^ k) = P * χ ^ (k + 1) by ring] at hone
    -- The step constant is at most `(E (2χ)ᵏ R^{-nδ})^{2/(Pχᵏ)}`.
    have hbase := mul_rpow_sub_mul_le_mul_pow_mul_rpow_neg (e := n * δ) k hC
      (div_nonneg h.upper_nonneg hlam.le) hlam hR hχ.le hP hσ hγ hβR hγR
    refine hone.trans ?_
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (by positivity) hbase (by positivity))) ih).trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have hexpo : n / (P * χ ^ (k + 1)) - n / P = (n / (P * χ ^ k) - n / P) +
        -(n * δ) * (2 / (P * χ ^ k)) := by
      simp only [δ]
      field_simp
      ring
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hR.le _), ← Real.rpow_mul hR.le,
      Finset.prod_range_succ, hexpo, Real.rpow_add hR]
    ring

/-- **Moser's lower bound from negative powers, with lower-order terms.** Let `n ≥ 1` be the
dimension, `p > 0` and `σ ≥ 0`. There is `D > 0`, depending only on `λ`, `Λ`, `p`, `σ`, the
dimension and the normalization of the additive Haar measure `mu`, with the following property.
Let `a` be measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `b` and `c` be
measurable with `‖b‖ ≤ β` and `|c| ≤ γ` on `Ω`, and let `u ∈ H¹(Ω)` be a weak supersolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≥ 0`, that is `a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, with
`u ≥ m` almost everywhere for some `m > 0`. Then on every ball `B(x₀, R) ⊆ Ω` with `βR ≤ σλ` and
`γR² ≤ σλ`,

`u⁻¹ ≤ D R^{-n/p} (∫_{B(x₀, R)} u⁻ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.

The constant does not depend on `u`, `m`, `β`, `γ`, the centre or the radius, and no sign
condition on `c` is needed. -/
theorem exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_lowerOrder [Nonempty ι] {p σ : ℝ}
    (hp : 0 < p) (hσ : 0 ≤ σ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {c : EuclideanSpace ℝ ι → ℝ} {beta gamma : ℝ} {u : W1p mu Omega 2} {m : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) → AEStronglyMeasurable b (mu.restrict Omega) →
      AEStronglyMeasurable c (mu.restrict Omega) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta) →
      (∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      beta * R ≤ σ * lam → gamma * R ^ 2 ≤ σ * lam →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        (W1p.value u x)⁻¹ ≤ D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu) ^ p⁻¹ := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  -- The exponent `χ = 1 + 1/n` of the Sobolev inequality, with `(n - 2) χ = n - 1 - 2/n < n`.
  set χ : ℝ := 1 + n⁻¹
  have hχ : 1 < χ := lt_add_of_pos_right 1 (by positivity)
  have hχn : (n - 2) * χ < n := by
    have : (n - 2) * χ = n - 1 - 2 * n⁻¹ := by
      simp only [χ]
      field_simp
      ring
    rw [this]
    have : 0 < n⁻¹ := by positivity
    linarith
  obtain ⟨E, hE, hiter⟩ := exists_eLpNorm_inv_iterate_le (mu := mu) (lam := lam) (Lam := Lam) hχ
    hχn hp hσ
  obtain ⟨F, hF, hprod⟩ := exists_prod_rpow_le hE hp hχ
  refine ⟨F, hF, ?_⟩
  intro Omega a b c beta gamma u m x₀ R h ha hb hc hb_bound hc_bound hu hm hmu hR hball hβR hγR
  obtain ⟨hmem, hN⟩ := memLp_inv_and_toReal_eLpNorm_inv_eq hm hmu hp hball
  -- The `k`-th step bounds `‖u⁻¹‖_{L^{pχᵏ}(B(x₀, R/2))}` uniformly in `k`.
  have hk : ∀ k : ℕ, eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal (p * χ ^ k))
      (mu.restrict (ball x₀ (R / 2))) ≤ ENNReal.ofReal (F * R ^ (n / (p * χ ^ k) - n / p)) *
        eLpNorm (fun x => (W1p.value u x)⁻¹) (ENNReal.ofReal p) (mu.restrict (ball x₀ R)) := by
    intro k
    refine (eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball ?_) le_rfl)).trans
      ((hiter h ha hb hc hb_bound hc_bound hu hm hmu hR hball hβR hγR k).trans ?_)
    · have : 0 < R / 2 ^ (k + 1) := by positivity
      linarith
    · gcongr
      exact hprod k
  -- The exponents `pχᵏ` tend to `∞` and the right sides to `F R^{-n/p} ‖u⁻¹‖_{L^p(B(x₀, R))}`.
  have hχk := (tendsto_pow_atTop_atTop_of_one_lt hχ).const_mul_atTop hp
  have hexp : Tendsto (fun k : ℕ => n / (p * χ ^ k) - n / p) atTop (𝓝 (-n / p)) := by
    simpa [neg_div] using (tendsto_const_nhds (x := n)).div_atTop hχk |>.sub_const (n / p)
  have hlim := ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_ofReal ((tendsto_const_nhds.rpow hexp (.inl hR.ne')).const_mul F))
    (.inr hmem.eLpNorm_ne_top)
  filter_upwards [ae_enorm_le_of_tendsto_of_eLpNorm_le (tendsto_real_toNNReal_atTop.comp hχk)
    hlim (.of_forall hk)] with x hx
  rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top, ← ENNReal.ofReal_mul (by positivity),
    Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff (by positivity), hN] at hx
  exact (le_abs_self _).trans hx

end Iteration

end PDE

end TauCeti
