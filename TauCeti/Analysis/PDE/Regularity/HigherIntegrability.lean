/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Divergence
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Gehring

/-!
# Meyers' higher integrability for divergence-form equations

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` in `Ω`, with `F ∈ L²(Ω; ℝⁿ)`,

that is, `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. No regularity of `a` beyond
measurability is assumed, and no boundary condition is imposed on `u`.

**Meyers' theorem** says that `∇u` is better than square integrable: there is `ε₀ > 0`,
depending on an upper bound `K` for the ellipticity ratio `Λ/λ` but not on the domain, the
coefficients, the solution or the datum, such that for `0 < ε ≤ ε₀` and every ball
`B = B(x₀, R) ⊆ Ω`, with `½B = B(x₀, R/2)`,

`⨍_{½B} ‖∇u‖ ^ (2 + ε) ≤ C ((⨍_B ‖∇u‖²) ^ ((2 + ε)/2) + ⨍_B (‖F‖/λ) ^ (2 + ε))`,

with `C` likewise independent of `Ω`, `a`, `u`, `F` and the ball. In particular
`∇u ∈ L^{2 + ε}_loc` whenever `F ∈ L^{2 + ε}_loc`. The gain `ε₀` cannot be uniform in `K`: in
Meyers' planar example (`TauCeti.PDE.exists_w1p_value_ae_eq_meyersSolution_iff`), with
ellipticity ratio `1 / μ²`, a weak solution of the homogeneous equation lies in `W^{1,p}` near the
origin exactly for `p < 2 / (1 - μ)`.

The proof is the classical one. Fix an exponent `s < 2` with `1/s - 1/2 < 1/n`. On a ball
`B(y, 2ρ) ⊆ Ω`, Caccioppoli's inequality for `u` minus its mean over the ball
(`TauCeti.PDE.exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence`) and the
Sobolev–Poincaré inequality `(⨍ |u - u_B|²)^{1/2} ≤ C ρ (⨍ ‖∇u‖^s)^{1/s}`
(`TauCeti.W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset`) combine to the
**reverse Hölder inequality**

`⨍_{B(y, ρ)} ‖∇u‖² ≤ b (⨍_{B(y, 2ρ)} ‖∇u‖ ^ s) ^ (2/s) + b ⨍_{B(y, 2ρ)} (‖F‖/λ)²`,

whose constant `b` is invariant under dilations. Gehring's lemma, applied to `‖∇u‖ ^ s` with the
exponent `2/s > 1` (`TauCeti.exists_setLAverage_rpow_add_le_of_rpow`), improves it to the higher
integrability.

## Main declarations

* `TauCeti.PDE.exists_setLAverage_enorm_gradient_sq_le_divergence`: the reverse Hölder
  inequality for the gradient.
* `TauCeti.PDE.exists_setLAverage_enorm_gradient_rpow_le_divergence`: **Meyers' higher
  integrability estimate**.
* `TauCeti.PDE.exists_memLp_gradient_ball_divergence`: its qualitative form, `∇u ∈ L^{2 + ε}` on
  `B(x₀, R/2)` whenever `F ∈ L^{2 + ε}` on `B(x₀, R) ⊆ Ω`.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorem 2.
* M. Giaquinta, G. Modica, *Regularity results for some classes of higher order nonlinear
  elliptic systems*, J. Reine Angew. Math. **311/312** (1979), 145–169.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 6.4.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

namespace PDE

/-- The integral of `‖f‖²` over a set, read in `ℝ≥0∞`. -/
private theorem ofReal_setIntegral_norm_sq_eq {X V : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup V] {f : X → V} {S : Set X}
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) S μ) :
    ENNReal.ofReal (∫ x in S, ‖f x‖ ^ 2 ∂μ) = ∫⁻ x in S, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

omit [DecidableEq ι] in
/-- An estimate `∫_{B(y, ρ)} ‖g‖² ≤ α ∫_{B(y, 2ρ)} ‖f‖² + β ∫_{B(y, 2ρ)} ‖G‖²` between Bochner
integrals, read as one between averages in `ℝ≥0∞`: the ratio of the measures of the two balls is
`2ⁿ`. -/
private theorem setLAverage_enorm_sq_le_of_setIntegral_le {V W X : Type*} [NormedAddCommGroup V]
    [NormedAddCommGroup W] [NormedAddCommGroup X] {g : EuclideanSpace ℝ ι → V}
    {f : EuclideanSpace ℝ ι → W} {G : EuclideanSpace ℝ ι → X} {y : EuclideanSpace ℝ ι}
    {ρ α β : ℝ} (hρ : 0 < ρ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hg : IntegrableOn (fun x => ‖g x‖ ^ 2) (ball y ρ) mu)
    (hf : IntegrableOn (fun x => ‖f x‖ ^ 2) (ball y (2 * ρ)) mu)
    (hG : IntegrableOn (fun x => ‖G x‖ ^ 2) (ball y (2 * ρ)) mu)
    (h : ∫ x in ball y ρ, ‖g x‖ ^ 2 ∂mu ≤
      α * ∫ x in ball y (2 * ρ), ‖f x‖ ^ 2 ∂mu + β * ∫ x in ball y (2 * ρ), ‖G x‖ ^ 2 ∂mu) :
    ⨍⁻ x in ball y ρ, ‖g x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι)) *
        (ENNReal.ofReal α * ⨍⁻ x in ball y (2 * ρ), ‖f x‖ₑ ^ (2 : ℝ) ∂mu +
          ENNReal.ofReal β * ⨍⁻ x in ball y (2 * ρ), ‖G x‖ₑ ^ (2 : ℝ) ∂mu) := by
  have hμ2 : mu (ball y (2 * ρ)) =
      ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι)) * mu (ball y ρ) := by
    rw [Measure.addHaar_ball_of_pos mu y (by positivity), Measure.addHaar_ball_of_pos mu y hρ,
      mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hμ2top : mu (ball y (2 * ρ)) ≠ ∞ := measure_ball_lt_top.ne
  rw [setLAverage_eq]
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ofReal_setIntegral_norm_sq_eq hg]
  calc ENNReal.ofReal (∫ x in ball y ρ, ‖g x‖ ^ 2 ∂mu)
      ≤ ENNReal.ofReal (α * ∫ x in ball y (2 * ρ), ‖f x‖ ^ 2 ∂mu
          + β * ∫ x in ball y (2 * ρ), ‖G x‖ ^ 2 ∂mu) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal α * ENNReal.ofReal (∫ x in ball y (2 * ρ), ‖f x‖ ^ 2 ∂mu)
          + ENNReal.ofReal β * ENNReal.ofReal (∫ x in ball y (2 * ρ), ‖G x‖ ^ 2 ∂mu) := by
        have hP := setIntegral_nonneg (μ := mu) (measurableSet_ball (x := y) (ε := 2 * ρ))
          fun x _ => sq_nonneg ‖f x‖
        have hQ := setIntegral_nonneg (μ := mu) (measurableSet_ball (x := y) (ε := 2 * ρ))
          fun x _ => sq_nonneg ‖G x‖
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hα,
          ENNReal.ofReal_mul hβ]
    _ = ENNReal.ofReal α * (mu (ball y (2 * ρ)) * ⨍⁻ x in ball y (2 * ρ), ‖f x‖ₑ ^ (2 : ℝ) ∂mu)
          + ENNReal.ofReal β *
            (mu (ball y (2 * ρ)) * ⨍⁻ x in ball y (2 * ρ), ‖G x‖ₑ ^ (2 : ℝ) ∂mu) := by
        rw [ofReal_setIntegral_norm_sq_eq hf, ofReal_setIntegral_norm_sq_eq hG,
          measure_mul_setLAverage _ hμ2top, measure_mul_setLAverage _ hμ2top]
    _ = _ := by
        rw [hμ2]
        ring

/-- The datum term of the reverse Hölder inequality, with `λ` moved inside the average. -/
private theorem ofReal_div_sq_mul_setLAverage_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S : Set X} (f : X → ℝ≥0∞) {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    ENNReal.ofReal (c / lam ^ 2) * ⨍⁻ x in S, f x ^ (2 : ℝ) ∂μ =
      ENNReal.ofReal c * ⨍⁻ x in S, (f x / ENNReal.ofReal lam) ^ (2 : ℝ) ∂μ := by
  rw [← laverage_const_mul ENNReal.ofReal_ne_top, ← laverage_const_mul ENNReal.ofReal_ne_top]
  congr 1
  funext x
  rw [ENNReal.div_rpow_of_nonneg _ _ zero_le_two, ENNReal.ofReal_rpow_of_pos hlam, Real.rpow_two,
    ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The constants of the reverse Hölder inequality: `A (C/ρ)² (2cρ)² = A C² (2c)²` does not depend
on `ρ`, and both coefficients are at most `2ⁿ (A C² (2c)² + 12)`. -/
private theorem ofReal_two_pow_mul_add_le {n : ℕ} {A C c ρ : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hρ : 0 < ρ) (G Φ : ℝ≥0∞) :
    ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (A * (C / ρ) ^ 2) *
        (ENNReal.ofReal (c * (2 * ρ)) ^ (2 : ℝ) * G) + 12 * Φ) ≤
      ((2 ^ n * (A * C ^ 2 * (2 * c) ^ 2) + 2 ^ n * 12).toNNReal : ℝ≥0∞) * G +
        ((2 ^ n * (A * C ^ 2 * (2 * c) ^ 2) + 2 ^ n * 12).toNNReal : ℝ≥0∞) * Φ := by
  have hconst : ENNReal.ofReal (A * (C / ρ) ^ 2) * ENNReal.ofReal (c * (2 * ρ)) ^ (2 : ℝ) =
      ENNReal.ofReal (A * C ^ 2 * (2 * c) ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc (by positivity)) zero_le_two,
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_two]
    congr 1
    field_simp
  have hsplit : ENNReal.ofReal (2 ^ n) * (ENNReal.ofReal (A * C ^ 2 * (2 * c) ^ 2) * G + 12 * Φ) =
      ENNReal.ofReal (2 ^ n * (A * C ^ 2 * (2 * c) ^ 2)) * G + ENNReal.ofReal (2 ^ n * 12) * Φ := by
    rw [ENNReal.ofReal_mul (p := 2 ^ n) (by positivity),
      ENNReal.ofReal_mul (p := 2 ^ n) (by positivity), ENNReal.ofReal_ofNat]
    ring
  rw [← mul_assoc, hconst, hsplit]
  gcongr
  · exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  · exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (by positivity))

omit [DecidableEq ι] in
/-- The Sobolev–Poincaré inequality from `Lˢ` to `L²` for `u ∈ H¹(Ω)` on a ball `B(y, r) ⊆ Ω`,
squared: `⨍_B |u - u_B|² ≤ (c r)² (⨍_B ‖∇u‖ ^ s) ^ (2/s)`. -/
private theorem setLAverage_enorm_value_sub_setAverage_sq_le [Nonempty ι] {s : ℝ≥0}
    [Fact (1 ≤ (s : ℝ≥0∞))] (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹)
    {Omega : Opens (EuclideanSpace ℝ ι)} (u : W1p mu Omega 2) {y : EuclideanSpace ℝ ι} {r : ℝ}
    (hr : 0 < r) (hball : ball y r ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ⨍⁻ x in ball y r, ‖W1p.value u x - ⨍ z in ball y r, W1p.value u z ∂mu‖ₑ ^ (2 : ℝ) ∂mu ≤
      ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι) / finrank ℝ (EuclideanSpace ℝ ι) *
          ((1 - ((s : ℝ)⁻¹ - 2⁻¹)) / ((finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹ -
            ((s : ℝ)⁻¹ - 2⁻¹))) ^ (1 - ((s : ℝ)⁻¹ - 2⁻¹)) * r) ^ (2 : ℝ) *
        (⨍⁻ x in ball y r, ‖W1p.gradient u x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) := by
  have hSP := W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset (p := s)
    ENNReal.coe_ne_top (by exact_mod_cast hs2 : (s : ℝ≥0∞) ≤ 2) hr hball (q := 2)
    (by exact_mod_cast hs2) (by simp) hsn u
  rw [ENNReal.coe_toReal, NNReal.coe_ofNat] at hSP
  have := ENNReal.rpow_le_rpow hSP (by norm_num : (0 : ℝ) ≤ 2)
  rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul,
    inv_mul_eq_div] at this

/-- **The reverse Hölder inequality for the gradient of a weak solution.** Let `n ≥ 1` be the
dimension, let `1 ≤ s ≤ 2` with `1/s - 1/2 < 1/n`, and let `K` bound the ellipticity ratio.
There is `b`, independent of the domain, the coefficients, the solution, the datum and the ball,
with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for
every `v ∈ H¹₀(Ω)`. For every ball with `B(y, 2ρ) ⊆ Ω`,

`⨍_{B(y, ρ)} ‖∇u‖² ≤ b (⨍_{B(y, 2ρ)} ‖∇u‖ ^ s) ^ (2/s) + b ⨍_{B(y, 2ρ)} (‖F‖/λ)²`.

The averages are extended-valued. -/
theorem exists_setLAverage_enorm_gradient_sq_le_divergence [Nonempty ι] {s : ℝ≥0}
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) (K : ℝ) :
    ∃ b : ℝ≥0, ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {y : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < ρ → ball y (2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍⁻ x in ball y ρ, ‖W1p.gradient u x‖ₑ ^ (2 : ℝ) ∂mu ≤
        b * (⨍⁻ x in ball y (2 * ρ), ‖W1p.gradient u x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) +
          b * ⨍⁻ x in ball y (2 * ρ), (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ) ∂mu := by
  obtain ⟨C, -, hC⟩ :=
    exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence (ι := ι)
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set δ : ℝ := (s : ℝ)⁻¹ - 2⁻¹
  set c : ℝ := 2 ^ n / n * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ)
  set A : ℝ := 2 * ((2 * K) ^ 2 + 1)
  have hA0 : 0 ≤ A := by
    simp only [A]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Module.finrank_pos
  have hδ1 : δ < 1 := hsn.trans_le (inv_le_one_of_one_le₀ hn1)
  have hc : 0 ≤ c := mul_nonneg (by positivity)
    (Real.rpow_nonneg (div_nonneg (by linarith) (sub_nonneg.2 hsn.le)) _)
  refine ⟨(2 ^ n * (A * C ^ 2 * (2 * c) ^ 2) + 2 ^ n * 12).toNNReal, ?_⟩
  intro Omega a lam Lam F u y ρ h hK ha hF hu hρ hball
  have hlam : 0 < lam := h.pos
  set m := ⨍ z in ball y (2 * ρ), W1p.value u z ∂mu
  -- Caccioppoli's inequality for `u - m`, with its constant bounded through `Λ ≤ K λ`.
  have hIρ : ∫ x in ball y ρ, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      A * (C / ρ) ^ 2 * ∫ x in ball y (2 * ρ), ‖W1p.value u x - m‖ ^ 2 ∂mu
        + 12 / lam ^ 2 * ∫ x in ball y (2 * ρ), ‖F x‖ ^ 2 ∂mu := by
    refine (hC h ha hF hu hρ hball).trans ?_
    have hratio : 2 * Lam / lam ≤ 2 * K := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hlam).2 hK) zero_le_two
    have hratio0 : 0 ≤ 2 * Lam / lam :=
      div_nonneg (mul_nonneg zero_le_two (hlam.le.trans h.le)) hlam.le
    have hP0 := setIntegral_nonneg (μ := mu) (measurableSet_ball (x := y) (ε := 2 * ρ))
      fun x _ => sq_nonneg (W1p.value u x - m)
    have hA : 2 * ((2 * Lam / lam) ^ 2 + 1) ≤ A := by
      simp only [A]
      gcongr
    simp only [Real.norm_eq_abs, sq_abs]
    gcongr
  -- The Sobolev–Poincaré inequality on `B(y, 2ρ)`, and the averaged Caccioppoli inequality.
  have hP := setLAverage_enorm_value_sub_setAverage_sq_le hs2 hsn u (by positivity) hball
  have : IsFiniteMeasure (mu.restrict (ball y (2 * ρ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hav := setLAverage_enorm_sq_le_of_setIntegral_le (f := fun x => W1p.value u x - m) hρ
    (by positivity) (by positivity)
    ((W1p.integrable_norm_gradient_sq u).mono_measure
      (Measure.restrict_mono ((ball_subset_ball (by linarith)).trans hball) le_rfl))
    ((((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).sub
      (memLp_const m)).norm.integrable_sq)
    (hF.norm.integrable_sq.mono_measure (Measure.restrict_mono hball le_rfl)) hIρ
  rw [ofReal_div_sq_mul_setLAverage_eq _ hlam 12,
    ENNReal.ofReal_ofNat] at hav
  refine hav.trans (le_trans ?_ (ofReal_two_pow_mul_add_le hA0 hc hρ _ _))
  gcongr

/-- An exponent `s < 2` close enough to `2` for the Sobolev–Poincaré inequality from `Lˢ` to
`L²` in dimension `n ≥ 1`: `s = 2n/(n + 1)`, for which `1/s - 1/2 = 1/(2n) < 1/n`. -/
private theorem exists_one_le_lt_two_inv_sub_inv_lt {n : ℕ} (hn : 0 < n) :
    ∃ s : ℝ≥0, (1 : ℝ) ≤ s ∧ (s : ℝ) < 2 ∧ (s : ℝ)⁻¹ - 2⁻¹ < (n : ℝ)⁻¹ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(2 * n / (n + 1) : ℝ).toNNReal, ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  refine ⟨by rw [le_div_iff₀ (by positivity)]; linarith,
    by rw [div_lt_iff₀ (by positivity)]; linarith, ?_⟩
  have : (2 * n / (n + 1) : ℝ)⁻¹ - 2⁻¹ = (2 * n : ℝ)⁻¹ := by
    field_simp
    ring
  rw [this]
  exact inv_strictAnti₀ (by positivity) (by linarith)

/-- **Meyers' higher integrability estimate.** Let `n ≥ 1` be the dimension and let `K` bound the
ellipticity ratio. There is `ε₀ > 0`, and for each `0 < ε ≤ ε₀` a constant `C`, both independent
of the domain, the coefficients, the solution, the datum and the ball, with the following
property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, let
`F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`.
For every ball `B = B(x₀, R) ⊆ Ω`, with `½B = B(x₀, R/2)`,

`⨍_{½B} ‖∇u‖ ^ (2 + ε) ≤ C ((⨍_B ‖∇u‖²) ^ ((2 + ε)/2) + ⨍_B (‖F‖/λ) ^ (2 + ε))`.

The averages are extended-valued. When `F` is `(2 + ε)`-integrable on `B(x₀, R)` the right-hand
side is finite, so `∇u` is `(2 + ε)`-integrable on `B(x₀, R/2)`. -/
theorem exists_setLAverage_enorm_gradient_rpow_le_divergence [Nonempty ι] (K : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
        {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍⁻ x in ball x₀ (R / 2), ‖W1p.gradient u x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((⨍⁻ x in ball x₀ R, ‖W1p.gradient u x‖ₑ ^ (2 : ℝ) ∂mu) ^ ((2 + ε) / 2) +
          ⨍⁻ x in ball x₀ R, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu) := by
  obtain ⟨s, hs1', hs2', hsn⟩ := exists_one_le_lt_two_inv_sub_inv_lt
    (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ ι))
  have hs1 : 1 ≤ s := by exact_mod_cast hs1'
  have hs2 : s ≤ 2 := by exact_mod_cast hs2'.le
  have hs0 : (0 : ℝ) < s := one_pos.trans_le hs1'
  obtain ⟨b, hb⟩ := exists_setLAverage_enorm_gradient_sq_le_divergence (mu := mu) hs1 hs2 hsn K
  -- Gehring's lemma for the reverse Hölder inequality between the exponents `s < 2`.
  obtain ⟨ε₀, hε₀, hG⟩ := exists_setLAverage_rpow_add_le_of_rpow (μ := mu) hs0 hs2' b
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hG ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u x₀ R} h hK ha hF hu hball => ?_⟩
  have hball' : mu.restrict (ball x₀ R) ≤ mu.restrict Omega := Measure.restrict_mono hball le_rfl
  exact hC (f := fun x => ‖W1p.gradient u x‖ₑ) (φ := fun x => ‖F x‖ₑ / ENNReal.ofReal lam)
    ((Lp.aestronglyMeasurable (W1p.gradient u)).enorm.mono_measure hball')
    ((hF.aestronglyMeasurable.enorm.div_const _).mono_measure hball')
    fun y ρ hρ hsub => hb h hK ha hF hu hρ (hsub.trans hball)

/-- **Meyers' theorem: higher integrability of the gradient.** Let `n ≥ 1` be the dimension and
let `K` bound the ellipticity ratio. There is `ε₀ > 0`, depending only on `n` and `K`, with the
following property. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for
every `v ∈ H¹₀(Ω)`. If `B(x₀, R) ⊆ Ω`, `0 < ε ≤ ε₀` and `F` lies in `L^{2 + ε}(B(x₀, R))`, then
`∇u` lies in `L^{2 + ε}(B(x₀, R/2))`. -/
theorem exists_memLp_gradient_ball_divergence [Nonempty ι] (K : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
        {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      MemLp F (ENNReal.ofReal (2 + ε)) (mu.restrict (ball x₀ R)) →
      MemLp (W1p.gradient u) (ENNReal.ofReal (2 + ε)) (mu.restrict (ball x₀ (R / 2))) := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_setLAverage_enorm_gradient_rpow_le_divergence (mu := mu) K
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  intro Omega a lam Lam F u x₀ R h hK ha hF hu hball hFp
  -- For `R ≤ 0` the half ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 (by linarith : R / 2 ≤ 0), Measure.restrict_empty]
    exact memLp_measure_zero
  have hp0 : ENNReal.ofReal (2 + ε) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hpR : (ENNReal.ofReal (2 + ε)).toReal = 2 + ε := ENNReal.toReal_ofReal (by linarith)
  have hsub : mu.restrict (ball x₀ (R / 2)) ≤ mu.restrict Omega :=
    Measure.restrict_mono ((ball_subset_ball (by linarith)).trans hball) le_rfl
  have hm : AEStronglyMeasurable (W1p.gradient u) (mu.restrict (ball x₀ (R / 2))) :=
    (Lp.aestronglyMeasurable _).mono_measure hsub
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top hm, hpR,
    ← measure_mul_setLAverage _ measure_ball_lt_top.ne]
  refine ENNReal.mul_lt_top measure_ball_lt_top ((hC h hK ha hF hu hball).trans_lt ?_)
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · -- `∇u` is square integrable on `Ω`.
    have hL2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (Lp.memLp (W1p.gradient u)).eLpNorm_lt_top
    rw [ENNReal.toReal_ofNat] at hL2
    refine ENNReal.rpow_lt_top_of_nonneg (by linarith) (laverage_lt_top ?_).ne
    exact (lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl) hL2).ne
  · -- `F / λ` is `(2 + ε)`-integrable on `B(x₀, R)`.
    have hF' := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 ENNReal.ofReal_ne_top
      hFp.eLpNorm_lt_top
    rw [hpR] at hF'
    have hlam : (ENNReal.ofReal lam)⁻¹ ^ (2 + ε) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith)
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 h.pos).ne')
    refine laverage_lt_top ?_
    simp only [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ 2 + ε)]
    rw [lintegral_mul_const' _ _ hlam]
    exact ENNReal.mul_ne_top hF'.ne hlam

end PDE

end TauCeti
