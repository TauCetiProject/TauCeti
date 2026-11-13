/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Divergence
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.Analysis.Sobolev.LipschitzDomain.MeasureDensity
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Gehring
import TauCeti.MeasureTheory.Measure.Haar.Average

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

## Up to the boundary

For `u ∈ H¹₀(Ω)` the estimate holds on every ball, not only on balls inside `Ω`, once `Ω` satisfies
the **exterior measure density condition**

`θ μ(B(z, r)) ≤ μ(B(z, r) \ Ω)` for every `z ∉ Ω` and `0 < r ≤ R₀`,

with `θ > 0`; bounded Lipschitz domains satisfy it. The statement is about the extensions
`1_Ω ∇u` and `1_Ω F` of `∇u` and `F` by zero. A test function `ψ² u` lies in `H¹₀(Ω)` for every
cutoff `ψ`, so Caccioppoli's inequality for `u` holds on every ball. When `B(y, 2ρ)` leaves `Ω`
it contains a point `z ∉ Ω`, and `B(y, 4ρ) ⊇ B(z, 2ρ)` contains the proportion `θ / 2ⁿ` of the
complement, on which the extension of `u` vanishes. There the mean of `u` over `B(y, 4ρ)` is
controlled by its oscillation
(`TauCeti.setIntegral_sq_le_mul_setIntegral_sub_setAverage_sq_of_ae_eq_zero`), so Caccioppoli's
inequality without the mean and the Sobolev–Poincaré inequality give the reverse
Hölder inequality between `B(y, ρ)` and `B(y, 4ρ)`. A covering argument
(`TauCeti.exists_setLAverage_rpow_le_of_forall_ball_four`) returns it to the ratio `2` of Gehring's
lemma, with the interior inequality on the balls `B(y, 2ρ) ⊆ Ω`. The resulting gain `ε₀` depends
only on `n`, `K` and `θ`. On a bounded domain finitely many balls of radius `R₀ / 2` cover `Ω`,
which gives `∇u ∈ L^{2 + ε}(Ω)` whenever `F ∈ L^{2 + ε}(Ω)`, with a global estimate. This global
higher integrability is the input of the `W^{1,p}` theory of the Dirichlet problem for exponents
`p` near `2`, whose range below `2` follows by duality.

## Main declarations

* `TauCeti.PDE.exists_setLAverage_enorm_gradient_sq_le_divergence`: the reverse Hölder
  inequality for the gradient.
* `TauCeti.PDE.exists_setLAverage_enorm_gradient_rpow_le_divergence`: **Meyers' higher
  integrability estimate**.
* `TauCeti.PDE.exists_memLp_gradient_ball_divergence`: its qualitative form, `∇u ∈ L^{2 + ε}` on
  `B(x₀, R/2)` whenever `F ∈ L^{2 + ε}` on `B(x₀, R) ⊆ Ω`.
* `TauCeti.PDE.exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence`: Meyers' estimate
  up to the boundary for `u ∈ H¹₀(Ω)`, on every ball of radius at most `R₀`.
* `TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`: the global estimate
  `∫_Ω ‖∇u‖ ^ (2 + ε) ≤ C ((∫_Ω ‖∇u‖²) ^ ((2 + ε)/2) + ∫_Ω (‖F‖/λ) ^ (2 + ε))` on a bounded domain
  with the exterior measure density condition.
* `TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence_of_isLipschitzDomain`: the same
  on a bounded Lipschitz domain.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorems 1 and 2.
* T. Kilpeläinen, P. Koskela, *Global integrability of the gradients of solutions to partial
  differential equations*, Nonlinear Anal. **23** (1994), 899–909 (higher integrability up to the
  boundary under a uniform exterior density condition).
* M. Giaquinta, G. Modica, *Regularity results for some classes of higher order nonlinear
  elliptic systems*, J. Reine Angew. Math. **311/312** (1979), 145–169.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 6.4.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- The constants of the reverse Hölder inequality between `B(y, ρ)` and `B(y, kρ)`:
`A (C/ρ)² (c k ρ)² = A C² (k c)²` does not depend on `ρ`, and both coefficients are at most
`kⁿ (A C² (k c)² + 12)`. -/
private theorem ofReal_pow_mul_add_le {n : ℕ} {k A C c ρ : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (hρ : 0 < ρ) (G Φ : ℝ≥0∞) :
    ENNReal.ofReal (k ^ n) * (ENNReal.ofReal (A * (C / ρ) ^ 2) *
        (ENNReal.ofReal (c * (k * ρ)) ^ (2 : ℝ) * G) + 12 * Φ) ≤
      ((k ^ n * (A * C ^ 2 * (k * c) ^ 2) + k ^ n * 12).toNNReal : ℝ≥0∞) * G +
        ((k ^ n * (A * C ^ 2 * (k * c) ^ 2) + k ^ n * 12).toNNReal : ℝ≥0∞) * Φ := by
  have hconst : ENNReal.ofReal (A * (C / ρ) ^ 2) * ENNReal.ofReal (c * (k * ρ)) ^ (2 : ℝ) =
      ENNReal.ofReal (A * C ^ 2 * (k * c) ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two,
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_two]
    congr 1
    field_simp
  have hsplit : ENNReal.ofReal (k ^ n) * (ENNReal.ofReal (A * C ^ 2 * (k * c) ^ 2) * G + 12 * Φ) =
      ENNReal.ofReal (k ^ n * (A * C ^ 2 * (k * c) ^ 2)) * G +
        ENNReal.ofReal (k ^ n * 12) * Φ := by
    rw [ENNReal.ofReal_mul (p := k ^ n) (by positivity),
      ENNReal.ofReal_mul (p := k ^ n) (by positivity), ENNReal.ofReal_ofNat]
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
    have hA : 2 * ((2 * Lam / lam) ^ 2 + 1) ≤ A := by
      simp only [A]
      gcongr
    simp only [Real.norm_eq_abs, sq_abs]
    gcongr
  -- The Sobolev–Poincaré inequality on `B(y, 2ρ)`, and the averaged Caccioppoli inequality.
  have hP := setLAverage_enorm_value_sub_setAverage_sq_le hs2 hsn u (by positivity) hball
  have : IsFiniteMeasure (mu.restrict (ball y (2 * ρ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The ratio of the measures of the two balls is `2ⁿ`.
  have hμ2 : mu (ball y (2 * ρ)) = ENNReal.ofReal (2 ^ n) * mu (ball y ρ) := by
    rw [Measure.addHaar_ball_of_pos mu y (by positivity), Measure.addHaar_ball_of_pos mu y hρ,
      mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hav := setLAverage_enorm_sq_le_of_setIntegral_le (f := fun x => W1p.value u x - m)
    (by positivity) (by positivity) hμ2 measure_ball_lt_top.ne
    ((W1p.integrable_norm_gradient_sq u).mono_measure
      (Measure.restrict_mono ((ball_subset_ball (by linarith)).trans hball) le_rfl))
    ((((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).sub
      (memLp_const m)).norm.integrable_sq)
    (hF.norm.integrable_sq.mono_measure (Measure.restrict_mono hball le_rfl)) hIρ
  rw [ofReal_div_sq_mul_setLAverage_eq _ hlam 12,
    ENNReal.ofReal_ofNat] at hav
  refine hav.trans (le_trans ?_ (ofReal_pow_mul_add_le zero_le_two hA0 hc hρ _ _))
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
    ((Lp.aestronglyMeasurable (W1p.gradient u)).eNorm.mono_measure hball')
    ((hF.aestronglyMeasurable.eNorm.div_const _).mono_measure hball')
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
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 ENNReal.ofReal_ne_top hm, hpR,
    ← measure_mul_setLAverage _ measure_ball_lt_top.ne]
  refine ENNReal.mul_lt_top measure_ball_lt_top ((hC h hK ha hF hu hball).trans_lt ?_)
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · -- `∇u` is square integrable on `Ω`.
    have hL2 := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      (Lp.memLp (W1p.gradient u)).eLpNorm_lt_top
    rw [ENNReal.toReal_ofNat] at hL2
    refine ENNReal.rpow_lt_top_of_nonneg (by linarith) (laverage_lt_top ?_).ne
    exact (lt_of_le_of_lt (lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl) hL2).ne
  · -- `F / λ` is `(2 + ε)`-integrable on `B(x₀, R)`.
    have hF' := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 ENNReal.ofReal_ne_top
      hFp.eLpNorm_lt_top
    rw [hpR] at hF'
    have hlam : (ENNReal.ofReal lam)⁻¹ ^ (2 + ε) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith)
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 h.pos).ne')
    refine laverage_lt_top ?_
    simp only [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ 2 + ε)]
    rw [lintegral_mul_const' _ _ hlam]
    exact ENNReal.mul_ne_top hF'.ne hlam

/-! ### Up to the boundary -/

omit [Fintype ι] [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- An integral over the whole space of an expression in the zero extension of `g` from `Ω` is the
integral over `Ω` of the same expression in `g`, when the expression vanishes at `0`. -/
private theorem integral_indicator_eq_setIntegral {V : Type*} [Zero V]
    {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S) (h : EuclideanSpace ℝ ι → V → ℝ)
    (h0 : ∀ x, h x 0 = 0) (g : EuclideanSpace ℝ ι → V) :
    ∫ x, h x (S.indicator g x) ∂mu = ∫ x in S, h x (g x) ∂mu := by
  rw [← integral_indicator hS]
  congr 1
  funext x
  by_cases hx : x ∈ S <;> simp [hx, h0]

/-- **The reverse Hölder inequality for the gradient near the boundary.** Let `n ≥ 1` be the
dimension, let `1 ≤ s ≤ 2` with `1/s - 1/2 < 1/n`, let `K` bound the ellipticity ratio and let
`M ≥ 0`. There is `b`, independent of the domain, the coefficients, the solution, the datum and
the ball, with the following property. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ ≤ K λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹₀(Ω)` satisfy
`a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. Write `1_Ω ∇u` and `1_Ω F` for the extensions
of `∇u` and `F` by zero. For every ball `B(y, 4ρ)` with `μ(B(y, 4ρ)) ≤ M μ(B(y, 4ρ) \ Ω)`,

`⨍_{B(y, ρ)} ‖1_Ω ∇u‖² ≤ b (⨍_{B(y, 4ρ)} ‖1_Ω ∇u‖ ^ s) ^ (2/s) + b ⨍_{B(y, 4ρ)} (‖1_Ω F‖/λ)²`.

The ball need not lie in `Ω`. Since the extension of `u` by zero vanishes on a fixed proportion of
`B(y, 4ρ)`, Caccioppoli's inequality for `u` itself and the Sobolev–Poincaré inequality combine
with no mean to subtract. -/
private theorem exists_setLAverage_enorm_indicator_gradient_sq_le_of_measure_le [Nonempty ι]
    {s : ℝ≥0} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) (K : ℝ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ b : ℝ≥0, ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
      {y : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      u ∈ w1p0Submodule mu Omega 2 → 0 < ρ →
      mu (ball y (4 * ρ)) ≤ ENNReal.ofReal M * mu (ball y (4 * ρ) \ Omega) →
      ⨍⁻ x in ball y ρ, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ ^
          (2 : ℝ) ∂mu ≤
        b * (⨍⁻ x in ball y (4 * ρ),
            ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ ^ (s : ℝ) ∂mu) ^
              (2 / (s : ℝ)) +
          b * ⨍⁻ x in ball y (4 * ρ),
            (‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ)
              ∂mu := by
  obtain ⟨C, -, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_add_setIntegral_of_cutoff
    (ι := ι)
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set δ : ℝ := (s : ℝ)⁻¹ - 2⁻¹
  set c : ℝ := 2 ^ n / n * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ)
  set A : ℝ := 2 * ((2 * K) ^ 2 + 1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Module.finrank_pos
  have hδ1 : δ < 1 := hsn.trans_le (inv_le_one_of_one_le₀ hn1)
  have hc : 0 ≤ c := mul_nonneg (by positivity)
    (Real.rpow_nonneg (div_nonneg (by linarith) (sub_nonneg.2 hsn.le)) _)
  refine ⟨(4 ^ n * (A * (2 + 2 * M) * (C / 3) ^ 2 * (4 * c) ^ 2) + 4 ^ n * 12).toNNReal, ?_⟩
  intro Omega a lam Lam F u y ρ h hK ha hF hu hu0 hρ hmeas
  have hlam : 0 < lam := h.pos
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
  -- Integrals over the whole space `⊤`, and restriction from `⊤` to a ball.
  have hT : ∀ f : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), f x ∂mu =
        ∫ x, f x ∂mu :=
    fun f => setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => (hx (by simp)).elim
  have hTball : mu.restrict (ball y (4 * ρ)) ≤
      mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    Measure.restrict_mono (fun x _ => by simp) le_rfl
  -- The extension `U` of `u` by zero to the whole space, and the extension `1_Ω F` of `F`.
  set U : W1p mu ⊤ 2 := (W1p0.extendByZeroL le_top (⟨u, hu0⟩ : W1p0 mu Omega 2)).1
  set Fb := (Omega : Set (EuclideanSpace ℝ ι)).indicator F
  have hgU : W1p.gradient U =ᵐ[mu]
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) := by
    simp only [U, W1p0.gradient_extendByZeroL]
    simpa only [Opens.coe_top, Measure.restrict_univ] using coeFn_extendByZeroLpₗᵢ ℝ hΩ
      (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.gradient u)
  have hvU : W1p.value U =ᵐ[mu] (Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value u) := by
    simp only [U, W1p0.value_extendByZeroL]
    simpa only [Opens.coe_top, Measure.restrict_univ] using coeFn_extendByZeroLpₗᵢ ℝ hΩ
      (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.value u)
  have hFb : MemLp Fb 2 mu := (memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 hF
  -- Caccioppoli's inequality for `U` with an arbitrary cutoff, from the one for `u ∈ H¹₀(Ω)`.
  set A₀ : ℝ := 2 * ((2 * Lam / lam) ^ 2 + 1)
  have hA₀ : A₀ ≤ A := by
    have hratio : 2 * Lam / lam ≤ 2 * K := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hlam).2 hK) zero_le_two
    have hratio0 : 0 ≤ 2 * Lam / lam :=
      div_nonneg (mul_nonneg zero_le_two (hlam.le.trans h.le)) hlam.le
    simp only [A₀, A]
    gcongr
  have hcacc := hC U (A := A₀) (g := fun x => 12 / lam ^ 2 * ‖Fb x‖ ^ 2) (x₀ := y) (r := ρ)
    (R := 4 * ρ) (by positivity)
    ((hFb.norm.integrable_sq.const_mul _).mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall fun x => by positivity) (by linarith) (subset_univ _)
    fun ψ hψ hcpt _ => by
      have hdiv := h.setIntegral_sq_mul_norm_gradient_sq_le_divergence ha hF hu hψ hcpt
        (.inr hu0)
      have e1 : ∫ x, ψ x ^ 2 * ‖W1p.gradient U x‖ ^ 2 ∂mu =
          ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu := by
        rw [← integral_indicator_eq_setIntegral hΩ (fun x g => ψ x ^ 2 * ‖g‖ ^ 2)
          (fun x => by simp)]
        exact integral_congr_ae (hgU.mono fun x hx => by simp only [hx])
      have e2 : ∫ x, ‖∇ ψ x‖ ^ 2 * W1p.value U x ^ 2 ∂mu =
          ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu := by
        rw [← integral_indicator_eq_setIntegral hΩ (fun x g => ‖∇ ψ x‖ ^ 2 * g ^ 2)
          (fun x => by simp)]
        exact integral_congr_ae (hvU.mono fun x hx => by simp only [hx])
      rw [hT, hT, hT, e1, e2, integral_indicator_eq_setIntegral hΩ
        (fun x g => ψ x ^ 2 * (12 / lam ^ 2 * ‖g‖ ^ 2)) (fun x => by simp)]
      simp_rw [mul_left_comm (ψ _ ^ 2), integral_const_mul]
      exact hdiv
  -- `U` vanishes on `B(y, 4ρ) \ Ω`, which is a fixed proportion of the ball.
  have : IsFiniteMeasure (mu.restrict (ball y (4 * ρ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hU2 : MemLp (W1p.value U) 2 (mu.restrict (ball y (4 * ρ))) :=
    (Lp.memLp _).mono_measure hTball
  have hzero := setIntegral_sq_le_mul_setIntegral_sub_setAverage_sq_of_ae_eq_zero
    (S := ball y (4 * ρ) \ Omega) sdiff_subset
    measure_ball_lt_top.ne hmeas hU2 (by
      filter_upwards [ae_restrict_of_ae hvU, ae_restrict_mem (measurableSet_ball.diff hΩ)]
        with x hx hxS
      rw [hx, indicator_of_notMem hxS.2])
  set m := ⨍ z in ball y (4 * ρ), W1p.value U z ∂mu
  have hIρ : ∫ x in ball y ρ, ‖W1p.gradient U x‖ ^ 2 ∂mu ≤
      A * (2 + 2 * M) * (C / 3 / ρ) ^ 2 * ∫ x in ball y (4 * ρ), ‖W1p.value U x - m‖ ^ 2 ∂mu
        + 12 / lam ^ 2 * ∫ x in ball y (4 * ρ), ‖Fb x‖ ^ 2 ∂mu := by
    have h3 : 4 * ρ - ρ = 3 * ρ := by ring
    have hCρ : C / (4 * ρ - ρ) = C / 3 / ρ := by rw [h3, div_div]
    rw [integral_const_mul] at hcacc
    refine hcacc.trans ?_
    simp only [Real.norm_eq_abs, sq_abs, hCρ]
    have hmono : A₀ * (C / 3 / ρ) ^ 2 * ∫ x in ball y (4 * ρ), W1p.value U x ^ 2 ∂mu ≤
        A₀ * (C / 3 / ρ) ^ 2 * ((2 + 2 * M) *
          ∫ x in ball y (4 * ρ), (W1p.value U x - m) ^ 2 ∂mu) :=
      mul_le_mul_of_nonneg_left hzero (by positivity)
    have hmono' : A₀ * (C / 3 / ρ) ^ 2 * ((2 + 2 * M) *
          ∫ x in ball y (4 * ρ), (W1p.value U x - m) ^ 2 ∂mu) ≤
        A * (2 + 2 * M) * (C / 3 / ρ) ^ 2 *
          ∫ x in ball y (4 * ρ), (W1p.value U x - m) ^ 2 ∂mu := by
      have := mul_le_mul_of_nonneg_right hA₀ (by positivity : (0 : ℝ) ≤ (C / 3 / ρ) ^ 2 *
        ((2 + 2 * M) * ∫ x in ball y (4 * ρ), (W1p.value U x - m) ^ 2 ∂mu))
      linarith
    linarith
  -- Pass to averages; the ratio of the measures of the two balls is `4ⁿ`.
  have hμ4 : mu (ball y (4 * ρ)) = ENNReal.ofReal (4 ^ n) * mu (ball y ρ) := by
    rw [Measure.addHaar_ball_of_pos mu y (by positivity), Measure.addHaar_ball_of_pos mu y hρ,
      mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hgint : IntegrableOn (fun x => ‖W1p.gradient U x‖ ^ 2) (ball y ρ) mu :=
    (W1p.integrable_norm_gradient_sq U).mono_measure
      ((Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl).trans hTball)
  have hav := setLAverage_enorm_sq_le_of_setIntegral_le (f := fun x => W1p.value U x - m)
    (by positivity) (by positivity) hμ4 measure_ball_lt_top.ne hgint
    ((hU2.sub (memLp_const m)).norm.integrable_sq) hFb.norm.integrable_sq.integrableOn hIρ
  rw [ofReal_div_sq_mul_setLAverage_eq _ hlam 12, ENNReal.ofReal_ofNat] at hav
  -- The Sobolev–Poincaré inequality on `B(y, 4ρ)`.
  have hP := setLAverage_enorm_value_sub_setAverage_sq_le hs2 hsn U (by positivity)
    (subset_univ (ball y (4 * ρ)))
  have hgrad : ∀ (r : ℝ) (q : ℝ), ⨍⁻ x in ball y r, ‖W1p.gradient U x‖ₑ ^ q ∂mu =
      ⨍⁻ x in ball y r,
        ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ ^ q ∂mu :=
    fun r q => laverage_congr ((ae_restrict_of_ae hgU).mono fun x hx => by simp only [hx])
  rw [← hgrad, ← hgrad]
  refine hav.trans (le_trans ?_ (ofReal_pow_mul_add_le (k := 4) (C := C / 3) (by norm_num)
    (by positivity) hc hρ _ _))
  gcongr

/-- **Meyers' higher integrability estimate up to the boundary.** Let `n ≥ 1` be the dimension,
let `K` bound the ellipticity ratio and let `θ > 0`. There is `ε₀ > 0`, and for each
`0 < ε ≤ ε₀` a constant `C`, both depending only on `n`, `K` and `θ`, with the following property.
Let `Ω` satisfy the exterior measure density condition

`θ μ(B(z, r)) ≤ μ(B(z, r) \ Ω)` for every `z ∉ Ω` and `0 < r ≤ R₀`,

as a bounded Lipschitz domain does
(`Set.IsLipschitzDomain.exists_pos_mul_measure_ball_le_measure_ball_sdiff_closure`). Let `a` be
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, let `F ∈ L²(Ω; ℝⁿ)`,
and let `u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. Write `1_Ω ∇u`
and `1_Ω F` for the extensions of `∇u` and `F` by zero. For every ball `B = B(x₀, R)` with
`R ≤ R₀`, centred anywhere in the space,

`⨍_{½B} ‖1_Ω ∇u‖ ^ (2 + ε) ≤ C ((⨍_B ‖1_Ω ∇u‖²) ^ ((2 + ε)/2) + ⨍_B (‖1_Ω F‖/λ) ^ (2 + ε))`.

This is the interior estimate `TauCeti.PDE.exists_setLAverage_enorm_gradient_rpow_le_divergence`
with the condition `B ⊆ Ω` replaced by the zero boundary values of `u`. Balls in `Ω` are handled
by the interior reverse Hölder inequality, and balls `B(y, 4ρ)` whose concentric half meets the
complement contain a fixed proportion of it, on which the extension of `u` vanishes. -/
theorem exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence [Nonempty ι] (K : ℝ)
    {θ : ℝ≥0} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2}
        {R₀ : ℝ} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r : ℝ, 0 < r → r ≤ R₀ →
        (θ : ℝ≥0∞) * mu (ball z r) ≤ mu (ball z r \ Omega)) →
      R ≤ R₀ →
      ⨍⁻ x in ball x₀ (R / 2),
          ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((⨍⁻ x in ball x₀ R,
            ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ ^ (2 : ℝ) ∂mu) ^
              ((2 + ε) / 2) +
          ⨍⁻ x in ball x₀ R,
            (‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε)
              ∂mu) := by
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  obtain ⟨s, hs1', hs2', hsn⟩ := exists_one_le_lt_two_inv_sub_inv_lt
    (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ ι))
  have hs1 : 1 ≤ s := by exact_mod_cast hs1'
  have hs2 : s ≤ 2 := by exact_mod_cast hs2'.le
  have hs0 : (0 : ℝ) < s := one_pos.trans_le hs1'
  have h2s : 1 ≤ 2 / (s : ℝ) := (one_le_div hs0).2 hs2'.le
  -- The interior reverse Hölder inequality, read between `B(y, ρ)` and `B(y, 4ρ)`.
  obtain ⟨b₀, hb₀⟩ := exists_setLAverage_enorm_gradient_sq_le_divergence (mu := mu) hs1 hs2 hsn K
  -- The reverse Hölder inequality near the boundary, for the exterior proportion `θ / 2ⁿ`.
  set M : ℝ := 2 ^ n * (θ : ℝ)⁻¹
  have hM : 0 ≤ M := by positivity
  obtain ⟨b₁, hb₁⟩ :=
    exists_setLAverage_enorm_indicator_gradient_sq_le_of_measure_le (mu := mu) hs1 hs2 hsn K hM
  set b₂ : ℝ≥0 := b₀ * ((2 : ℝ≥0) ^ n) ^ (2 / (s : ℝ))
  obtain ⟨b', hb'⟩ := exists_setLAverage_rpow_le_of_forall_ball_four (μ := mu) hs0 hs2 (b₂ + b₁)
  obtain ⟨ε₀, hε₀, hG⟩ := exists_setLAverage_rpow_add_le_of_rpow (μ := mu) hs0 hs2' b'
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hG ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u R₀ x₀ R} h hK ha hF hu hu0 hΩ hRR₀ => ?_⟩
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  let f : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ
  let φ : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam
  -- The reverse Hölder inequality between `B(y, ρ)` and `B(y, 4ρ)`, on every ball in `B(x₀, R)`.
  have hRH4 : ∀ y ρ, 0 < ρ → ball y (4 * ρ) ⊆ ball x₀ R →
      ⨍⁻ x in ball y ρ, f x ^ (2 : ℝ) ∂mu ≤
        ↑(b₂ + b₁) * (⨍⁻ x in ball y (4 * ρ), f x ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) +
          ↑(b₂ + b₁) * ⨍⁻ x in ball y (4 * ρ), φ x ^ (2 : ℝ) ∂mu := by
    intro y ρ hρ hsub
    set Af := ⨍⁻ x in ball y (4 * ρ), f x ^ (s : ℝ) ∂mu
    set Aφ := ⨍⁻ x in ball y (4 * ρ), φ x ^ (2 : ℝ) ∂mu
    have hmono : ∀ b : ℝ≥0, b ≤ b₂ + b₁ → (b : ℝ≥0∞) * Af ^ (2 / (s : ℝ)) + b * Aφ ≤
        ↑(b₂ + b₁) * Af ^ (2 / (s : ℝ)) + ↑(b₂ + b₁) * Aφ := fun b hb => by
      gcongr
    by_cases hin : ball y (2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι))
    · -- Inside `Ω`: the interior inequality, with the averages enlarged from `B(y, 2ρ)`.
      refine le_trans ?_ (hmono b₂ le_self_add)
      have hρΩ : ball y ρ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
        (ball_subset_ball (by linarith)).trans hin
      -- On balls inside `Ω` the extensions by zero are the functions themselves.
      have hf' : ∀ {r : ℝ} (q : ℝ), ball y r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
          ⨍⁻ x in ball y r, f x ^ q ∂mu = ⨍⁻ x in ball y r, ‖W1p.gradient u x‖ₑ ^ q ∂mu :=
        fun q hr => laverage_congr (ae_restrict_of_forall_mem measurableSet_ball fun x hx => by
          simp only [f, indicator_of_mem (hr hx)])
      have hφ' : ∀ {r : ℝ} (q : ℝ), ball y r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
          ⨍⁻ x in ball y r, φ x ^ q ∂mu =
            ⨍⁻ x in ball y r, (‖F x‖ₑ / ENNReal.ofReal lam) ^ q ∂mu :=
        fun q hr => laverage_congr (ae_restrict_of_forall_mem measurableSet_ball fun x hx => by
          simp only [φ, indicator_of_mem (hr hx)])
      have h24 : ball y (2 * ρ) ⊆ ball y (4 * ρ) := ball_subset_ball (by linarith)
      have hK2 : ENNReal.ofReal ((4 * ρ / (2 * ρ)) ^ n) = ((2 : ℝ≥0) ^ n : ℝ≥0) := by
        rw [show 4 * ρ / (2 * ρ) = 2 by field_simp; norm_num, ← ENNReal.ofReal_coe_nnreal]
        simp
      have hAf : ⨍⁻ x in ball y (2 * ρ), f x ^ (s : ℝ) ∂mu ≤ ((2 : ℝ≥0) ^ n : ℝ≥0) * Af :=
        hK2 ▸ setLAverage_ball_le _ (by positivity) h24
      have hAφ : ⨍⁻ x in ball y (2 * ρ), φ x ^ (2 : ℝ) ∂mu ≤ ((2 : ℝ≥0) ^ n : ℝ≥0) * Aφ :=
        hK2 ▸ setLAverage_ball_le _ (by positivity) h24
      have hK1 : (((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ≤
          (((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ (2 / (s : ℝ)) := by
        simpa using ENNReal.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2)) h2s
      rw [hf' _ hρΩ]
      refine (hb₀ h hK ha hF hu hρ hin).trans ?_
      rw [← hf' _ hin, ← hφ' _ hin]
      calc (b₀ : ℝ≥0∞) * (⨍⁻ x in ball y (2 * ρ), f x ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) +
            b₀ * ⨍⁻ x in ball y (2 * ρ), φ x ^ (2 : ℝ) ∂mu
          ≤ b₀ * ((((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) * Af) ^ (2 / (s : ℝ)) +
              b₀ * ((((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) * Aφ) := by gcongr
        _ ≤ b₀ * ((((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ (2 / (s : ℝ)) * Af ^ (2 / (s : ℝ))) +
              b₀ * ((((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) ^ (2 / (s : ℝ)) * Aφ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
            gcongr
        _ = b₂ * Af ^ (2 / (s : ℝ)) + b₂ * Aφ := by
            simp only [b₂, ENNReal.coe_mul,
              ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 2 / (s : ℝ))]
            ring
    · -- Near the boundary: `B(y, 4ρ)` contains `B(z, 2ρ)` for some `z ∉ Ω`.
      refine le_trans ?_ (hmono b₁ le_add_self)
      obtain ⟨z, hzy, hzΩ⟩ := not_subset.1 hin
      have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.1 (hsub (mem_ball_self (by positivity))))
      have h4ρ : 4 * ρ ≤ R := by
        have := diam_mono hsub isBounded_ball
        rw [Metric.diam_ball_eq y (by positivity)] at this
        linarith [diam_ball (x := x₀) hR.le]
      have hdens := hΩ z hzΩ (2 * ρ) (by positivity) (by linarith)
      have hzsub : ball z (2 * ρ) ⊆ ball y (4 * ρ) :=
        ball_subset_ball' (by linarith [mem_ball.1 hzy])
      have hμ : mu (ball y (4 * ρ)) = ENNReal.ofReal (2 ^ n) * mu (ball z (2 * ρ)) := by
        rw [show 4 * ρ = 2 * (2 * ρ) by ring,
          Measure.addHaar_ball_mul_of_pos mu y (by norm_num : (0 : ℝ) < 2),
          Measure.addHaar_ball_center mu z]
      have hθ0 : (θ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hθ.ne'
      have hmeas : mu (ball y (4 * ρ)) ≤
          ENNReal.ofReal M * mu (ball y (4 * ρ) \ (Omega : Set (EuclideanSpace ℝ ι))) := by
        have hz : mu (ball z (2 * ρ)) ≤ (θ : ℝ≥0∞)⁻¹ *
            mu (ball y (4 * ρ) \ (Omega : Set (EuclideanSpace ℝ ι))) :=
          calc mu (ball z (2 * ρ)) = (θ : ℝ≥0∞)⁻¹ * ((θ : ℝ≥0∞) * mu (ball z (2 * ρ))) := by
                rw [← mul_assoc, ENNReal.inv_mul_cancel hθ0 ENNReal.coe_ne_top, one_mul]
            _ ≤ (θ : ℝ≥0∞)⁻¹ * mu (ball y (4 * ρ) \ (Omega : Set (EuclideanSpace ℝ ι))) := by
                gcongr
                exact hdens.trans (measure_mono (sdiff_subset_sdiff_left hzsub))
        rw [hμ]
        calc ENNReal.ofReal (2 ^ n) * mu (ball z (2 * ρ))
            ≤ ENNReal.ofReal (2 ^ n) * ((θ : ℝ≥0∞)⁻¹ *
                mu (ball y (4 * ρ) \ (Omega : Set (EuclideanSpace ℝ ι)))) := by gcongr
          _ = ENNReal.ofReal M * mu (ball y (4 * ρ) \ (Omega : Set (EuclideanSpace ℝ ι))) := by
              rw [← mul_assoc, ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_inv_of_pos (by exact_mod_cast hθ), ENNReal.ofReal_coe_nnreal]
      exact hb₁ h hK ha hF hu hu0 hρ hmeas
  -- Gehring's lemma.
  have hf : AEMeasurable f (mu.restrict (ball x₀ R)) :=
    ((memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2
      (Lp.memLp (W1p.gradient u))).aestronglyMeasurable.eNorm.mono_measure
        Measure.restrict_le_self
  have hφ : AEMeasurable φ (mu.restrict (ball x₀ R)) :=
    (((memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2
      hF).aestronglyMeasurable.eNorm.div_const _).mono_measure Measure.restrict_le_self
  exact hC hf hφ fun y ρ hρ hsub => hb' hRH4 y ρ hρ hsub

omit [Fintype ι] [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- The integral of a power of the extension by zero of `‖g‖` from `Ω` is the integral over `Ω`. -/
private theorem lintegral_enorm_indicator_rpow {V : Type*} [NormedAddCommGroup V]
    {S : Set (EuclideanSpace ℝ ι)} (hS : MeasurableSet S) (g : EuclideanSpace ℝ ι → V) (c : ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, (‖S.indicator g x‖ₑ / c) ^ p ∂mu = ∫⁻ x in S, (‖g x‖ₑ / c) ^ p ∂mu := by
  rw [← lintegral_indicator hS]
  congr 1
  funext x
  by_cases hx : x ∈ S <;> simp [hx, ENNReal.zero_rpow_of_pos hp]

/-- **Meyers' global higher integrability estimate.** Let `n ≥ 1` be the dimension, let `K`
bound the ellipticity ratio and let `θ > 0`, and let `ε₀ > 0` be the gain of
`TauCeti.PDE.exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence`, which depends only on
`n`, `K` and `θ`. Let `Ω` be bounded and satisfy the exterior measure density condition

`θ μ(B(z, r)) ≤ μ(B(z, r) \ Ω)` for every `z ∉ Ω` and `0 < r ≤ R₀`.

For `0 < ε ≤ ε₀` there is `C`, depending on `Ω` and `R₀` as well, such that whenever `a` is
measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, `F ∈ L²(Ω; ℝⁿ)` and
`u ∈ H¹₀(Ω)` satisfies `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`,

`∫_Ω ‖∇u‖ ^ (2 + ε) ≤ C ((∫_Ω ‖∇u‖²) ^ ((2 + ε)/2) + ∫_Ω (‖F‖/λ) ^ (2 + ε))`.

In particular `∇u ∈ L^{2 + ε}(Ω)` whenever `F ∈ L^{2 + ε}(Ω)`. Finitely many balls of radius
`R₀ / 2` cover `Ω`, and the local estimate up to the boundary applies on each. -/
theorem exists_lintegral_enorm_gradient_rpow_le_divergence [Nonempty ι] (K : ℝ) {θ : ℝ≥0}
    (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {R₀ : ℝ}, 0 < R₀ →
      Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r : ℝ, 0 < r → r ≤ R₀ →
        (θ : ℝ≥0∞) * mu (ball z r) ≤ mu (ball z r \ Omega)) →
      ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
        {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      u ∈ w1p0Submodule mu Omega 2 →
      ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ (2 : ℝ) ∂mu) ^ ((2 + ε) / 2) +
          ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu) := by
  obtain ⟨ε₀, hε₀, hloc⟩ :=
    exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle Omega R₀ hR₀ hb hΩ => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hloc ε hε hεle
  have hΩm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  set p : ℝ := 2 + ε
  have hp : 0 < p := by positivity
  -- A cover of `Ω` by finitely many balls `B(z, R₀/2)`.
  obtain ⟨D, hD⟩ := (isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ ι)).1 hb
  set δ : ℝ≥0 := ⟨R₀ / 4, by positivity⟩
  obtain ⟨N, -, hNcov, -⟩ := exists_finset_isCover_of_subset_closedBall
    (x := 0) (r := D.toNNReal) (ε := δ)
    (by rw [← NNReal.coe_ne_zero]; exact (by positivity : (0 : ℝ) < R₀ / 4).ne')
    (hD.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal D)))
  have hcover : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ ⋃ z : N, ball (z : EuclideanSpace ℝ ι)
      (R₀ / 2) := by
    intro x hx
    obtain ⟨z, hzN, hxz⟩ := hNcov hx
    refine mem_iUnion.2 ⟨⟨z, hzN⟩, mem_ball.2 ?_⟩
    have hxz : nndist x z ≤ δ := edist_le_coe.1 hxz
    have : dist x z ≤ R₀ / 4 := by
      rw [← coe_nndist]
      exact_mod_cast hxz
    linarith
  -- The measures of the balls of radii `R₀/2` and `R₀`, which do not depend on the centre.
  set m₁ := mu (ball (0 : EuclideanSpace ℝ ι) (R₀ / 2))
  set m₂ := mu (ball (0 : EuclideanSpace ℝ ι) R₀)
  have hm₂ : m₂ ≠ 0 := (measure_ball_pos mu 0 hR₀).ne'
  set C : ℝ≥0∞ := N.card * m₁ * C₁ * (m₂⁻¹ ^ (p / 2) + m₂⁻¹)
  have hC : C ≠ ∞ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      measure_ball_lt_top.ne) ENNReal.coe_ne_top) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.2 hm₂)
    · exact ENNReal.inv_ne_top.2 hm₂
  refine ⟨C.toNNReal, fun {a lam Lam F u} h hK ha hF hu hu0 => ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  set X := ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ (2 : ℝ) ∂mu
  set Y := ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ p ∂mu
  let f : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient u) x‖ₑ
  let φ : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam
  have hX : ∫⁻ x, f x ^ (2 : ℝ) ∂mu = X := by
    have := lintegral_enorm_indicator_rpow (mu := mu) hΩm (W1p.gradient u) 1 two_pos
    simp only [div_one] at this
    exact this
  have hY : ∫⁻ x, φ x ^ p ∂mu = Y := lintegral_enorm_indicator_rpow hΩm F _ hp
  have hfp : ∫⁻ x, f x ^ p ∂mu = ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ p ∂mu := by
    have := lintegral_enorm_indicator_rpow (mu := mu) hΩm (W1p.gradient u) 1 hp
    simp only [div_one] at this
    exact this
  -- The local estimate on each ball, with the averages over `B(z, R₀)` bounded by integrals.
  have hball : ∀ z : EuclideanSpace ℝ ι, ∫⁻ x in ball z (R₀ / 2), f x ^ p ∂mu ≤
      m₁ * C₁ * (m₂⁻¹ ^ (p / 2) * X ^ (p / 2) + m₂⁻¹ * Y) := by
    intro z
    have hz := hC₁ (x₀ := z) h hK ha hF hu hu0 hΩ le_rfl
    have hav : ∀ g : EuclideanSpace ℝ ι → ℝ≥0∞, ⨍⁻ x in ball z R₀, g x ∂mu ≤
        m₂⁻¹ * ∫⁻ x, g x ∂mu := fun g => by
      rw [setLAverage_eq, Measure.addHaar_ball_center mu z, ENNReal.div_eq_inv_mul]
      gcongr
      exact Measure.restrict_le_self
    rw [← measure_mul_setLAverage _ measure_ball_lt_top.ne, Measure.addHaar_ball_center mu z,
      mul_assoc]
    gcongr
    refine hz.trans ?_
    gcongr
    · refine (ENNReal.rpow_le_rpow (hav _) (by positivity)).trans_eq ?_
      rw [hX, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    · exact (hav _).trans_eq (by rw [hY])
  calc ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ p ∂mu
      = ∫⁻ x in Omega, f x ^ p ∂mu := by
        rw [← hfp, ← lintegral_indicator hΩm]
        congr 1
        funext x
        by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) <;>
          simp [f, hx, ENNReal.zero_rpow_of_pos hp]
    _ ≤ ∫⁻ x in ⋃ z : N, ball (z : EuclideanSpace ℝ ι) (R₀ / 2), f x ^ p ∂mu :=
        lintegral_mono_set hcover
    _ ≤ ∑' z : N, ∫⁻ x in ball (z : EuclideanSpace ℝ ι) (R₀ / 2), f x ^ p ∂mu :=
        lintegral_iUnion_le _ _
    _ = ∑ z : N, ∫⁻ x in ball (z : EuclideanSpace ℝ ι) (R₀ / 2), f x ^ p ∂mu := tsum_fintype _
    _ ≤ ∑ _z : N, m₁ * C₁ * (m₂⁻¹ ^ (p / 2) * X ^ (p / 2) + m₂⁻¹ * Y) :=
        Finset.sum_le_sum fun z _ => hball z
    _ = N.card * (m₁ * C₁ * (m₂⁻¹ ^ (p / 2) * X ^ (p / 2) + m₂⁻¹ * Y)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ C * (X ^ (p / 2) + Y) := by
        simp only [C]
        rw [mul_add, mul_add, mul_add]
        have h1 : m₂⁻¹ ^ (p / 2) ≤ m₂⁻¹ ^ (p / 2) + m₂⁻¹ := le_self_add
        have h2 : m₂⁻¹ ≤ m₂⁻¹ ^ (p / 2) + m₂⁻¹ := le_add_self
        calc (N.card : ℝ≥0∞) * (m₁ * C₁ * (m₂⁻¹ ^ (p / 2) * X ^ (p / 2))) +
              N.card * (m₁ * C₁ * (m₂⁻¹ * Y))
            ≤ N.card * (m₁ * C₁ * ((m₂⁻¹ ^ (p / 2) + m₂⁻¹) * X ^ (p / 2))) +
              N.card * (m₁ * C₁ * ((m₂⁻¹ ^ (p / 2) + m₂⁻¹) * Y)) := by gcongr
          _ = _ := by ring

/-- **Meyers' global higher integrability estimate on a bounded Lipschitz domain.** Let `n ≥ 1`
be the dimension, let `K` bound the ellipticity ratio, and let `Ω` be a bounded Lipschitz domain.
There is `ε₀ > 0`, depending on `n`, `K` and `Ω`, such that for `0 < ε ≤ ε₀` there is `C` with the
following property. Whenever `a` is measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, `F ∈ L²(Ω; ℝⁿ)` and `u ∈ H¹₀(Ω)` satisfies `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every
`v ∈ H¹₀(Ω)`,

`∫_Ω ‖∇u‖ ^ (2 + ε) ≤ C ((∫_Ω ‖∇u‖²) ^ ((2 + ε)/2) + ∫_Ω (‖F‖/λ) ^ (2 + ε))`.

A bounded Lipschitz domain satisfies the exterior measure density condition of
`TauCeti.PDE.exists_lintegral_enorm_gradient_rpow_le_divergence`
(`Set.IsLipschitzDomain.exists_pos_mul_measure_ball_le_measure_ball_sdiff_closure`). -/
theorem exists_lintegral_enorm_gradient_rpow_le_divergence_of_isLipschitzDomain [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ℝ)
    {Omega : Opens (EuclideanSpace ℝ ι)}
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
        {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu Omega 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      u ∈ w1p0Submodule mu Omega 2 →
      ∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((∫⁻ x in Omega, ‖W1p.gradient u x‖ₑ ^ (2 : ℝ) ∂mu) ^ ((2 + ε) / 2) +
          ∫⁻ x in Omega, (‖F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε) ∂mu) := by
  have hK : IsCompact (frontier (Omega : Set (EuclideanSpace ℝ ι))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨θ, hθ, hdens⟩ :=
    hΩ.exists_pos_mul_measure_ball_le_measure_ball_sdiff_closure (μ := mu) hK one_pos
  obtain ⟨ε₀, hε₀, hglob⟩ := exists_lintegral_enorm_gradient_rpow_le_divergence (mu := mu) K hθ
  exact ⟨ε₀, hε₀, fun ε hε hεle => hglob ε hε hεle one_pos hb fun z hz r hr hr1 =>
    (hdens z hz r hr hr1).trans (measure_mono (sdiff_subset_sdiff_right subset_closure))⟩

end PDE

end TauCeti
