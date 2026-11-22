/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Divergence
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Sobolev
import TauCeti.Analysis.Sobolev.W1p.Extension
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

For a solution of the Dirichlet problem, `u ∈ H¹₀(Ω)`, the same estimate holds on every ball, not
only on balls inside `Ω`, provided the complement of `Ω` is not too thin: suppose that
`θ |B(z, r)| ≤ |B(z, r) \ Ω|` for every `z ∉ Ω` and `0 < r ≤ r₀`, an exterior measure density
condition satisfied for instance by Lipschitz domains. Write `u₀` for the zero extension of `u`,
whose gradient is `1_Ω ∇u`. On a ball `B(y, 2ρ)` with `ρ ≤ 2 r₀` either `B(y, 3ρ/2) ⊆ Ω`, and the
interior argument applies there, or some `z ∉ Ω` lies in `B(y, 3ρ/2)`. In the second case the
cutoff `ψ² u` is still a test function, since `u ∈ H¹₀(Ω)`, so Caccioppoli's inequality bounds
`∇u₀` on `B(y, ρ)` by `u₀` on `B(y, 2ρ)` with no mean subtracted
(`TauCeti.PDE.exists_setIntegral_ball_norm_indicator_gradient_sq_le_divergence`); and `u₀`
vanishes on `B(z, ρ/2) \ Ω`, a proportion `θ / 4ⁿ` of `B(y, 2ρ)`, so the mean of `u₀` is
controlled by its oscillation (`TauCeti.setLAverage_enorm_sq_le_of_ae_eq_zero`) and the
Sobolev–Poincaré inequality for `u₀` applies again. Gehring's lemma then gives Meyers' estimate
for `1_Ω ∇u` on all balls of radius at most `r₀`, and for bounded `Ω` the qualitative global
higher integrability `∇u ∈ L^{2 + ε}(Ω)` of `H¹₀` solutions whenever `F ∈ L^{2 + ε}(Ω)`. This is
the integrability part of the upper range of Meyers' Theorem 1. Its norm bound
`‖∇u‖_{2 + ε} ≤ C ‖F‖_{2 + ε}`, and the bound for the conjugate exponent below `2`, are in
`TauCeti.Analysis.PDE.Regularity.Boundary.Meyers`, together with the existence of solutions in
`W^{1,p}_0(Ω)` of the Dirichlet problem for data `F ∈ Lᵖ(Ω)` below `2`, by extension from `L²`
data. Their uniqueness in `W^{1,p}_0(Ω)` is not formalised.

## Main declarations

* `TauCeti.PDE.exists_setLAverage_enorm_gradient_sq_le_divergence`: the reverse Hölder
  inequality for the gradient.
* `TauCeti.PDE.exists_setLAverage_enorm_gradient_rpow_le_divergence`: **Meyers' higher
  integrability estimate**.
* `TauCeti.PDE.exists_memLp_gradient_ball_divergence`: its qualitative form, `∇u ∈ L^{2 + ε}` on
  `B(x₀, R/2)` whenever `F ∈ L^{2 + ε}` on `B(x₀, R) ⊆ Ω`.
* `TauCeti.PDE.exists_setLAverage_enorm_indicator_gradient_sq_le_divergence`: the reverse
  Hölder inequality up to the boundary, for the gradient `1_Ω ∇u` of the zero extension.
* `TauCeti.PDE.exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence`: **Meyers' higher
  integrability estimate up to the boundary**.
* `TauCeti.PDE.exists_memLp_gradient_divergence`: its global qualitative form on bounded `Ω`,
  `∇u ∈ L^{2 + ε}(Ω)` whenever `F ∈ L^{2 + ε}(Ω)`.

## References

* N. G. Meyers, *An `Lᵖ`-estimate for the gradient of solutions of second order elliptic
  divergence equations*, Ann. Scuola Norm. Sup. Pisa **17** (1963), 189–206, Theorems 1 and 2.
* M. Giaquinta, G. Modica, *Regularity results for some classes of higher order nonlinear
  elliptic systems*, J. Reine Angew. Math. **311/312** (1979), 145–169.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 6.4.
* T. Kilpeläinen, P. Koskela, *Global integrability of the gradients of solutions to partial
  differential equations*, Nonlinear Anal. **23** (1994), 899–909 (higher integrability up to the
  boundary under a density condition on the complement).
-/

public section

noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- The constant `2 ((2Λ/λ)² + 1)` of the Caccioppoli inequality is at most `2 ((2K)² + 1)` when
`Λ ≤ K λ`. -/
private theorem two_mul_sq_add_one_le_of_le_mul
    {S : Set (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam K : ℝ}
    (h : UniformlyEllipticOn S a lam Lam) (hK : Lam ≤ K * lam) :
    2 * ((2 * Lam / lam) ^ 2 + 1) ≤ 2 * ((2 * K) ^ 2 + 1) := by
  have hlam : 0 < lam := h.pos
  have hratio : 2 * Lam / lam ≤ 2 * K := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hlam).2 hK) zero_le_two
  have hratio0 : 0 ≤ 2 * Lam / lam :=
    div_nonneg (mul_nonneg zero_le_two (hlam.le.trans h.le)) hlam.le
  gcongr

omit [DecidableEq ι] in
/-- The Sobolev–Poincaré inequality from `Lˢ` to `L²` for `u ∈ H¹(Ω)` on a ball `B(y, r) ⊆ Ω`,
squared, with a constant `c` depending only on `n` and `s`:
`⨍_B |u - u_B|² ≤ c² r² (⨍_B ‖∇u‖ ^ s) ^ (2/s)`. -/
private theorem exists_setLAverage_enorm_value_sub_setAverage_sq_le [Nonempty ι] {s : ℝ≥0}
    [Fact (1 ≤ (s : ℝ≥0∞))] (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} (u : W1p mu Omega 2)
      {y : EuclideanSpace ℝ ι} {r : ℝ}, 0 < r → ball y r ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍⁻ x in ball y r, ‖W1p.value u x - ⨍ z in ball y r, W1p.value u z ∂mu‖ₑ ^ (2 : ℝ) ∂mu ≤
        ENNReal.ofReal (c ^ 2 * r ^ 2) *
          (⨍⁻ x in ball y r, ‖W1p.gradient u x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ finrank ℝ (EuclideanSpace ℝ ι) := by exact_mod_cast Module.finrank_pos
  have hδ1 : (s : ℝ)⁻¹ - 2⁻¹ < 1 := hsn.trans_le (inv_le_one_of_one_le₀ hn1)
  have hc : 0 ≤ 2 ^ finrank ℝ (EuclideanSpace ℝ ι) / (finrank ℝ (EuclideanSpace ℝ ι) : ℝ) *
      ((1 - ((s : ℝ)⁻¹ - 2⁻¹)) / ((finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹ -
        ((s : ℝ)⁻¹ - 2⁻¹))) ^ (1 - ((s : ℝ)⁻¹ - 2⁻¹)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg (by linarith)
      (sub_nonneg.2 hsn.le)) _)
  refine ⟨_, hc, fun {Omega} u y r hr hball => ?_⟩
  have hSP := W1p.setLAverage_rpow_enorm_value_sub_setAverage_le_of_ball_subset (p := s)
    ENNReal.coe_ne_top (by exact_mod_cast hs2 : (s : ℝ≥0∞) ≤ 2) hr hball (q := 2)
    (by exact_mod_cast hs2) (by simp) hsn u
  rw [ENNReal.coe_toReal, NNReal.coe_ofNat] at hSP
  have := ENNReal.rpow_le_rpow hSP (by norm_num : (0 : ℝ) ≤ 2)
  rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul,
    inv_mul_eq_div, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc hr.le) zero_le_two,
    Real.rpow_two, mul_pow] at this

omit [DecidableEq ι] in
/-- **Assembling a reverse Hölder inequality.** On balls `B(y, ρ) ⊆ B(y, κρ) ⊆ B(y, 2ρ)`, a
Caccioppoli inequality from `B(y, ρ)` to `B(y, κρ)` with the constant `A (C / (κρ - ρ))²`, and a
Poincaré inequality on `B(y, κρ)` with the constant `M (κρ)²`, give a reverse Hölder inequality
from `B(y, ρ)` to `B(y, 2ρ)` with constants independent of `ρ`. -/
private theorem setLAverage_enorm_sq_le_of_setIntegral_le_of_le_mul_sq
    {G Fv : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {W : EuclideanSpace ℝ ι → ℝ}
    {y : EuclideanSpace ℝ ι} {ρ κ A C M β s : ℝ} (hρ : 0 < ρ) (hκ1 : 1 < κ) (hκ2 : κ ≤ 2)
    (hs : 0 < s) (hA : 0 ≤ A) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hG : MemLp G 2 (mu.restrict (ball y ρ))) (hW : MemLp W 2 (mu.restrict (ball y (κ * ρ))))
    (hF : MemLp Fv 2 (mu.restrict (ball y (κ * ρ))))
    (hc : ∫ x in ball y ρ, ‖G x‖ ^ 2 ∂mu ≤
      A * (C / (κ * ρ - ρ)) ^ 2 * ∫ x in ball y (κ * ρ), ‖W x‖ ^ 2 ∂mu +
        β * ∫ x in ball y (κ * ρ), ‖Fv x‖ ^ 2 ∂mu)
    (hP : ⨍⁻ x in ball y (κ * ρ), ‖W x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ENNReal.ofReal (M * (κ * ρ) ^ 2) *
        (⨍⁻ x in ball y (κ * ρ), ‖G x‖ₑ ^ s ∂mu) ^ (2 / s)) :
    ⨍⁻ x in ball y ρ, ‖G x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ENNReal.ofReal (κ ^ finrank ℝ (EuclideanSpace ℝ ι) * (A * C ^ 2 * M * (κ / (κ - 1)) ^ 2) *
          ((2 / κ) ^ finrank ℝ (EuclideanSpace ℝ ι)) ^ (2 / s)) *
        (⨍⁻ x in ball y (2 * ρ), ‖G x‖ₑ ^ s ∂mu) ^ (2 / s) +
      ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι) * β) *
        ⨍⁻ x in ball y (2 * ρ), ‖Fv x‖ₑ ^ (2 : ℝ) ∂mu := by
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  have hκ0 : 0 < κ := one_pos.trans hκ1
  set k : ℝ := (2 / κ) ^ n
  have hk : 0 ≤ k := by positivity
  -- Passing from `B(y, κρ)` to `B(y, 2ρ)` costs the ratio `(2 / κ)ⁿ` of their measures.
  have henl : ∀ g : EuclideanSpace ℝ ι → ℝ≥0∞,
      ⨍⁻ x in ball y (κ * ρ), g x ∂mu ≤ ENNReal.ofReal k * ⨍⁻ x in ball y (2 * ρ), g x ∂mu :=
    fun g => (setLAverage_ball_le g (by positivity)
      (ball_subset_ball (by nlinarith) : ball y (κ * ρ) ⊆ ball y (2 * ρ))).trans_eq
      (by rw [mul_div_mul_right _ _ hρ.ne'])
  -- The Caccioppoli inequality between averages.
  have hav := setLAverage_enorm_sq_le_of_setIntegral_le (μ := mu) (k := ENNReal.ofReal (κ ^ n))
    (by positivity) hβ
    (by rw [Measure.addHaar_ball_mul_of_pos mu y hκ0, Measure.addHaar_ball_center mu y])
    measure_ball_lt_top.ne hG.norm.integrable_sq hW.norm.integrable_sq hF.norm.integrable_sq hc
  refine hav.trans ?_
  have hPk : ⨍⁻ x in ball y (κ * ρ), ‖W x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ENNReal.ofReal (M * (κ * ρ) ^ 2) * (ENNReal.ofReal (k ^ (2 / s)) *
        (⨍⁻ x in ball y (2 * ρ), ‖G x‖ₑ ^ s ∂mu) ^ (2 / s)) := by
    refine hP.trans ?_
    gcongr
    refine (ENNReal.rpow_le_rpow (henl _) (by positivity)).trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.ofReal_rpow_of_nonneg hk
      (by positivity)]
  calc ENNReal.ofReal (κ ^ n) * (ENNReal.ofReal (A * (C / (κ * ρ - ρ)) ^ 2) *
          ⨍⁻ x in ball y (κ * ρ), ‖W x‖ₑ ^ (2 : ℝ) ∂mu +
        ENNReal.ofReal β * ⨍⁻ x in ball y (κ * ρ), ‖Fv x‖ₑ ^ (2 : ℝ) ∂mu)
      ≤ ENNReal.ofReal (κ ^ n) * (ENNReal.ofReal (A * (C / (κ * ρ - ρ)) ^ 2) *
          (ENNReal.ofReal (M * (κ * ρ) ^ 2) * (ENNReal.ofReal (k ^ (2 / s)) *
            (⨍⁻ x in ball y (2 * ρ), ‖G x‖ₑ ^ s ∂mu) ^ (2 / s))) +
        ENNReal.ofReal β * (ENNReal.ofReal k *
          ⨍⁻ x in ball y (2 * ρ), ‖Fv x‖ₑ ^ (2 : ℝ) ∂mu)) := by
        gcongr
        exact henl _
    _ = _ := by
        have hc1 : κ ^ n * (A * (C / (κ * ρ - ρ)) ^ 2 * (M * (κ * ρ) ^ 2 * k ^ (2 / s))) =
            κ ^ n * (A * C ^ 2 * M * (κ / (κ - 1)) ^ 2) * k ^ (2 / s) := by
          rw [show κ * ρ - ρ = (κ - 1) * ρ by ring]
          field_simp
        have hc2 : κ ^ n * (β * k) = 2 ^ n * β := by
          simp only [k, div_pow]
          field_simp
        rw [← hc1, ← hc2]
        simp (disch := positivity) only [ENNReal.ofReal_mul]
        ring

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
  obtain ⟨c, -, hP⟩ := exists_setLAverage_enorm_value_sub_setAverage_sq_le (mu := mu) hs2 hsn
  set n := finrank ℝ (EuclideanSpace ℝ ι)
  set A : ℝ := 2 * ((2 * K) ^ 2 + 1)
  set K₁ : ℝ := 2 ^ n * (A * C ^ 2 * c ^ 2 * (2 / (2 - 1)) ^ 2) * ((2 / 2) ^ n) ^ (2 / (s : ℝ))
  have hA0 : 0 ≤ A := by positivity
  have hK₁ : 0 ≤ K₁ := by positivity
  refine ⟨(K₁ + 2 ^ n * 12).toNNReal, ?_⟩
  intro Omega a lam Lam F u y ρ h hK ha hF hu hρ hball
  set m := ⨍ z in ball y (2 * ρ), W1p.value u z ∂mu
  -- Caccioppoli's inequality for `u - m`, with its constant bounded through `Λ ≤ K λ`.
  have hIρ : ∫ x in ball y ρ, ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      A * (C / (2 * ρ - ρ)) ^ 2 * ∫ x in ball y (2 * ρ), ‖W1p.value u x - m‖ ^ 2 ∂mu
        + 12 / lam ^ 2 * ∫ x in ball y (2 * ρ), ‖F x‖ ^ 2 ∂mu := by
    have hA : 2 * ((2 * Lam / lam) ^ 2 + 1) ≤ A := two_mul_sq_add_one_le_of_le_mul h hK
    refine (hC h ha hF hu (by linarith : ρ < 2 * ρ) hball).trans ?_
    simp only [Real.norm_eq_abs, sq_abs]
    gcongr
  -- The Sobolev–Poincaré inequality on `B(y, 2ρ)`, and the assembly.
  have : IsFiniteMeasure (mu.restrict (ball y (2 * ρ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hav := setLAverage_enorm_sq_le_of_setIntegral_le_of_le_mul_sq
    (W := fun x => W1p.value u x - m) hρ (by norm_num) le_rfl (one_pos.trans_le hs1) hA0
    (sq_nonneg c) (by positivity)
    ((Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono ((ball_subset_ball (by linarith)).trans hball) le_rfl))
    (((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).sub
      (memLp_const m))
    (hF.mono_measure (Measure.restrict_mono hball le_rfl)) hIρ
    (hP u (by positivity) hball)
  rw [← mul_div_assoc, ofReal_div_sq_mul_setLAverage_eq _ h.pos] at hav
  refine hav.trans (add_le_add ?_ ?_)
  · gcongr ?_ * _
    rw [ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  · gcongr ?_ * _
    rw [ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hK₁)

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
    exact setLAverage_div_rpow_lt_top (ENNReal.ofReal_pos.2 h.pos).ne' (by linarith) hF'.ne

/-! ### Up to the boundary -/

omit [DecidableEq ι] in
/-- The zero extension `u₀ ∈ W^{1,2}(ℝⁿ)` of `u ∈ H¹₀(Ω)`: its value and gradient are almost
everywhere `1_Ω u` and `1_Ω ∇u`, so the averages of `‖1_Ω ∇u‖ₑ ^ p` are those of `‖∇u₀‖ₑ ^ p`. -/
private theorem exists_value_gradient_ae_eq_indicator {Omega : Opens (EuclideanSpace ℝ ι)}
    (u : W1p0 mu Omega 2) :
    ∃ u₀ : W1p mu ⊤ 2, (W1p.value u₀ : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu]
        (Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value (u : W1p mu Omega 2)) ∧
      (W1p.gradient u₀ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =ᵐ[mu]
        (Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.gradient (u : W1p mu Omega 2)) ∧
      ∀ (S : Set (EuclideanSpace ℝ ι)) (p : ℝ),
        ⨍⁻ x in S, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
            (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ p ∂mu =
          ⨍⁻ x in S, ‖W1p.gradient u₀ x‖ₑ ^ p ∂mu := by
  have hgrad := W1p0.gradient_extendByZeroL_top_ae u
  exact ⟨_, W1p0.value_extendByZeroL_top_ae u, hgrad, fun _ _ =>
    laverage_congr (ae_restrict_of_ae (hgrad.mono fun x hx => by simp only [hx]))⟩

open Filter in
/-- **The reverse Hölder inequality for the zero extension, on balls well inside `Ω`.** If
`B(y, 3ρ/2) ⊆ Ω`, the gradient `1_Ω ∇u` of the zero extension `u₀` of a weak solution
`u ∈ H¹₀(Ω)` satisfies a reverse Hölder inequality from `B(y, ρ)` to `B(y, 2ρ)`, by the
Caccioppoli inequality for `u` minus its mean on `B(y, 3ρ/2)` and the Sobolev–Poincaré inequality
there. -/
private theorem exists_setLAverage_enorm_indicator_gradient_sq_le_of_ball_subset [Nonempty ι]
    {s : ℝ≥0} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) (K : ℝ) :
    ∃ K₁ : ℝ, ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
      {y : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < ρ → ball y (3 / 2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ⨍⁻ x in ball y ρ, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 : ℝ) ∂mu ≤
        ENNReal.ofReal K₁ *
          (⨍⁻ x in ball y (2 * ρ), ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
            (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) +
        ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι) * (12 / lam ^ 2)) *
          ⨍⁻ x in ball y (2 * ρ),
            ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ ^ (2 : ℝ) ∂mu := by
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
  obtain ⟨C, -, hC⟩ :=
    exists_setIntegral_ball_norm_gradient_sq_le_sub_setAverage_divergence (ι := ι)
  obtain ⟨c, -, hP⟩ := exists_setLAverage_enorm_value_sub_setAverage_sq_le (mu := mu) hs2 hsn
  refine ⟨(3 / 2) ^ finrank ℝ (EuclideanSpace ℝ ι) * (2 * ((2 * K) ^ 2 + 1) * C ^ 2 * c ^ 2 *
    (3 / 2 / (3 / 2 - 1)) ^ 2) * ((2 / (3 / 2)) ^ finrank ℝ (EuclideanSpace ℝ ι)) ^
      (2 / (s : ℝ)), ?_⟩
  intro Omega a lam Lam F u y ρ h hK ha hF hu hρ hin
  obtain ⟨ub, hval0, hgrad0, hL⟩ := exists_value_gradient_ae_eq_indicator u
  rw [hL, hL]
  have hs0 : (0 : ℝ) < s := one_pos.trans_le (by exact_mod_cast hs1)
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have : IsFiniteMeasure (mu.restrict (ball y (3 / 2 * ρ))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- On `B(y, 3ρ/2) ⊆ Ω` the zero extensions are `u` and `F` themselves.
  have hval := hval0.restrict.trans (ae_restrict_of_ae_restrict_of_subset hin
    (indicator_ae_eq_restrict hOm.nullMeasurableSet))
  have hgrad := hgrad0.restrict.trans (ae_restrict_of_ae_restrict_of_subset hin
    (indicator_ae_eq_restrict hOm.nullMeasurableSet))
  have hF' := ae_restrict_of_ae_restrict_of_subset hin
    (indicator_ae_eq_restrict (μ := mu) (f := F) hOm.nullMeasurableSet)
  have hm : ⨍ z in ball y (3 / 2 * ρ), W1p.value ub z ∂mu =
      ⨍ z in ball y (3 / 2 * ρ), W1p.value (u : W1p mu Omega 2) z ∂mu := average_congr hval
  -- The Caccioppoli inequality for `u` minus its mean, written for the zero extension.
  have hcacc : ∫ x in ball y ρ, ‖W1p.gradient ub x‖ ^ 2 ∂mu ≤
      2 * ((2 * K) ^ 2 + 1) * (C / (3 / 2 * ρ - ρ)) ^ 2 *
          ∫ x in ball y (3 / 2 * ρ),
            ‖W1p.value ub x - ⨍ z in ball y (3 / 2 * ρ), W1p.value ub z ∂mu‖ ^ 2 ∂mu +
        12 / lam ^ 2 * ∫ x in ball y (3 / 2 * ρ),
          ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ ^ 2 ∂mu := by
    have hc := hC h ha hF hu (by linarith : ρ < 3 / 2 * ρ) hin
    have e1 : ∫ x in ball y ρ, ‖W1p.gradient ub x‖ ^ 2 ∂mu =
        ∫ x in ball y ρ, ‖W1p.gradient (u : W1p mu Omega 2) x‖ ^ 2 ∂mu :=
      integral_congr_ae ((ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith))
        hgrad).mono fun x hx => by simp only [hx])
    have e2 : ∫ x in ball y (3 / 2 * ρ),
          ‖W1p.value ub x - ⨍ z in ball y (3 / 2 * ρ), W1p.value ub z ∂mu‖ ^ 2 ∂mu =
        ∫ x in ball y (3 / 2 * ρ), (W1p.value (u : W1p mu Omega 2) x -
          ⨍ z in ball y (3 / 2 * ρ), W1p.value (u : W1p mu Omega 2) z ∂mu) ^ 2 ∂mu :=
      integral_congr_ae (hval.mono fun x hx => by simp only [hx, hm, Real.norm_eq_abs, sq_abs])
    have e3 : ∫ x in ball y (3 / 2 * ρ),
          ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ ^ 2 ∂mu =
        ∫ x in ball y (3 / 2 * ρ), ‖F x‖ ^ 2 ∂mu :=
      integral_congr_ae (hF'.mono fun x hx => by simp only [hx])
    have hA := two_mul_sq_add_one_le_of_le_mul h hK
    rw [e1, e2, e3]
    exact hc.trans (by gcongr)
  -- The Sobolev–Poincaré inequality for the zero extension, and the assembly.
  have hPB := hP ub (by positivity : 0 < 3 / 2 * ρ)
    (by simp : ball y (3 / 2 * ρ) ⊆ ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
  exact setLAverage_enorm_sq_le_of_setIntegral_le_of_le_mul_sq
    (W := fun x => W1p.value ub x - ⨍ z in ball y (3 / 2 * ρ), W1p.value ub z ∂mu)
    hρ (by norm_num) (by norm_num) hs0 (by positivity) (sq_nonneg c) (by positivity)
    (((Lp.memLp (W1p.gradient ub)).mono_measure (by simp)).restrict _)
    ((((Lp.memLp (W1p.value ub)).mono_measure (by simp)).restrict _).sub (memLp_const _))
    (((memLp_indicator_iff_restrict hOm.nullMeasurableSet).2 hF).restrict _) hcacc hPB

omit [DecidableEq ι] in
/-- If the complement of `T` fills a proportion `θ` of `B(z, ρ/2)`, then `B(z, ρ/2) \ T` has
measure at least `θ / 4ⁿ` times that of any ball of radius `2ρ`. -/
private theorem toNNReal_div_pow_mul_measure_ball_le {T : Set (EuclideanSpace ℝ ι)}
    {y z : EuclideanSpace ℝ ι} {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ)
    (hdens : θ * mu.real (ball z (ρ / 2)) ≤ mu.real (ball z (ρ / 2) \ T)) :
    ((θ / 4 ^ finrank ℝ (EuclideanSpace ℝ ι)).toNNReal : ℝ≥0∞) * mu (ball y (2 * ρ)) ≤
      mu (ball z (ρ / 2) \ T) := by
  have hz' : ENNReal.ofReal θ * mu (ball z (ρ / 2)) ≤ mu (ball z (ρ / 2) \ T) := by
    refine (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      measure_ball_lt_top.ne) (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne)).1 ?_
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le]
  refine le_trans (le_of_eq ?_) hz'
  rw [ENNReal.ofNNReal_toNNReal, Measure.addHaar_ball_of_pos mu y (by positivity),
    Measure.addHaar_ball_of_pos mu z (by positivity)]
  simp (disch := positivity) only [← mul_assoc, ← ENNReal.ofReal_mul]
  congr 2
  have h4 : (4 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ ι) =
      2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 2 ^ finrank ℝ (EuclideanSpace ℝ ι) := by
    rw [← mul_pow]
    norm_num
  rw [h4, mul_pow, div_pow]
  field_simp

open Filter in
/-- **The reverse Hölder inequality for the zero extension, at the boundary.** If the complement
of `Ω` fills a proportion `θ > 0` of a ball `B(z, ρ/2)` with `z ∈ B(y, 3ρ/2)`, the gradient
`1_Ω ∇u` of the zero extension `u₀` of a weak solution `u ∈ H¹₀(Ω)` satisfies a reverse Hölder
inequality from `B(y, ρ)` to `B(y, 2ρ)`: the Caccioppoli inequality up to the boundary bounds it
by `u₀` itself, and `u₀` vanishes on a proportion `θ / 4ⁿ` of `B(y, 2ρ)`, which turns the
Sobolev–Poincaré inequality for `u₀` minus its mean into one for `u₀`. -/
private theorem exists_setLAverage_enorm_indicator_gradient_sq_le_of_mul_le [Nonempty ι]
    {s : ℝ≥0} (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) (K : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ K₂ : ℝ, ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
      {y z : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      0 < ρ → z ∈ ball y (3 / 2 * ρ) →
      θ * mu.real (ball z (ρ / 2)) ≤
        mu.real (ball z (ρ / 2) \ (Omega : Set (EuclideanSpace ℝ ι))) →
      ⨍⁻ x in ball y ρ, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 : ℝ) ∂mu ≤
        ENNReal.ofReal K₂ *
          (⨍⁻ x in ball y (2 * ρ), ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
            (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) +
        ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι) * (12 / lam ^ 2)) *
          ⨍⁻ x in ball y (2 * ρ),
            ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ ^ (2 : ℝ) ∂mu := by
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
  obtain ⟨C, -, hC⟩ := exists_setIntegral_ball_norm_indicator_gradient_sq_le_divergence (ι := ι)
  obtain ⟨c, -, hP⟩ := exists_setLAverage_enorm_value_sub_setAverage_sq_le (mu := mu) hs2 hsn
  have hθ4 : 0 < θ / 4 ^ finrank ℝ (EuclideanSpace ℝ ι) := by positivity
  refine ⟨2 ^ finrank ℝ (EuclideanSpace ℝ ι) * (2 * ((2 * K) ^ 2 + 1) * C ^ 2 *
    (2 * (1 + (θ / 4 ^ finrank ℝ (EuclideanSpace ℝ ι))⁻¹) * c ^ 2) * (2 / (2 - 1)) ^ 2) *
      ((2 / 2) ^ finrank ℝ (EuclideanSpace ℝ ι)) ^ (2 / (s : ℝ)), ?_⟩
  intro Omega a lam Lam F u y z ρ h hK ha hF hu hρ hz hdens
  obtain ⟨ub, hval0, hgrad0, hL⟩ := exists_value_gradient_ae_eq_indicator u
  rw [hL, hL]
  have hs0 : (0 : ℝ) < s := one_pos.trans_le (by exact_mod_cast hs1)
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  -- The Caccioppoli inequality up to the boundary.
  have hcacc : ∫ x in ball y ρ, ‖W1p.gradient ub x‖ ^ 2 ∂mu ≤
      2 * ((2 * K) ^ 2 + 1) * (C / (2 * ρ - ρ)) ^ 2 *
          ∫ x in ball y (2 * ρ), ‖W1p.value ub x‖ ^ 2 ∂mu +
        12 / lam ^ 2 * ∫ x in ball y (2 * ρ),
          ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ ^ 2 ∂mu := by
    have hA := two_mul_sq_add_one_le_of_le_mul h hK
    rw [integral_congr_ae (f := fun x => ‖W1p.gradient ub x‖ ^ 2)
        (ae_restrict_of_ae (hgrad0.mono fun x hx => by beta_reduce; rw [hx])),
      integral_congr_ae (f := fun x => ‖W1p.value ub x‖ ^ 2)
        (ae_restrict_of_ae (hval0.mono fun x hx => by beta_reduce; rw [hx]))]
    refine (hC h ha hF hu (by linarith : ρ < 2 * ρ)).trans ?_
    gcongr
  -- `u₀` vanishes on `S = B(z, ρ/2) \ Ω ⊆ B(y, 2ρ)`, a proportion `θ / 4ⁿ` of `B(y, 2ρ)`.
  set S := ball z (ρ / 2) \ (Omega : Set (EuclideanSpace ℝ ι))
  have hSsub : S ⊆ ball y (2 * ρ) := fun x hx =>
    mem_ball.2 (by linarith [dist_triangle x z y, mem_ball.1 hx.1, mem_ball.1 hz])
  have hS0 : ∀ᵐ x ∂mu.restrict S, W1p.value ub x = 0 := by
    filter_upwards [ae_restrict_of_ae hval0,
      ae_restrict_mem (measurableSet_ball.diff hOm)] with x hx hxS
    rw [hx, indicator_of_notMem hxS.2]
  have hSmeas := toNNReal_div_pow_mul_measure_ball_le (mu := mu) (y := y) hρ hθ hdens
  -- The Poincaré inequality for `u₀` on `B(y, 2ρ)`.
  have hPB : ⨍⁻ x in ball y (2 * ρ), ‖W1p.value ub x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ENNReal.ofReal (2 * (1 + (θ / 4 ^ finrank ℝ (EuclideanSpace ℝ ι))⁻¹) * c ^ 2 *
        (2 * ρ) ^ 2) *
        (⨍⁻ x in ball y (2 * ρ), ‖W1p.gradient ub x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) := by
    refine (setLAverage_enorm_sq_le_of_ae_eq_zero (Real.toNNReal_pos.2 hθ4).ne' hSsub hSmeas hS0
      (⨍ z in ball y (2 * ρ), W1p.value ub z ∂mu)).trans ?_
    have hPB := hP ub (by positivity : 0 < 2 * ρ)
      (by simp : ball y (2 * ρ) ⊆ ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
    refine (mul_le_mul_right hPB _).trans_eq ?_
    rw [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_inv_of_pos hθ4]
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add, ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
    ring
  exact setLAverage_enorm_sq_le_of_setIntegral_le_of_le_mul_sq (W := fun x => W1p.value ub x)
    hρ (by norm_num) le_rfl hs0 (by positivity) (by positivity) (by positivity)
    (((Lp.memLp (W1p.gradient ub)).mono_measure (by simp)).restrict _)
    (((Lp.memLp (W1p.value ub)).mono_measure (by simp)).restrict _)
    (((memLp_indicator_iff_restrict hOm.nullMeasurableSet).2 hF).restrict _) hcacc hPB

open Filter in
/-- **The reverse Hölder inequality up to the boundary.** Let `n ≥ 1` be the dimension, let
`1 ≤ s ≤ 2` with `1/s - 1/2 < 1/n`, let `K` bound the ellipticity ratio and let `θ > 0`. There is
`b`, independent of the domain, the coefficients, the solution, the datum and the ball, with the
following property. Let `a` be measurable and uniformly elliptic on `Ω` with constants
`0 < λ ≤ Λ ≤ K λ`, let `F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫`
for every `v ∈ H¹₀(Ω)`. Suppose that the complement of `Ω` has density at least `θ` at its points
up to the scale `r₀`: `θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and `0 < r ≤ r₀`. Then, writing
`1_Ω ∇u` for the gradient of the zero extension of `u`, for every ball with `ρ ≤ 2 r₀`,

`⨍_{B(y, ρ)} ‖1_Ω ∇u‖² ≤ b (⨍_{B(y, 2ρ)} ‖1_Ω ∇u‖ ^ s) ^ (2/s) + b ⨍_{B(y, 2ρ)} (‖1_Ω F‖/λ)²`.

The ball need not lie in `Ω`. The averages are extended-valued. -/
theorem exists_setLAverage_enorm_indicator_gradient_sq_le_divergence [Nonempty ι] {s : ℝ≥0}
    (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (hsn : (s : ℝ)⁻¹ - 2⁻¹ < (finrank ℝ (EuclideanSpace ℝ ι) : ℝ)⁻¹) (K : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ b : ℝ≥0, ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
      {r₀ : ℝ} {y : EuclideanSpace ℝ ι} {ρ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < ρ → ρ ≤ 2 * r₀ →
      ⨍⁻ x in ball y ρ, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 : ℝ) ∂mu ≤
        b * (⨍⁻ x in ball y (2 * ρ), ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (s : ℝ) ∂mu) ^ (2 / (s : ℝ)) +
          b * ⨍⁻ x in ball y (2 * ρ),
            (‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ)
              ∂mu := by
  obtain ⟨K₁, hK₁⟩ :=
    exists_setLAverage_enorm_indicator_gradient_sq_le_of_ball_subset (mu := mu) hs1 hs2 hsn K
  obtain ⟨K₂, hK₂⟩ :=
    exists_setLAverage_enorm_indicator_gradient_sq_le_of_mul_le (mu := mu) hs1 hs2 hsn K hθ
  refine ⟨(|K₁| + |K₂| + 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 12).toNNReal, ?_⟩
  intro Omega a lam Lam F u r₀ y ρ h hK ha hF hu hdens hρ hρr₀
  -- Both cases give a bound with a constant `K'` at most `b`.
  have hb : ∀ K' : ℝ, K' ≤ |K₁| + |K₂| + 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 12 →
      ENNReal.ofReal K' ≤ ((|K₁| + |K₂| + 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 12).toNNReal :
        ℝ≥0∞) := fun K' hK' => by
    rw [ENNReal.ofNNReal_toNNReal]
    exact ENNReal.ofReal_le_ofReal hK'
  have hF12 : ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ ι) * (12 / lam ^ 2)) *
      ⨍⁻ x in ball y (2 * ρ), ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ ^ (2 : ℝ) ∂mu ≤
      ((|K₁| + |K₂| + 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 12).toNNReal : ℝ≥0∞) *
        ⨍⁻ x in ball y (2 * ρ),
          (‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam) ^ (2 : ℝ)
            ∂mu := by
    rw [← mul_div_assoc, ofReal_div_sq_mul_setLAverage_eq _ h.pos]
    gcongr
    exact hb _ (by linarith [abs_nonneg K₁, abs_nonneg K₂])
  by_cases hin : ball y (3 / 2 * ρ) ⊆ (Omega : Set (EuclideanSpace ℝ ι))
  · refine (hK₁ h hK ha hF hu hρ hin).trans (add_le_add ?_ hF12)
    gcongr
    exact hb _ (by linarith [le_abs_self K₁, abs_nonneg K₂,
      (by positivity : (0 : ℝ) ≤ 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 12)])
  · obtain ⟨z, hz, hzΩ⟩ := not_subset.1 hin
    refine (hK₂ h hK ha hF hu hρ hz
      (hdens z hzΩ (ρ / 2) (by positivity) (by linarith))).trans (add_le_add ?_ hF12)
    gcongr
    exact hb _ (by linarith [le_abs_self K₂, abs_nonneg K₁,
      (by positivity : (0 : ℝ) ≤ 2 ^ finrank ℝ (EuclideanSpace ℝ ι) * 12)])

/-- **Meyers' higher integrability estimate up to the boundary.** Let `n ≥ 1` be the dimension,
let `K` bound the ellipticity ratio and let `θ > 0`. There is `ε₀ > 0`, and for each
`0 < ε ≤ ε₀` a constant `C`, both depending only on `n`, `K` and `θ`, with the following
property. Let `a` be measurable and uniformly elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, let
`F ∈ L²(Ω; ℝⁿ)`, and let `u ∈ H¹₀(Ω)` satisfy `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`.
Suppose that the complement of `Ω` has density at least `θ` at its points up to the scale `r₀`:
`θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and `0 < r ≤ r₀`. Then for every ball `B = B(x₀, R)`
with `R ≤ r₀`, centred anywhere,

`⨍_{½B} ‖1_Ω ∇u‖ ^ (2 + ε) ≤ C ((⨍_B ‖1_Ω ∇u‖²) ^ ((2 + ε)/2) + ⨍_B (‖1_Ω F‖/λ) ^ (2 + ε))`,

where `1_Ω ∇u` is the gradient of the zero extension of `u`. The averages are extended-valued.
When `F` is `(2 + ε)`-integrable on `Ω ∩ B` the right-hand side is finite, so `∇u` is
`(2 + ε)`-integrable on `Ω ∩ ½B`. -/
theorem exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence [Nonempty ι] (K : ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ C : ℝ≥0,
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
        {r₀ : ℝ} {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) → MemLp F 2 (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      R ≤ r₀ →
      ⨍⁻ x in ball x₀ (R / 2), ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 + ε) ∂mu ≤
        C * ((⨍⁻ x in ball x₀ R, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 : ℝ) ∂mu) ^ ((2 + ε) / 2) +
          ⨍⁻ x in ball x₀ R,
            (‖(Omega : Set (EuclideanSpace ℝ ι)).indicator F x‖ₑ / ENNReal.ofReal lam) ^ (2 + ε)
              ∂mu) := by
  obtain ⟨s, hs1', hs2', hsn⟩ := exists_one_le_lt_two_inv_sub_inv_lt
    (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ ι))
  have hs1 : 1 ≤ s := by exact_mod_cast hs1'
  have hs0 : (0 : ℝ) < s := one_pos.trans_le hs1'
  obtain ⟨b, hb⟩ := exists_setLAverage_enorm_indicator_gradient_sq_le_divergence (mu := mu) hs1
    (by exact_mod_cast hs2'.le) hsn K hθ
  -- Gehring's lemma for the reverse Hölder inequality between the exponents `s < 2`.
  obtain ⟨ε₀, hε₀, hG⟩ := exists_setLAverage_rpow_add_le_of_rpow (μ := mu) hs0 hs2' b
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hG ε hε hεle
  refine ⟨C, fun {Omega a lam Lam F u r₀ x₀ R} h hK ha hF hu hdens hR => ?_⟩
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  exact hC
    ((((aestronglyMeasurable_indicator_iff hOm).2
      (Lp.aestronglyMeasurable (W1p.gradient (u : W1p mu Omega 2)))).eNorm).restrict)
    ((((aestronglyMeasurable_indicator_iff hOm).2 hF.aestronglyMeasurable).eNorm.div_const
      _).restrict)
    fun y ρ hρ hsub => hb h hK ha hF hu hdens hρ
      (by linarith [(ball_subset_ball_iff (by positivity)).1 hsub, dist_nonneg (x := y) (y := x₀)])

/-- **Meyers' theorem up to the boundary: higher integrability of the gradient.** Let `n ≥ 1` be
the dimension, let `K` bound the ellipticity ratio and let `θ > 0`. There is `ε₀ > 0`, depending
only on `n`, `K` and `θ`, with the following property. Let `Ω` be bounded, and suppose that the
complement of `Ω` has density at least `θ` at its points up to a scale `r₀ > 0`:
`θ |B(z, r)| ≤ |B(z, r) \ Ω|` for `z ∉ Ω` and `0 < r ≤ r₀`. Let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ ≤ K λ`, and let `u ∈ H¹₀(Ω)` satisfy
`a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`. If `0 < ε ≤ ε₀` and `F ∈ L^{2 + ε}(Ω; ℝⁿ)`, then
`∇u ∈ L^{2 + ε}(Ω)`.

Bounded Lipschitz domains satisfy the density condition. Without a condition on the boundary
the conclusion is only local (`TauCeti.PDE.exists_memLp_gradient_ball_divergence`). -/
theorem exists_memLp_gradient_divergence [Nonempty ι] (K : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {lam Lam : ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p0 mu Omega 2}
        {r₀ : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam → Lam ≤ K * lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu) →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ r, 0 < r → r ≤ r₀ →
        θ * mu.real (ball z r) ≤ mu.real (ball z r \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      0 < r₀ → Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)) →
      MemLp F (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) →
      MemLp (W1p.gradient (u : W1p mu Omega 2)) (ENNReal.ofReal (2 + ε)) (mu.restrict Omega) := by
  obtain ⟨ε₀, hε₀, hM⟩ := exists_setLAverage_enorm_indicator_gradient_rpow_le_divergence
    (mu := mu) K hθ
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨C, hC⟩ := hM ε hε hεle
  intro Omega a lam Lam F u r₀ h hK ha hu hdens hr₀ hΩb hFp
  have hOm : MeasurableSet (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.measurableSet
  have : IsFiniteMeasure (mu.restrict Omega) := isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  have hp0 : ENNReal.ofReal (2 + ε) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hpR : (ENNReal.ofReal (2 + ε)).toReal = 2 + ε := ENNReal.toReal_ofReal (by linarith)
  have hF : MemLp F 2 (mu.restrict Omega) := hFp.mono_exponent <|
    (ENNReal.ofReal_ofNat 2).symm.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  -- The zero extensions of `∇u` and `F` are `2`- and `(2 + ε)`-integrable on the whole space.
  have hG2 := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    ((memLp_indicator_iff_restrict hOm.nullMeasurableSet).2
      (Lp.memLp (W1p.gradient (u : W1p mu Omega 2)))).eLpNorm_lt_top
  have hFt := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 ENNReal.ofReal_ne_top
    ((memLp_indicator_iff_restrict hOm.nullMeasurableSet).2 hFp).eLpNorm_lt_top
  rw [ENNReal.toReal_ofNat] at hG2
  rw [hpR] at hFt
  -- On each ball `B(x, r₀ / 2)` the gradient of the zero extension is `(2 + ε)`-integrable.
  have hball : ∀ x, ∫⁻ y in ball x (r₀ / 2), ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
      (W1p.gradient (u : W1p mu Omega 2)) y‖ₑ ^ (2 + ε) ∂mu < ∞ := fun x => by
    rw [← measure_mul_setLAverage _ measure_ball_lt_top.ne]
    refine ENNReal.mul_lt_top measure_ball_lt_top ((hC h hK ha hF hu hdens le_rfl).trans_lt ?_)
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · exact ENNReal.rpow_lt_top_of_nonneg (by linarith) (laverage_lt_top
        (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hG2).ne).ne
    · exact setLAverage_div_rpow_lt_top (ENNReal.ofReal_pos.2 h.pos).ne' (by linarith)
        (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hFt).ne
  -- Finitely many such balls cover `Ω`.
  obtain ⟨t, -, ht, hcover⟩ := finite_cover_balls_of_compact hΩb.isCompact_closure
    (by positivity : 0 < r₀ / 2)
  have : Fintype t := ht.fintype
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 ENNReal.ofReal_ne_top
    (Lp.aestronglyMeasurable _), hpR]
  calc ∫⁻ x in Omega, ‖W1p.gradient (u : W1p mu Omega 2) x‖ₑ ^ (2 + ε) ∂mu
      = ∫⁻ x in Omega, ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
          (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 + ε) ∂mu :=
        setLIntegral_congr_fun hOm fun x hx => by rw [indicator_of_mem hx]
    _ ≤ ∫⁻ x in ⋃ i : t, ball (i : EuclideanSpace ℝ ι) (r₀ / 2),
          ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
            (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 + ε) ∂mu := by
        refine lintegral_mono_set (subset_closure.trans (hcover.trans_eq ?_))
        rw [biUnion_eq_iUnion]
    _ ≤ ∑' i : t, ∫⁻ x in ball (i : EuclideanSpace ℝ ι) (r₀ / 2),
          ‖(Omega : Set (EuclideanSpace ℝ ι)).indicator
            (W1p.gradient (u : W1p mu Omega 2)) x‖ₑ ^ (2 + ε) ∂mu := lintegral_iUnion_le _ _
    _ < ∞ := by
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.2 fun i _ => hball i

end PDE

end TauCeti
