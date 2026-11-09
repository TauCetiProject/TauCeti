/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ReducedFunctional
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.W1p.Mollification
import TauCeti.Analysis.Sobolev.W1p.Truncation
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Submodule
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.MeasureTheory.Function.Lp.UniformConvex

/-!
# A minimizer of Taubes's functional on `H¹(ℂ)`

Let `P` be a complex polynomial of degree `m ≥ 1`. A vortex with zero divisor `P` is obtained from
a decaying solution `w` of the reduced equation `Δw = (exp (2w) h - 1) / 8 + g`, with
`h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`
(`TauCeti.Vortex.equation_amplitudeField_backgroundAmplitude_add_eq_zero_iff`), and Taubes finds
`w` as the minimizer of the functional `TauCeti.Vortex.reducedFunctional`. That functional is
defined for classical functions and is coercive on compactly supported ones. This file carries
out the direct method on the Sobolev space `H¹(ℂ) = W^{1,2}(ℂ)` (`TauCeti.W1p volume ⊤ 2`).

* `sobolevReducedFunctional P u` is the functional
  `I(u) = ∫ ‖∇u‖² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u`
  for the value and weak gradient of a Sobolev function. It agrees with the classical functional
  on test functions (`sobolevReducedFunctional_ofTestFunctionₗ`). Its finite-energy domain
  `sobolevReducedFunctionalDomain P` consists of the `u` with integrable potential
  `h (exp (2u) - 1 - 2u)`; test functions belong to it.
* `exists_reducedFunctional_lt`: every `u` of finite energy is approximated from above by test
  functions, `I(φ) < I(u) + ε`. The approximations truncate `u` at a height `N`, multiply it by a
  cutoff and mollify. Truncation and the cutoff move values towards `0`, which can only decrease
  the potential, and on functions bounded by `N` the potential is continuous in `L²`.
* `exists_isMinOn_sobolevReducedFunctional`: `I` attains its minimum on the finite-energy
  domain. A minimizing sequence of test functions is bounded in `H¹(ℂ)` by the coercivity
  estimate `TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`; since `H¹(ℂ)` is
  reflexive, a subsequence converges weakly. The Dirichlet and potential terms are weakly lower
  semicontinuous (`TauCeti.Vortex.lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub` for
  the potential) and the linear term is a continuous linear functional, because `g - 1/8 (1 +
  ‖P‖²)⁻¹` is square integrable. So the weak limit has finite energy and `I` at most the
  infimum, while the approximation from above shows that no function of finite energy goes
  below that infimum.

The Euler–Lagrange equation of the minimizer, its regularity and decay, and the resulting vortex
are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient Topology

/-- The whole-plane restriction of Lebesgue measure is Lebesgue measure. -/
private theorem volume_restrict_top :
    (volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ) = volume := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- **Taubes's functional on `H¹(ℂ)`** for the vortex with zero divisor `P`:

`I(u) = ∫ ‖∇u‖² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u`,

where `h = ‖P‖² / (1 + ‖P‖²)`, `g = 2 ‖P'‖² / (1 + ‖P‖²)²`, and `u` and its weak gradient `∇u` are
the components of a Sobolev function. On test functions it is
`TauCeti.Vortex.reducedFunctional P` (`sobolevReducedFunctional_ofTestFunctionₗ`). The middle
integral is a Bochner integral, so it is meaningful when its integrand is integrable, that is,
on `sobolevReducedFunctionalDomain P`; the results below are stated on that domain. -/
def sobolevReducedFunctional (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) : ℝ :=
  (∫ z, ‖W1p.gradient u z‖ ^ 2) / 2 +
    (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
    ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z

/-- The defining formula of Taubes's functional on `H¹(ℂ)`. -/
theorem sobolevReducedFunctional_def (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u =
      (∫ z, ‖W1p.gradient u z‖ ^ 2) / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := (rfl)

/-- The **finite-energy domain** of Taubes's functional on `H¹(ℂ)`: the Sobolev functions `u`
whose potential `h (exp (2u) - 1 - 2u)`, `h = ‖P‖² / (1 + ‖P‖²)`, is integrable. On this set
every term of `sobolevReducedFunctional P` is a genuine integral. -/
def sobolevReducedFunctionalDomain (P : Polynomial ℂ) : Set (W1p (volume : Measure ℂ) ⊤ 2) :=
  {u | Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)}

/-- Membership in the finite-energy domain is integrability of the potential. -/
theorem mem_sobolevReducedFunctionalDomain {P : Polynomial ℂ}
    {u : W1p (volume : Measure ℂ) ⊤ 2} :
    u ∈ sobolevReducedFunctionalDomain P ↔ Integrable fun z ↦
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) :=
  Iff.rfl

private theorem value_ofTestFunctionₗ_ae (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =ᵐ[volume] φ := by
  simpa only [volume_restrict_top] using
    W1p.value_ofTestFunctionₗ_ae (mu := (volume : Measure ℂ)) (p := 2) φ

private theorem gradient_ofTestFunctionₗ_ae (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    ∀ᵐ z ∂volume, W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z = ∇ (φ : ℂ → ℝ) z := by
  simpa only [W1p.gradient_ofTestFunctionₗ, volume_restrict_top] using
    gradientTestFunctionLp_apply_ae (mu := (volume : Measure ℂ)) 2 φ

private theorem integral_norm_sq_gradient_ofTestFunctionₗ (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    ∫ z, ‖W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z‖ ^ 2 = ∫ z, ‖fderiv ℝ φ z‖ ^ 2 :=
  integral_congr_ae ((gradient_ofTestFunctionₗ_ae φ).mono fun z hz ↦ by
    simp only [hz, norm_gradient_eq_norm_fderiv])

/-- On a test function, Taubes's functional on `H¹(ℂ)` is the classical functional
`TauCeti.Vortex.reducedFunctional`. -/
theorem sobolevReducedFunctional_ofTestFunctionₗ (P : Polynomial ℂ)
    (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    sobolevReducedFunctional P (W1p.ofTestFunctionₗ volume ⊤ 2 φ) = reducedFunctional P φ := by
  have hv := value_ofTestFunctionₗ_ae φ
  rw [sobolevReducedFunctional_def, reducedFunctional_def,
    integral_norm_sq_gradient_ofTestFunctionₗ]
  congr 1
  · exact congrArg (_ + · / 16) (integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz]))
  · exact integral_congr_ae (hv.mono fun z hz ↦ by simp only [hz])

/-- Test functions lie in the finite-energy domain of Taubes's functional. -/
theorem ofTestFunctionₗ_mem_sobolevReducedFunctionalDomain (P : Polynomial ℂ)
    (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    W1p.ofTestFunctionₗ volume ⊤ 2 φ ∈ sobolevReducedFunctionalDomain P := by
  refine (integrable_mul_exp_sub_one_sub P φ.continuous φ.hasCompactSupport).congr ?_
  filter_upwards [value_ofTestFunctionₗ_ae φ] with z hz
  rw [hz]

/-! ### The potential term on bounded functions -/

/-- The integrand `h (exp (2t) - 1 - 2t)` of the potential term, with
`h = ‖P‖² / (1 + ‖P‖²)`. -/
private def potentialDensity (P : Polynomial ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * t) - 1 - 2 * t)

private theorem potentialDensity_zero (P : Polynomial ℂ) (z : ℂ) : potentialDensity P z 0 = 0 := by
  simp [potentialDensity]

private theorem potentialDensity_le (P : Polynomial ℂ) (z : ℂ) {s t : ℝ} (h : s ∈ uIcc 0 t) :
    potentialDensity P z s ≤ potentialDensity P z t :=
  mul_le_mul_of_nonneg_left (Real.exp_two_mul_sub_one_sub_two_mul_le_of_mem_uIcc h)
    (by positivity)

private theorem potentialDensity_nonneg (P : Polynomial ℂ) (z : ℂ) (t : ℝ) :
    0 ≤ potentialDensity P z t :=
  mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg t)

private theorem abs_potentialDensity_sub_le (P : Polynomial ℂ) (z : ℂ) {N a b : ℝ} (ha : |a| ≤ N)
    (hb : |b| ≤ N) : |potentialDensity P z a - potentialDensity P z b| ≤
      4 * Real.exp (2 * N) * (|a| + |b|) * |a - b| := by
  have h1 : ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [potentialDensity, potentialDensity, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans
    (Real.abs_exp_two_mul_sub_one_sub_two_mul_sub_le ha hb)

private theorem aestronglyMeasurable_potentialDensity (P : Polynomial ℂ) {μ : Measure ℂ}
    {f : ℂ → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun z ↦ potentialDensity P z (f z)) μ := by
  have hc : Continuous fun p : ℂ × ℝ ↦ potentialDensity P p.1 p.2 := by
    unfold potentialDensity
    fun_prop (disch := intro p; positivity)
  exact hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hf)

/-- A square-integrable function bounded by `N` has integrable potential. -/
private theorem integrable_potentialDensity (P : Polynomial ℂ) {f : ℂ → ℝ} {N : ℝ}
    (hf : MemLp f 2) (hN : ∀ᵐ z, |f z| ≤ N) :
    Integrable fun z ↦ potentialDensity P z (f z) := by
  refine Integrable.mono' (hf.integrable_sq.const_mul (4 * Real.exp (2 * N)))
    (aestronglyMeasurable_potentialDensity P hf.aestronglyMeasurable) ?_
  filter_upwards [hN] with z hz
  have h0 : |(0 : ℝ)| ≤ N := by simpa using (abs_nonneg _).trans hz
  have h := abs_potentialDensity_sub_le P z hz h0
  rw [potentialDensity_zero, sub_zero, abs_zero, add_zero, sub_zero] at h
  rw [Real.norm_eq_abs]
  calc |potentialDensity P z (f z)| ≤ 4 * Real.exp (2 * N) * |f z| * |f z| := h
    _ = 4 * Real.exp (2 * N) * f z ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `∫ (|f| + |g|)² ≤ 2 ∫ (f - g)² + 8 ∫ g²`. -/
private theorem integral_sq_abs_add_abs_le {f g : ℂ → ℝ} (hf : MemLp f 2) (hg : MemLp g 2) :
    ∫ z, (|f z| + |g z|) ^ 2 ≤ (2 * ∫ z, (f z - g z) ^ 2) + 8 * ∫ z, g z ^ 2 := by
  have i₁ : Integrable fun z ↦ 2 * (f z - g z) ^ 2 := (hf.sub hg).integrable_sq.const_mul 2
  have i₂ : Integrable fun z ↦ 8 * g z ^ 2 := hg.integrable_sq.const_mul 8
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i₁ i₂]
  refine integral_mono (hf.abs.add hg.abs).integrable_sq (i₁.add i₂) fun z ↦ ?_
  have h1 : |f z| ≤ |f z - g z| + |g z| := by simpa using abs_add_le (f z - g z) (g z)
  have h2 : (|f z| + |g z|) ^ 2 ≤ (|f z - g z| + 2 * |g z|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h3 := sq_abs (f z - g z)
  have h4 := sq_abs (g z)
  nlinarith [sq_nonneg (|f z - g z| - 2 * |g z|)]

/-- On functions bounded by `N`, the potential term is controlled by the `L²` distance:
`(V(f) - V(g))² ≤ K² (2e + 8 ∫ g²) e` with `e = ∫ (f - g)²` and `K = 4 exp (2N)`. -/
private theorem sq_integral_potentialDensity_sub_le (P : Polynomial ℂ) {f g : ℂ → ℝ} {N : ℝ}
    (hf : MemLp f 2) (hg : MemLp g 2) (hfN : ∀ᵐ z, |f z| ≤ N) (hgN : ∀ᵐ z, |g z| ≤ N) :
    ((∫ z, potentialDensity P z (f z)) - ∫ z, potentialDensity P z (g z)) ^ 2 ≤
      (4 * Real.exp (2 * N)) ^ 2 * ((2 * ∫ z, (f z - g z) ^ 2) + 8 * ∫ z, g z ^ 2) *
        ∫ z, (f z - g z) ^ 2 := by
  set K := 4 * Real.exp (2 * N)
  have hA : MemLp (fun z ↦ |f z| + |g z|) 2 := hf.abs.add hg.abs
  have hB : MemLp (fun z ↦ |f z - g z|) 2 := (hf.sub hg).abs
  have hdiff : |(∫ z, potentialDensity P z (f z)) - ∫ z, potentialDensity P z (g z)| ≤
      K * ∫ z, (|f z| + |g z|) * |f z - g z| := by
    rw [← integral_sub (integrable_potentialDensity P hf hfN)
      (integrable_potentialDensity P hg hgN), ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae ?_ ?_ ?_)
    · exact ((integrable_potentialDensity P hf hfN).sub (integrable_potentialDensity P hg hgN)).abs
    · exact (hA.integrable_mul hB).const_mul K
    · filter_upwards [hfN, hgN] with z hfz hgz
      exact (abs_potentialDensity_sub_le P z hfz hgz).trans_eq (by ring)
  -- Cauchy–Schwarz for `(|f| + |g|) |f - g|`.
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hA hB
  simp only [sq_abs] at hcs
  have he : 0 ≤ ∫ z, (f z - g z) ^ 2 := integral_nonneg fun z ↦ sq_nonneg _
  calc ((∫ z, potentialDensity P z (f z)) - ∫ z, potentialDensity P z (g z)) ^ 2
      ≤ (K * ∫ z, (|f z| + |g z|) * |f z - g z|) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    _ = K ^ 2 * (∫ z, (|f z| + |g z|) * |f z - g z|) ^ 2 := by ring
    _ ≤ K ^ 2 * ((2 * ∫ z, (f z - g z) ^ 2) + 8 * ∫ z, g z ^ 2) * ∫ z, (f z - g z) ^ 2 := by
        rw [mul_assoc]
        gcongr
        exact hcs.trans (mul_le_mul_of_nonneg_right (integral_sq_abs_add_abs_le hf hg) he)

/-- On functions bounded by a fixed `N`, the potential term is continuous for convergence
in `L²`. -/
private theorem tendsto_integral_potentialDensity (P : Polynomial ℂ) {f : ℕ → ℂ → ℝ}
    {g : ℂ → ℝ} {N : ℝ} (hf : ∀ k, MemLp (f k) 2) (hg : MemLp g 2)
    (hfN : ∀ k, ∀ᵐ z, |f k z| ≤ N) (hgN : ∀ᵐ z, |g z| ≤ N)
    (hlim : Tendsto (fun k ↦ ∫ z, (f k z - g z) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫ z, potentialDensity P z (f k z)) atTop
      (𝓝 (∫ z, potentialDensity P z (g z))) := by
  have hzero : Tendsto (fun k ↦ (4 * Real.exp (2 * N)) ^ 2 *
      ((2 * ∫ z, (f k z - g z) ^ 2) + 8 * ∫ z, g z ^ 2) * ∫ z, (f k z - g z) ^ 2) atTop
      (𝓝 0) := by
    simpa using (((hlim.const_mul 2).add_const _).const_mul _).mul hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
    ((Real.continuous_sqrt.tendsto 0).comp hzero |>.trans (by rw [Real.sqrt_zero]))
  rw [Real.norm_eq_abs, Function.comp_apply]
  exact Real.abs_le_sqrt (sq_integral_potentialDensity_sub_le P (hf k) hg (hfN k) hgN)

/-! ### Approximation by test functions -/

/-- The whole-plane restriction of Lebesgue measure is an additive Haar measure. -/
local instance : ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)).IsAddHaarMeasure := by
  rw [volume_restrict_top]
  infer_instance

private theorem ae_of_ae_restrict_top {p : ℂ → Prop}
    (h : ∀ᵐ z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ), p z) : ∀ᵐ z, p z := by
  rwa [volume_restrict_top] at h

private theorem ae_restrict_top_of_ae {p : ℂ → Prop} (h : ∀ᵐ z, p z) :
    ∀ᵐ z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ), p z := by
  rwa [volume_restrict_top]

private theorem integral_restrict_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) : ∫ z, f z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ) = ∫ z, f z := by
  rw [volume_restrict_top]

private theorem integrable_restrict_top {f : ℂ → ℝ} (h : Integrable f) :
    Integrable f ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) := by
  rwa [volume_restrict_top]

private theorem integrable_of_integrable_restrict_top {f : ℂ → ℝ}
    (h : Integrable f ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))) :
    Integrable f := by
  rwa [volume_restrict_top] at h

private theorem memLp_value (u : W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (W1p.value u) 2 volume := by
  simpa only [volume_restrict_top] using Lp.memLp (W1p.value u)

private theorem integral_sq_value_sub (u w : W1p (volume : Measure ℂ) ⊤ 2) :
    ∫ z, (W1p.value u z - W1p.value w z) ^ 2 = ‖W1p.value u - W1p.value w‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq, integral_restrict_top]
  refine integral_congr_ae ?_
  filter_upwards [ae_of_ae_restrict_top (Lp.coeFn_sub (W1p.value u) (W1p.value w))] with z hz
  rw [hz, Pi.sub_apply, Real.norm_eq_abs, sq_abs]

/-- Truncation of `t` at the levels `± N`, written with positive parts. -/
private theorem abs_le_and_of_eq_truncate {N t c : ℝ} (hN : 0 ≤ N)
    (hc : c = t - max (t - N) 0 + max (-t - N) 0) :
    |c| ≤ N ∧ c ∈ uIcc 0 t := by
  subst hc
  rw [mem_uIcc]
  rcases le_total t N with h₁ | h₁ <;> rcases le_total (-N) t with h₂ | h₂
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), abs_le]
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rcases le_total 0 t with h | h
    · exact .inl ⟨by linarith, by linarith⟩
    · exact .inr ⟨by linarith, by linarith⟩
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_le]
    exact ⟨⟨by linarith, by linarith⟩, .inr ⟨by linarith, by linarith⟩⟩
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_le]
    exact ⟨⟨by linarith, by linarith⟩, .inl ⟨by linarith, by linarith⟩⟩
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), abs_le]
    exact ⟨⟨by linarith, by linarith⟩, .inl ⟨by linarith, by linarith⟩⟩

/-- Multiplying by `a ∈ [0, 1]` keeps a value between `0` and `t`. -/
private theorem mul_mem_uIcc_zero {a c t : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (h : c ∈ uIcc 0 t) :
    a * c ∈ uIcc 0 t := by
  rw [mem_uIcc] at h ⊢
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .inl ⟨mul_nonneg ha₀ h₁, by nlinarith⟩
  · exact .inr ⟨by nlinarith, mul_nonpos_of_nonneg_of_nonpos ha₀ h₂⟩

/-- **Truncation.** A Sobolev function is approximated by Sobolev functions bounded by some `N`
whose values lie between `0` and its own. -/
private theorem exists_truncation_near (v : W1p (volume : Measure ℂ) ⊤ 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℝ) (w : W1p (volume : Measure ℂ) ⊤ 2), ‖w - v‖ < δ ∧
      ∀ᵐ z, |W1p.value w z| ≤ N ∧ W1p.value w z ∈ uIcc 0 (W1p.value v z) := by
  have hp : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  -- `v - (v - N)⁺ + (-v - N)⁺` truncates `v` at the levels `± N`.
  set T : ℕ → W1p (volume : Measure ℂ) ⊤ 2 := fun N ↦
    v - W1p.posPartAbove hp N.cast_nonneg v + W1p.posPartAbove hp N.cast_nonneg (-v)
  have hT : Tendsto T atTop (𝓝 v) := by
    have h₁ := W1p.tendsto_posPartAbove_atTop hp (fun N : ℕ ↦ N.cast_nonneg)
      tendsto_natCast_atTop_atTop v
    have h₂ := W1p.tendsto_posPartAbove_atTop hp (fun N : ℕ ↦ N.cast_nonneg)
      tendsto_natCast_atTop_atTop (-v)
    simpa using (tendsto_const_nhds.sub h₁).add h₂
  obtain ⟨N, hN⟩ := (hT.eventually (Metric.ball_mem_nhds v hδ)).exists
  refine ⟨N, T N, by rwa [← dist_eq_norm], ?_⟩
  filter_upwards [ae_of_ae_restrict_top (W1p.value_add_ae
      (v - W1p.posPartAbove hp N.cast_nonneg v) (W1p.posPartAbove hp N.cast_nonneg (-v))),
    ae_of_ae_restrict_top (W1p.value_sub_ae v (W1p.posPartAbove hp N.cast_nonneg v)),
    ae_of_ae_restrict_top (W1p.value_posPartAbove_ae hp N.cast_nonneg v),
    ae_of_ae_restrict_top (W1p.value_posPartAbove_ae hp N.cast_nonneg (-v)),
    ae_of_ae_restrict_top (W1p.value_neg_ae v)] with z h₁ h₂ h₃ h₄ h₅
  refine abs_le_and_of_eq_truncate N.cast_nonneg ?_
  rw [h₁, Pi.add_apply, h₂, Pi.sub_apply, h₃, h₄, h₅, Pi.neg_apply]

/-- **Cutoff.** A Sobolev function `w` bounded by `N` with values between `0` and those of `v`
is approximated by Sobolev functions with the same two properties whose jets vanish outside
compact sets. -/
private theorem exists_cutoff_near {v w : W1p (volume : Measure ℂ) ⊤ 2} {N : ℝ}
    (hw : ∀ᵐ z, |W1p.value w z| ≤ N ∧ W1p.value w z ∈ uIcc 0 (W1p.value v z)) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ u : W1p (volume : Measure ℂ) ⊤ 2, ‖u - w‖ < δ ∧
      (∀ᵐ z, |W1p.value u z| ≤ N ∧ W1p.value u z ∈ uIcc 0 (W1p.value v z)) ∧
      ∃ K, IsCompact K ∧ ∀ᵐ z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ), z ∉ K →
        (u : Sobolev1JetLp (volume : Measure ℂ) ⊤ 2) z = 0 := by
  obtain ⟨ψ, ws, hws, hψ⟩ := W1p.exists_seq_smul_tendsto ENNReal.ofNat_ne_top w
  obtain ⟨n, hn⟩ := (hws.eventually (Metric.ball_mem_nhds w hδ)).exists
  obtain ⟨-, hψ01, hψv, K, hK, hKz⟩ := hψ n
  refine ⟨ws n, by rwa [← dist_eq_norm], ?_, K, hK, hKz⟩
  filter_upwards [hw, ae_of_ae_restrict_top hψv] with z hz hψz
  rw [hψz]
  refine ⟨?_, mul_mem_uIcc_zero (hψ01 z).1 (hψ01 z).2 hz.2⟩
  rw [abs_mul, abs_of_nonneg (hψ01 z).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hψ01 z).2).trans hz.1

/-- **Mollification.** A Sobolev function bounded by `N` whose jet vanishes outside a compact set
is a limit of test functions whose potentials converge to its own. -/
private theorem exists_mollification_near (P : Polynomial ℂ) {u : W1p (volume : Measure ℂ) ⊤ 2}
    {N : ℝ} (huN : ∀ᵐ z, |W1p.value u z| ≤ N) {K : Set ℂ} (hK : IsCompact K)
    (hKz : ∀ᵐ z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ), z ∉ K →
      (u : Sobolev1JetLp (volume : Measure ℂ) ⊤ 2) z = 0) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ φ : 𝓓((⊤ : Opens ℂ), ℝ), ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ - u‖ < δ ∧
      ∫ z, potentialDensity P z (W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z) <
        (∫ z, potentialDensity P z (W1p.value u z)) + η := by
  have hp : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  let φk : ℕ → ContDiffBump (0 : ℂ) := fun k ↦
    ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hφk : Tendsto (fun k ↦ (φk k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set m : ℕ → W1p (volume : Measure ℂ) ⊤ 2 := fun k ↦ W1p.normedBumpL hp (φk k) u
  have hm : Tendsto m atTop (𝓝 u) := W1p.tendsto_normedBumpL hp hφk u
  -- Mollification preserves the bound `N`, so the potentials converge.
  have hmN (k : ℕ) : ∀ᵐ z, |W1p.value (m k) z| ≤ N := by
    have huN' : ∀ᵐ z ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ),
        ‖W1p.value u z‖ ≤ N :=
      ae_restrict_top_of_ae huN
    simpa only [m, W1p.value_normedBumpL, Real.norm_eq_abs] using
      ae_of_ae_restrict_top (ae_norm_normedBumpLp_le hp (φk k) huN')
  have hmV : Tendsto (fun k ↦ ∫ z, potentialDensity P z (W1p.value (m k) z)) atTop
      (𝓝 (∫ z, potentialDensity P z (W1p.value u z))) := by
    refine tendsto_integral_potentialDensity P (fun k ↦ memLp_value _) (memLp_value _) hmN huN ?_
    have hval : Tendsto (fun k ↦ ‖W1p.value (m k) - W1p.value u‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (by
        simpa only [Function.comp_def, W1p.valueL_apply] using
          (W1p.valueL.continuous.tendsto u).comp hm)
    simpa only [integral_sq_value_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] using hval.pow 2
  obtain ⟨k, hk₁, hk₂⟩ := ((hm.eventually (Metric.ball_mem_nhds u hδ)).and
    (hmV.eventually (gt_mem_nhds (lt_add_of_pos_right _ hη)))).exists
  obtain ⟨Φ, hΦ⟩ := W1p.normedBumpL_mem_range_of_ae_eq_zero hp (φk k) hK hKz
  refine ⟨Φ, ?_, ?_⟩ <;> rw [hΦ]
  · rwa [← dist_eq_norm]
  · exact hk₂

/-- **Approximation from above by test functions.** A Sobolev function with integrable potential
is a limit of test functions whose potentials are at most its own, up to an arbitrarily small
error. The approximations truncate at a height `N`, multiply by a cutoff and mollify. -/
private theorem exists_ofTestFunctionₗ_near (P : Polynomial ℂ) {v : W1p (volume : Measure ℂ) ⊤ 2}
    (hv : Integrable fun z ↦ potentialDensity P z (W1p.value v z)) {δ η : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) :
    ∃ φ : 𝓓((⊤ : Opens ℂ), ℝ), ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ - v‖ < δ ∧
      ∫ z, potentialDensity P z (W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z) <
        (∫ z, potentialDensity P z (W1p.value v z)) + η := by
  obtain ⟨N, w, hw, hwv⟩ := exists_truncation_near v (by positivity : 0 < δ / 3)
  obtain ⟨u, hu, huv, K, hK, hKz⟩ := exists_cutoff_near hwv (by positivity : 0 < δ / 3)
  obtain ⟨φ, hφ, hφV⟩ := exists_mollification_near P (huv.mono fun z hz ↦ hz.1) hK hKz
    (by positivity : 0 < δ / 3) hη
  refine ⟨φ, ?_, hφV.trans_le (add_le_add_left ?_ η)⟩
  · calc ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ - v‖
        = ‖(W1p.ofTestFunctionₗ volume ⊤ 2 φ - u) + (u - w) + (w - v)‖ := by abel_nf
      _ ≤ ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ - u‖ + ‖u - w‖ + ‖w - v‖ := norm_add₃_le
      _ < δ / 3 + δ / 3 + δ / 3 := by gcongr
      _ = δ := by ring
  · exact integral_mono_ae (integrable_potentialDensity P (memLp_value _)
      (huv.mono fun z hz ↦ hz.1)) hv (huv.mono fun z hz ↦ potentialDensity_le P z hz.2)

/-! ### The quadratic and linear terms -/

/-- The coefficient `2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` of the linear term. -/
private def linearCoeff (P : Polynomial ℂ) (z : ℂ) : ℝ :=
  2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8

private theorem memLp_linearCoeff {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    MemLp (linearCoeff P) 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) := by
  have h1 := (P.memLp_norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq).const_mul 2
  have h2 := (Polynomial.memLp_inv_one_add_norm_eval_sq hm).const_mul (1 / 8 : ℝ)
  rw [volume_restrict_top]
  convert h1.sub h2 using 1
  funext z
  simp only [linearCoeff, Pi.sub_apply]
  ring

/-- The linear term `u ↦ ∫ c u` of Taubes's functional, as a continuous linear functional on
`H¹(ℂ)`. -/
private def linearTerm {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    W1p (volume : Measure ℂ) ⊤ 2 →L[ℝ] ℝ :=
  (innerSL ℝ ((memLp_linearCoeff hm).toLp (linearCoeff P))).comp W1p.valueL

private theorem linearTerm_apply {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    linearTerm hm u = ∫ z, linearCoeff P z * W1p.value u z := by
  rw [linearTerm, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def,
    integral_restrict_top]
  refine integral_congr_ae ?_
  filter_upwards [ae_of_ae_restrict_top (memLp_linearCoeff hm).coeFn_toLp] with z hz
  rw [hz, W1p.valueL_apply, RCLike.inner_apply', conj_trivial]

private theorem sobolevReducedFunctional_eq {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u = ‖W1p.gradient u‖ ^ 2 / 2 +
      (∫ z, potentialDensity P z (W1p.value u z)) / 16 + linearTerm hm u := by
  rw [linearTerm_apply, ← Lp.integral_norm_sq_eq_norm_sq, integral_restrict_top,
    sobolevReducedFunctional_def]
  simp only [potentialDensity, linearCoeff]

/-! ### Test functions approximate the functional from above -/

/-- **Test functions approximate Taubes's functional from above.** For a polynomial of positive
degree and every Sobolev function `v` of finite energy, there are test functions `φ` with
`reducedFunctional P φ < sobolevReducedFunctional P v + ε`, for every `ε > 0`. So the infimum of
the functional over the finite-energy domain is its infimum over test functions. -/
theorem exists_reducedFunctional_lt {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    {v : W1p (volume : Measure ℂ) ⊤ 2} (hv : v ∈ sobolevReducedFunctionalDomain P) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : 𝓓((⊤ : Opens ℂ), ℝ), reducedFunctional P φ < sobolevReducedFunctional P v + ε := by
  set F : W1p (volume : Measure ℂ) ⊤ 2 → ℝ := fun u ↦ ‖W1p.gradient u‖ ^ 2 / 2 + linearTerm hm u
  have hF : Continuous F := by
    simp only [F, ← W1p.gradientL_apply]
    fun_prop
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuous_iff.mp hF v (ε / 2) (by positivity)
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_ofTestFunctionₗ_near P hv hδ (by positivity : 0 < 8 * ε)
  refine ⟨φ, ?_⟩
  have hclose := hδF _ (by rwa [dist_eq_norm])
  rw [Real.dist_eq, abs_lt] at hclose
  rw [← sobolevReducedFunctional_ofTestFunctionₗ, sobolevReducedFunctional_eq hm,
    sobolevReducedFunctional_eq hm]
  simp only [F] at hclose
  linarith

/-! ### Existence of a minimizer -/

/-- `H¹(ℂ)` is reflexive, as a closed subspace of an `L²` space of jets. -/
private theorem surjective_inclusionInDoubleDual_w1p :
    Function.Surjective
      (NormedSpace.inclusionInDoubleDual ℝ (W1p (volume : Measure ℂ) ⊤ 2)) :=
  Submodule.surjective_inclusionInDoubleDual _ (w1pSubmodule volume ⊤ 2).isClosed
    (MeasureTheory.Lp.surjective_inclusionInDoubleDual (by norm_num) (by norm_num))

private theorem norm_sq_ofTestFunctionₗ (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ‖ ^ 2 = (∫ z, φ z ^ 2) + ∫ z, ‖fderiv ℝ φ z‖ ^ 2 := by
  have hv : ∫ z, ‖W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 φ) z‖ ^ 2 = ∫ z, φ z ^ 2 :=
    integral_congr_ae ((value_ofTestFunctionₗ_ae φ).mono fun z hz ↦ by
      simp only [hz, Real.norm_eq_abs, sq_abs])
  rw [← Submodule.norm_coe, Sobolev1JetLp.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    ← W1p.value_coe, ← W1p.gradient_coe, ← Lp.integral_norm_sq_eq_norm_sq,
    ← Lp.integral_norm_sq_eq_norm_sq, integral_restrict_top, integral_restrict_top,
    integral_norm_sq_gradient_ofTestFunctionₗ, hv]

/-- The Dirichlet and potential part `∫ ‖∇u‖² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u)` of
Taubes's functional, as an extended nonnegative function on `H¹(ℂ)` with its weak topology. -/
private def weakEnergy (P : Polynomial ℂ) (x : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)) :
    ℝ≥0∞ :=
  (∫⁻ z, ENNReal.ofReal (‖(toWeakSpace ℝ (Lp ℂ 2 ((volume : Measure ℂ).restrict
      ((⊤ : Opens ℂ) : Set ℂ)))).symm (WeakSpace.map W1p.gradientL x) z‖ ^ 2)
    ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) / 2 +
  (∫⁻ z, ENNReal.ofReal (potentialDensity P z ((toWeakSpace ℝ (Lp ℝ 2 ((volume : Measure ℂ).restrict
      ((⊤ : Opens ℂ) : Set ℂ)))).symm (WeakSpace.map W1p.valueL x) z))
    ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) / 16

/-- The Dirichlet and potential terms are weakly lower semicontinuous on `H¹(ℂ)`. -/
private theorem lowerSemicontinuous_weakEnergy (P : Polynomial ℂ) :
    LowerSemicontinuous (weakEnergy P) := by
  have hconv : ConvexOn ℝ univ fun y : ℂ ↦ ‖y‖ ^ 2 :=
    (convexOn_norm convex_univ).pow (fun x _ ↦ norm_nonneg x) 2
  have hG₁ := lowerSemicontinuous_lintegral_ofReal_comp_toWeakSpace_symm (p := 2)
    (μ := (volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))
    Measure.AbsolutelyContinuous.rfl (by fun_prop : Continuous fun y : ℂ ↦ ‖y‖ ^ 2) hconv
  have hG₂ := lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P
    ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))
  exact ((ENNReal.continuous_div_const 2 two_ne_zero).comp_lowerSemicontinuous
    (hG₁.comp (WeakSpace.map W1p.gradientL).continuous)
    fun _ _ h ↦ ENNReal.div_le_div_right h 2).add
    ((ENNReal.continuous_div_const 16 (by norm_num)).comp_lowerSemicontinuous
      (hG₂.comp (WeakSpace.map W1p.valueL).continuous)
      fun _ _ h ↦ ENNReal.div_le_div_right h 16)

private theorem weakEnergy_toWeakSpace (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    weakEnergy P (toWeakSpace ℝ _ u) =
      (∫⁻ z, ENNReal.ofReal (‖W1p.gradient u z‖ ^ 2)
        ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) / 2 +
      (∫⁻ z, ENNReal.ofReal (potentialDensity P z (W1p.value u z))
        ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) / 16 := by
  have h₁ : (toWeakSpace ℝ (Lp ℂ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)))).symm
      (WeakSpace.map W1p.gradientL (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) u)) =
        W1p.gradient u :=
    W1p.gradientL_apply u
  have h₂ : (toWeakSpace ℝ (Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)))).symm
      (WeakSpace.map W1p.valueL (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) u)) =
        W1p.value u :=
    W1p.valueL_apply u
  rw [weakEnergy, h₁, h₂]

/-- On the finite-energy domain, `weakEnergy` is the Dirichlet and potential part of Taubes's
functional. -/
private theorem weakEnergy_toWeakSpace_of_mem (P : Polynomial ℂ)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : u ∈ sobolevReducedFunctionalDomain P) :
    weakEnergy P (toWeakSpace ℝ _ u) = ENNReal.ofReal (‖W1p.gradient u‖ ^ 2 / 2 +
      (∫ z, potentialDensity P z (W1p.value u z)) / 16) := by
  have hgi : Integrable (fun z ↦ ‖W1p.gradient u z‖ ^ 2)
      ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hpi : Integrable (fun z ↦ potentialDensity P z (W1p.value u z))
      ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) :=
    integrable_restrict_top hu
  rw [weakEnergy_toWeakSpace,
    ← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun z ↦ by positivity),
    ← ofReal_integral_eq_lintegral_ofReal hpi
      (Eventually.of_forall fun z ↦ potentialDensity_nonneg P z _),
    Lp.integral_norm_sq_eq_norm_sq, integral_restrict_top, ENNReal.ofReal_add (by positivity)
      (div_nonneg (integral_nonneg fun z ↦ potentialDensity_nonneg P z _) (by norm_num)),
    ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]

/-- A Sobolev function of finite `weakEnergy` lies in the finite-energy domain. -/
private theorem mem_sobolevReducedFunctionalDomain_of_weakEnergy_ne_top (P : Polynomial ℂ)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (h : weakEnergy P (toWeakSpace ℝ _ u) ≠ ⊤) :
    u ∈ sobolevReducedFunctionalDomain P := by
  rw [weakEnergy_toWeakSpace] at h
  have hfin : (∫⁻ z, ENNReal.ofReal (potentialDensity P z (W1p.value u z))
      ∂(volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) ≠ ⊤ := fun htop ↦
    h (by rw [htop, ENNReal.top_div_of_ne_top (by norm_num), add_top])
  have hint : Integrable (fun z ↦ potentialDensity P z (W1p.value u z))
      ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)) :=
    ⟨aestronglyMeasurable_potentialDensity P (Lp.aestronglyMeasurable _),
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z ↦
        potentialDensity_nonneg P z _)).mpr hfin.lt_top⟩
  exact integrable_of_integrable_restrict_top hint

/-- The values of the classical functional on test functions are bounded below. -/
private theorem bddBelow_range_reducedFunctional {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    BddBelow (range fun φ : 𝓓((⊤ : Opens ℂ), ℝ) ↦ reducedFunctional P φ) := by
  obtain ⟨C₀, hC₀⟩ := exists_le_reducedFunctional hm
  exact ⟨C₀, by
    rintro _ ⟨φ, rfl⟩
    exact hC₀ φ (φ.contDiff.of_le (mod_cast le_top)) φ.hasCompactSupport⟩

/-- A minimizing sequence of test functions for the classical functional, bounded in `H¹(ℂ)`. -/
private theorem exists_seq_tendsto_sInf_reducedFunctional {P : Polynomial ℂ}
    (hm : 0 < P.natDegree) :
    ∃ (φ : ℕ → 𝓓((⊤ : Opens ℂ), ℝ)) (R : ℝ),
      Tendsto (fun n ↦ reducedFunctional P (φ n)) atTop
        (𝓝 (sInf (range fun φ : 𝓓((⊤ : Opens ℂ), ℝ) ↦ reducedFunctional P φ))) ∧
      ∀ n, W1p.ofTestFunctionₗ volume ⊤ 2 (φ n) ∈ Metric.closedBall 0 R := by
  obtain ⟨a, ha, hlim, hmem⟩ := exists_seq_tendsto_sInf (range_nonempty _)
    (bddBelow_range_reducedFunctional hm)
  choose φ hφ using hmem
  obtain ⟨C, hC⟩ := exists_integral_le_of_reducedFunctional_le hm (a 0)
  refine ⟨φ, √(2 * C), by simpa only [hφ] using hlim, fun n ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := hC (φ n) ((φ n).contDiff.of_le (mod_cast le_top)) (φ n).hasCompactSupport
    ((hφ n).trans_le (ha (Nat.zero_le n)))
  rw [mem_closedBall_zero_iff, ← abs_norm]
  exact Real.abs_le_sqrt (by rw [norm_sq_ofTestFunctionₗ]; linarith)

/-- **Existence of a minimizer of Taubes's functional.** For a polynomial `P` of positive degree,
Taubes's functional `I = sobolevReducedFunctional P` attains its minimum on its finite-energy
domain in `H¹(ℂ)`. The minimizer is a weak limit of a minimizing sequence of test functions: the
sequence is bounded by the coercivity estimate
`TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`, `H¹(ℂ)` is reflexive, the Dirichlet
and potential terms are weakly lower semicontinuous and the linear term is weakly continuous.
That no Sobolev function of finite energy does better than the test functions is
`TauCeti.Vortex.exists_reducedFunctional_lt`. -/
theorem exists_isMinOn_sobolevReducedFunctional {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    ∃ w ∈ sobolevReducedFunctionalDomain P,
      IsMinOn (sobolevReducedFunctional P) (sobolevReducedFunctionalDomain P) w := by
  set m := sInf (range fun φ : 𝓓((⊤ : Opens ℂ), ℝ) ↦ reducedFunctional P φ)
  -- No function of finite energy goes below the infimum `m` over test functions.
  have hmv (v : W1p (volume : Measure ℂ) ⊤ 2) (hv : v ∈ sobolevReducedFunctionalDomain P) :
      m ≤ sobolevReducedFunctional P v := le_of_forall_pos_le_add fun ε hε ↦ by
    obtain ⟨φ, hφ⟩ := exists_reducedFunctional_lt hm hv hε
    exact (csInf_le (bddBelow_range_reducedFunctional hm) ⟨φ, rfl⟩).trans hφ.le
  -- A bounded minimizing sequence has a weakly convergent subsequence.
  obtain ⟨φ, R, hlim, hbdd⟩ := exists_seq_tendsto_sInf_reducedFunctional hm
  set u : ℕ → W1p (volume : Measure ℂ) ⊤ 2 := fun n ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ n)
  have hK := isCompact_toWeakSpace_closedBall surjective_inclusionInDoubleDual_w1p 0 R
  obtain ⟨w, ns, hns, hw⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure (𝕜 := ℝ)
    (by rwa [hK.isClosed.closure_eq]) hbdd
  -- Along the sequence, the energy part is the functional minus the weakly continuous
  -- linear term.
  have hE (n : ℕ) : weakEnergy P (toWeakSpace ℝ _ (u n)) =
      ENNReal.ofReal (reducedFunctional P (φ n) - linearTerm hm (u n)) := by
    rw [weakEnergy_toWeakSpace_of_mem P (ofTestFunctionₗ_mem_sobolevReducedFunctionalDomain P
      (φ n)), ← sobolevReducedFunctional_ofTestFunctionₗ, sobolevReducedFunctional_eq hm,
      add_sub_cancel_right]
  have hL : Tendsto (fun k ↦ linearTerm hm (u (ns k))) atTop (𝓝 (linearTerm hm w)) :=
    ((WeakBilin.eval_continuous _ (linearTerm hm)).tendsto _).comp hw
  have hlim' := (hlim.comp hns.tendsto_atTop).sub hL
  have hmL : 0 ≤ m - linearTerm hm w := ge_of_tendsto' hlim' fun k ↦ by
    rw [Function.comp_apply, ← sobolevReducedFunctional_ofTestFunctionₗ,
      sobolevReducedFunctional_eq hm, add_sub_cancel_right]
    exact add_nonneg (by positivity)
      (div_nonneg (integral_nonneg fun z ↦ potentialDensity_nonneg P z _) (by norm_num))
  -- Lower semicontinuity bounds the energy part at the weak limit.
  have hGw (ε : ℝ) (hε : 0 < ε) :
      weakEnergy P (toWeakSpace ℝ _ w) ≤ ENNReal.ofReal (m - linearTerm hm w + ε) := by
    refine ((lowerSemicontinuous_weakEnergy P).isClosed_preimage _).mem_of_tendsto hw ?_
    filter_upwards [hlim'.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with k hk
    rw [mem_preimage, mem_Iic, hE]
    exact ENNReal.ofReal_le_ofReal hk.le
  have hwdom : w ∈ sobolevReducedFunctionalDomain P :=
    mem_sobolevReducedFunctionalDomain_of_weakEnergy_ne_top P
      ((hGw 1 one_pos).trans_lt ENNReal.ofReal_lt_top).ne
  have hwm : sobolevReducedFunctional P w ≤ m := le_of_forall_pos_le_add fun ε hε ↦ by
    have h := hGw ε hε
    have h₀ : 0 ≤ ‖W1p.gradient w‖ ^ 2 / 2 +
        (∫ z, potentialDensity P z (W1p.value w z)) / 16 := add_nonneg (by positivity)
      (div_nonneg (integral_nonneg fun z ↦ potentialDensity_nonneg P z _) (by norm_num))
    rw [weakEnergy_toWeakSpace_of_mem P hwdom, ENNReal.ofReal_le_ofReal_iff'] at h
    rw [sobolevReducedFunctional_eq hm]
    rcases h with h | h <;> linarith
  exact ⟨w, hwdom, isMinOn_iff.mpr fun v hv ↦ hwm.trans (hmv v hv)⟩

end TauCeti.Vortex
