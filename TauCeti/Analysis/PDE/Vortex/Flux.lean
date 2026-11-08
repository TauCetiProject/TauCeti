/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.PDE.Vortex.Decay
public import TauCeti.Analysis.PDE.Vortex.Divisor
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.Zeros
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.Calculus.ContDiff.Removable
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.Normed.Module.LocalFactorization
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# The flux of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`), so `|α|² = 4 (p² + q²)`. At a zero `z` of a
smooth vortex, `α` factors as `(w - z) ^ n v(w)` with `v(z) ≠ 0`
(`TauCeti.Vortex.exists_contDiffAt_sectionValue_eq_pow_mul`); the exponent `n` is the
multiplicity of the zero. Away from the zeros, `log |α|²` satisfies the scalar equation
`Δ log |α|² = (|α|² - 1) / 4` (`TauCeti.Vortex.laplacian_log_normSq_of_equation_eq_zero`).

Across the zeros the scalar equation holds in the sense of distributions, with point masses:

`Δ log |α|² = (|α|² - 1) / 4 + 4π ∑_z n_z δ_z`

(`TauCeti.Vortex.integral_laplacian_mul_log_normSq`). Indeed `log |α|²` differs from the `C²`
function `log |v|²` near `z` by `2 n_z log |w - z|`, and `log |w - z|` is `-2π` times the planar
Newtonian kernel `TauCeti.planarNewtonianKernel`, a fundamental solution of `-Δ`. Subtracting
these singular terms leaves a `C²` function (`TauCeti.exists_contDiff_eq_of_eventuallyEq_nhdsNE`)
to which Green's second identity applies.

Testing this identity against dilated cutoffs `χ_R`, the left side tends to zero because
`log |α|² → 0` at infinity while `∫ |Δ χ_R|` stays bounded. This gives the flux identity

`∫ (1 - |α|²) = 16π ∑_z n_z`

(`TauCeti.Vortex.integral_one_sub_normSq_eq_mul_finsum`). Since the curvature equation is
`∂₁ b₂ - ∂₂ b₁ = -(1 - |α|²) / 8` and `iF_a = -(∂₁ b₂ - ∂₂ b₁) ds ∧ dt`, the total flux
`(2π)⁻¹ ∫ iF_a` is the number of zeros of `α`, counted with multiplicity
(`TauCeti.Vortex.integral_curvature_eq_neg_mul_finsum`).

In terms of the zero divisor `D` of the section (`TauCeti.HasZeroDivisor (sectionValue x) D`),
the total multiplicity is the degree of `D`, so `(2π)⁻¹ ∫ iF_a = deg D`
(`TauCeti.Vortex.integral_curvature_eq_neg_mul_card`). If the section has the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, its zero divisor has degree `m`
(`TauCeti.Vortex.exists_sym_hasZeroDivisor_sectionValue`). Hence
`∫ (1 - |α|²) = 16π m` and the flux `(2π)⁻¹ ∫ iF_a` equals the framing degree `m`
(`TauCeti.Vortex.integral_curvature_eq_of_tendsto_sectionValue_mul_inv_pow`). For `s > 1` every
continuous field of the affine Sobolev space `A_m^s` has this end framing, so every `C²` vortex in
`A_m^s` has flux `m` (`TauCeti.Vortex.integral_curvature_eq_of_mem_framedFieldSpace`).

The multiplicities enter through any function `n` with the local factorization property. The
similarity principle supplies one, and it is unique (`TauCeti.eq_of_eventually_sub_pow_smul_eq`).
Smoothness `C²` of the connection is assumed so that the factor `v` is `C²`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory Set Topology InnerProductSpace Laplacian
open scoped Distributions ContDiff Real

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- A multiplicity function for the zeros of the section vanishes off the zeros. -/
private theorem eq_zero_of_sectionValue_ne_zero {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w)
    {z : ℂ} (hz : sectionValue x z ≠ 0) : n z = 0 := by
  obtain ⟨v, -, -, hfac⟩ := hn z
  by_contra h
  exact hz (by simpa [zero_pow h] using hfac.self_of_nhds)

/-- Near each point `z₀`, and off `z₀`, the function `log |α|² + 4π ∑ n_z G(· - z)` agrees with
a function `C²` at `z₀`: writing `α = (w - z₀) ^ n z₀ * v` with `v` of class `C²`, the singular
part `2 n_{z₀} log |w - z₀| = -4π n_{z₀} G(w - z₀)` of `log |α|²` cancels. -/
private theorem exists_contDiffAt_eventuallyEq_log_normSq_add
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (hfin : {z | sectionValue x z = 0}.Finite) {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w) (z₀ : ℂ) :
    ∃ g : ℂ → ℝ, ContDiffAt ℝ 2 g z₀ ∧
      (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) +
        4 * π * ∑ z ∈ hfin.toFinset, (n z : ℝ) * planarNewtonianKernel (w - z)) =ᶠ[𝓝[≠] z₀] g := by
  set S := hfin.toFinset
  have hne : ∃ w, sectionValue x w ≠ 0 := hfin.infinite_compl.nonempty
  obtain ⟨k, v, hv, hv₀, hfac⟩ := exists_contDiffAt_sectionValue_eq_pow_mul (k := 2) (by norm_num)
    hb₁ hb₂ (hp.differentiable (by norm_num)) (hq.differentiable (by norm_num))
    (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hne z₀
  obtain ⟨v', hv', hv'₀, hfac'⟩ := hn z₀
  have hk : n z₀ = k := eq_of_eventually_sub_pow_smul_eq hv' hv'₀ hv.continuousAt hv₀
    (hfac'.and hfac |>.mono fun w hw ↦ by simpa only [smul_eq_mul] using hw.1.symm.trans hw.2)
  refine ⟨fun w ↦ Real.log (‖v w‖ ^ 2) +
    4 * π * ∑ z ∈ S.erase z₀, (n z : ℝ) * planarNewtonianKernel (w - z), ?_, ?_⟩
  · exact ((hv.norm_sq ℝ).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv₀))).add
      (contDiffAt_const.mul (ContDiffAt.sum fun z hz ↦ contDiffAt_const.mul
        (contDiffAt_planarNewtonianKernel_sub (Finset.ne_of_mem_erase hz).symm)))
  -- Split off the term of the sum at `z₀`; it vanishes when `z₀` is not a zero.
  have hsplit : ∀ w, ∑ z ∈ S, (n z : ℝ) * planarNewtonianKernel (w - z) =
      (n z₀ : ℝ) * planarNewtonianKernel (w - z₀) +
        ∑ z ∈ S.erase z₀, (n z : ℝ) * planarNewtonianKernel (w - z) := by
    intro w
    by_cases h : z₀ ∈ S
    · exact (Finset.add_sum_erase S _ h).symm
    · rw [Finset.erase_eq_of_notMem h, eq_zero_of_sectionValue_ne_zero hn
        fun h' ↦ h ((Set.Finite.mem_toFinset hfin).mpr h')]
      simp
  filter_upwards [nhdsWithin_le_nhds hfac,
    nhdsWithin_le_nhds (hv.continuousAt.eventually_ne hv₀), self_mem_nhdsWithin]
    with w hw hvw hwz
  have hwz' : ‖w - z₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwz)
  have hlog : Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) =
      2 * k * Real.log ‖w - z₀‖ + Real.log (‖v w‖ ^ 2) := by
    rw [← sq_norm_sectionValue x w, hw]
    simp [norm_pow, Real.log_mul, Real.log_pow, hwz', hvw]
    ring
  rw [hsplit w, hlog, hk, planarNewtonianKernel_def]
  field_simp
  ring

/-- The regular part of `log |α|²`: adding `4π ∑ n_z G(· - z)`, for the planar Newtonian kernel
`G`, to `log |α|²` off the zeros gives a `C²` function whose Laplacian is `(|α|² - 1) / 4`. -/
private theorem exists_contDiff_laplacian_eq_log_normSq_add
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (hfin : {z | sectionValue x z = 0}.Finite) {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w) :
    ∃ g : ℂ → ℝ, ContDiff ℝ 2 g ∧ Δ g = (fun w ↦ (4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) / 4) ∧
      ∀ w, sectionValue x w ≠ 0 → g w = Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) +
        4 * π * ∑ z ∈ hfin.toFinset, (n z : ℝ) * planarNewtonianKernel (w - z) := by
  set L : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
  set K : ℂ → ℝ := fun w ↦ ∑ z ∈ hfin.toFinset, (n z : ℝ) * planarNewtonianKernel (w - z)
  have hs : ContDiff ℝ 2 (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) := contDiff_normSq hp hq
  have hsne : ∀ {w}, sectionValue x w ≠ 0 → 4 * (x w 2 ^ 2 + x w 3 ^ 2) ≠ 0 := fun hw ↦
    mul_ne_zero four_ne_zero (mt (sectionValue_eq_zero_iff x _).mpr hw)
  -- Off the zeros every kernel term is harmonic.
  have hKh : ∀ w, sectionValue x w ≠ 0 → HarmonicAt (fun y ↦ 4 * π * K y) w := fun w hw ↦
    (HarmonicAt.sum _ (f := fun z y ↦ (n z : ℝ) * planarNewtonianKernel (y - z))
      fun z hz ↦ (harmonicAt_planarNewtonianKernel_sub fun h ↦ hw <| by
        rw [h]; exact (Set.Finite.mem_toFinset hfin).mp hz).const_smul
          (c := (n z : ℝ))).const_smul (c := 4 * π)
  have huc : ∀ w, sectionValue x w ≠ 0 → ContDiffAt ℝ 2 (fun y ↦ L y + 4 * π * K y) w :=
    fun w hw ↦ (hs.contDiffAt.log (hsne hw)).add (hKh w hw).1
  obtain ⟨g, hg, hgu⟩ := exists_contDiff_eq_of_eventuallyEq_nhdsNE
    (exists_contDiffAt_eventuallyEq_log_normSq_add hb₁ hb₂ hp hq hsol hfin hn)
  have hgu' : ∀ w, sectionValue x w ≠ 0 → g =ᶠ[𝓝 w] fun y ↦ L y + 4 * π * K y :=
    fun w hw ↦ Filter.eventually_of_mem (hfin.isClosed.isOpen_compl.mem_nhds hw)
      fun w' hw' ↦ hgu w' (huc w' hw').continuousAt
  -- The Laplacian of `g` is `(|α|² - 1) / 4` everywhere: off the zeros by the scalar equation,
  -- since the kernel terms are harmonic there, and at the zeros by continuity.
  have hΔ : Δ g = fun w ↦ (4 * (x w 2 ^ 2 + x w 3 ^ 2) - 1) / 4 := by
    refine Continuous.ext_on (Set.Countable.dense_compl ℝ hfin.countable) hg.continuous_laplacian
      ((hs.continuous.sub continuous_const).div_const 4) fun w hw ↦ ?_
    have hw' : sectionValue x w ≠ 0 := hw
    have hα : x w 2 ^ 2 + x w 3 ^ 2 ≠ 0 := fun h ↦ hsne hw' (by rw [h, mul_zero])
    rw [(laplacian_congr_nhds (hgu' w hw')).eq_of_nhds]
    -- Write `L + 4π K` as a sum of functions to apply additivity of the Laplacian.
    change Δ (L + fun y ↦ 4 * π * K y) w = _
    rw [ContDiffAt.laplacian_add (hs.contDiffAt.log (hsne hw')) (hKh w hw').1,
      laplacian_log_normSq_of_equation_eq_zero ((hb₁.differentiable (by norm_num)) w)
        ((hb₂.differentiable (by norm_num)) w) hp.contDiffAt hq.contDiffAt hα
        (Eventually.of_forall hsol), (hKh w hw').2.self_of_nhds, Pi.zero_apply, add_zero]
  exact ⟨g, hg, hΔ, fun w hw ↦ hgu w (huc w hw).continuousAt⟩

/-- **The distributional scalar equation of a plane vortex.** Let `x` be a `C²` vortex whose
section `α` has finitely many zeros, and let `n z` be the multiplicity of the zero `z`, in the
sense that `α(w) = (w - z) ^ n z * v(w)` near `z` with `v` continuous and nonzero at `z`. Then
`Δ log |α|² = (|α|² - 1) / 4 + 4π ∑ n_z δ_z` as distributions: for every test function `φ`,
`∫ Δφ log |α|² = ∫ φ (|α|² - 1) / 4 + 4π ∑ᶠ z, n_z φ(z)`. -/
theorem integral_laplacian_mul_log_normSq
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (hfin : {z | sectionValue x z = 0}.Finite) {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℂ), ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) =
      (∫ z, φ z * ((4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4)) +
        4 * π * ∑ᶠ z, (n z : ℝ) * φ z := by
  obtain ⟨g, hg, hΔ, hgu⟩ :=
    exists_contDiff_laplacian_eq_log_normSq_add hb₁ hb₂ hp hq hsol hfin hn
  set S := hfin.toFinset
  set K : ℂ → ℝ := fun w ↦ ∑ z ∈ S, (n z : ℝ) * planarNewtonianKernel (w - z) with hK
  -- Integrate against `Δφ`.
  set Φ : ℂ → ℝ := Δ (φ : ℂ → ℝ)
  have hΦc : Continuous Φ := (φ.contDiff.of_le (by simp)).continuous_laplacian
  have hΦs : HasCompactSupport Φ :=
    φ.hasCompactSupport.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _))
  have hint₁ : Integrable (fun z ↦ Φ z * g z) :=
    (hΦc.mul hg.continuous).integrable_of_hasCompactSupport hΦs.mul_right
  have hintG : ∀ y, Integrable (fun z ↦ Φ z * planarNewtonianKernel (z - y)) := fun y ↦ by
    have hc : Continuous fun z ↦ Φ (z + y) := hΦc.comp (continuous_id.add continuous_const)
    have hcs : HasCompactSupport fun z ↦ Φ (z + y) := hΦs.comp_homeomorph (Homeomorph.addRight y)
    have := (locallyIntegrable_planarNewtonianKernel.integrable_smul_left_of_hasCompactSupport
      hc hcs).comp_sub_right y
    simpa only [smul_eq_mul, sub_add_cancel] using this
  have hΦK : ∀ z, Φ z * K z = ∑ y ∈ S, (n y : ℝ) * (Φ z * planarNewtonianKernel (z - y)) :=
    fun z ↦ by
      rw [hK, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ ↦ by ring
  have hintK : Integrable (fun z ↦ Φ z * K z) := by
    simp_rw [hΦK]
    exact integrable_finsetSum _ fun y _ ↦ (hintG y).const_mul _
  have hLae : (fun z ↦ Φ z * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2))) =ᵐ[volume]
      fun z ↦ Φ z * g z - 4 * π * (Φ z * K z) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfin.measure_zero volume)] with z hz
    rw [hgu z hz]
    ring
  have hGreen :
      ∫ z, Φ z * g z = ∫ z, φ z * ((4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4) := by
    have := hg.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume) φ
    simpa only [smul_eq_mul, hΔ] using this
  have hKint : ∫ z, Φ z * K z = -∑ y ∈ S, (n y : ℝ) * φ y := by
    simp_rw [hΦK]
    rw [integral_finsetSum _ fun y _ ↦ (hintG y).const_mul _, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [integral_const_mul, integral_laplacian_mul_planarNewtonianKernel_sub
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport y, mul_neg]
  have hsum : ∑ᶠ z, (n z : ℝ) * φ z = ∑ y ∈ S, (n y : ℝ) * φ y := by
    refine finsum_eq_sum_of_support_subset _ fun z hz ↦ ?_
    have hnz : n z ≠ 0 := fun h ↦ hz (by simp [h])
    exact (Set.Finite.mem_toFinset hfin).mpr
      (by_contra fun h ↦ hnz (eq_zero_of_sectionValue_ne_zero hn h))
  rw [integral_congr_ae hLae, integral_sub hint₁ (hintK.const_mul _), integral_const_mul, hGreen,
    hKint, hsum]
  ring

/-- The distributional identity for `Δ log |α|²`, tested against a smooth compactly supported
cutoff `χ` that equals `1` at every zero of `α`:
`∫ Δχ log |α|² = ∫ χ (|α|² - 1) / 4 + 4π ∑ᶠ z, n z`. -/
theorem integral_laplacian_mul_log_normSq_of_eq_one
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (hfin : {z | sectionValue x z = 0}.Finite) {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ z, sectionValue x z = 0 → χ z = 1) :
    ∫ z, Δ χ z * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) =
      (∫ z, χ z * ((4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4)) + 4 * π * ∑ᶠ z, (n z : ℝ) := by
  have h := integral_laplacian_mul_log_normSq hb₁ hb₂ hp hq hsol hfin hn
    ⟨χ, hχ, hχc, subset_univ _⟩
  simp only [TestFunction.coe_mk] at h
  rw [h]
  congr 2
  refine finsum_congr fun z ↦ ?_
  by_cases hz : sectionValue x z = 0
  · rw [hχ1 z hz, mul_one]
  · simp [eq_zero_of_sectionValue_ne_zero hn hz]

/-- **The flux identity for a plane vortex.** Let `x` be a `C²` vortex on the whole plane whose
section satisfies `|α| → 1` at infinity, and let `n z` be the multiplicity of the zero `z` of
`α`, in the sense that `α(w) = (w - z) ^ n z * v(w)` near `z` with `v` continuous and nonzero at
`z`. Then `∫ (1 - |α|²) = 16π ∑ᶠ z, n z`. -/
theorem integral_one_sub_normSq_eq_mul_finsum
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w) :
    ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) = 16 * π * ∑ᶠ z, (n z : ℝ) := by
  -- Test the distributional scalar equation against dilated cutoffs `χ_m`. The left side tends
  -- to `0` and the right side to `∫ (|α|² - 1) / 4 + 4π ∑ n_z`.
  have hfin : {z | sectionValue x z = 0}.Finite :=
    finite_setOfPred_sectionValue_eq_zero (k := 2) (by norm_num) hb₁ hb₂
      (hp.differentiable (by norm_num)) (hq.differentiable (by norm_num))
      (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hlim
  set N := ∑ᶠ z, (n z : ℝ)
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2) with hs
  set F : ℂ → ℝ := fun z ↦ (s z - 1) / 4 with hF
  have hFint : Integrable F := by
    refine ((integrable_one_sub_normSq volume (hb₁.differentiable (by norm_num))
      (hb₂.differentiable (by norm_num)) hp hq hsol hlim).div_const 4).neg.congr
      (.of_forall fun z ↦ ?_)
    simp only [hF, hs, Pi.neg_apply]
    ring
  -- Dilated cutoffs `χ_m`, equal to `1` on a disc of radius `R m` containing every zero.
  obtain ⟨C, hC⟩ := exists_forall_contDiff_cutoff_ball_norm_laplacian_le (E := ℂ)
  obtain ⟨R₀, hR₀⟩ := hfin.isBounded.subset_closedBall 0
  set R : ℕ → ℝ := fun m ↦ m + (max R₀ 0 + 1) with hR
  have hRpos : ∀ m, 0 < R m := fun m ↦ by positivity
  have hRm : ∀ m : ℕ, (m : ℝ) ≤ R m := fun m ↦ by simp only [hR]; linarith [le_max_right R₀ 0]
  choose χ hχ hχc hχ1 hχ0 _ hχΔ hχI using fun m ↦ hC (R m) (hRpos m)
  have hid : ∀ m, ∫ z, Δ (χ m) z * Real.log (s z) = (∫ z, χ m z * F z) + 4 * π * N :=
    fun m ↦ integral_laplacian_mul_log_normSq_of_eq_one hb₁ hb₂ hp hq hsol hfin hn (hχ m) (hχc m)
      fun z hz ↦ (hχ1 m z (by
        have := mem_closedBall_zero_iff.mp (hR₀ hz)
        simp only [hR]
        linarith [le_max_left R₀ 0, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)])).self_of_nhds
  have hRt : Tendsto R atTop atTop := tendsto_atTop_mono hRm tendsto_natCast_atTop_atTop
  -- The cutoff integrals of the right side converge to `∫ F`.
  have hB : Tendsto (fun m ↦ ∫ z, χ m z * F z) atTop (𝓝 (∫ z, F z)) :=
    tendsto_integral_smul_of_eq_one_ball hRt (fun m ↦ (hχ m).continuous.aestronglyMeasurable)
      (fun m z hz ↦ (hχ1 m z hz).self_of_nhds) hχI hFint
  -- The left side tends to zero, because `log |α|² → 0` while `∫ |Δ χ_m|` stays bounded.
  have hL : Tendsto (fun z ↦ Real.log (s z)) (cocompact ℂ) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    rwa [Real.log_one] at h
  have hA : Tendsto (fun m ↦ ∫ z, Δ (χ m) z * Real.log (s z)) atTop (𝓝 0) :=
    tendsto_integral_laplacian_smul_of_tendsto_cocompact volume Complex.finrank_real_complex hRt
      hχ1 hχ0 hχΔ hL
  have hlimit : Tendsto (fun m ↦ ∫ z, Δ (χ m) z * Real.log (s z)) atTop
      (𝓝 ((∫ z, F z) + 4 * π * N)) := by
    simp_rw [hid]
    exact hB.add_const _
  have hzero := tendsto_nhds_unique hlimit hA
  have h4 : ∀ z, 1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2) = -4 * F z := fun z ↦ by
    simp only [hF, hs]
    ring
  rw [integral_congr_ae (.of_forall h4), integral_const_mul]
  linarith

/-- **The total flux of a plane vortex is the number of its zeros.** Let `x` be a `C²` vortex on
the whole plane whose section satisfies `|α| → 1` at infinity, and let `n z` be the multiplicity
of the zero `z` of `α`. Then the curvature coefficient `∂₁ b₂ - ∂₂ b₁` integrates to
`-2π ∑ᶠ z, n z`; equivalently, since `iF_a = -(∂₁ b₂ - ∂₂ b₁) ds ∧ dt`, the flux
`(2π)⁻¹ ∫ iF_a` is the number of zeros of `α`, counted with multiplicity. -/
theorem integral_curvature_eq_neg_mul_finsum
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {n : ℂ → ℕ}
    (hn : ∀ z, ∃ v : ℂ → ℂ, ContinuousAt v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n z * v w) :
    ∫ z, curvature x z = -(2 * π * ∑ᶠ z, (n z : ℝ)) := by
  have h : (fun z ↦ curvature x z) = fun z ↦ -((1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 8) :=
    funext fun z ↦ by rw [curvature_apply]; exact curvature_eq_of_equation_eq_zero (hsol z)
  rw [h, integral_neg, integral_div,
    integral_one_sub_normSq_eq_mul_finsum hb₁ hb₂ hp hq hsol hlim hn]
  ring

/-! ### The flux of a framed vortex -/

/-- **The flux identity in terms of the zero divisor.** For a `C²` vortex on the whole plane with
`|α| → 1` at infinity and zero divisor `D`, `∫ (1 - |α|²) = 16π deg D`. -/
theorem integral_one_sub_normSq_eq_mul_card
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : HasZeroDivisor (sectionValue x) D) :
    ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) = 16 * π * Multiset.card D := by
  rw [integral_one_sub_normSq_eq_mul_finsum hb₁ hb₂ hp hq hsol hlim
    (hasZeroDivisor_iff.1 hD), Multiset.finsum_count_eq_card]

/-- **The flux is the degree of the zero divisor.** For a `C²` vortex on the whole plane with
`|α| → 1` at infinity and zero divisor `D`, the curvature coefficient `∂₁ b₂ - ∂₂ b₁` integrates
to `-2π deg D`; equivalently `(2π)⁻¹ ∫ iF_a = deg D`. -/
theorem integral_curvature_eq_neg_mul_card
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : HasZeroDivisor (sectionValue x) D) :
    ∫ z, curvature x z = -(2 * π * Multiset.card D) := by
  rw [integral_curvature_eq_neg_mul_finsum hb₁ hb₂ hp hq hsol hlim
    (hasZeroDivisor_iff.1 hD), Multiset.finsum_count_eq_card]

/-- **The flux identity for a framed plane vortex, modulus form.** Let `x` be a `C²` vortex on the
whole plane whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then
`∫ (1 - |α|²) = 16π m`. -/
theorem integral_one_sub_normSq_eq_of_tendsto_sectionValue_mul_inv_pow
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) = 16 * π * m := by
  -- The zero divisor `D` of the section has degree `m`.
  obtain ⟨D, hD⟩ := exists_sym_hasZeroDivisor_sectionValue (k := 2) (by norm_num) hb₁ hb₂
    (hp.differentiable (by norm_num)) (hq.differentiable (by norm_num))
    (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hframe
  rw [integral_one_sub_normSq_eq_mul_card hb₁ hb₂ hp hq hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

/-- **The flux of a framed plane vortex is its degree.** Let `x` be a `C²` vortex on the whole
plane whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then the curvature
coefficient `∂₁ b₂ - ∂₂ b₁` integrates to `-2π m`; equivalently, since
`iF_a = -(∂₁ b₂ - ∂₂ b₁) ds ∧ dt`, the flux `(2π)⁻¹ ∫ iF_a` is `m`. -/
theorem integral_curvature_eq_of_tendsto_sectionValue_mul_inv_pow
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∫ z, curvature x z = -(2 * π * m) := by
  have h : (fun z ↦ curvature x z) = fun z ↦ -((1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 8) :=
    funext fun z ↦ by rw [curvature_apply]; exact curvature_eq_of_equation_eq_zero (hsol z)
  rw [h, integral_neg, integral_div,
    integral_one_sub_normSq_eq_of_tendsto_sectionValue_mul_inv_pow hb₁ hb₂ hp hq hsol hframe]
  ring

/-- **The flux identity in the affine field space.** For `s > 1`, every `C²` vortex in `A_m^s` has
flux `(2π)⁻¹ ∫ iF_a = m`: its curvature coefficient `∂₁ b₂ - ∂₂ b₁` integrates to `-2π m`. -/
theorem integral_curvature_eq_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s)
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) :
    ∫ z, curvature x z = -(2 * π * m) := by
  have hcont : Continuous x :=
    (contDiff_euclidean.2 fun i ↦ by fin_cases i <;> assumption).continuous
  exact integral_curvature_eq_of_tendsto_sectionValue_mul_inv_pow hb₁ hb₂ hp hq hsol
    (tendsto_sectionValue_mul_inv_pow hs hx hcont)

end TauCeti.Vortex
