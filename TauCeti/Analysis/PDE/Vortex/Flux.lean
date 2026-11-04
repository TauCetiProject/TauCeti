/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.PDE.Vortex.Decay
public import TauCeti.Analysis.PDE.Vortex.Zeros
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.Calculus.ContDiff.Removable
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Cutoff
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# The flux of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`), so `|α|² = 4 (p² + q²)`. At a zero `z` of a
smooth vortex, `α` factors as `(w - z) ^ n v(w)` with `v(z) ≠ 0`
(`TauCeti.Vortex.exists_contDiffAt_section_eq_pow_mul`); the exponent `n` is the multiplicity of
the zero. Away from the zeros, `log |α|²` satisfies the scalar equation
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

The multiplicities enter through any function `n` with the local factorization property. The
similarity principle supplies one, and it is unique (`TauCeti.eq_of_eventually_sub_pow_mul_eq`).
Smoothness `C²` of the connection is assumed so that the factor `v` is `C²`. Relating the total
multiplicity to the winding degree of an end framing is not addressed here.

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

private theorem sectionValue_eq_section (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue x z = 2 * ((x z 2 : ℂ) + I * x z 3) := by
  rw [sectionValue_apply, mul_comm (x z 3 : ℂ) I]

/-- The local factorization of the section of a `C²` vortex, with a `C²` factor. -/
private theorem exists_contDiffAt_sectionValue_eq_pow_mul
    (hb₁ : ContDiff ℝ 2 (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ 2 (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (hne : ∃ w, sectionValue x w ≠ 0) (z : ℂ) :
    ∃ (k : ℕ) (v : ℂ → ℂ), ContDiffAt ℝ 2 v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ k * v w := by
  have hne' : ∃ w, (x w 2 : ℂ) + I * x w 3 ≠ 0 := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, fun h ↦ hw (by rw [sectionValue_eq_section, h, mul_zero])⟩
  obtain ⟨k, v, hv, hv₀, hfac⟩ := exists_contDiffAt_section_eq_pow_mul (k := 2) (by norm_num)
    hb₁ hb₂ (hp.differentiable (by norm_num)) (hq.differentiable (by norm_num))
    (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hne' z
  exact ⟨k, v, hv, hv₀, hfac.mono fun w hw ↦ by rw [sectionValue_eq_section, hw]⟩

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
  obtain ⟨k, v, hv, hv₀, hfac⟩ :=
    exists_contDiffAt_sectionValue_eq_pow_mul hb₁ hb₂ hp hq hsol hne z₀
  obtain ⟨v', hv', hv'₀, hfac'⟩ := hn z₀
  have hk : n z₀ = k := eq_of_eventually_sub_pow_mul_eq hv' hv'₀ hv.continuousAt hv₀
    (hfac'.and hfac |>.mono fun w hw ↦ hw.1.symm.trans hw.2)
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
    rw [← sq_norm_sectionValue x w, hw, norm_mul, norm_pow, mul_pow, ← pow_mul,
      Real.log_mul (pow_ne_zero _ hwz') (pow_ne_zero 2 (norm_ne_zero_iff.mpr hvw)),
      Real.log_pow]
    push_cast
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
  have hs : ContDiff ℝ 2 (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) :=
    contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  have hsne : ∀ {w}, sectionValue x w ≠ 0 → 4 * (x w 2 ^ 2 + x w 3 ^ 2) ≠ 0 := fun hw ↦ by
    rw [← sq_norm_sectionValue]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
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
  have hfin : {z | sectionValue x z = 0}.Finite := by
    refine (finite_setOfPred_section_eq_zero (k := 2) (by norm_num) hb₁ hb₂
      (hp.differentiable (by norm_num)) (hq.differentiable (by norm_num))
      (fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩) hlim).subset fun z hz ↦ ?_
    have hz' : sectionValue x z = 0 := hz
    rw [sectionValue_eq_section] at hz'
    simpa using hz'
  set N := ∑ᶠ z, (n z : ℝ)
  set s : ℂ → ℝ := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2) with hs
  set F : ℂ → ℝ := fun z ↦ (s z - 1) / 4 with hF
  have hsc : Continuous s := continuous_const.mul ((hp.continuous.pow 2).add (hq.continuous.pow 2))
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
  have hid : ∀ m, ∫ z, Δ (χ m) z * Real.log (s z) = (∫ z, χ m z * F z) + 4 * π * N := by
    intro m
    have h := integral_laplacian_mul_log_normSq hb₁ hb₂ hp hq hsol hfin hn
      ⟨χ m, hχ m, hχc m, subset_univ _⟩
    simp only [TestFunction.coe_mk] at h
    rw [h]
    congr 2
    refine finsum_congr fun z ↦ ?_
    by_cases hz : sectionValue x z = 0
    · have hzR : ‖z‖ < R m := by
        have := mem_closedBall_zero_iff.mp (hR₀ hz)
        simp only [hR]
        linarith [le_max_left R₀ 0, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      rw [(hχ1 m z hzR).self_of_nhds, mul_one]
    · simp [eq_zero_of_sectionValue_ne_zero hn hz]
  -- The cutoff integrals of the right side converge to `∫ F`.
  have hB : Tendsto (fun m ↦ ∫ z, χ m z * F z) atTop (𝓝 (∫ z, F z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ ‖F z‖)
      (fun m ↦ ((hχ m).continuous.mul
        ((hsc.sub continuous_const).div_const 4)).aestronglyMeasurable)
      hFint.norm (fun m ↦ .of_forall fun z ↦ ?_) (.of_forall fun z ↦ ?_)
    · rw [norm_mul, Real.norm_of_nonneg (hχI m z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχI m z).2
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖z‖] with m hm
      rw [(hχ1 m z (hm.trans_le (hRm m))).self_of_nhds, one_mul]
  -- The left side tends to zero, because `log |α|² → 0` while `∫ |Δ χ_m|` stays bounded.
  have hL : Tendsto (fun z ↦ Real.log (s z)) (cocompact ℂ) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    rw [Real.log_one] at h
    exact h
  have hA : Tendsto (fun m ↦ ∫ z, Δ (χ m) z * Real.log (s z)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set C' := max C 0
    set ε' := ε / (4 * π * (C' + 1)) with hε'
    have hε'pos : 0 < ε' := by positivity
    obtain ⟨R', -, hR'⟩ := hasBasis_cobounded_norm.eventually_iff.mp
      (cobounded_eq_cocompact (α := ℂ) ▸ Metric.tendsto_nhds.mp hL ε' hε'pos)
    refine ⟨⌈R'⌉₊, fun m hm ↦ ?_⟩
    have hRR' : R' ≤ R m := (Nat.le_ceil R').trans ((Nat.cast_le.mpr hm).trans (hRm m))
    set g : ℂ → ℝ := (closedBall (0 : ℂ) (2 * R m)).indicator fun _ ↦ C' / R m ^ 2 * ε'
    have hg : Integrable g :=
      (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    have hbound : ∀ z, ‖Δ (χ m) z * Real.log (s z)‖ ≤ g z := by
      intro z
      have hg₀ : 0 ≤ g z := indicator_nonneg (fun _ _ ↦ by positivity) z
      by_cases h₁ : ‖z‖ < R m
      · rw [(laplacian_congr_nhds (hχ1 m z h₁)).eq_of_nhds, laplacian_const]
        simpa using hg₀
      by_cases h₂ : 2 * R m < ‖z‖
      · rw [(laplacian_congr_nhds (hχ0 m z h₂)).eq_of_nhds, laplacian_const]
        simpa using hg₀
      have hz : z ∈ closedBall (0 : ℂ) (2 * R m) := mem_closedBall_zero_iff.mpr (not_lt.mp h₂)
      have hLz : ‖Real.log (s z)‖ ≤ ε' := by
        simpa using (hR' (hRR'.trans (not_lt.mp h₁))).le
      have hgz : g z = C' / R m ^ 2 * ε' := indicator_of_mem hz _
      rw [hgz, norm_mul]
      exact mul_le_mul ((hχΔ m z).trans (div_le_div_of_nonneg_right (le_max_left _ _)
        (by positivity))) hLz (norm_nonneg _) (by positivity)
    have hgint : ∫ z, g z = 4 * π * C' * ε' := by
      rw [integral_indicator_const _ measurableSet_closedBall, Measure.real,
        Complex.volume_closedBall]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by
        positivity : (0 : ℝ) ≤ 2 * R m), ENNReal.coe_toReal, NNReal.coe_real_pi, smul_eq_mul]
      field_simp [(hRpos m).ne']
      ring
    rw [dist_zero_right]
    calc ‖∫ z, Δ (χ m) z * Real.log (s z)‖ ≤ ∫ z, g z :=
          norm_integral_le_of_norm_le hg (.of_forall hbound)
      _ = 4 * π * C' * ε' := hgint
      _ < ε := by
        rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [Real.pi_pos, le_max_right C 0]
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

end TauCeti.Vortex
