/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import TauCeti.Analysis.PDE.Vortex.Deformation
public import TauCeti.Analysis.PDE.Vortex.LogVariation
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Zero modes of a plane vortex with a prescribed principal part

Let `x` be a field on the plane with section `α` (`TauCeti.Vortex.sectionValue`), and write
`P = |α|² / 4`, which in the real field coordinates is `x₂² + x₃²`. For a plane vortex the
infinitesimal deformations `y` with section variation `δα` are described by the function
`η = δα / α`, which solves the scalar equation

`Δη = P η`

away from the zeros of `α` (Samols). At a zero `a` of multiplicity `n`, `η` may have a pole of
order at most `n`, and the principal parts of `η` at the zeros of `α` record how the zeros move:
together they are a tangent vector to the space `Sym^m ℂ` of effective divisors of degree `m`.

This file constructs, for every point `a` at which `α` vanishes to order at least `k`, in the
sense that `‖α z‖ ≤ C ‖z - a‖ ^ k` near `a`, and every `c ∈ ℂ`, a solution of `Δη = P η` on
`ℂ \ {a}` with principal part `c / (z - a)^k` at `a` and in `H²` away from `a`
(`TauCeti.Vortex.exists_integral_mul_laplacian_sub_mul_eq_zero`). Precisely, for a smooth
compactly supported cutoff `ρ` equal to one near `a`,

`η = ρ c / (z - a)^k + h`,  `h ∈ H²(ℂ; ℂ)`,

and `∫ η (Δφ - P φ) = 0` for every smooth compactly supported real `φ` vanishing near `a`. At a
zero of multiplicity `n(a)` (`TauCeti.IsZeroMultiplicity`) the section vanishes to every order
`k ≤ n(a)` (`TauCeti.IsZeroMultiplicity.exists_eventually_norm_le_mul_pow`). Since the equation is
linear, sums of these solutions realize every principal part of order at most `n(a)` at each zero.
These are the zero modes behind the lower bound in the identification of the kernel of the
linearized vortex operator with the tangent space of `Sym^m ℂ`.

The construction is the following. The function `η₀ = ρ c / (z - a)^k` is holomorphic near `a`
off `a` itself, hence harmonic there, so `g = Δη₀ - P η₀` equals `-P η₀` near `a`. Since `α`
vanishes to order `k` at `a`, `P ≤ C |z - a|^(2k)` near `a`, so `g` is bounded there; away from
`a` it is continuous with compact support. Hence `g ∈ L²`. The potential `P` is nonnegative,
bounded, and at least `1 / 8` outside a disc when `|α| → 1` at infinity, so the stationary
Schrödinger equation `-Δh + P h = g` has a solution `h ∈ H²`
(`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`, applied to
the real and imaginary parts of `g` and combined by
`TauCeti.integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im`), and `η = η₀ + h` solves
`Δη = P η` off `a`.

Only the vanishing order of `α` at `a` and the limit `|α| → 1` at infinity enter; neither the
vortex equations nor the smoothness of the field are used beyond continuity. The equation is
stated weakly, for test functions supported away from `a`.

**Kernel elements.** For a smooth field with `∂bar_a α = 0` and `α = (z - a)^k ψ` with `ψ`
smooth, the zero mode yields a classical kernel element of the gauge-fixed operator
`L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_eq_logVariation`). Here `g` is
smooth: off `a`, `ρ c / (z - a)^k = u - v` with `u = c / (z - a)^k` harmonic and `v = (1 - ρ) u`
smooth on the whole plane, so `Δη₀ = -Δv`, and `P η₀ = ρ conj(α) c ψ / 4`. The solution `h` of
`-Δh + P h = g` is then smooth
(`TauCeti.exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`), and
`η` solves `Δη = P η` classically off `a`. Its logarithmic variation
(`TauCeti.Vortex.logVariation`), with
section variation `δα = α η` and connection variation `δb₁ + i δb₂ = 2 i ∂bar η`, lies in the
kernel of `L_x` off `a` (`TauCeti.Vortex.gaugeFixedOperator_logVariation_eq_zero_iff`). It extends
smoothly across `a`: the logarithmic variation of `u` has no connection part, and its section
variation `α u = c ψ` is smooth. By continuity the extension `y` satisfies `L_x y = 0` everywhere.
It is square integrable, because `h ∈ H²` and the remaining part is supported in the support of
`ρ`. Its section variation is `α η`, so `δα / α` has principal part `c / (z - a)^k` at `a`.

## Main results

* `TauCeti.Vortex.exists_integral_mul_laplacian_sub_mul_eq_zero`: the zero mode with principal
  part `c / (z - a)^k`.
* `TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_eq_logVariation`: a smooth square-integrable
  kernel element of `L_x` whose `δα / α` has principal part `c / (z - a)^k`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179, Section 3 (the
  zero modes `η = δα / α` and the equation `Δη = |φ|² η`).
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter Metric Complex TemperedDistribution
open scoped Laplacian ContDiff Topology Distributions

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The potential `P = |α|² / 4` of a continuous field whose section has unit modulus at infinity
is bounded above. -/
private theorem exists_forall_potential_le (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ M, ∀ z, x z 2 ^ 2 + x z 3 ^ 2 ≤ M := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (hlim.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hPc.continuousOn
  refine ⟨max M 1, fun z ↦ ?_⟩
  by_cases hz : z ∈ K
  · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM z hz).trans (le_max_left _ _))
  · have h2 : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 2 := hKc hz
    linarith [le_max_right M 1]

/-- The potential `P = |α|² / 4` of a field whose section has unit modulus at infinity is
bounded, nonnegative, and at least `1 / 8` outside some ball: the hypotheses of the Schrödinger
solve. -/
private theorem exists_memLp_top_potential_and_le (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ R : ℝ, MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ volume ∧
      (∀ᵐ z ∂volume, 0 ≤ x z 2 ^ 2 + x z 3 ^ 2) ∧
      ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → 1 / 8 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨M, hM⟩ := exists_forall_potential_le hx hlim
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  refine ⟨R, memLp_top_of_bound hPc.aestronglyMeasurable M (ae_of_all _ fun z ↦ ?_),
    ae_of_all _ fun z ↦ by positivity, ae_of_all _ fun z hz ↦ (hR z hz).le⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hM z

/-- Where the section vanishes to order `k`, `‖α‖ ≤ C ‖z - a‖ ^ k`, the potential
`P = |α|² / 4` vanishes to order `2k`. -/
private theorem exists_eventually_potential_le {a : ℂ} {k : ℕ}
    (hα : ∃ C, ∀ᶠ z in 𝓝 a, ‖sectionValue x z‖ ≤ C * ‖z - a‖ ^ k) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ z in 𝓝 a, x z 2 ^ 2 + x z 3 ^ 2 ≤ C * ‖z - a‖ ^ (2 * k) := by
  obtain ⟨C, hC⟩ := hα
  refine ⟨C ^ 2 / 4, by positivity, ?_⟩
  filter_upwards [hC] with z hz
  have hsq := sq_norm_sectionValue x z
  have h1 : ‖sectionValue x z‖ ^ 2 ≤ (C * ‖z - a‖ ^ k) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [pow_mul', mul_pow] at *
  linarith

/-- The pole `c / (z - a)^k` is holomorphic off `a`. -/
private theorem analyticAt_div_sub_pow (c a : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ a) :
    AnalyticAt ℂ (fun w ↦ c / (w - a) ^ k) z :=
  analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow k)
    (pow_ne_zero k (sub_ne_zero.2 hz))

/-- The principal part `η₀ = ρ c / (z - a)^k` is smooth off `a`. -/
private theorem contDiffAt_principalPart {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (c a : ℂ) (k : ℕ)
    {z : ℂ} (hz : z ≠ a) : ContDiffAt ℝ ∞ (fun w ↦ (ρ w : ℂ) * (c / (w - a) ^ k)) z := by
  have hden : ContDiffAt ℝ ∞ (fun w : ℂ ↦ (w - a) ^ k) z := by fun_prop
  have hinv := hden.inv (pow_ne_zero k (sub_ne_zero.2 hz))
  exact (ofRealCLM.contDiff.comp hρ).contDiffAt.mul (contDiffAt_const.mul hinv)

/-- The defect `g = Δη₀ - P η₀` of the principal part `η₀ = ρ c / (z - a)^k` is square
integrable: it is bounded near `a`, where `η₀` is harmonic and `P` vanishes to order `2k`, and
continuous with compact support away from `a`. -/
private theorem memLp_laplacian_sub_mul_principalPart (hx : Continuous x) {a : ℂ} {k : ℕ}
    (hα : ∃ C, ∀ᶠ z in 𝓝 a, ‖sectionValue x z‖ ≤ C * ‖z - a‖ ^ k)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρa : ρ =ᶠ[𝓝 a] 1) (c : ℂ) :
    MemLp (fun z ↦ Δ (fun w ↦ (ρ w : ℂ) * (c / (w - a) ^ k)) z -
      ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * ((ρ z : ℂ) * (c / (z - a) ^ k))) 2 volume := by
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous P := by
    have := hxi 2; have := hxi 3; fun_prop
  set η₀ : ℂ → ℂ := fun z ↦ (ρ z : ℂ) * (c / (z - a) ^ k) with hη₀def
  have hη₀ (z : ℂ) (hz : z ≠ a) : ContDiffAt ℝ ∞ η₀ z := contDiffAt_principalPart hρ c a k hz
  have hη₀on : ContDiffOn ℝ 2 η₀ {a}ᶜ := fun z hz ↦
    ((hη₀ z hz).of_le (by simp)).contDiffWithinAt
  set g : ℂ → ℂ := fun z ↦ Δ η₀ z - P z * η₀ z with hgdef
  -- Near `a`, `η₀` is holomorphic off `a`, so `g = -P η₀`, which is bounded.
  obtain ⟨C, hC0, hC⟩ := exists_eventually_potential_le hα
  obtain ⟨r₀, hr₀, hr₀b⟩ := Metric.eventually_nhds_iff_ball.1 (hC.and hρa)
  set r := min r₀ 1
  have hr : 0 < r := lt_min hr₀ one_pos
  have hrb (z : ℂ) (hz : z ∈ ball a r) :
      P z ≤ C * ‖z - a‖ ^ (2 * k) ∧ ρ z = 1 ∧ ‖z - a‖ < 1 := by
    have hz₀ : z ∈ ball a r₀ := ball_subset_ball (min_le_left _ _) hz
    obtain ⟨h₁, h₂⟩ := hr₀b z hz₀
    exact ⟨h₁, h₂, (mem_ball_iff_norm.1 hz).trans_le (min_le_right _ _)⟩
  have hgnear (z : ℂ) (hz : z ∈ ball a r) (hza : z ≠ a) : g z = -(P z * η₀ z) := by
    have hloc : η₀ =ᶠ[𝓝 z] fun w ↦ c / (w - a) ^ k := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      simp [hη₀def, (hrb w hw).2.1]
    have hΔ : Δ η₀ z = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds hloc).eq_of_nhds]
      exact (analyticAt_div_sub_pow c a k hza).harmonicAt.2.eq_of_nhds
    simp [hgdef, hΔ]
  have hgnear_le (z : ℂ) (hz : z ∈ ball a r) (hza : z ≠ a) : ‖g z‖ ≤ C * ‖c‖ := by
    obtain ⟨hPz, hρz, hd⟩ := hrb z hz
    have hP0 : 0 ≤ P z := by positivity
    have hd0 : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
    rw [hgnear z hz hza, norm_neg, norm_mul, Complex.norm_of_nonneg hP0]
    simp only [hη₀def, hρz, ofReal_one, one_mul, norm_div, norm_pow]
    have hpk : ‖z - a‖ ^ k ≤ 1 := pow_le_one₀ hd0.le hd.le
    have _ : 0 < ‖z - a‖ ^ k := pow_pos hd0 k
    calc P z * (‖c‖ / ‖z - a‖ ^ k) ≤ C * ‖z - a‖ ^ (2 * k) * (‖c‖ / ‖z - a‖ ^ k) := by
          gcongr
      _ = C * ‖c‖ * ‖z - a‖ ^ k := by
          rw [pow_mul', sq]
          field_simp
      _ ≤ C * ‖c‖ := mul_le_of_le_one_right (by positivity) hpk
  -- Outside the support of `ρ`, `g` vanishes.
  have hgzero (z : ℂ) (hz : z ∉ tsupport ρ) : g z = 0 := by
    have hloc : η₀ =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with w hw
      simp [hη₀def, hw]
    have hΔ : Δ η₀ z = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds hloc).eq_of_nhds]
      simp
    simp [hgdef, hΔ, hloc.eq_of_nhds]
  -- Off `a`, `g` is continuous, hence bounded on the compact set `tsupport ρ \ ball a r`.
  have hgcont : ContinuousOn g {a}ᶜ :=
    (hη₀on.continuousOn_laplacian isOpen_compl_singleton).sub
      ((ofRealCLM.continuous.comp hPc).continuousOn.mul (fun z hz ↦
        (hη₀ z hz).continuousAt.continuousWithinAt))
  have hKc : IsCompact (tsupport ρ \ ball a r) := hρc.isCompact.diff isOpen_ball
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hgcont.mono fun z hz hza ↦
    hz.2 (hza ▸ mem_ball_self hr))
  set M := max (C * ‖c‖) M₂
  have hgbound (z : ℂ) (hza : z ≠ a) : ‖g z‖ ≤ (tsupport ρ).indicator (fun _ ↦ M) z := by
    by_cases hz : z ∈ tsupport ρ
    · rw [Set.indicator_of_mem hz]
      by_cases hzr : z ∈ ball a r
      · exact (hgnear_le z hzr hza).trans (le_max_left _ _)
      · exact (hM₂ z ⟨hz, hzr⟩).trans (le_max_right _ _)
    · rw [Set.indicator_of_notMem hz, hgzero z hz, norm_zero]
  have hgm : AEStronglyMeasurable g volume := by
    rw [← restrict_compl_singleton (μ := volume) a]
    exact hgcont.aestronglyMeasurable (measurableSet_singleton a).compl
  have hM0 : 0 ≤ M := (mul_nonneg hC0 (norm_nonneg c)).trans (le_max_left _ _)
  refine MemLp.of_le (memLp_indicator_const 2
    (isClosed_tsupport ρ).measurableSet.nullMeasurableSet M (Or.inr hρc.measure_lt_top.ne))
    hgm ?_
  filter_upwards [Measure.ae_ne volume a] with z hz
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ hM0) z)]
  exact hgbound z hz

/-- **The weak equation for the principal part.** For a smooth compactly supported real `φ`
vanishing near `a`, `η₀ (Δφ - P φ)` is integrable and `∫ η₀ (Δφ - P φ) = ∫ (Δη₀ - P η₀) φ`. This
is Green's identity on the punctured plane, where `η₀ = ρ c / (z - a)^k` is smooth and `φ` is a
test function. -/
private theorem integrable_and_integral_principalPart_mul_laplacian_sub_mul (hx : Continuous x)
    {a : ℂ} {k : ℕ} {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (c : ℂ)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (haφ : a ∉ tsupport φ) :
    Integrable (fun z ↦ (ρ z : ℂ) * (c / (z - a) ^ k) *
        ((Δ φ z - (x z 2 ^ 2 + x z 3 ^ 2) * φ z : ℝ) : ℂ)) volume ∧
      ∫ z, (ρ z : ℂ) * (c / (z - a) ^ k) * ((Δ φ z - (x z 2 ^ 2 + x z 3 ^ 2) * φ z : ℝ) : ℂ) =
        ∫ z, (Δ (fun w ↦ (ρ w : ℂ) * (c / (w - a) ^ k)) z -
          ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * ((ρ z : ℂ) * (c / (z - a) ^ k))) * (φ z : ℂ) := by
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous P := by
    have := hxi 2; have := hxi 3; fun_prop
  set η₀ : ℂ → ℂ := fun z ↦ (ρ z : ℂ) * (c / (z - a) ^ k)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  -- `φ` is a test function on the punctured plane `Ω`, where `η₀` is smooth.
  let Ω : TopologicalSpace.Opens ℂ := ⟨{a}ᶜ, isOpen_compl_singleton⟩
  have hφΩ : tsupport φ ⊆ Ω := fun z hz hza ↦ haφ (hza ▸ hz)
  let ψ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hφc, hφΩ⟩
  have hη₀ : ContDiffOn ℝ 2 η₀ Ω := fun z hz ↦
    ((contDiffAt_principalPart hρ c a k hz).of_le (by simp)).contDiffWithinAt
  have hΩm : MeasurableSet (Ω : Set ℂ) := Ω.isOpen.measurableSet
  -- Integrability of the pieces.
  have i₁ : Integrable (fun z ↦ Δ φ z • η₀ z) volume :=
    (hη₀.continuousOn.locallyIntegrableOn hΩm).integrable_smul_left_of_hasCompactSupport
      hφ2.continuous_laplacian
      (hφc.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _)))
      ((tsupport_laplacian_subset _).trans hφΩ)
  have i₂ : Integrable (fun z ↦ φ z • (P z • η₀ z)) volume :=
    ψ.integrable_smul ((hPc.continuousOn.smul hη₀.continuousOn).locallyIntegrableOn hΩm)
  have i₃ : Integrable (fun z ↦ φ z • Δ η₀ z) volume :=
    ψ.integrable_smul ((hη₀.continuousOn_laplacian Ω.isOpen).locallyIntegrableOn hΩm)
  have e (z : ℂ) : η₀ z * ((Δ φ z - P z * φ z : ℝ) : ℂ) = Δ φ z • η₀ z - φ z • (P z • η₀ z) := by
    simp only [Complex.real_smul, ofReal_sub, ofReal_mul]
    ring
  refine ⟨(i₁.sub i₂).congr (ae_of_all _ fun z ↦ (e z).symm), ?_⟩
  calc ∫ z, η₀ z * ((Δ φ z - P z * φ z : ℝ) : ℂ)
      = (∫ z, Δ φ z • η₀ z) - ∫ z, φ z • (P z • η₀ z) := by
        rw [← integral_sub i₁ i₂]
        exact integral_congr_ae (ae_of_all _ e)
    _ = (∫ z, φ z • Δ η₀ z) - ∫ z, φ z • (P z • η₀ z) := by
        congr 1
        exact hη₀.integral_laplacian_smul_eq_integral_smul_laplacian ψ
    _ = ∫ z, (Δ η₀ z - (P z : ℂ) * η₀ z) * (φ z : ℂ) := by
        rw [← integral_sub i₃ i₂]
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        simp only [Complex.real_smul]
        ring

/-- **Zero modes of a plane vortex with a prescribed principal part.** Let `x` be a continuous
field whose section `α` has unit modulus at infinity, and write `P = |α|² / 4 = x₂² + x₃²`.
Suppose that `α` vanishes to order `k` at `a`: `‖α z‖ ≤ C ‖z - a‖ ^ k` near `a`. Let `c ∈ ℂ` and
let `ρ` be a smooth compactly supported cutoff equal to one near `a`. Then there is
`h ∈ H²(ℂ; ℂ)` such that `η = ρ c / (z - a)^k + h` solves `Δη = P η` weakly on `ℂ \ {a}`:
`∫ η (Δφ - P φ) = 0` for every smooth compactly supported real function `φ` vanishing near
`a`. -/
theorem exists_integral_mul_laplacian_sub_mul_eq_zero (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {a : ℂ} {k : ℕ} (hα : ∃ C, ∀ᶠ z in 𝓝 a, ‖sectionValue x z‖ ≤ C * ‖z - a‖ ^ k)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρa : ρ =ᶠ[𝓝 a] 1) (c : ℂ) :
    ∃ h : ℂ → ℂ, (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → a ∉ tsupport φ →
        ∫ z, ((ρ z : ℂ) * (c / (z - a) ^ k) + h z) *
          ((Δ φ z - (x z 2 ^ 2 + x z 3 ^ 2) * φ z : ℝ) : ℂ) = 0 := by
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  obtain ⟨R, hP, hP₀, hPa⟩ := exists_memLp_top_potential_and_le hx hlim
  set η₀ : ℂ → ℂ := fun z ↦ (ρ z : ℂ) * (c / (z - a) ^ k)
  set g : ℂ → ℂ := fun z ↦ Δ η₀ z - P z * η₀ z
  have hg2 : MemLp g 2 volume := memLp_laplacian_sub_mul_principalPart hx hα hρ hρc hρa c
  -- Solve `-Δh + P h = g` in `H²`, componentwise.
  obtain ⟨h₁, hh₁, hw₁⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hP hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hg2.re
  obtain ⟨h₂, hh₂, hw₂⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hP hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hg2.im
  refine ⟨fun z ↦ h₁ z + h₂ z * I, by simpa using hh₁, by simpa using hh₂,
    fun φ hφ hφc haφ ↦ ?_⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  -- The principal part contributes `∫ g φ`, and the `H²` part `-∫ g φ`.
  obtain ⟨k₁, hA⟩ :=
    integrable_and_integral_principalPart_mul_laplacian_sub_mul hx hρ c hφ hφc haφ
  obtain ⟨k₂, hB⟩ := integrable_and_integral_mul_neg_laplacian_add_mul_eq_of_re_im hP hg2
    (memLp_of_mem_realSobolevFunctions hh₁) (memLp_of_mem_realSobolevFunctions hh₂)
    (by simpa only [RCLike.re_to_complex] using hw₁)
    (by simpa only [RCLike.im_to_complex] using hw₂) hφ2 hφc
  calc ∫ z, ((ρ z : ℂ) * (c / (z - a) ^ k) + (h₁ z + h₂ z * I)) *
        ((Δ φ z - P z * φ z : ℝ) : ℂ)
      = ∫ z, ((ρ z : ℂ) * (c / (z - a) ^ k) * ((Δ φ z - P z * φ z : ℝ) : ℂ) -
          (h₁ z + h₂ z * I) * ((-Δ φ z + P z * φ z : ℝ) : ℂ)) :=
        integral_congr_ae (ae_of_all _ fun z ↦ by push_cast; ring)
    _ = 0 := by rw [integral_sub k₁ k₂, hA, hB, sub_self]

/-! ### Smooth kernel elements with a prescribed principal part -/

/-- The section coordinates of a continuous field whose section has unit modulus at infinity are
bounded. -/
private theorem memLp_top_apply (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) : MemLp (fun z ↦ x z i) ⊤ volume := by
  obtain ⟨M, hM⟩ := exists_forall_potential_le hx hlim
  have hxi : Continuous fun z ↦ x z i := by fun_prop
  refine memLp_top_of_bound hxi.aestronglyMeasurable (M + 1) (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  have hz := hM z
  rcases hi with rfl | rfl
  · nlinarith [sq_nonneg (|x z 2| - 1), sq_abs (x z 2), sq_nonneg (x z 3), abs_nonneg (x z 2)]
  · nlinarith [sq_nonneg (|x z 3| - 1), sq_abs (x z 3), sq_nonneg (x z 2), abs_nonneg (x z 3)]

/-- A point outside the support of a cutoff `ρ` equal to one near `a` is not `a`. -/
private theorem ne_of_notMem_tsupport {ρ : ℂ → ℝ} {a w : ℂ} (hρa : ρ =ᶠ[𝓝 a] 1)
    (hw : w ∉ tsupport ρ) : w ≠ a := by
  rintro rfl
  exact hw (subset_tsupport _ (by simp [hρa.self_of_nhds]))

/-- `(1 - ρ) c / (z - a)^k` is smooth when the smooth function `ρ` equals one near `a`. -/
private theorem contDiff_one_sub_mul_div_sub_pow {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) {a : ℂ}
    (hρa : ρ =ᶠ[𝓝 a] 1) (c : ℂ) (k : ℕ) :
    ContDiff ℝ ∞ (fun w ↦ ((1 - ρ w : ℝ) : ℂ) * (c / (w - a) ^ k)) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  rcases eq_or_ne z a with rfl | hz
  · exact contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq <| by
      filter_upwards [hρa] with w hw
      simp [hw]
  · exact contDiffAt_principalPart (contDiff_const.sub hρ) c a k hz

/-- Outside the support of `ρ`, `(1 - ρ) c / (z - a)^k` agrees with `c / (z - a)^k` nearby. -/
private theorem one_sub_mul_div_sub_pow_eventuallyEq {ρ : ℂ → ℝ} {w : ℂ} (hw : w ∉ tsupport ρ)
    (c a : ℂ) (k : ℕ) :
    (fun w' ↦ ((1 - ρ w' : ℝ) : ℂ) * (c / (w' - a) ^ k)) =ᶠ[𝓝 w] fun w' ↦ c / (w' - a) ^ k := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hw] with w' hw'
  simp [hw']

/-- Where `α = (z - a)^k ψ`, the section variation `α c / (z - a)^k` of the pole is `c ψ` off
`a`. -/
private theorem sectionValue_mul_div_sub_pow {a : ℂ} {k : ℕ} {ψ : ℂ → ℂ}
    (hαψ : ∀ z, sectionValue x z = (z - a) ^ k * ψ z) (c : ℂ) {z : ℂ} (hz : z ≠ a) :
    sectionValue x z * (c / (z - a) ^ k) = c * ψ z := by
  rw [hαψ]
  field_simp [pow_ne_zero k (sub_ne_zero.2 hz)]

/-- The defect `g = -Δv - ρ conj(α) c ψ / 4` of the principal part `ρ c / (z - a)^k`, where
`v = (1 - ρ) c / (z - a)^k`, is smooth and compactly supported. Off `a` it is
`Δ(ρ u) - P ρ u` for `u = c / (z - a)^k` and `α = (z - a)^k ψ`, written smoothly across `a`. -/
private theorem contDiff_and_hasCompactSupport_defect (hx : ContDiff ℝ ∞ x) {a : ℂ} {k : ℕ}
    {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρa : ρ =ᶠ[𝓝 a] 1) (c : ℂ) :
    ContDiff ℝ ∞ (fun w ↦ -Δ (fun w' ↦ ((1 - ρ w' : ℝ) : ℂ) * (c / (w' - a) ^ k)) w -
        (ρ w : ℂ) * starRingEnd ℂ (sectionValue x w) * (c * ψ w) / 4) ∧
      HasCompactSupport (fun w ↦ -Δ (fun w' ↦ ((1 - ρ w' : ℝ) : ℂ) * (c / (w' - a) ^ k)) w -
        (ρ w : ℂ) * starRingEnd ℂ (sectionValue x w) * (c * ψ w) / 4) := by
  have hαs : ContDiff ℝ ∞ (sectionValue x) :=
    contDiff_sectionValue (contDiff_euclidean.mp hx 2) (contDiff_euclidean.mp hx 3)
  refine ⟨((contDiff_one_sub_mul_div_sub_pow hρ hρa c k).laplacian (by simp)).neg.sub
    ((((ofRealCLM.contDiff.comp hρ).mul (conjCLE.contDiff.comp hαs)).mul
      (contDiff_const.mul hψ)).div_const 4), hρc.mono' fun w hw ↦ ?_⟩
  -- Outside the support of `ρ`, `v` is the harmonic `c / (z - a)^k` near `w`.
  by_contra hn
  apply hw
  have hΔ : Δ (fun w' ↦ ((1 - ρ w' : ℝ) : ℂ) * (c / (w' - a) ^ k)) w = 0 := by
    rw [(InnerProductSpace.laplacian_congr_nhds
      (one_sub_mul_div_sub_pow_eventuallyEq hn c a k)).eq_of_nhds]
    exact (analyticAt_div_sub_pow c a k (ne_of_notMem_tsupport hρa hn)).harmonicAt.2.eq_of_nhds
  simp only [hΔ, image_eq_zero_of_notMem_tsupport hn]
  simp

/-- **Smooth continuation of the logarithmic variation of the principal part.** If
`α = (z - a)^k ψ` with `ψ` smooth, the logarithmic variation of `ρ c / (z - a)^k` agrees off `a`
with a smooth compactly supported field. Write `ρ u = u - v` with `u = c / (z - a)^k` and
`v = (1 - ρ) u` smooth: the logarithmic variation of the holomorphic `u` has no connection part
and section part `α u / 2 = c ψ / 2`. -/
private theorem exists_contDiff_hasCompactSupport_eq_logVariation (hx : ContDiff ℝ ∞ x)
    {a : ℂ} {k : ℕ} {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hαψ : ∀ z, sectionValue x z = (z - a) ^ k * ψ z) {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρa : ρ =ᶠ[𝓝 a] 1) (c : ℂ) :
    ∃ Y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧
      ∀ z, z ≠ a → Y z = logVariation x (fun w ↦ (ρ w : ℂ) * (c / (w - a) ^ k)) z := by
  set u : ℂ → ℂ := fun w ↦ c / (w - a) ^ k
  set v : ℂ → ℂ := fun w ↦ ((1 - ρ w : ℝ) : ℂ) * u w
  have hu (z : ℂ) (hz : z ≠ a) : AnalyticAt ℂ u z := analyticAt_div_sub_pow c a k hz
  have hv : ContDiff ℝ ∞ v := contDiff_one_sub_mul_div_sub_pow hρ hρa c k
  have hvu (w : ℂ) (hw : w ∉ tsupport ρ) : v =ᶠ[𝓝 w] u :=
    one_sub_mul_div_sub_pow_eventuallyEq hw c a k
  have hαu (z : ℂ) (hz : z ≠ a) : sectionValue x z * u z = c * ψ z :=
    sectionValue_mul_div_sub_pow hαψ c hz
  -- The smooth continuation `Y₀` of `logVariation x u` across `a`.
  set Y₀ : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦
    !₂[0, 0, (c * ψ w / 2).re, (c * ψ w / 2).im] with hY₀def
  have hY₀u (z : ℂ) (hz : z ≠ a) : logVariation x u z = Y₀ z := by
    rw [logVariation_eq_of_differentiableAt x (hu z hz).differentiableAt, mul_div_assoc,
      ← mul_div_assoc, hαu z hz]
  have hY₀s : ContDiff ℝ ∞ Y₀ := by
    have hcψ : ContDiff ℝ ∞ (fun w ↦ c * ψ w / 2) := (contDiff_const.mul hψ).div_const 2
    refine contDiff_euclidean.mpr fun i ↦ ?_
    fin_cases i
    · simpa [hY₀def] using (contDiff_const : ContDiff ℝ ∞ fun _ : ℂ ↦ (0 : ℝ))
    · simpa [hY₀def] using (contDiff_const : ContDiff ℝ ∞ fun _ : ℂ ↦ (0 : ℝ))
    · convert reCLM.contDiff.comp hcψ using 1
      funext w
      simp [hY₀def]
    · convert imCLM.contDiff.comp hcψ using 1
      funext w
      simp [hY₀def]
  refine ⟨fun w ↦ Y₀ w - logVariation x v w,
    hY₀s.sub (contDiff_logVariation hx (hv.of_le (by simp))), ?_, fun z hz ↦ ?_⟩
  · refine hρc.mono' fun w hw ↦ ?_
    by_contra hn
    apply hw
    beta_reduce
    rw [logVariation_congr_nhds x (hvu w hn), hY₀u w (ne_of_notMem_tsupport hρa hn), sub_self]
  · have hρu : (fun w ↦ (ρ w : ℂ) * u w) = u + (-1 : ℝ) • v := funext fun w ↦ by
      simp only [v, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      push_cast
      ring
    rw [hρu, logVariation_add_apply x ((hu z hz).differentiableAt.restrictScalars ℝ)
      ((hv.differentiable (by simp)).const_smul (-1 : ℝ) z), logVariation_smul, hY₀u z hz]
    simp only [Pi.smul_apply, neg_smul, one_smul, sub_eq_add_neg]

/-- For a smooth field whose section has unit modulus at infinity and a smooth `g ∈ L²(ℂ; ℂ)`,
the equation `Δh = P h - g`, `P = |α|² / 4`, has a smooth solution `h ∈ H²(ℂ; ℂ)`. -/
private theorem exists_contDiff_laplacian_eq_mul_sub (hx : ContDiff ℝ ∞ x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {g : ℂ → ℂ}
    (hgs : ContDiff ℝ ∞ g) (hg2 : MemLp g 2 volume) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, Δ h z = ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * h z - g z := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  obtain ⟨R, hP, hP₀, hPa⟩ := exists_memLp_top_potential_and_le hx.continuous hlim
  obtain ⟨h, hhs, hh₁, hh₂, he⟩ :=
    exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq
      (((hxi 2).pow 2).add ((hxi 3).pow 2)) hP hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hgs hg2
  exact ⟨h, hhs, hh₁, hh₂, fun z ↦ by linear_combination -he z⟩

/-- The potential `P = |α|² / 4` in terms of the section `α`. -/
private theorem ofReal_potential_eq (x : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) =
      starRingEnd ℂ (sectionValue x z) * sectionValue x z / 4 := by
  apply Complex.ext <;> simp [sectionValue_apply, sq] <;> ring

/-- At a point where `u` is holomorphic, if `h` solves `Δh = P h - g` for the defect
`g = -Δv - P (u - v)` of `u - v`, then `η = h + (u - v)` solves `Δη = P η` there. -/
private theorem laplacian_add_sub_eq_smul {P : ℝ} {h u v : ℂ → ℂ} {z : ℂ}
    (hh : ContDiffAt ℝ 2 h z) (hu : AnalyticAt ℂ u z) (hv : ContDiffAt ℝ 2 v z)
    (hΔh : Δ h z = P * h z - (-Δ v z - P * (u z - v z))) :
    Δ (h + (u - v)) z = P • (h + (u - v)) z := by
  have hu₂ : ContDiffAt ℝ 2 u z := (hu.contDiffAt (n := 2)).restrict_scalars ℝ
  have hΔu : Δ u z = 0 := hu.harmonicAt.2.eq_of_nhds
  rw [hh.laplacian_add (f₂ := u - v) (hu₂.sub hv), hu₂.laplacian_sub hv, hΔu, hΔh, Pi.add_apply,
    Pi.sub_apply, Complex.real_smul]
  ring

/-- **Kernel elements of the gauge-fixed operator with a prescribed principal part.** Let `x` be
a smooth field whose holomorphicity rows vanish, `∂bar_a α = 0`, and whose section has unit
modulus at infinity. Suppose that `α` vanishes to order `k` at `a` in the sense that
`α = (z - a)^k ψ` with `ψ` smooth. Let `c ∈ ℂ` and let `ρ` be a smooth compactly supported
cutoff equal to one near `a`. Then there are a smooth `h ∈ H²(ℂ; ℂ)` and a smooth square-integrable
field `y` with `L_x y = 0` which, off `a`, is the logarithmic variation of
`η = ρ c / (z - a)^k + h`: its section variation is `δα = α η`, so `δα / α` has principal part
`c / (z - a)^k` at `a`. -/
theorem exists_gaugeFixedOperator_eq_zero_eq_logVariation (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {a : ℂ} {k : ℕ} {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hαψ : ∀ z, sectionValue x z = (z - a) ^ k * ψ z)
    {ρ : ℂ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρa : ρ =ᶠ[𝓝 a] 1) (c : ℂ) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
        (∀ z, gaugeFixedOperator x y z = 0) ∧
        ∀ z, z ≠ a → y z = logVariation x (fun w ↦ (ρ w : ℂ) * (c / (w - a) ^ k) + h w) z := by
  -- Outline: write `ρ u = u - v` with `u = c / (z - a)^k` and `v` smooth; solve for `h` against
  -- the smooth compactly supported defect `g` of `ρ u`; check `Δη = P η` off `a`; and continue
  -- the logarithmic variation of `η` smoothly across `a`.
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2
  set u : ℂ → ℂ := fun w ↦ c / (w - a) ^ k
  set v : ℂ → ℂ := fun w ↦ ((1 - ρ w : ℝ) : ℂ) * u w
  have hu (z : ℂ) (hz : z ≠ a) : AnalyticAt ℂ u z := analyticAt_div_sub_pow c a k hz
  have hv : ContDiff ℝ 2 v := (contDiff_one_sub_mul_div_sub_pow hρ hρa c k).of_le (by simp)
  have hαu (z : ℂ) (hz : z ≠ a) : sectionValue x z * u z = c * ψ z :=
    sectionValue_mul_div_sub_pow hαψ c hz
  have hρu (w : ℂ) : (ρ w : ℂ) * u w = u w - v w := by
    simp only [v]
    push_cast
    ring
  -- Solve `-Δh + P h = g` with a smooth `h ∈ H²` for the defect `g = Δ(ρ u) - P ρ u` of the
  -- principal part, written smoothly across `a`.
  set g : ℂ → ℂ := fun w ↦
    -Δ v w - (ρ w : ℂ) * starRingEnd ℂ (sectionValue x w) * (c * ψ w) / 4 with hgdef
  obtain ⟨hgs, hgc⟩ : ContDiff ℝ ∞ g ∧ HasCompactSupport g :=
    contDiff_and_hasCompactSupport_defect hx hψ hρ hρc hρa c
  obtain ⟨h, hhs, hh₁, hh₂, hΔh⟩ :=
    exists_contDiff_laplacian_eq_mul_sub hx hlim hgs (hgs.continuous.memLp_of_hasCompactSupport hgc)
  refine ⟨h, hhs, hh₁, hh₂, ?_⟩
  have hh2 : ContDiff ℝ 2 h := hhs.of_le (by simp)
  -- The zero mode `η = ρ u + h` solves `Δη = P η` off `a`.
  set η : ℂ → ℂ := fun w ↦ (ρ w : ℂ) * u w + h w with hηdef
  have hηs (z : ℂ) (hz : z ≠ a) : ContDiffAt ℝ 2 η z :=
    ((contDiffAt_principalPart hρ c a k hz).of_le (by simp)).add hh2.contDiffAt
  have hΔη (z : ℂ) (hz : z ≠ a) : Δ η z = P z • η z := by
    have hηuv : η = h + (u - v) := funext fun w ↦ by
      simp only [hηdef, hρu, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hηuv]
    refine laplacian_add_sub_eq_smul hh2.contDiffAt (hu z hz) hv.contDiffAt ?_
    have hPz : (P z : ℂ) = starRingEnd ℂ (sectionValue x z) * sectionValue x z / 4 :=
      ofReal_potential_eq x z
    rw [hΔh z, ← hρu z, hPz]
    simp only [hgdef]
    linear_combination (-(ρ z : ℂ) * starRingEnd ℂ (sectionValue x z) / 4) * hαu z hz
  -- The kernel element: `y = Y + logVariation x h`, where `Y` is the smooth compactly supported
  -- continuation of the logarithmic variation of `ρ u` across `a`.
  obtain ⟨Y, hYs, hYc, hYu⟩ :=
    exists_contDiff_hasCompactSupport_eq_logVariation hx hψ hαψ hρ hρc hρa c
  set y : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ Y w + logVariation x h w with hydef
  have hys : ContDiff ℝ ∞ y := hYs.add (contDiff_logVariation hx (hhs.of_le (by simp)))
  have hyη (z : ℂ) (hz : z ≠ a) : y z = logVariation x η z := by
    have hρη : η = (fun w ↦ (ρ w : ℂ) * (c / (w - a) ^ k)) + h := rfl
    simp only [hydef]
    rw [hρη, logVariation_add_apply x
      ((contDiffAt_principalPart hρ c a k hz).differentiableAt (by simp))
      (hhs.differentiable (by simp) z), hYu z hz]
  refine ⟨y, hys, ?_, ?_, hyη⟩
  · -- `Y` is continuous with compact support, and `logVariation x h` is square integrable since
    -- `h ∈ H²`.
    exact (hYs.continuous.memLp_of_hasCompactSupport hYc).add
      (memLp_logVariation_of_mem_realSobolevFunctions (memLp_top_apply hx.continuous hlim (by simp))
        (memLp_top_apply hx.continuous hlim (by simp)) (hhs.of_le (by simp)) hh₁ hh₂)
  · -- Off `a`, `y` is the logarithmic variation of the zero mode `η`; at `a`, by continuity.
    have hcont : Continuous (gaugeFixedOperator x y) :=
      continuous_gaugeFixedOperator hx.continuous (hys.of_le (by simp))
    have hoff (z : ℂ) (hz : z ≠ a) : gaugeFixedOperator x y z = 0 := by
      have hrep : y =ᶠ[𝓝 z] logVariation x η := by
        filter_upwards [eventually_ne_nhds hz] with w hw
        exact hyη w hw
      rw [gaugeFixedOperator_congr_nhds x hrep]
      exact (gaugeFixedOperator_logVariation_eq_zero_iff (hx.differentiable (by simp) z)
        (hηs z hz) (hhol z).1 (hhol z).2).2 (hΔη z hz)
    intro z
    exact congrFun (hcont.ext_on (dense_compl_singleton a) continuous_const
      fun w hw ↦ hoff w hw) z

end TauCeti.Vortex
