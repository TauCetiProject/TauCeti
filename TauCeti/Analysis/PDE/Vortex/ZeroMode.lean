/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import TauCeti.Analysis.PDE.Vortex.Deformation
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

## Main results

* `TauCeti.Vortex.exists_integral_mul_laplacian_sub_mul_eq_zero`: the zero mode with principal
  part `c / (z - a)^k`.

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

/-- The potential `P = |α|² / 4` of a field whose section has unit modulus at infinity is
bounded. -/
private theorem memLp_top_potential (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ volume := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (hlim.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hPc.continuousOn
  refine memLp_top_of_bound hPc.aestronglyMeasurable (max M 1) (ae_of_all _ fun z ↦ ?_)
  by_cases hz : z ∈ K
  · exact (hM z hz).trans (le_max_left _ _)
  · have h2 : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 2 := hKc hz
    have h0 : 0 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by positivity
    rw [Real.norm_of_nonneg h0]
    linarith [le_max_right M 1]

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
    have han : AnalyticAt ℂ (fun w : ℂ ↦ c / (w - a) ^ k) z :=
      analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow k)
        (pow_ne_zero k (sub_ne_zero.2 hza))
    have hΔ : Δ η₀ z = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds hloc).eq_of_nhds]
      exact han.harmonicAt.2.eq_of_nhds
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
  have hP : MemLp P ⊤ volume := memLp_top_potential hx hlim
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  set η₀ : ℂ → ℂ := fun z ↦ (ρ z : ℂ) * (c / (z - a) ^ k)
  set g : ℂ → ℂ := fun z ↦ Δ η₀ z - P z * η₀ z
  have hg2 : MemLp g 2 volume := memLp_laplacian_sub_mul_principalPart hx hα hρ hρc hρa c
  -- Solve `-Δh + P h = g` in `H²`, componentwise.
  have hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z := ae_of_all _ fun z ↦ by positivity
  have hPa : ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → 1 / 8 ≤ P z :=
    ae_of_all _ fun z hz ↦ (hR z hz).le
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

end TauCeti.Vortex
