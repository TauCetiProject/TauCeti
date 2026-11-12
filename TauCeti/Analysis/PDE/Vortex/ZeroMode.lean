/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Analysis.PDE.Schrodinger.Stationary
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Schrodinger.Planar
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate
import TauCeti.Analysis.PDE.Vortex.LogVariation
import TauCeti.Analysis.PDE.Vortex.Zeros
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
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

## Smooth zero modes in the kernel of `L_x`

At a smooth field `x` satisfying the holomorphicity rows `∂bar_a α = 0` of the vortex equation,
the same construction produces actual kernel elements of the gauge-fixed operator
`L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.gaugeFixedOperator`). Suppose `α = (z - a)^k β` near `a` with
`β` smooth at `a`; then `α = (z - a)^k q` on the whole plane with `q` smooth. Split
`η₀ = c / (z - a)^k + χ`, where `χ = (ρ - 1) c / (z - a)^k` is smooth. Off `a`,
`Δη₀ = Δχ` and `P η₀ = ρ c (conj α) q / 4`, so the right side `g` above agrees off `a` with
the smooth compactly supported function `Δχ - ρ c (conj α) q / 4`. With this right side the weak
solution `h ∈ H²` of `-Δh + P h = g` has a smooth representative solving the equation classically
(`TauCeti.exists_contDiff_ae_eq_and_laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq`).
Then `η = χ + h` is smooth and `ζ = c / (z - a)^k + η` solves `Δζ = P ζ` off `a`.

The kernel element is `y = logVariation x η + (0, 0, c q / 2)`: its section variation is
`α η + c q = α (c / (z - a)^k + η)` off `a`. Off `a`, `y` is the logarithmic variation
(`TauCeti.Vortex.logVariation`) of `c / (z - a)^k + η`, since the logarithmic variation of a
holomorphic function has no connection part, so `L_x y = 0` there by
`TauCeti.Vortex.gaugeFixedOperator_logVariation_eq_zero_iff`; at `a` it follows by continuity. The
field `y` is smooth, and square integrable: it is the logarithmic variation of `h ∈ H²`, whose
first derivatives lie in `L²`, plus a smooth field vanishing outside the support of `ρ`
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_of_sectionValue_eq_pow_mul`). At a zero of
multiplicity `n(a)`, the factorization exists for every `k ≤ n(a)`
(`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_of_isZeroMultiplicity`).

So at a smooth framed vortex every principal part `c / (z - a)^k`, `k ≤ n(a)`, of `δα / α` at a
zero is realized by a smooth square-integrable kernel element of `L_x` whose `δα / α` is regular
at the other zeros. Kernel elements are determined by the principal parts of `δα / α`
(`TauCeti.Vortex.principalPartMap_injective`, with
`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`); this
file does not assemble the elements constructed here into a subspace of the kernel or compute its
dimension.

## Main results

* `TauCeti.Vortex.exists_integral_mul_laplacian_sub_mul_eq_zero`: the weak zero mode with
  principal part `c / (z - a)^k`.
* `TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_of_sectionValue_eq_pow_mul`: where
  `α = (z - a)^k β` near `a` with `β` smooth at `a`, a smooth square-integrable kernel element of
  `L_x` with `δα = α (c / (z - a)^k + η)` off `a`, `η` smooth.
* `TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_of_isZeroMultiplicity`: the same at a zero of
  multiplicity at least `k`.

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
is bounded. -/
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
  · exact (Real.le_norm_self _).trans ((hM z hz).trans (le_max_left _ _))
  · have h2 : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 2 := hKc hz
    linarith [le_max_right M 1]

/-- The potential `P = |α|² / 4` of a field whose section has unit modulus at infinity is
bounded. -/
private theorem memLp_top_potential (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ volume := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨M, hM⟩ := exists_forall_potential_le hx hlim
  refine memLp_top_of_bound hPc.aestronglyMeasurable M (ae_of_all _ fun z ↦ ?_)
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

/-! ### Smooth square-integrable zero modes in the kernel of `L_x` -/

section Kernel

/-- A section vanishing to order `k` at `a`, with a factor smooth at `a`, is `(z - a)^k` times a
smooth function on the whole plane. -/
private theorem exists_contDiff_forall_sectionValue_eq_pow_mul (hx : ContDiff ℝ ∞ x) {a : ℂ}
    {k : ℕ} {β : ℂ → ℂ} (hβ : ContDiffAt ℝ ∞ β a)
    (hαβ : ∀ᶠ z in 𝓝 a, sectionValue x z = (z - a) ^ k * β z) :
    ∃ q : ℂ → ℂ, ContDiff ℝ ∞ q ∧ ∀ z, sectionValue x z = (z - a) ^ k * q z := by
  have hα : ContDiff ℝ ∞ (sectionValue x) :=
    contDiff_sectionValue (contDiff_euclidean.mp hx 2) (contDiff_euclidean.mp hx 3)
  have hpow (z : ℂ) (hz : z ≠ a) : (z - a) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.2 hz)
  set q : ℂ → ℂ := Function.update (fun z ↦ sectionValue x z / (z - a) ^ k) a (β a) with hqdef
  have hqa : q =ᶠ[𝓝 a] β := by
    filter_upwards [hαβ] with z hz
    rcases eq_or_ne z a with rfl | hza
    · simp [hqdef]
    · rw [hqdef, Function.update_of_ne hza, hz, mul_div_cancel_left₀ _ (hpow z hza)]
  have hq (z : ℂ) (hza : z ≠ a) : q =ᶠ[𝓝 z] fun w ↦ sectionValue x w / (w - a) ^ k := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hza] with w hw
    exact Function.update_of_ne hw _ _
  refine ⟨q, contDiff_iff_contDiffAt.2 fun z ↦ ?_, fun z ↦ ?_⟩
  · rcases eq_or_ne z a with rfl | hza
    · exact hβ.congr_of_eventuallyEq hqa
    · have hden : ContDiffAt ℝ ∞ (fun w : ℂ ↦ (w - a) ^ k) z := by fun_prop
      exact (hα.contDiffAt.mul (hden.inv (hpow z hza))).congr_of_eventuallyEq
        ((hq z hza).trans (.of_forall fun w ↦ div_eq_mul_inv _ _))
  · rcases eq_or_ne z a with rfl | hza
    · rw [hqa.self_of_nhds]
      exact hαβ.self_of_nhds
    · rw [(hq z hza).self_of_nhds, mul_div_cancel₀ _ (hpow z hza)]

/-- The variation with zero connection part and section `f`. -/
private noncomputable def sectionField (f : ℂ → ℂ) (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[0, 0, (f z).re / 2, (f z).im / 2]

private theorem sectionValue_sectionField (f : ℂ → ℂ) (z : ℂ) :
    sectionValue (sectionField f) z = f z := by
  apply Complex.ext <;> simp [sectionField, sectionValue_apply] <;> ring

private theorem contDiff_sectionField {n : WithTop ℕ∞} {f : ℂ → ℂ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (sectionField f) := by
  refine contDiff_euclidean.mpr fun i ↦ ?_
  fin_cases i
  · simpa [sectionField] using contDiff_const (c := (0 : ℝ))
  · simpa [sectionField] using contDiff_const (c := (0 : ℝ))
  · simpa [sectionField] using (reCLM.contDiff.comp hf).div_const (2 : ℝ)
  · simpa [sectionField] using (imCLM.contDiff.comp hf).div_const (2 : ℝ)

/-- The section of the logarithmic variation of `η` plus the section variation `c q`, where
`α = (z - a)^k q`, is `α (c / (z - a)^k + η)` off `a`. -/
private theorem sectionValue_logVariation_add_sectionField {a c : ℂ} {k : ℕ} {q : ℂ → ℂ}
    (hαq : ∀ z, sectionValue x z = (z - a) ^ k * q z) (η : ℂ → ℂ) {z : ℂ} (hz : z ≠ a) :
    sectionValue (logVariation x η + sectionField fun w ↦ c * q w) z =
      sectionValue x z * (c / (z - a) ^ k + η z) := by
  rw [sectionValue_add, sectionValue_logVariation, sectionValue_sectionField, hαq z]
  field_simp [pow_ne_zero k (sub_ne_zero.2 hz)]
  ring

/-- **Assembling a kernel element from its regular part.** Let `x` be a smooth field satisfying the
holomorphicity rows of the vortex equation, with section `α = (z - a)^k q`, `q` smooth. If `η` is
smooth and `c / (z - a)^k + η` solves `Δη = P η` off `a`, then the logarithmic variation of `η`
plus the section variation `c q` lies in the kernel of `L_x` on the whole plane. Off `a` it is the
logarithmic variation of `c / (z - a)^k + η`; at `a` the conclusion follows by continuity. -/
private theorem gaugeFixedOperator_logVariation_add_sectionField_eq_zero (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0) {a c : ℂ} {k : ℕ} {q η : ℂ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hαq : ∀ z, sectionValue x z = (z - a) ^ k * q z)
    (hη : ContDiff ℝ ∞ η)
    (heq : ∀ z, z ≠ a → Δ η z = (x z 2 ^ 2 + x z 3 ^ 2) • (c / (z - a) ^ k + η z)) (z : ℂ) :
    gaugeFixedOperator x (logVariation x η + sectionField fun w ↦ c * q w) z = 0 := by
  set y := logVariation x η + sectionField fun w ↦ c * q w with hydef
  have hη2 : ContDiff ℝ 2 η := hη.of_le (by simp)
  have hy : ContDiff ℝ 1 y :=
    (contDiff_logVariation (hx.of_le (by simp)) hη2).add
      (contDiff_sectionField ((contDiff_const.mul hq).of_le (by simp)))
  set pole : ℂ → ℂ := fun w ↦ c / (w - a) ^ k with hpoledef
  have hpole (w : ℂ) (hw : w ≠ a) : AnalyticAt ℂ pole w :=
    analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow k)
      (pow_ne_zero k (sub_ne_zero.2 hw))
  -- Off `a`, `y` is the logarithmic variation of `c / (z - a)^k + η`.
  have hoff (z : ℂ) (hza : z ≠ a) : gaugeFixedOperator x y z = 0 := by
    have hrep : y =ᶠ[𝓝 z] logVariation x (pole + η) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hza] with w hw
      have hpw := (hpole w hw).differentiableAt
      rw [logVariation_add_apply x (hpw.restrictScalars ℝ) (hη2.differentiable (by simp) w),
        hydef, Pi.add_apply, add_comm]
      congr 1
      refine (apply_eq_of_sectionValue_eq ?_ ?_ ?_).symm
      · simp [logVariation_apply_zero_of_differentiableAt x hpw, sectionField]
      · simp [logVariation_apply_one_of_differentiableAt x hpw, sectionField]
      · rw [sectionValue_logVariation, sectionValue_sectionField, hαq w, hpoledef]
        field_simp [pow_ne_zero k (sub_ne_zero.2 hw)]
    rw [gaugeFixedOperator_congr_nhds x hrep]
    have hp2 : ContDiffAt ℝ 2 pole z := ((hpole z hza).contDiffAt).restrict_scalars ℝ
    refine (gaugeFixedOperator_logVariation_eq_zero_iff (hx.differentiable (by simp) z)
      (hp2.add hη2.contDiffAt) (hhol z).1 (hhol z).2).2 ?_
    have hΔ : Δ (fun w ↦ pole w + η w) z = Δ pole z + Δ η z := hp2.laplacian_add hη2.contDiffAt
    rw [hΔ, (hpole z hza).harmonicAt.2.eq_of_nhds, Pi.zero_apply, zero_add, heq z hza]
  -- At `a`, by continuity of `L_x y`.
  have hcont : Continuous (gaugeFixedOperator x y) :=
    continuous_gaugeFixedOperator hx.continuous hy
  exact congrFun (hcont.ext_on (dense_compl_singleton a) continuous_const fun w hw ↦ hoff w hw) z

/-- The logarithmic variation of a `C¹` function `h` whose real and imaginary parts lie in `H²(ℂ)`
is square integrable at a field whose section components are bounded. -/
private theorem memLp_logVariation {M : ℝ} (hM : ∀ z, |x z 2| ≤ M ∧ |x z 3| ≤ M)
    (hx₂ : Continuous fun z ↦ x z 2) (hx₃ : Continuous fun z ↦ x z 3) {h : ℂ → ℂ}
    (hh : ContDiff ℝ 1 h) (hs₁ : (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2)
    (hs₂ : (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2) :
    MemLp (logVariation x h) 2 volume := by
  have hd {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w) (hs : w ∈ realSobolevFunctions ℂ 2 2) (v : ℂ) :
      MemLp (fun z ↦ fderiv ℝ w z v) 2 volume :=
    memLp_of_mem_realSobolevFunctions (fderiv_apply_mem_realSobolevFunctions (by norm_num)
      (by norm_num) zero_le_one hw (by norm_num [hs]) v)
  have hL {w u : ℂ → ℝ} (hu : Continuous u) (hMu : ∀ z, |u z| ≤ M)
      (hs : w ∈ realSobolevFunctions ℂ 2 2) : MemLp (fun z ↦ u z * w z) 2 volume := by
    have hw := memLp_of_mem_realSobolevFunctions hs
    refine (hw.const_mul M).of_le (hu.aestronglyMeasurable.mul hw.aestronglyMeasurable)
      (.of_forall fun z ↦ ?_)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMu z)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hMu z) (norm_nonneg _)
  have hw₁ : ContDiff ℝ 1 fun z ↦ (h z).re := reCLM.contDiff.comp hh
  have hw₂ : ContDiff ℝ 1 fun z ↦ (h z).im := imCLM.contDiff.comp hh
  refine memLp_piLp_iff.2 fun i ↦ ?_
  fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    logVariation_apply_zero, logVariation_apply_one, logVariation_apply_two,
    logVariation_apply_three]
  · simpa [Pi.sub_def, Pi.neg_def] using ((hd hw₂ hs₂ 1).neg).sub (hd hw₁ hs₁ I)
  · simpa [Pi.sub_def] using (hd hw₁ hs₁ 1).sub (hd hw₂ hs₂ I)
  · simpa [Pi.sub_def] using (hL hx₂ (fun z ↦ (hM z).1) hs₁).sub (hL hx₃ (fun z ↦ (hM z).2) hs₂)
  · simpa [Pi.add_def] using (hL hx₂ (fun z ↦ (hM z).1) hs₂).add (hL hx₃ (fun z ↦ (hM z).2) hs₁)

/-- **Smooth solutions of `-Δh + P h = g` in `H²`.** At a smooth field whose section has unit
modulus at infinity, for `g` smooth with compact support the equation `Δh = P h - g`,
`P = |α|² / 4`, has a smooth solution whose real and imaginary parts lie in `H²(ℂ)`: solve it
weakly in `H²` (`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`)
and pass to the classical representatives. -/
private theorem exists_contDiff_laplacian_eq_mul_sub (hx : ContDiff ℝ ∞ x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, Δ h z = ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * h z - g z := by
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 with hPdef
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  have hPs : ContDiff ℝ ∞ P := ((hxi 2).pow 2).add ((hxi 3).pow 2)
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  have hPt : MemLp P ⊤ volume := memLp_top_potential hx.continuous hlim
  have hP₀ : ∀ᵐ z ∂volume, 0 ≤ P z := ae_of_all _ fun z ↦ by positivity
  have hPa : ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → 1 / 8 ≤ P z :=
    ae_of_all _ fun z hz ↦ (hR z hz).le
  obtain ⟨h₁, hh₁, hw₁⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hPt hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hg2.re
  obtain ⟨h₂, hh₂, hw₂⟩ := exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq
    hPt hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hg2.im
  obtain ⟨w₁, hw₁s, hhw₁, hΔw₁⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq
      (k := ⊤) le_top hPs (g := fun z ↦ (g z).re) (reCLM.contDiff.comp hg) one_lt_two hh₁
      (by simpa only [RCLike.re_to_complex] using hw₁)
  obtain ⟨w₂, hw₂s, hhw₂, hΔw₂⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq
      (k := ⊤) le_top hPs (g := fun z ↦ (g z).im) (imCLM.contDiff.comp hg) one_lt_two hh₂
      (by simpa only [RCLike.im_to_complex] using hw₂)
  set h : ℂ → ℂ := fun z ↦ (w₁ z : ℂ) + w₂ z * I with hhdef
  have hre : (fun w ↦ (h w).re) = w₁ := funext fun w ↦ by simp [hhdef]
  have him : (fun w ↦ (h w).im) = w₂ := funext fun w ↦ by simp [hhdef]
  have hhs : ContDiff ℝ ∞ h :=
    (ofRealCLM.contDiff.comp (hw₁s.of_le le_self_add)).add
      ((ofRealCLM.contDiff.comp (hw₂s.of_le le_self_add)).mul contDiff_const)
  refine ⟨h, hhs, hre ▸ mem_realSobolevFunctions_of_ae_eq hh₁ hhw₁,
    him ▸ mem_realSobolevFunctions_of_ae_eq hh₂ hhw₂, fun z ↦ ?_⟩
  have h2 : ContDiffAt ℝ 2 h z := (hhs.of_le (by simp)).contDiffAt
  apply Complex.ext
  · have e : (Δ h z).re = Δ (fun w ↦ (h w).re) z :=
      (h2.laplacian_CLM_comp_left (l := reCLM)).symm
    rw [e, hre, hΔw₁ z]
    simp [hhdef, hPdef, pow_two]
  · have e : (Δ h z).im = Δ (fun w ↦ (h w).im) z :=
      (h2.laplacian_CLM_comp_left (l := imCLM)).symm
    rw [e, him, hΔw₂ z]
    simp [hhdef, hPdef, pow_two]

/-- **Smooth zero modes of a plane vortex with a prescribed principal part.** Let `x` be a smooth
field satisfying the holomorphicity rows `∂bar_a α = 0` of the vortex equation, whose section has
unit modulus at infinity, and suppose that `α` vanishes to order `k` at `a`:
`α = (z - a)^k β` near `a`, with `β` smooth at `a`. Then for every `c ∈ ℂ` there is a smooth
square-integrable field `y` in the kernel of the gauge-fixed operator, `L_x y = 0` everywhere,
whose section variation is

`δα = α (c / (z - a)^k + η)` off `a`,

with `η` smooth on the whole plane. So `δα / α` has principal part `c / (z - a)^k` at `a` and no
singular part at the other zeros of `α`. -/
theorem exists_gaugeFixedOperator_eq_zero_of_sectionValue_eq_pow_mul (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {a : ℂ} {k : ℕ} {β : ℂ → ℂ} (hβ : ContDiffAt ℝ ∞ β a)
    (hαβ : ∀ᶠ z in 𝓝 a, sectionValue x z = (z - a) ^ k * β z) (c : ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ∃ η : ℂ → ℂ, ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ z, gaugeFixedOperator x y z = 0) ∧ ContDiff ℝ ∞ η ∧
      ∀ z, z ≠ a → sectionValue y z = sectionValue x z * (c / (z - a) ^ k + η z) := by
  obtain ⟨q, hq, hαq⟩ := exists_contDiff_forall_sectionValue_eq_pow_mul hx hβ hαβ
  set P : ℂ → ℝ := fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 with hPdef
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  have hα : ContDiff ℝ ∞ (sectionValue x) := contDiff_sectionValue (hxi 2) (hxi 3)
  -- A cutoff `ρ` equal to one near `a`. The principal part `ρ c / (z - a)^k` differs from
  -- `c / (z - a)^k` by the smooth function `χ = (ρ - 1) c / (z - a)^k`.
  let b : ContDiffBump a := ⟨1, 2, one_pos, one_lt_two⟩
  set ρ : ℂ → ℝ := ⇑b
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff
  have hρc : HasCompactSupport ρ := b.hasCompactSupport
  have hρa : ρ =ᶠ[𝓝 a] 1 := b.eventuallyEq_one
  have haρ : a ∈ tsupport ρ := subset_tsupport _ (by simp [hρa.self_of_nhds])
  have hpow (z : ℂ) (hz : z ≠ a) : (z - a) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.2 hz)
  have hpole (z : ℂ) (hz : z ≠ a) : AnalyticAt ℂ (fun w ↦ c / (w - a) ^ k) z :=
    analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow k) (hpow z hz)
  set χ : ℂ → ℂ := fun z ↦ ((ρ z - 1 : ℝ) : ℂ) * (c / (z - a) ^ k) with hχdef
  have hχ : ContDiff ℝ ∞ χ := by
    refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    rcases eq_or_ne z a with rfl | hza
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hρa] with w hw
      simp [hχdef, hw]
    · exact (ofRealCLM.contDiff.comp (hρ.sub contDiff_const)).contDiffAt.mul
        ((hpole z hza).contDiffAt.restrict_scalars ℝ)
  -- Outside the support of `ρ`, `χ` is minus the principal part, which is holomorphic.
  have hne (z : ℂ) (hz : z ∉ tsupport ρ) : z ≠ a := fun h ↦ hz (h ▸ haρ)
  have hχout (z : ℂ) (hz : z ∉ tsupport ρ) : χ =ᶠ[𝓝 z] fun w ↦ -(c / (w - a) ^ k) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with w hw
    simp [hχdef, hw]
  have hχan (z : ℂ) (hz : z ∉ tsupport ρ) : AnalyticAt ℂ (fun w ↦ -(c / (w - a) ^ k)) z :=
    (hpole z (hne z hz)).neg
  -- The right side `g = Δχ - ρ c (conj α) q / 4` of the equation `-Δh + P h = g` for the
  -- square-integrable part `h`. It is smooth with compact support.
  set g : ℂ → ℂ := fun z ↦ Δ χ z - (ρ z : ℂ) * c * starRingEnd ℂ (sectionValue x z) * q z / 4
    with hgdef
  have hg : ContDiff ℝ ∞ g := by
    refine (hχ.laplacian (by simp)).sub (ContDiff.div_const ?_ _)
    exact ((ofRealCLM.contDiff.comp hρ).mul contDiff_const).mul (conjCLE.contDiff.comp hα)
      |>.mul hq
  have hgc : HasCompactSupport g := HasCompactSupport.intro hρc fun z hz ↦ by
    have hΔ : Δ χ z = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds (hχout z hz)).eq_of_nhds]
      exact (hχan z hz).harmonicAt.2.eq_of_nhds
    simp [hgdef, hΔ, image_eq_zero_of_notMem_tsupport hz]
  -- Solve `-Δh + P h = g` with `h` smooth and its real and imaginary parts in `H²`.
  obtain ⟨h, hhs, hh₁, hh₂, hΔh⟩ := exists_contDiff_laplacian_eq_mul_sub hx hlim hg hgc
  -- The regular part `η = χ + h` makes `c / (z - a)^k + η = ρ c / (z - a)^k + h` a solution of
  -- `Δη = P η` off `a`.
  set η : ℂ → ℂ := χ + h with hηdef
  have hη : ContDiff ℝ ∞ η := hχ.add hhs
  have heq (z : ℂ) (hz : z ≠ a) : Δ η z = P z • (c / (z - a) ^ k + η z) := by
    rw [hηdef, (hχ.of_le (by simp)).contDiffAt.laplacian_add (hhs.of_le (by simp)).contDiffAt,
      hΔh z]
    have hPα : ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) =
        starRingEnd ℂ (sectionValue x z) * sectionValue x z / 4 := by
      rw [sectionValue_apply]
      apply Complex.ext <;> simp [pow_two] <;> ring
    have hq' : q z = sectionValue x z / (z - a) ^ k := by
      rw [hαq z, mul_div_cancel_left₀ _ (hpow z hz)]
    simp only [hgdef, hχdef, hPdef, Pi.add_apply, Complex.real_smul, hPα]
    push_cast
    linear_combination (↑(ρ z) * c * starRingEnd ℂ (sectionValue x z) / 4) * hq'
  refine ⟨logVariation x η + sectionField fun w ↦ c * q w, η,
    (contDiff_logVariation hx (hη.of_le (by simp))).add
      (contDiff_sectionField (contDiff_const.mul hq)), ?_,
    gaugeFixedOperator_logVariation_add_sectionField_eq_zero hx hhol hq hαq hη heq, hη,
    fun z hz ↦ sectionValue_logVariation_add_sectionField hαq η hz⟩
  -- Square integrability: `y` is the logarithmic variation of `h ∈ H²` plus a smooth field
  -- vanishing outside the support of `ρ`.
  have hsplit : logVariation x η + (sectionField fun w ↦ c * q w) =
      (logVariation x χ + sectionField fun w ↦ c * q w) + logVariation x h := by
    rw [hηdef, logVariation_add x (hχ.differentiable (by simp)) (hhs.differentiable (by simp))]
    abel
  rw [hsplit]
  refine MemLp.add ?_ ?_
  · have hT : ContDiff ℝ ∞ (logVariation x χ + sectionField fun w ↦ c * q w) :=
      (contDiff_logVariation hx (hχ.of_le (by simp))).add
        (contDiff_sectionField (contDiff_const.mul hq))
    refine hT.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hρc fun z hz ↦ ?_)
    have hdχ : DifferentiableAt ℂ χ z :=
      (hχan z hz).differentiableAt.congr_of_eventuallyEq (hχout z hz)
    refine apply_eq_of_sectionValue_eq (y := 0) ?_ ?_ ?_
    · simp [logVariation_apply_zero_of_differentiableAt x hdχ, sectionField]
    · simp [logVariation_apply_one_of_differentiableAt x hdχ, sectionField]
    · rw [sectionValue_add, sectionValue_logVariation, sectionValue_sectionField, hαq z]
      simp only [hχdef, image_eq_zero_of_notMem_tsupport hz]
      field_simp [hpow z (hne z hz)]
      simp [sectionValue_apply]
  · obtain ⟨M, hM⟩ := exists_forall_potential_le hx.continuous hlim
    refine memLp_logVariation (M := √M) (fun z ↦ ⟨Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_⟩)
      (hxi 2).continuous (hxi 3).continuous (hhs.of_le (by simp)) hh₁ hh₂
    · nlinarith [hM z, sq_nonneg (x z 3)]
    · nlinarith [hM z, sq_nonneg (x z 2)]

/-- **Smooth zero modes realizing every principal part at a zero.** Let `x` be a smooth field
satisfying the holomorphicity rows of the vortex equation, whose section has unit modulus at
infinity and zero multiplicities `n`. At a zero `a` of multiplicity `n a`, for every
`k ≤ n a` and `c ∈ ℂ` there is a smooth square-integrable field `y` with `L_x y = 0` everywhere
and section variation `δα = α (c / (z - a)^k + η)` off `a`, with `η` smooth. -/
theorem exists_gaugeFixedOperator_eq_zero_of_isZeroMultiplicity (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {n : ℂ → ℕ} (hn : IsZeroMultiplicity (sectionValue x) n) {a : ℂ} {k : ℕ} (hk : k ≤ n a)
    (c : ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ∃ η : ℂ → ℂ, ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ z, gaugeFixedOperator x y z = 0) ∧ ContDiff ℝ ∞ η ∧
      ∀ z, z ≠ a → sectionValue y z = sectionValue x z * (c / (z - a) ^ k + η z) := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  -- The section is not identically zero, since it has unit modulus at infinity.
  have hne : ∃ w, sectionValue x w ≠ 0 := by
    obtain ⟨w, hw⟩ := (hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))).exists
    refine ⟨w, fun h0 ↦ ?_⟩
    rw [sectionValue_eq_zero_iff] at h0
    linarith
  -- A smooth factorization at `a`, whose exponent is the multiplicity `n a`.
  obtain ⟨m, V, hV, hV₀, hfac⟩ := exists_contDiffAt_sectionValue_eq_pow_mul (k := ⊤) le_top
    (hxi 0) (hxi 1) ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol
    hne a
  obtain ⟨v, hv, hv₀, hfv⟩ := isZeroMultiplicity_iff.1 hn a
  obtain rfl : m = n a := eq_of_eventually_sub_pow_mul_eq hV.continuousAt hV₀ hv hv₀ <| by
    filter_upwards [hfac, hfv] with w h₁ h₂
    rw [← h₁, ← h₂]
  refine exists_gaugeFixedOperator_eq_zero_of_sectionValue_eq_pow_mul hx hhol hlim
    (β := fun w ↦ (w - a) ^ (n a - k) * V w) ((by fun_prop : ContDiffAt ℝ ∞ _ a).mul hV) ?_ c
  filter_upwards [hfac] with w hw
  rw [hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]

end Kernel

end TauCeti.Vortex
