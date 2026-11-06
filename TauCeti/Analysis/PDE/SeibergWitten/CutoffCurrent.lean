/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Analysis.Calculus.DifferentialForm.PhaseForm
public import TauCeti.Analysis.Calculus.DifferentialForm.TwistedDifferential
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Topology.Algebra.GroupWithZero.DivId

/-!
# The cutoff current of an abelian Higgs pair

Let `(a, α)` be a pair consisting of an imaginary connection form `a = i b` on a trivial
Hermitian line and a section `α`, so that the covariant derivative is `∇_a α = dα + i b α`.
Write `s = |α|²`. Away from the zeros of `α` the pair has the gauge-invariant phase form

`τ = Im (conj α ∇_a α) / s = Im (α⁻¹ dα) + b`,

whose first summand is the differential of a local branch of `arg α`. In Taubes's passage from
Seiberg–Witten solutions to pseudoholomorphic curves, `α` is the component of the rescaled
spinor along the canonical unit spinor, its zero set concentrates along the limiting curve, and
the curvature `i F_a = -db` is compared with the current of that curve through the **cutoff
current**

`Θ = i F_a + d(χ(s) τ)`,

where `χ` is a cutoff function vanishing near `0` and equal to `1` above a threshold `c`, and
`χ(s) τ` is extended by zero across the zeros of `α`. This file constructs `Θ` and proves:

* `χ(s) τ` and `Θ` are smooth (`contDiff_cutoffPhaseForm`, `contDiff_cutoffCurrent`);
* `Θ` is closed (`extDeriv_cutoffCurrent`);
* `Θ` vanishes where `s > c`, because there `dτ = db`; hence its support lies in `{s ≤ c}`
  (`tsupport_cutoffCurrent_subset`);
* `Θ` and `χ(s) τ` are invariant under gauge transformations
  `(b, α) ↦ (b - Im (u⁻¹ du), u α)` by unit-modulus functions `u`, which is how they are defined
  on a nontrivial line from local trivializations (`cutoffCurrent_sub_phaseForm_mul`);
* on a disc in the plane on whose boundary circle `χ(s) = 1`, the integral of `Θ` is the winding
  integral `∮ Im (α⁻¹ dα)` of `α`, with no contribution from `b`
  (`integral_cutoffCurrent_closedBall`). The flux of `i F_a` instead retains the boundary term
  `∮ b`.

Given an almost complex structure `J`, the cutoff phase form also has a modulus potential: with
`d^c_J f = -(1/2) df ∘ J`, `∂bar_a α = (∇_a α + i ∇_a α ∘ J) / 2` and `H` a primitive of
`χ(s) / s`,

`χ(s) τ = d^c_J H(s) + E`,  `E = 2 χ(s) Re (α⁻¹ ∂bar_a α) ∘ J`

(`cutoffPhaseForm_eq_twistedDifferential_add`). The primitive with `H(1) = 0` is
`TauCeti.SeibergWitten.modulusPotential χ` when `χ` is continuous and vanishes near `0`
(`hasDerivAt_modulusPotential`). If `χ` vanishes on `[0, c)` and `|χ| ≤ 1`, then
`|H(s)| ≤ |s - 1| / c` and `‖E‖ ≤ (2 / √c) ‖∂bar_a α‖` pointwise
(`abs_modulusPotential_le`, `norm_cutoffDBarForm_le`). Since `Θ - i F_a = d(χ(s) τ)`, its pairing
with a test form `ζ` is the pairing of `χ(s) τ = d^c_J H(s) + E` with `dζ`; after an integration
by parts in the first term, these pointwise bounds reduce that pairing to integral bounds on
`1 - |α|²` and on `∂bar_a α`. Those integral bounds and the integration by parts are not part of
this file.

The cutoff phase form, the cutoff current, their regularity, support and gauge invariance are
stated on an arbitrary real normed space, which plays the role of a coordinate chart; the gauge
invariance makes the constructions independent of the trivialization. The flux identity is
stated on the plane `ℂ`, and the modulus-potential decomposition and the bound on the correction
form on a finite-dimensional real normed space carrying an almost complex structure.

The phase form `Im (α⁻¹ dα)` (`TauCeti.phaseForm`) and the twisted differential `d^c_J`
(`TauCeti.AlmostComplexStructure.twistedDifferential`) are general constructions defined in
`TauCeti.Analysis.Calculus.DifferentialForm.PhaseForm` and
`TauCeti.Analysis.Calculus.DifferentialForm.TwistedDifferential`.

## Main definitions

* `TauCeti.SeibergWitten.covariantDeriv b α`: the covariant derivative `dα + i b α`.
* `TauCeti.SeibergWitten.covariantPhaseForm b α`: the phase form `τ = Im (α⁻¹ dα) + b`.
* `TauCeti.SeibergWitten.cutoffPhaseForm χ b α`: the one-form `χ(|α|²) τ`.
* `TauCeti.SeibergWitten.cutoffCurrent χ b α`: the two-form `Θ = -db + d(χ(|α|²) τ)`.
* `TauCeti.SeibergWitten.covariantDBar J b α`: the `J`-antilinear part `∂bar_a α`.
* `TauCeti.SeibergWitten.cutoffDBarForm J χ b α`: the one-form `2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`.
* `TauCeti.SeibergWitten.modulusPotential χ`: the integral `H(s) = ∫₁ˢ χ(t) / t dt`, a primitive of
  `χ(s) / s` when `χ` is continuous and vanishes near `0`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Set MeasureTheory
open scoped Topology ComplexConjugate Real

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α u : E → ℂ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {χ : ℝ → ℝ} {x : E}

/-! ### The covariant derivative and the covariant phase form -/

/-- The covariant derivative `∇_a α = dα + i b α` of a section `α` of the trivial line for the
imaginary connection form `a = i b`. -/
def covariantDeriv (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) : E →L[ℝ] ℂ :=
  fderiv ℝ α x + ((ofSubsingletonLIE (0 : Fin 1)).symm (b x)).smulRight (I * α x)

/-- The covariant derivative evaluated on a vector. -/
@[simp]
theorem covariantDeriv_apply (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x v : E) :
    covariantDeriv b α x v = fderiv ℝ α x v + I * b x (fun _ ↦ v) * α x := by
  simp [covariantDeriv, ofSubsingletonLIE_symm_apply]
  ring

/-- The phase form `τ = Im (α⁻¹ dα) + b` of a pair `(a, α)` with `a = i b`. Away from the zeros
of `α` it is `Im (conj α ∇_a α) / |α|²` (`covariantPhaseForm_apply_eq_div`). -/
def covariantPhaseForm (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) : E → E [⋀^Fin 1]→L[ℝ] ℝ :=
  phaseForm α + b

/-- The covariant phase form at a point is `Im (α⁻¹ dα) + b`. -/
@[simp]
theorem covariantPhaseForm_apply (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) :
    covariantPhaseForm b α x = phaseForm α x + b x := (rfl)

/-- Away from the zeros of `α`, the covariant phase form is `Im (conj α ∇_a α) / |α|²`. -/
theorem covariantPhaseForm_apply_eq_div (h : α x ≠ 0) (v : E) :
    covariantPhaseForm b α x (fun _ ↦ v) =
      (conj (α x) * covariantDeriv b α x v).im / normSq (α x) := by
  have hn := (normSq_pos.2 h).ne'
  rw [covariantPhaseForm_apply, ContinuousAlternatingMap.add_apply, phaseForm_apply,
    covariantDeriv_apply]
  simp only [add_re, add_im, mul_im, mul_re, conj_re, conj_im, ofReal_re, ofReal_im, I_re, I_im,
    inv_re, inv_im]
  field_simp
  rw [normSq_apply]
  ring

/-- The covariant phase form is invariant under gauge transformations
`(b, α) ↦ (b - Im (u⁻¹ du), u α)` at points where `α` does not vanish. -/
theorem covariantPhaseForm_sub_phaseForm_mul (hu : DifferentiableAt ℝ u x)
    (hα : DifferentiableAt ℝ α x) (hu₀ : u x ≠ 0) (hα₀ : α x ≠ 0) :
    covariantPhaseForm (b - phaseForm u) (u * α) x = covariantPhaseForm b α x := by
  rw [covariantPhaseForm_apply, covariantPhaseForm_apply, phaseForm_mul hu hα hu₀ hα₀,
    Pi.sub_apply]
  abel

/-! ### The cutoff phase form and the cutoff current -/

/-- The cutoff phase form `χ(|α|²) τ`. When `χ` vanishes near `0` this is the extension by zero
of `χ(|α|²) τ` across the zeros of `α`. -/
def cutoffPhaseForm (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) :
    E [⋀^Fin 1]→L[ℝ] ℝ :=
  χ (normSq (α x)) • covariantPhaseForm b α x

/-- The cutoff phase form at a point is `χ(|α|²) τ`. -/
@[simp]
theorem cutoffPhaseForm_apply (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) :
    cutoffPhaseForm χ b α x = χ (normSq (α x)) • covariantPhaseForm b α x := (rfl)

/-- The cutoff current `Θ = i F_a + d(χ(|α|²) τ)`, where `i F_a = -db` is `i` times the curvature
of `a = i b`. -/
def cutoffCurrent (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) :
    E → E [⋀^Fin 2]→L[ℝ] ℝ :=
  extDeriv (cutoffPhaseForm χ b α) - extDeriv b

/-- The cutoff current at a point is `d(χ(|α|²) τ) - db`. -/
theorem cutoffCurrent_apply (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) :
    cutoffCurrent χ b α x = extDeriv (cutoffPhaseForm χ b α) x - extDeriv b x := (rfl)

/-- Near a point where `χ` vanishes near `|α|²`, the cutoff phase form vanishes identically. -/
theorem cutoffPhaseForm_eventuallyEq_zero (hα : ContinuousAt α x)
    (hχ : χ =ᶠ[𝓝 (normSq (α x))] 0) : cutoffPhaseForm χ b α =ᶠ[𝓝 x] 0 := by
  filter_upwards [(continuous_normSq.continuousAt.comp hα).tendsto.eventually hχ] with y hy
  rw [Pi.zero_apply, Function.comp_apply] at hy
  simp [hy]

/-- Near a point where `χ` is `1` near `|α|²`, the cutoff phase form is the covariant phase
form. -/
theorem cutoffPhaseForm_eventuallyEq_covariantPhaseForm (hα : ContinuousAt α x)
    (hχ : χ =ᶠ[𝓝 (normSq (α x))] 1) : cutoffPhaseForm χ b α =ᶠ[𝓝 x] covariantPhaseForm b α := by
  filter_upwards [(continuous_normSq.continuousAt.comp hα).tendsto.eventually hχ] with y hy
  rw [Pi.one_apply, Function.comp_apply] at hy
  simp [hy]

/-- The cutoff phase form of a `C^(n+1)` section and a `C^n` connection form is `C^n`, for a
`C^n` cutoff vanishing near `0`. -/
theorem contDiffAt_cutoffPhaseForm {n : WithTop ℕ∞} (hα : ContDiffAt ℝ (n + 1) α x)
    (hb : ContDiffAt ℝ n b x) (hχ : ContDiff ℝ n χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) :
    ContDiffAt ℝ n (cutoffPhaseForm χ b α) x := by
  by_cases h : α x = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cutoffPhaseForm_eventuallyEq_zero hα.continuousAt (by simpa [h] using hχ₀))
  · have hs : ContDiffAt ℝ n (fun y ↦ normSq (α y)) x := by
      simp_rw [normSq_eq_norm_sq]
      exact (contDiff_norm_sq ℝ).contDiffAt.comp x (hα.of_le le_self_add)
    exact (hχ.contDiffAt.comp x hs).fun_smul ((contDiffAt_phaseForm hα h le_rfl).add hb)

/-- The cutoff phase form of a `C^(n+1)` section and a `C^n` connection form is `C^n`, for a
`C^n` cutoff vanishing near `0`. -/
theorem contDiff_cutoffPhaseForm {n : WithTop ℕ∞} (hα : ContDiff ℝ (n + 1) α)
    (hb : ContDiff ℝ n b) (hχ : ContDiff ℝ n χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) :
    ContDiff ℝ n (cutoffPhaseForm χ b α) :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    contDiffAt_cutoffPhaseForm hα.contDiffAt hb.contDiffAt hχ hχ₀

/-- The cutoff current of a `C^(n+1)` section and a `C^n` connection form is `C^m` for
`m + 1 ≤ n`, for a `C^n` cutoff vanishing near `0`. -/
theorem contDiff_cutoffCurrent {m n : WithTop ℕ∞} (hα : ContDiff ℝ (n + 1) α)
    (hb : ContDiff ℝ n b) (hχ : ContDiff ℝ n χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (cutoffCurrent χ b α) :=
  (contDiff_extDeriv (contDiff_cutoffPhaseForm hα hb hχ hχ₀) hmn).sub (contDiff_extDeriv hb hmn)

/-- The cutoff current is closed. -/
theorem extDeriv_cutoffCurrent (hα : ContDiff ℝ 3 α) (hb : ContDiff ℝ 2 b) (hχ : ContDiff ℝ 2 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) : extDeriv (cutoffCurrent χ b α) = 0 := by
  have hτ : ContDiff ℝ 2 (cutoffPhaseForm χ b α) := contDiff_cutoffPhaseForm hα hb hχ hχ₀
  funext x
  rw [cutoffCurrent, extDeriv_sub
      ((contDiff_extDeriv hτ le_rfl).differentiable one_ne_zero x)
      ((contDiff_extDeriv hb le_rfl).differentiable one_ne_zero x),
    extDeriv_extDeriv_apply hτ.contDiffAt (by simp),
    extDeriv_extDeriv_apply hb.contDiffAt (by simp), sub_zero, Pi.zero_apply]

/-- The cutoff current vanishes at a point `x` with `α x ≠ 0` where `χ` is `1` near `|α x|²`:
there `d(χ(|α|²) τ) = dτ = db`. -/
theorem cutoffCurrent_eq_zero (hα : ContDiffAt ℝ 2 α x) (h : α x ≠ 0)
    (hb : DifferentiableAt ℝ b x) (hχ : χ =ᶠ[𝓝 (normSq (α x))] 1) :
    cutoffCurrent χ b α x = 0 := by
  rw [cutoffCurrent_apply,
    (cutoffPhaseForm_eventuallyEq_covariantPhaseForm hα.continuousAt hχ).extDeriv_eq,
    covariantPhaseForm,
    extDeriv_add ((contDiffAt_phaseForm hα h le_rfl).differentiableAt one_ne_zero) hb,
    extDeriv_phaseForm hα h, zero_add, sub_self]

/-- **Support of the cutoff current.** If `χ = 1` on `(c, ∞)` with `c ≥ 0`, the cutoff current is
supported in `{|α|² ≤ c}`. -/
theorem tsupport_cutoffCurrent_subset {c : ℝ} (hc : 0 ≤ c) (hα : ContDiff ℝ 2 α)
    (hb : Differentiable ℝ b) (hχ : EqOn χ 1 (Ioi c)) :
    tsupport (cutoffCurrent χ b α) ⊆ {x | normSq (α x) ≤ c} := by
  refine closure_minimal (fun x hx ↦ ?_)
    (isClosed_le (continuous_normSq.comp hα.continuous) continuous_const)
  by_contra hlt
  have hlt : c < normSq (α x) := not_le.1 hlt
  have h₀ : α x ≠ 0 := by
    rintro h
    rw [h, normSq_zero] at hlt
    exact hlt.not_ge hc
  exact hx (cutoffCurrent_eq_zero hα.contDiffAt h₀ (hb x)
    (eventuallyEq_of_mem (Ioi_mem_nhds hlt) hχ))

/-! ### Gauge invariance -/

/-- **Gauge invariance of the cutoff phase form** under `(b, α) ↦ (b - Im (u⁻¹ du), u α)` for a
differentiable `u` of unit modulus. -/
theorem cutoffPhaseForm_sub_phaseForm_mul (hu : ∀ y, ‖u y‖ = 1) (hud : Differentiable ℝ u)
    (hα : Differentiable ℝ α) (hχ : χ 0 = 0) :
    cutoffPhaseForm χ (b - phaseForm u) (u * α) = cutoffPhaseForm χ b α := by
  funext y
  have hs : normSq ((u * α) y) = normSq (α y) := by
    rw [Pi.mul_apply, map_mul, normSq_eq_norm_sq (u y), hu y, one_pow, one_mul]
  rw [cutoffPhaseForm_apply, cutoffPhaseForm_apply, hs]
  by_cases h : α y = 0
  · simp [h, hχ]
  · rw [covariantPhaseForm_sub_phaseForm_mul (hud y) (hα y) (norm_ne_zero_iff.1 (by simp [hu y])) h]

/-- **Gauge invariance of the cutoff current** under `(b, α) ↦ (b - Im (u⁻¹ du), u α)` for a `C²`
function `u` of unit modulus. -/
theorem cutoffCurrent_sub_phaseForm_mul (hu : ∀ y, ‖u y‖ = 1) (hu₂ : ContDiff ℝ 2 u)
    (hα : Differentiable ℝ α) (hb : Differentiable ℝ b) (hχ : χ 0 = 0) :
    cutoffCurrent χ (b - phaseForm u) (u * α) = cutoffCurrent χ b α := by
  funext y
  have hu₀ : u y ≠ 0 := norm_ne_zero_iff.1 (by simp [hu y])
  rw [cutoffCurrent_apply, cutoffCurrent_apply, cutoffPhaseForm_sub_phaseForm_mul hu
      (hu₂.differentiable two_ne_zero) hα hχ,
    extDeriv_sub (hb y)
      ((contDiffAt_phaseForm hu₂.contDiffAt hu₀ le_rfl).differentiableAt one_ne_zero),
    extDeriv_phaseForm hu₂.contDiffAt hu₀, sub_zero]

/-! ### The flux through a disc -/

/-- **The flux of the cutoff current through a disc.** For fields on the plane such that
`χ(|α|²) = 1` on the boundary circle of a closed disc, the integral of the cutoff current over
the disc is the winding integral `∮ Im (α⁻¹ dα)` of `α` around the circle; the connection form
does not contribute. -/
theorem integral_cutoffCurrent_closedBall {α : ℂ → ℂ} {b : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} {z₀ : ℂ}
    {r : ℝ} (hr : 0 ≤ r) (hα : ContDiff ℝ 2 α) (hb : ContDiff ℝ 1 b) (hχ : ContDiff ℝ 1 χ)
    (hχ₀ : χ =ᶠ[𝓝 0] 0) (hbd : ∀ θ, χ (normSq (α (circleMap z₀ r θ))) = 1) :
    (∫ z in Metric.closedBall z₀ r, cutoffCurrent χ b α z ![1, I]) =
      ∫ θ in -π..π, phaseForm α (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I) := by
  have hτ : ContDiff ℝ 1 (cutoffPhaseForm χ b α) := contDiff_cutoffPhaseForm hα hb hχ hχ₀
  -- The two exterior derivatives are continuous, hence integrable on the closed disc.
  have hint {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} (hω : ContDiff ℝ 1 ω) :
      IntegrableOn (fun z ↦ extDeriv ω z ![1, I]) (Metric.closedBall z₀ r) :=
    (continuousOn_of_forall_continuousAt fun z _ ↦ continuousAt_extDeriv_apply hω.contDiffAt _
      ).integrableOn_compact (isCompact_closedBall z₀ r)
  -- The boundary integrands are continuous along the circle.
  have hcirc {ω : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℝ} (hω : Continuous ω) :
      IntervalIntegrable (fun θ ↦ ω (circleMap z₀ r θ) (fun _ ↦ circleMap 0 r θ * I))
        volume (-π) π :=
    ((hω.comp (continuous_circleMap z₀ r)).eval
      (continuous_pi fun _ ↦ (continuous_circleMap 0 r).mul continuous_const)).intervalIntegrable
      _ _
  simp_rw [cutoffCurrent_apply, ContinuousAlternatingMap.sub_apply]
  rw [integral_sub (hint hτ) (hint hb),
    integral_extDeriv_closedBall hr fun z _ ↦ hτ.contDiffAt,
    integral_extDeriv_closedBall hr fun z _ ↦ hb.contDiffAt,
    ← intervalIntegral.integral_sub (hcirc hτ.continuous) (hcirc hb.continuous)]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp [hbd θ]

/-! ### The modulus potential -/

/-- The modulus potential `H(s) = ∫₁ˢ χ(t) / t dt`, normalized by `H(1) = 0`. When `χ` is
continuous and vanishes near `0` it is a primitive of `χ(s) / s`
(`hasDerivAt_modulusPotential`). -/
def modulusPotential (χ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..s, χ t / t

/-- The modulus potential vanishes at `1`. -/
@[simp]
theorem modulusPotential_one (χ : ℝ → ℝ) : modulusPotential χ 1 = 0 :=
  intervalIntegral.integral_same

/-- The modulus potential is a primitive of `χ(s) / s` on all of `ℝ`, for a continuous cutoff
vanishing near `0`. At `s = 0` the derivative is `0`, which is `χ(0) / 0` in Lean. -/
theorem hasDerivAt_modulusPotential (hχ : Continuous χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) (s : ℝ) :
    HasDerivAt (modulusPotential χ) (χ s / s) s :=
  let hcont := hχ.div_id_of_eventuallyEq_zero hχ₀
  intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

/-- The modulus potential is constant near `0`, for a continuous cutoff vanishing near `0`. -/
theorem modulusPotential_eventuallyEq (hχ : Continuous χ) (hχ₀ : χ =ᶠ[𝓝 0] 0) :
    modulusPotential χ =ᶠ[𝓝 0] fun _ ↦ modulusPotential χ 0 := by
  obtain ⟨ε, hε, hzero⟩ := (nhds_basis_Ioo_pos (0 : ℝ)).eventually_iff.1 hχ₀
  rw [zero_sub, zero_add] at hzero
  have hcont := hχ.div_id_of_eventuallyEq_zero hχ₀
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hε) hε] with s hs
  have hsub : uIcc 0 s ⊆ Ioo (-ε) ε := ordConnected_Ioo.uIcc_subset ⟨by linarith, hε⟩ hs
  have h0s : (∫ t in (0 : ℝ)..s, χ t / t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ by
      simp [hzero (hsub ht)]]
    exact intervalIntegral.integral_zero
  rw [modulusPotential, modulusPotential,
    ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), h0s, add_zero]

/-- **Pointwise bound on the modulus potential.** If `χ` vanishes on `(0, c)` and `|χ| ≤ 1`, then
`|H(s)| ≤ |s - 1| / c` for `s ≥ 0`. -/
theorem abs_modulusPotential_le {c : ℝ} (hc : 0 < c) (hχc : ∀ t, 0 < t → t < c → χ t = 0)
    (hχ₁ : ∀ t, |χ t| ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    |modulusPotential χ s| ≤ |s - 1| / c := by
  rw [div_eq_inv_mul, modulusPotential, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
  have ht₀ : 0 < t := (le_inf zero_le_one hs).trans_lt ht.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht₀]
  rcases lt_or_ge t c with htc | htc
  · rw [hχc t ht₀ htc, abs_zero, zero_div]
    exact inv_nonneg.2 hc.le
  · calc |χ t| / t ≤ 1 / t := div_le_div_of_nonneg_right (hχ₁ t) ht₀.le
      _ ≤ 1 / c := one_div_le_one_div_of_le hc htc
      _ = c⁻¹ := one_div c

/-! ### The modulus-potential decomposition of the cutoff phase form -/

section AlmostComplex

variable [FiniteDimensional ℝ E] (J : AlmostComplexStructure E)

/-- The `J`-antilinear part `∂bar_a α = (∇_a α + i ∇_a α ∘ J) / 2` of the covariant derivative. -/
def covariantDBar (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) : E →L[ℝ] ℂ :=
  (2⁻¹ : ℂ) • (covariantDeriv b α x +
    I • (covariantDeriv b α x).comp (LinearMap.toContinuousLinearMap J.toLinearMap))

/-- `∂bar_a α` evaluated on a vector. -/
@[simp]
theorem covariantDBar_apply (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x v : E) :
    covariantDBar J b α x v = (covariantDeriv b α x v + I * covariantDeriv b α x (J v)) / 2 := by
  simp [covariantDBar, div_eq_inv_mul, mul_add]

/-- `∂bar_a α` is the complex-antilinear part `TauCeti.complexAntilinearPart` of `∇_a α`, for the
structure `J` on `E` and multiplication by `I` on `ℂ`. -/
theorem coe_covariantDBar_eq_complexAntilinearPart (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ)
    (x : E) :
    ⇑(covariantDBar J b α x) =
      complexAntilinearPart J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ I)
        (covariantDeriv b α x : E →ₗ[ℝ] ℂ) := by
  ext v
  simp only [covariantDBar_apply, complexAntilinearPart_apply, ContinuousLinearMap.coe_coe,
    DistribSMul.toLinearMap_apply, smul_eq_mul, real_smul, ofReal_inv, ofReal_ofNat]
  ring

/-- `∂bar_a α` is `J`-antilinear: `∂bar_a α (J v) = -i ∂bar_a α v`. -/
theorem covariantDBar_apply_apply (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x v : E) :
    covariantDBar J b α x (J v) = -I * covariantDBar J b α x v := by
  have hI : DistribSMul.toLinearMap ℝ ℂ I ∘ₗ DistribSMul.toLinearMap ℝ ℂ I = -LinearMap.id := by
    ext z
    simp [← mul_assoc]
  have h := (complexAntilinearPart_isComplexAntilinear J.square_neg hI
    (covariantDeriv b α x : E →ₗ[ℝ] ℂ)).apply v
  rw [← coe_covariantDBar_eq_complexAntilinearPart, DistribSMul.toLinearMap_apply] at h
  rw [h, smul_eq_mul, neg_mul]

/-- The correction one-form `E = 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J`. -/
def cutoffDBarForm (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) :
    E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1) ((2 * χ (normSq (α x))) •
    (reCLM.comp ((α x)⁻¹ • covariantDBar J b α x)).comp
      (LinearMap.toContinuousLinearMap J.toLinearMap))

/-- The correction form evaluated on a vector. -/
@[simp]
theorem cutoffDBarForm_apply (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E)
    (v : Fin 1 → E) :
    cutoffDBarForm J χ b α x v =
      2 * χ (normSq (α x)) * ((α x)⁻¹ * covariantDBar J b α x (J (v 0))).re := by
  simp [cutoffDBarForm]

/-- Since `∂bar_a α` is `J`-antilinear, `E = 2 χ(|α|²) Im (α⁻¹ ∂bar_a α)`. -/
theorem cutoffDBarForm_apply_eq_im (χ : ℝ → ℝ) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ)
    (x : E) (v : Fin 1 → E) :
    cutoffDBarForm J χ b α x v =
      2 * χ (normSq (α x)) * ((α x)⁻¹ * covariantDBar J b α x (v 0)).im := by
  rw [cutoffDBarForm_apply, covariantDBar_apply_apply]
  congr 1
  simp only [mul_re, mul_im, neg_re, neg_im, I_re, I_im]
  ring

/-- **The modulus-potential decomposition.** If `χ(0) = 0` and `H` has derivative `χ(s) / s` at
`s = |α x|²`, then `χ(|α|²) τ = d^c_J H(|α|²) + 2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J` at `x`. The modulus
potential `TauCeti.SeibergWitten.modulusPotential χ` has this derivative at every `s` when `χ` is
continuous and vanishes near `0` (`TauCeti.SeibergWitten.hasDerivAt_modulusPotential`). -/
theorem cutoffPhaseForm_eq_twistedDifferential_add {H : ℝ → ℝ}
    (hH : HasDerivAt H (χ (normSq (α x)) / normSq (α x)) (normSq (α x))) (hχ : χ 0 = 0)
    (hα : DifferentiableAt ℝ α x) :
    cutoffPhaseForm χ b α x =
      J.twistedDifferential (fun y ↦ H (normSq (α y))) x + cutoffDBarForm J χ b α x := by
  -- The derivative of `|α|²` is `2 Re (conj α dα)`.
  have hd : HasFDerivAt (fun y ↦ normSq (α y))
      (2 • (innerSL ℝ (α x)).comp (fderiv ℝ α x)) x := by
    simp_rw [normSq_eq_norm_sq]
    exact hα.hasFDerivAt.norm_sq
  have hc := J.twistedDifferential_comp hH hd.differentiableAt
  rw [Function.comp_def] at hc
  rw [hc]
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = fun _ ↦ w := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  simp only [ContinuousAlternatingMap.add_apply, J.twistedDifferential_apply, cutoffDBarForm_apply,
    hd.fderiv, covariantDBar_apply, J.apply_apply, map_neg, cutoffPhaseForm_apply,
    ContinuousAlternatingMap.smul_apply, covariantPhaseForm_apply, phaseForm_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.inner,
    covariantDeriv_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : α x = 0
  · simp [h, hχ]
  · have hn := (normSq_pos.2 h).ne'
    simp only [mul_re, mul_im, add_re, add_im, neg_re, neg_im, conj_re, conj_im, ofReal_re,
      ofReal_im, I_re, I_im, div_ofNat_re, div_ofNat_im, inv_re, inv_im]
    field_simp
    rw [normSq_apply]
    ring

/-- **Pointwise bound on the correction form.** If `χ` vanishes on `[0, c)` and `|χ| ≤ 1`, then
`‖2 χ(|α|²) Re (α⁻¹ ∂bar_a α) ∘ J‖ ≤ (2 / √c) ‖∂bar_a α‖`. -/
theorem norm_cutoffDBarForm_le {c : ℝ} (hc : 0 < c) (hχc : ∀ t, 0 ≤ t → t < c → χ t = 0)
    (hχ₁ : ∀ t, |χ t| ≤ 1) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α : E → ℂ) (x : E) :
    ‖cutoffDBarForm J χ b α x‖ ≤ 2 / √c * ‖covariantDBar J b α x‖ := by
  have hB : 0 ≤ 2 / √c * ‖covariantDBar J b α x‖ := by positivity
  refine (cutoffDBarForm J χ b α x).opNorm_le_bound hB fun v ↦ ?_
  rw [Fin.prod_univ_one, cutoffDBarForm_apply_eq_im, Real.norm_eq_abs]
  rcases lt_or_ge (normSq (α x)) c with hlt | hge
  · rw [hχc _ (normSq_nonneg _) hlt]
    simp only [mul_zero, zero_mul, abs_zero]
    positivity
  · have hα : √c ≤ ‖α x‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (α x)), ← normSq_eq_norm_sq]
      exact Real.sqrt_le_sqrt hge
    have hsc : 0 < √c := Real.sqrt_pos.2 hc
    have hα₀ : 0 < ‖α x‖ := hsc.trans_le hα
    calc |2 * χ (normSq (α x)) * ((α x)⁻¹ * covariantDBar J b α x (v 0)).im|
        ≤ 2 * 1 * (‖α x‖⁻¹ * (‖covariantDBar J b α x‖ * ‖v 0‖)) := by
          rw [abs_mul, abs_mul, abs_two]
          gcongr
          · exact hχ₁ _
          · refine (abs_im_le_norm _).trans ?_
            rw [norm_mul, norm_inv]
            gcongr
            exact (covariantDBar J b α x).le_opNorm (v 0)
      _ ≤ 2 / √c * ‖covariantDBar J b α x‖ * ‖v 0‖ := by
          have hinv := inv_anti₀ hsc hα
          have hD := mul_nonneg (norm_nonneg (covariantDBar J b α x)) (norm_nonneg (v 0))
          rw [mul_one, div_eq_mul_inv]
          nlinarith

end AlmostComplex

end TauCeti.SeibergWitten
