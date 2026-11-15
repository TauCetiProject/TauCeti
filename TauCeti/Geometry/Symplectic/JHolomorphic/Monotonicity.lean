/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Monotonicity of area for holomorphic curves

Let `u` be a holomorphic map from an open set `U ⊆ ℂ` to a complex Hilbert space `E`, a
holomorphic curve for the standard complex structure. Its energy density `‖∂ₛu‖²`, its area
density and the density of `u^*ω` all equal `‖u'‖²`, so the area of the part of the curve inside
the ball `B(c, s)` is

`A(s) = ∫_{U ∩ u⁻¹(B(c, s))} ‖u'‖²`.

When `U ∩ u⁻¹(closedBall c r)` is compact, the curve has no boundary inside `B(c, r)`, and this
file proves:

* the **monotonicity formula**: `A(s) / s²` is nondecreasing on `(0, r]`
  (`TauCeti.monotoneOn_setIntegral_norm_deriv_sq_div_sq`);
* the **monotonicity lower bound**: if `c = u z₀` and `u` is not constant near `z₀`, then
  `π r² ≤ A(r)` (`TauCeti.pi_mul_sq_le_setIntegral_norm_deriv_sq`). This holds also when `z₀` is a
  critical point of `u`.

The lower bound is the area estimate in Gromov's proof of the nonsqueezing theorem: a holomorphic
curve passing through the centre of the standard ball of radius `r`, without boundary inside the
ball, has area at least `π r²` there. The bound is sharp, with equality for a complex line through
the centre.

## Proof

Put `ρ = ‖u - c‖²` and `q = ⟪u - c, u'⟫`. For a `C¹` function `χ` vanishing on `[r², ∞)`, the
function `χ(ρ) q` has compact support, and its antiholomorphic derivative `(∂ₓ + i ∂_y) / 2` is
`χ'(ρ) |q|² + χ(ρ) ‖u'‖²`, so the integral of the latter vanishes. With the Cauchy–Schwarz
inequality `|q|² ≤ ρ ‖u'‖²`, a nonincreasing `χ` gives `∫ (t χ(t))'|_{t = ρ} ‖u'‖² ≤ 0`.
For `t χ(t) = Φ(t / ε²) - Φ(t / r²)`, where `Φ` is an antiderivative of a nonincreasing profile `φ`
equal to `0` on `[1, ∞)`, this says that `ε⁻² ∫ φ(ρ / ε²) ‖u'‖²` is nondecreasing in `ε`; letting
`φ` increase to the indicator of `(-∞, 1)` gives the monotonicity formula. Near an immersed point
`z₀` the curve covers a disc of area close to `π ε²` in the ball of radius `ε`, so the monotonicity
formula gives the lower bound. At a critical point, compare instead with balls about the images of
nearby immersed points.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347 (monotonicity and the nonsqueezing theorem).
* L. Simon, *Lectures on geometric measure theory*, Proc. Centre Math. Anal. Austral. Nat. Univ.
  **3** (1983), §17 (the monotonicity formula, proved with test functions of `|x|² / ε²`).
* J.-P. Demailly, *Complex analytic and differential geometry*, Chapter III (Lelong numbers:
  monotonicity of the mass of a positive closed current in balls).
-/

public section

namespace TauCeti

open MeasureTheory Metric Complex Filter Topology Set
open scoped InnerProductSpace ComplexConjugate Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Twice the antiholomorphic derivative of `χ(‖u‖²) ⟪u, u'⟫`, written as `∂ₓ + i ∂_y`, at a point
where `u` and `u'` are complex differentiable: it is
`2 (χ'(‖u‖²) |⟪u, u'⟫|² + χ(‖u‖²) ‖u'‖²)`. -/
private theorem fderiv_one_add_I_mul_fderiv_I {u : ℂ → E} {z : ℂ} {χ : ℝ → ℝ}
    (hu : HasDerivAt u (deriv u z) z) (hu' : HasDerivAt (deriv u) (deriv (deriv u) z) z)
    (hχ : DifferentiableAt ℝ χ (‖u z‖ ^ 2)) :
    fderiv ℝ (fun y ↦ χ (‖u y‖ ^ 2) • ⟪u y, deriv u y⟫_ℂ) z 1 +
        I * fderiv ℝ (fun y ↦ χ (‖u y‖ ^ 2) • ⟪u y, deriv u y⟫_ℂ) z I =
      ((2 * (deriv χ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
        χ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2) : ℝ) : ℂ) := by
  have h1 := hu.hasFDerivAt.restrictScalars ℝ
  have h2 := hu'.hasFDerivAt.restrictScalars ℝ
  have hq := h1.inner ℂ h2
  -- `E` carries no real inner product instance, so differentiate `‖u‖²` as `re ⟪u, u⟫`.
  have hρ : HasFDerivAt (fun y ↦ ‖u y‖ ^ 2)
      (reCLM.comp ((fderivInnerCLM ℂ (u z, u z)).comp
        ((ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (deriv u z))).prod
        (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (deriv u z)))))) z := by
    have := reCLM.hasFDerivAt.comp z (h1.inner ℂ h1)
    convert this using 1
    funext y
    simp only [Function.comp_apply, reCLM_apply, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hf := (hχ.hasDerivAt.comp_hasFDerivAt z hρ).smul hq
  rw [show (fun y ↦ χ (‖u y‖ ^ 2) • ⟪u y, deriv u y⟫_ℂ) =
    (χ ∘ fun y ↦ ‖u y‖ ^ 2) • fun t ↦ ⟪u t, deriv u t⟫_ℂ from rfl, hf.fderiv]
  simp only [fderivInnerCLM_apply, inner_smul_left, inner_smul_right,
    ← inner_conj_symm (u z) (deriv u z), add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.smulRight_apply, reCLM_apply, inner_self_eq_norm_sq_to_K]
  generalize ⟪deriv u z, u z⟫_ℂ = q
  generalize ⟪u z, deriv (deriv u) z⟫_ℂ = r
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, ← ofReal_pow] <;> ring

/-- The function `χ(‖u‖²) ⟪u, u'⟫` is `C¹` at a point where `u` is analytic. -/
private theorem contDiffAt_smul_inner {u : ℂ → E} {z : ℂ} (ha : AnalyticAt ℂ u z) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ) :
    ContDiffAt ℝ 1 (fun y ↦ χ (‖u y‖ ^ 2) • ⟪u y, deriv u y⟫_ℂ) z := by
  have h1 : ContDiffAt ℝ 1 u z := (ha.contDiffAt (n := 1)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 1 (deriv u) z := (ha.deriv.contDiffAt (n := 1)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ 1 (fun y ↦ ‖u y‖ ^ 2) z := by
    refine (reCLM.contDiff.contDiffAt.comp z (h1.inner ℂ h1)).congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦ ?_)
    simp only [Function.comp_apply, reCLM_apply, inner_self_eq_norm_sq_to_K]
    norm_cast
  exact (hχ.contDiffAt.comp z hρ).smul (h1.inner ℂ h2)

/-- A function continuous on `U` that vanishes on `U` outside a compact subset `K` of `U` is
integrable on `U`. -/
private theorem integrableOn_of_continuousOn_of_eq_zero {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {g : ℂ → ℝ} (hg : ContinuousOn g U)
    (h0 : ∀ z ∈ U, z ∉ K → g z = 0) : IntegrableOn g U :=
  ((hg.mono hKU).integrableOn_compact hK).of_forall_sdiff_eq_zero hU.measurableSet
    fun z hz ↦ h0 z hz.1 hz.2

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- A point of `U` outside `U ∩ u⁻¹(closedBall 0 R)` has `R² < ‖u z‖²`. -/
private theorem lt_norm_sq_of_notMem {U : Set ℂ} {u : ℂ → E} {R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : z ∈ U) (hzK : z ∉ U ∩ u ⁻¹' closedBall 0 R) : R ^ 2 < ‖u z‖ ^ 2 := by
  have : R < ‖u z‖ := by simpa [hz, mem_closedBall, dist_zero_right] using hzK
  exact pow_lt_pow_left₀ this hR two_ne_zero

/-- A function vanishing on `[T, ∞)` vanishes, together with its derivative, beyond `T`. -/
private theorem apply_eq_zero_and_deriv_eq_zero_of_lt {χ : ℝ → ℝ} {T t : ℝ}
    (hχT : ∀ s, T ≤ s → χ s = 0) (ht : T < t) : χ t = 0 ∧ deriv χ t = 0 := by
  refine ⟨hχT t ht.le, ?_⟩
  have : χ =ᶠ[𝓝 t] fun _ ↦ 0 := eventually_of_mem (Ioi_mem_nhds ht) fun s hs ↦ hχT s (le_of_lt hs)
  rw [this.deriv_eq, deriv_const]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Shrinking the ball keeps the preimage sublevel set compact. -/
private theorem isCompact_inter_preimage_closedBall_of_subset {U : Set ℂ} {u : ℂ → E}
    (hu : ContinuousOn u U) {c c' : E} {r s : ℝ} (hK : IsCompact (U ∩ u ⁻¹' closedBall c r))
    (h : closedBall c' s ⊆ closedBall c r) : IsCompact (U ∩ u ⁻¹' closedBall c' s) := by
  have : U ∩ u ⁻¹' closedBall c' s = (U ∩ u ⁻¹' closedBall c r) ∩ u ⁻¹' closedBall c' s := by
    ext z
    simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun hz ↦ ⟨⟨hz.1, h hz.2⟩, hz.2⟩, fun hz ↦ ⟨hz.1.1, hz.2⟩⟩
  rw [this]
  exact hK.of_isClosed_subset ((hu.mono inter_subset_left).preimage_isClosed_of_isClosed
    hK.isClosed isClosed_closedBall) inter_subset_left

variable {U : Set ℂ} {u : ℂ → E}

/-- Integration by parts against `χ(‖u‖²)`: for a holomorphic map `u` on `U` whose sublevel set
`U ∩ u⁻¹(closedBall 0 R)` is compact and a `C¹` function `χ` vanishing on `[R², ∞)`,
`∫_U (χ'(‖u‖²) |⟪u, u'⟫|² + χ(‖u‖²) ‖u'‖²) = 0`. It is the vanishing of the integral of
the antiholomorphic derivative `(∂ₓ + i ∂_y) / 2` of `χ(‖u‖²) ⟪u, u'⟫`. -/
private theorem setIntegral_deriv_mul_norm_inner_sq_add_mul_norm_deriv_sq_eq_zero
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) {R : ℝ} (hR : 0 ≤ R)
    (hK : IsCompact (U ∩ u ⁻¹' closedBall 0 R)) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχR : ∀ t, R ^ 2 ≤ t → χ t = 0) :
    ∫ z in U, (deriv χ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
      χ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2) = 0 := by
  have hKc : IsClosed (U ∩ u ⁻¹' closedBall 0 R) := hK.isClosed
  have hout : ∀ z ∈ U, z ∉ U ∩ u ⁻¹' closedBall 0 R → R ^ 2 < ‖u z‖ ^ 2 := fun _ hz hzK ↦
    lt_norm_sq_of_notMem hR hz hzK
  have hχ0 : ∀ t, R ^ 2 < t → χ t = 0 := fun t ht ↦ hχR t ht.le
  set f : ℂ → ℂ := fun y ↦ χ (‖u y‖ ^ 2) • ⟪u y, deriv u y⟫_ℂ
  set F : ℂ → ℂ := U.indicator f
  have hFout : ∀ z ∉ U, F =ᶠ[𝓝 z] fun _ ↦ 0 := by
    intro z hz
    filter_upwards [hKc.isOpen_compl.mem_nhds fun h ↦ hz h.1] with y hy
    by_cases hyU : y ∈ U
    · simp [F, indicator_of_mem hyU, f, hχ0 _ (hout y hyU hy)]
    · simp [F, indicator_of_notMem hyU]
  have hFin : ∀ z ∈ U, F =ᶠ[𝓝 z] f := fun z hz ↦
    eventually_of_mem (hU.mem_nhds hz) fun y hy ↦ indicator_of_mem hy f
  have hfC : ∀ z ∈ U, ContDiffAt ℝ 1 f z := fun z hz ↦
    contDiffAt_smul_inner (hu.analyticAt (hU.mem_nhds hz)) hχ
  have hFC : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ U
    · exact (hfC z hz).congr_of_eventuallyEq (hFin z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (hFout z hz)
  have hFs : HasCompactSupport F := HasCompactSupport.intro hK fun z hz ↦ by
    by_cases hzU : z ∈ U
    · simp [F, indicator_of_mem hzU, f, hχ0 _ (hout z hzU hz)]
    · simp [F, indicator_of_notMem hzU]
  have hpt : ∀ z, fderiv ℝ F z 1 + I * fderiv ℝ F z I = U.indicator (fun z ↦
      (((2 * (deriv χ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
        χ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2)) : ℝ) : ℂ)) z := by
    intro z
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz, (hFin z hz).fderiv_eq]
      have ha := hu.analyticAt (hU.mem_nhds hz)
      exact fderiv_one_add_I_mul_fderiv_I ha.differentiableAt.hasDerivAt
        ha.deriv.differentiableAt.hasDerivAt (hχ.differentiable one_ne_zero _)
    · rw [indicator_of_notMem hz, (hFout z hz).fderiv_eq]
      simp
  have h0 : ∫ z, (fderiv ℝ F z 1 + I * fderiv ℝ F z I) = 0 := by
    rw [integral_add (integrable_fderiv_apply_of_hasCompactSupport hFC hFs 1)
      ((integrable_fderiv_apply_of_hasCompactSupport hFC hFs I).const_mul I),
      integral_const_mul, integral_fderiv_apply_eq_zero_of_hasCompactSupport hFC hFs,
      integral_fderiv_apply_eq_zero_of_hasCompactSupport hFC hFs]
    simp
  simp_rw [hpt] at h0
  rw [integral_indicator hU.measurableSet, integral_complex_ofReal, integral_const_mul] at h0
  exact_mod_cast (mul_eq_zero.1 (ofReal_eq_zero.1 h0)).resolve_left two_ne_zero

/-- The integrated monotonicity inequality: with `χ` as in
`setIntegral_deriv_mul_norm_inner_sq_add_mul_norm_deriv_sq_eq_zero` and moreover nonincreasing
on `[0, ∞)`, `∫_U (t χ(t))'|_{t = ‖u‖²} ‖u'‖² ≤ 0`. -/
private theorem setIntegral_deriv_mul_self_mul_norm_deriv_sq_nonpos
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) {R : ℝ} (hR : 0 ≤ R)
    (hK : IsCompact (U ∩ u ⁻¹' closedBall 0 R)) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχR : ∀ t, R ^ 2 ≤ t → χ t = 0) (hχ' : ∀ t, 0 ≤ t → deriv χ t ≤ 0) :
    ∫ z in U, deriv (fun t ↦ t * χ t) (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2 ≤ 0 := by
  have hcu : ContinuousOn u U := hu.continuousOn
  have hcu' : ContinuousOn (deriv u) U := (hu.deriv hU).continuousOn
  have hcχ : Continuous χ := hχ.continuous
  have hχ0 : ∀ z ∈ U, z ∉ U ∩ u ⁻¹' closedBall 0 R →
      χ (‖u z‖ ^ 2) = 0 ∧ deriv χ (‖u z‖ ^ 2) = 0 := fun z hz hzK ↦
    apply_eq_zero_and_deriv_eq_zero_of_lt hχR (lt_norm_sq_of_notMem hR hz hzK)
  have hd : ∀ t, deriv (fun t ↦ t * χ t) t = χ t + t * deriv χ t := fun t ↦ by
    simpa using ((hasDerivAt_id' t).fun_mul (hχ.differentiable one_ne_zero t).hasDerivAt).deriv
  have hAB : IntegrableOn (fun z ↦ deriv χ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
      χ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2) U :=
    integrableOn_of_continuousOn_of_eq_zero hU hK inter_subset_left (by fun_prop)
      fun z hz hzK ↦ by simp [(hχ0 z hz hzK).1, (hχ0 z hz hzK).2]
  have hC : IntegrableOn (fun z ↦ deriv χ (‖u z‖ ^ 2) *
      (‖u z‖ ^ 2 * ‖deriv u z‖ ^ 2 - ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2)) U :=
    integrableOn_of_continuousOn_of_eq_zero hU hK inter_subset_left (by fun_prop)
      fun z hz hzK ↦ by simp [(hχ0 z hz hzK).2]
  calc ∫ z in U, deriv (fun t ↦ t * χ t) (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2
      = ∫ z in U, ((deriv χ (‖u z‖ ^ 2) * ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2 +
          χ (‖u z‖ ^ 2) * ‖deriv u z‖ ^ 2) + deriv χ (‖u z‖ ^ 2) *
            (‖u z‖ ^ 2 * ‖deriv u z‖ ^ 2 - ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2)) := by
        congr 1
        funext z
        rw [hd]
        ring
    _ = ∫ z in U, deriv χ (‖u z‖ ^ 2) *
          (‖u z‖ ^ 2 * ‖deriv u z‖ ^ 2 - ‖⟪u z, deriv u z⟫_ℂ‖ ^ 2) := by
        rw [integral_add hAB hC,
          setIntegral_deriv_mul_norm_inner_sq_add_mul_norm_deriv_sq_eq_zero hU hu hR hK hχ hχR,
          zero_add]
    _ ≤ 0 := by
        refine setIntegral_nonpos hU.measurableSet fun z _ ↦ mul_nonpos_of_nonpos_of_nonneg
          (hχ' _ (by positivity)) (sub_nonneg.2 ?_)
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-! ### Test functions built from a profile -/

section Profile

variable {φ : ℝ → ℝ}

/-- An antiderivative of a function constant on `(-∞, a]` is linear there. -/
private theorem intervalIntegral_eq_mul_of_le {a σ : ℝ} (ha : 0 ≤ a)
    (hφ0 : ∀ t ≤ a, φ t = φ 0) (hσ : σ ≤ a) : ∫ x in (0 : ℝ)..σ, φ x = φ 0 * σ := by
  rw [intervalIntegral.integral_congr (g := fun _ ↦ φ 0) fun x hx ↦ hφ0 x ?_]
  · simp [mul_comm]
  · rcases Set.mem_uIcc.1 hx with h | h
    exacts [h.2.trans hσ, h.2.trans ha]

/-- An antiderivative of a function vanishing on `[1, ∞)` is constant there. -/
private theorem intervalIntegral_sub_intervalIntegral_eq_zero (hφ : Continuous φ)
    (hφ1 : ∀ t, 1 ≤ t → φ t = 0) {σ₁ σ₂ : ℝ} (h₁ : 1 ≤ σ₁) (h₂ : 1 ≤ σ₂) :
    (∫ x in (0 : ℝ)..σ₂, φ x) - ∫ x in (0 : ℝ)..σ₁, φ x = 0 := by
  rw [intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
    (hφ.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun x hx ↦ hφ1 x ?_]
  · simp
  · rcases Set.mem_uIcc.1 hx with h | h
    exacts [h₁.trans h.1, h₂.trans h.1]

/-- For a nonincreasing `φ` with antiderivative `Φ`, the function `σ ↦ σ φ(σ) - Φ(σ)` is
nonincreasing on `[0, ∞)`. -/
private theorem mul_sub_intervalIntegral_le (hφ : Continuous φ) (hφa : Antitone φ)
    {σ₁ σ₂ : ℝ} (h₁ : 0 ≤ σ₁) (h₁₂ : σ₁ ≤ σ₂) :
    σ₂ * φ σ₂ - ∫ x in (0 : ℝ)..σ₂, φ x ≤ σ₁ * φ σ₁ - ∫ x in (0 : ℝ)..σ₁, φ x := by
  have hint : (σ₂ - σ₁) * φ σ₂ ≤ (∫ x in (0 : ℝ)..σ₂, φ x) - ∫ x in (0 : ℝ)..σ₁, φ x := by
    rw [intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
      (hφ.intervalIntegrable _ _), ← smul_eq_mul, ← intervalIntegral.integral_const]
    exact intervalIntegral.integral_mono_on h₁₂ intervalIntegrable_const
      (hφ.intervalIntegrable _ _) fun x hx ↦ hφa hx.2
  nlinarith [mul_le_mul_of_nonneg_left (hφa h₁₂) h₁]

/-- The difference `Φ(t / ε²) - Φ(t / R²)` of rescaled antiderivatives of `φ`. -/
private noncomputable def profileDiff (φ : ℝ → ℝ) (ε R t : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..t / ε ^ 2, φ x) - ∫ x in (0 : ℝ)..t / R ^ 2, φ x

/-- The test function `χ(t) = (Φ(t / ε²) - Φ(t / R²)) / t`, written so that it is visibly
constant near `0` when `φ` is. -/
private noncomputable def profileTest (φ : ℝ → ℝ) (ε R t : ℝ) : ℝ :=
  φ 0 * (1 / ε ^ 2 - 1 / R ^ 2) +
    (profileDiff φ ε R t - φ 0 * (1 / ε ^ 2 - 1 / R ^ 2) * t) / t

private theorem hasDerivAt_profileDiff (hφ : Continuous φ) (ε R t : ℝ) :
    HasDerivAt (profileDiff φ ε R)
      (φ (t / ε ^ 2) * (1 / ε ^ 2) - φ (t / R ^ 2) * (1 / R ^ 2)) t :=
  ((hφ.integral_hasStrictDerivAt 0 _).hasDerivAt.comp t ((hasDerivAt_id t).div_const _)).sub
    ((hφ.integral_hasStrictDerivAt 0 _).hasDerivAt.comp t ((hasDerivAt_id t).div_const _))

private theorem mul_profileTest (ε R t : ℝ) : t * profileTest φ ε R t = profileDiff φ ε R t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [profileDiff]
  · simp only [profileTest]
    field_simp
    ring

private theorem profileTest_eventuallyEq {a ε R : ℝ} (ha : 0 < a) (hφ0 : ∀ t ≤ a, φ t = φ 0)
    (hε : 0 < ε) (hεR : ε ≤ R) {t : ℝ} (ht : t < a * ε ^ 2) :
    profileTest φ ε R =ᶠ[𝓝 t] fun _ ↦ φ 0 * (1 / ε ^ 2 - 1 / R ^ 2) := by
  have hR : 0 < R := hε.trans_le hεR
  filter_upwards [Iio_mem_nhds ht] with s hs
  have h₁ : s / ε ^ 2 ≤ a := ((div_lt_iff₀ (by positivity)).2 hs).le
  have h₂ : s / R ^ 2 ≤ a := by
    rcases le_or_gt 0 s with h0 | h0
    · exact (div_le_div_of_nonneg_left h0 (by positivity)
        (pow_le_pow_left₀ hε.le hεR 2)).trans h₁
    · exact (div_neg_of_neg_of_pos h0 (by positivity)).le.trans ha.le
  simp only [profileTest, profileDiff, intervalIntegral_eq_mul_of_le ha.le hφ0 h₁,
    intervalIntegral_eq_mul_of_le ha.le hφ0 h₂]
  ring

private theorem contDiff_profileTest (hφ : Continuous φ) {a ε R : ℝ} (ha : 0 < a)
    (hφ0 : ∀ t ≤ a, φ t = φ 0) (hε : 0 < ε) (hεR : ε ≤ R) : ContDiff ℝ 1 (profileTest φ ε R) := by
  have hΦ : ContDiff ℝ 1 fun σ ↦ ∫ x in (0 : ℝ)..σ, φ x :=
    contDiff_one_iff_deriv.2
      ⟨fun σ ↦ (hφ.integral_hasStrictDerivAt 0 σ).hasDerivAt.differentiableAt, by
      rw [show deriv (fun σ ↦ ∫ x in (0 : ℝ)..σ, φ x) = φ from
        funext fun σ ↦ (hφ.integral_hasStrictDerivAt 0 σ).hasDerivAt.deriv]
      exact hφ⟩
  have hD : ContDiff ℝ 1 (profileDiff φ ε R) :=
    (hΦ.comp (contDiff_id.div_const _)).sub (hΦ.comp (contDiff_id.div_const _))
  refine contDiff_iff_contDiffAt.2 fun t ↦ ?_
  rcases lt_or_ge t (a * ε ^ 2) with ht | ht
  · exact contDiffAt_const.congr_of_eventuallyEq (profileTest_eventuallyEq ha hφ0 hε hεR ht)
  · exact contDiffAt_const.add (((hD.sub (contDiff_const.mul contDiff_id)).contDiffAt).div
      contDiffAt_id ((by positivity : 0 < a * ε ^ 2).trans_le ht).ne')

private theorem profileTest_eq_zero (hφ : Continuous φ) (hφ1 : ∀ t, 1 ≤ t → φ t = 0)
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {t : ℝ} (ht : R ^ 2 ≤ t) : profileTest φ ε R t = 0 := by
  have hR2 : 0 < R ^ 2 := by have := hε.trans_le hεR; positivity
  have : t * profileTest φ ε R t = 0 := by
    rw [mul_profileTest]
    exact intervalIntegral_sub_intervalIntegral_eq_zero hφ hφ1 ((one_le_div hR2).2 ht)
      ((one_le_div (by positivity)).2 ((pow_le_pow_left₀ hε.le hεR 2).trans ht))
  exact (mul_eq_zero.1 this).resolve_left (hR2.trans_le ht).ne'

private theorem deriv_profileTest_nonpos (hφ : Continuous φ) (hφa : Antitone φ) {a ε R : ℝ}
    (ha : 0 < a) (hφ0 : ∀ t ≤ a, φ t = φ 0) (hε : 0 < ε) (hεR : ε ≤ R) {t : ℝ} (ht : 0 ≤ t) :
    deriv (profileTest φ ε R) t ≤ 0 := by
  rcases lt_or_ge t (a * ε ^ 2) with ht' | ht'
  · rw [(profileTest_eventuallyEq ha hφ0 hε hεR ht').deriv_eq, deriv_const]
  have htpos : 0 < t := (by positivity : 0 < a * ε ^ 2).trans_le ht'
  have heq : profileTest φ ε R =ᶠ[𝓝 t] fun s ↦ profileDiff φ ε R s / s := by
    filter_upwards [Ioi_mem_nhds htpos] with s hs
    rw [← mul_profileTest, mul_div_cancel_left₀ _ (ne_of_gt hs)]
  rw [heq.deriv_eq, ((hasDerivAt_profileDiff hφ ε R t).fun_div (hasDerivAt_id' t)
    htpos.ne').deriv]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  have := mul_sub_intervalIntegral_le hφ hφa (by positivity : 0 ≤ t / R ^ 2)
    (div_le_div_of_nonneg_left ht (by positivity) (pow_le_pow_left₀ hε.le hεR 2))
  have e : (φ (t / ε ^ 2) * (1 / ε ^ 2) - φ (t / R ^ 2) * (1 / R ^ 2)) * t -
      profileDiff φ ε R t * 1 = (t / ε ^ 2 * φ (t / ε ^ 2) - ∫ x in (0 : ℝ)..t / ε ^ 2, φ x) -
        (t / R ^ 2 * φ (t / R ^ 2) - ∫ x in (0 : ℝ)..t / R ^ 2, φ x) := by
    simp only [profileDiff]
    ring
  linarith

private theorem deriv_mul_profileTest (hφ : Continuous φ) (ε R t : ℝ) :
    deriv (fun t ↦ t * profileTest φ ε R t) t = φ (t / ε ^ 2) / ε ^ 2 - φ (t / R ^ 2) / R ^ 2 := by
  rw [show (fun t ↦ t * profileTest φ ε R t) = profileDiff φ ε R from funext (mul_profileTest ε R),
    (hasDerivAt_profileDiff hφ ε R t).deriv]
  ring

end Profile

/-- The monotonicity inequality against a profile `φ`: for a continuous nonincreasing `φ` that is
constant near `0` and vanishes on `[1, ∞)`, the quantity
`ε⁻² ∫_U φ(‖u‖² / ε²) ‖u'‖²` is nondecreasing in `ε` as long as the sublevel sets stay compact. -/
private theorem setIntegral_profile_div_sq_le (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφa : Antitone φ) (hφ1 : ∀ t, 1 ≤ t → φ t = 0) {a : ℝ}
    (ha : 0 < a) (hφ0 : ∀ t ≤ a, φ t = φ 0) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hK : IsCompact (U ∩ u ⁻¹' closedBall 0 R)) :
    (∫ z in U, φ (‖u z‖ ^ 2 / ε ^ 2) * ‖deriv u z‖ ^ 2) / ε ^ 2 ≤
      (∫ z in U, φ (‖u z‖ ^ 2 / R ^ 2) * ‖deriv u z‖ ^ 2) / R ^ 2 := by
  have hR : 0 < R := hε.trans_le hεR
  have key := setIntegral_deriv_mul_self_mul_norm_deriv_sq_nonpos hU hu hR.le hK
    (contDiff_profileTest hφ ha hφ0 hε hεR) (fun t ht ↦ profileTest_eq_zero hφ hφ1 hε hεR ht)
    (fun t ht ↦ deriv_profileTest_nonpos hφ hφa ha hφ0 hε hεR ht)
  simp_rw [deriv_mul_profileTest hφ] at key
  have hint : ∀ s, 0 < s → s ≤ R →
      IntegrableOn (fun z ↦ φ (‖u z‖ ^ 2 / s ^ 2) * ‖deriv u z‖ ^ 2) U := fun s hs hsR ↦
    integrableOn_of_continuousOn_of_eq_zero hU hK inter_subset_left
      (by have := hu.continuousOn; have := (hu.deriv hU).continuousOn; fun_prop)
      fun z hz hzK ↦ by
        have := lt_norm_sq_of_notMem hR.le hz hzK
        rw [hφ1 _ ((one_le_div (by positivity)).2
          ((pow_le_pow_left₀ hs.le hsR 2).trans this.le)), zero_mul]
  have hsplit : ∀ z, (φ (‖u z‖ ^ 2 / ε ^ 2) / ε ^ 2 - φ (‖u z‖ ^ 2 / R ^ 2) / R ^ 2) *
      ‖deriv u z‖ ^ 2 = φ (‖u z‖ ^ 2 / ε ^ 2) * ‖deriv u z‖ ^ 2 / ε ^ 2 -
        φ (‖u z‖ ^ 2 / R ^ 2) * ‖deriv u z‖ ^ 2 / R ^ 2 := fun z ↦ by ring
  simp_rw [hsplit] at key
  rw [integral_sub ((hint ε hε hεR).div_const _) ((hint R hR le_rfl).div_const _),
    integral_div, integral_div] at key
  linarith

/-! ### Smooth approximations of the indicator of `(-∞, 1)` -/

/-- A smooth nonincreasing profile, equal to `1` on `(-∞, 1 - 1 / (n + 2)]` and to `0` on
`[1, ∞)`; as `n → ∞` these increase to the indicator of `(-∞, 1)`. -/
private noncomputable def stepProfile (n : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((1 - x) * (n + 2))

private theorem continuous_stepProfile (n : ℕ) : Continuous (stepProfile n) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

private theorem antitone_stepProfile (n : ℕ) : Antitone (stepProfile n) := fun _ _ hxy ↦
  Real.smoothTransition.monotone (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

private theorem stepProfile_eq_zero (n : ℕ) {x : ℝ} (hx : 1 ≤ x) : stepProfile n x = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith)
    (by positivity))

private theorem stepProfile_mem_Icc (n : ℕ) (x : ℝ) : stepProfile n x ∈ Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem stepProfile_eq_one (n : ℕ) {x : ℝ} (hx : x ≤ 1 - 1 / ((n : ℝ) + 2)) :
    stepProfile n x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  calc (1 : ℝ) = 1 / (n + 2) * (n + 2) := by field_simp
    _ ≤ (1 - x) * (n + 2) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private theorem one_sub_one_div_pos (n : ℕ) : 0 < 1 - 1 / ((n : ℝ) + 2) := by
  have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
private theorem stepProfile_div_eq_zero (n : ℕ) {x : E} {w : ℝ} (hw : 0 < w) (hx : w ≤ ‖x‖) :
    stepProfile n (‖x‖ ^ 2 / w ^ 2) = 0 :=
  stepProfile_eq_zero n ((one_le_div (by positivity)).2 (pow_le_pow_left₀ hw.le hx 2))

private theorem integrableOn_norm_deriv_sq (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) {c : E}
    {r : ℝ} (hK : IsCompact (U ∩ u ⁻¹' closedBall c r)) :
    IntegrableOn (fun z ↦ ‖deriv u z‖ ^ 2) (U ∩ u ⁻¹' closedBall c r) :=
  (((hu.deriv hU).continuousOn.norm.pow 2).mono inter_subset_left).integrableOn_compact hK

private theorem integrableOn_stepProfile_mul (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    {c : E} {r : ℝ} (hK : IsCompact (U ∩ u ⁻¹' closedBall c r)) (n : ℕ) {w : ℝ} (hw : 0 < w)
    (hwr : w ≤ r) :
    IntegrableOn (fun z ↦ stepProfile n (‖u z - c‖ ^ 2 / w ^ 2) * ‖deriv u z‖ ^ 2) U :=
  integrableOn_of_continuousOn_of_eq_zero hU hK inter_subset_left
    (by have := hu.continuousOn; have := (hu.deriv hU).continuousOn
        have := continuous_stepProfile n; fun_prop)
    fun z hz hzK ↦ by
      have : r < ‖u z - c‖ := by simpa [hz, mem_closedBall, dist_eq_norm] using hzK
      rw [stepProfile_div_eq_zero n hw (hwr.trans this.le), zero_mul]

omit [CompleteSpace E] in
/-- The area as the integral over `U` of an indicator. -/
private theorem setIntegral_indicator_preimage_ball (hU : IsOpen U)
    (hu : DifferentiableOn ℂ u U) (c : E) (w : ℝ) :
    ∫ z in U, (U ∩ u ⁻¹' ball c w).indicator (fun z ↦ ‖deriv u z‖ ^ 2) z =
      ∫ z in U ∩ u ⁻¹' ball c w, ‖deriv u z‖ ^ 2 := by
  rw [setIntegral_indicator (hu.continuousOn.isOpen_inter_preimage hU isOpen_ball).measurableSet,
    inter_eq_right.2 inter_subset_left]

/-- The integrals against the step profiles are bounded by the area. -/
private theorem setIntegral_stepProfile_le (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) {c : E}
    {r : ℝ} (hK : IsCompact (U ∩ u ⁻¹' closedBall c r)) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (htr : t ≤ r) : ∫ z in U, stepProfile n (‖u z - c‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2 ≤
      ∫ z in U ∩ u ⁻¹' ball c t, ‖deriv u z‖ ^ 2 := by
  rw [← setIntegral_indicator_preimage_ball hU hu]
  have hS := (hu.continuousOn.isOpen_inter_preimage hU isOpen_ball (t := ball c t)).measurableSet
  refine setIntegral_mono_on (integrableOn_stepProfile_mul hU hu hK n ht htr)
    ((((integrableOn_norm_deriv_sq hU hu hK).mono_set (inter_subset_inter_right _
      (preimage_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall htr)))))
        |>.integrable_indicator hS).integrableOn) hU.measurableSet fun z hz ↦ ?_
  by_cases hzt : z ∈ U ∩ u ⁻¹' ball c t
  · rw [indicator_of_mem hzt]
    exact mul_le_of_le_one_left (sq_nonneg _) (stepProfile_mem_Icc _ _).2
  · have : t ≤ ‖u z - c‖ := by simpa [hz, mem_ball, dist_eq_norm] using hzt
    rw [indicator_of_notMem hzt, stepProfile_div_eq_zero n ht this, zero_mul]

/-- The integrals against the step profiles converge to the area. -/
private theorem tendsto_setIntegral_stepProfile (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    {c : E} {r : ℝ} (hK : IsCompact (U ∩ u ⁻¹' closedBall c r)) {s : ℝ} (hs : 0 < s)
    (hsr : s ≤ r) :
    Tendsto (fun n ↦ ∫ z in U, stepProfile n (‖u z - c‖ ^ 2 / s ^ 2) * ‖deriv u z‖ ^ 2) atTop
      (𝓝 (∫ z in U ∩ u ⁻¹' ball c s, ‖deriv u z‖ ^ 2)) := by
  have hKs := isCompact_inter_preimage_closedBall_of_subset hu.continuousOn hK
    (closedBall_subset_closedBall hsr)
  rw [← setIntegral_indicator_preimage_ball hU hu]
  refine tendsto_integral_of_dominated_convergence
    ((U ∩ u ⁻¹' closedBall c s).indicator fun z ↦ ‖deriv u z‖ ^ 2)
    (fun n ↦ (integrableOn_stepProfile_mul hU hu hK n hs hsr).aestronglyMeasurable)
    (((integrableOn_norm_deriv_sq hU hu hKs).integrable_indicator
      hKs.isClosed.measurableSet).integrableOn)
    (fun n ↦ ae_restrict_of_forall_mem hU.measurableSet fun z hz ↦ ?_)
    (ae_restrict_of_forall_mem hU.measurableSet fun z hz ↦ ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stepProfile_mem_Icc _ _).1 (sq_nonneg _))]
    by_cases hzs : z ∈ U ∩ u ⁻¹' closedBall c s
    · rw [indicator_of_mem hzs]
      exact mul_le_of_le_one_left (sq_nonneg _) (stepProfile_mem_Icc _ _).2
    · have : s < ‖u z - c‖ := by simpa [hz, mem_closedBall, dist_eq_norm] using hzs
      rw [indicator_of_notMem hzs, stepProfile_div_eq_zero n hs this.le, zero_mul]
  · by_cases hzs : z ∈ U ∩ u ⁻¹' ball c s
    · rw [indicator_of_mem hzs]
      have hlt : ‖u z - c‖ ^ 2 / s ^ 2 < 1 := (div_lt_one (by positivity)).2
        (pow_lt_pow_left₀ (by simpa [mem_ball, dist_eq_norm] using hzs.2) (norm_nonneg _)
          two_ne_zero)
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩)
      dsimp only
      rw [stepProfile_eq_one n ?_, one_mul]
      have : 1 / ((n : ℝ) + 2) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show N + 1 ≤ n + 2 by omega))
      linarith
    · have : s ≤ ‖u z - c‖ := by simpa [hz, mem_ball, dist_eq_norm] using hzs
      rw [indicator_of_notMem hzs]
      exact tendsto_const_nhds.congr fun n ↦ by rw [stepProfile_div_eq_zero n hs this, zero_mul]

/-- **Monotonicity formula for holomorphic curves.** Let `u` be a holomorphic map from an open set
`U ⊆ ℂ` to a complex Hilbert space, and `c` a point such that `U ∩ u⁻¹(closedBall c r)` is
compact. Then the area `∫_{U ∩ u⁻¹(B(c, s))} ‖u'‖²` of the part of the curve inside the ball of
radius `s` about `c`, divided by `s²`, is nondecreasing in `s ∈ (0, r]`. -/
theorem monotoneOn_setIntegral_norm_deriv_sq_div_sq (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    (c : E) {r : ℝ} (hK : IsCompact (U ∩ u ⁻¹' closedBall c r)) :
    MonotoneOn (fun s ↦ (∫ z in U ∩ u ⁻¹' ball c s, ‖deriv u z‖ ^ 2) / s ^ 2) (Ioc 0 r) := by
  intro s hs t ht hst
  have hKt := isCompact_inter_preimage_closedBall_of_subset hu.continuousOn hK
    (closedBall_subset_closedBall ht.2)
  have hcb : (fun z ↦ u z - c) ⁻¹' closedBall 0 t = u ⁻¹' closedBall c t := by
    ext z; simp [dist_eq_norm]
  rw [← hcb] at hKt
  -- The monotonicity inequality for each step profile, applied to `u - c`.
  have hprof : ∀ n, (∫ z in U, stepProfile n (‖u z - c‖ ^ 2 / s ^ 2) * ‖deriv u z‖ ^ 2) / s ^ 2 ≤
      (∫ z in U, stepProfile n (‖u z - c‖ ^ 2 / t ^ 2) * ‖deriv u z‖ ^ 2) / t ^ 2 := fun n ↦ by
    have := setIntegral_profile_div_sq_le hU (hu.sub_const c) (continuous_stepProfile n)
      (antitone_stepProfile n) (fun x ↦ stepProfile_eq_zero n) (one_sub_one_div_pos n)
      (fun x hx ↦ by rw [stepProfile_eq_one n hx, stepProfile_eq_one n (one_sub_one_div_pos n).le])
      hs.1 hst hKt
    simpa only [deriv_sub_const] using this
  exact le_of_tendsto' ((tendsto_setIntegral_stepProfile hU hu hK hs.1 (hst.trans ht.2)).div_const
    _) fun n ↦ (hprof n).trans (div_le_div_of_nonneg_right
      (setIntegral_stepProfile_le hU hu hK n ht.1 ht.2) (by positivity))

/-- Near an immersed point `z₀`, for `0 < θ < 1`, the map `u` moves at speed at most `A / θ` and
`‖u'‖ ≥ θ A`, where `A = ‖u'(z₀)‖`. -/
private theorem exists_ball_norm_sub_le_and_le_norm_deriv (hU : IsOpen U)
    (hu : DifferentiableOn ℂ u U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hd : deriv u z₀ ≠ 0) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) : ∃ δ > 0, ∀ z ∈ ball z₀ δ,
      ‖u z - u z₀‖ ≤ ‖deriv u z₀‖ / θ * ‖z - z₀‖ ∧ θ * ‖deriv u z₀‖ ≤ ‖deriv u z‖ ∧ z ∈ U := by
  have hA0 : 0 < ‖deriv u z₀‖ := norm_pos_iff.2 hd
  have ha : AnalyticAt ℂ u z₀ := hu.analyticAt (hU.mem_nhds hz₀)
  have hpos : 0 < ‖deriv u z₀‖ / θ - ‖deriv u z₀‖ := by
    rw [sub_pos, lt_div_iff₀ hθ0]
    nlinarith
  have h1 : ∀ᶠ z in 𝓝 z₀, ‖u z - u z₀‖ ≤ ‖deriv u z₀‖ / θ * ‖z - z₀‖ := by
    filter_upwards [(hasDerivAt_iff_isLittleO.1 ha.differentiableAt.hasDerivAt).def hpos]
      with z hz
    calc ‖u z - u z₀‖ = ‖(u z - u z₀ - (z - z₀) • deriv u z₀) + (z - z₀) • deriv u z₀‖ := by
          rw [sub_add_cancel]
      _ ≤ (‖deriv u z₀‖ / θ - ‖deriv u z₀‖) * ‖z - z₀‖ + ‖z - z₀‖ * ‖deriv u z₀‖ :=
          (norm_add_le _ _).trans (add_le_add hz (norm_smul _ _).le)
      _ = ‖deriv u z₀‖ / θ * ‖z - z₀‖ := by ring
  have h2 : ∀ᶠ z in 𝓝 z₀, θ * ‖deriv u z₀‖ ≤ ‖deriv u z‖ :=
    (ha.deriv.continuousAt.norm.eventually (lt_mem_nhds (by nlinarith))).mono fun _ hz ↦ hz.le
  exact Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (hU.mem_nhds hz₀)))

/-- At an immersed point `z₀` and for `0 < θ < 1`, the curve has area at least `π θ⁴ ε²` in the
ball of radius `ε` about `u z₀` for some `ε ∈ (0, r]`. -/
private theorem exists_pi_mul_pow_four_mul_sq_le (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hd : deriv u z₀ ≠ 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact (U ∩ u ⁻¹' closedBall (u z₀) r)) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ ε ∈ Ioc 0 r, π * θ ^ 4 * ε ^ 2 ≤ ∫ z in U ∩ u ⁻¹' ball (u z₀) ε, ‖deriv u z‖ ^ 2 := by
  set A := ‖deriv u z₀‖
  have hA0 : 0 < A := norm_pos_iff.2 hd
  obtain ⟨δ, hδ, hball⟩ := exists_ball_norm_sub_le_and_le_norm_deriv hU hu hz₀ hd hθ0 hθ1
  -- At the scale `ε`, the curve covers the disc of radius `ρ₀ = θ ε / A` about `z₀`.
  set ε := min r (δ * A / θ)
  have hε0 : 0 < ε := lt_min hr (by positivity)
  set ρ₀ := θ * ε / A with hρ₀
  have hρ₀δ : ρ₀ ≤ δ := by
    rw [hρ₀, div_le_iff₀ hA0]
    calc θ * ε ≤ θ * (δ * A / θ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hθ0.le
      _ = δ * A := by field_simp
  have hsub : ball z₀ ρ₀ ⊆ U ∩ u ⁻¹' ball (u z₀) ε := fun z hz ↦ by
    obtain ⟨hz1, -, hzU⟩ := hball z (ball_subset_ball hρ₀δ hz)
    refine ⟨hzU, ?_⟩
    rw [mem_preimage, mem_ball, dist_eq_norm]
    calc ‖u z - u z₀‖ ≤ A / θ * ‖z - z₀‖ := hz1
      _ < A / θ * ρ₀ := mul_lt_mul_of_pos_left (by rwa [mem_ball, dist_eq_norm] at hz)
          (by positivity)
      _ = ε := by rw [hρ₀]; field_simp
  have hint : IntegrableOn (fun z ↦ ‖deriv u z‖ ^ 2) (U ∩ u ⁻¹' ball (u z₀) ε) :=
    (integrableOn_norm_deriv_sq hU hu hK).mono_set (inter_subset_inter_right _
      (preimage_mono (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (min_le_left _ _)))))
  refine ⟨ε, ⟨hε0, min_le_left _ _⟩, ?_⟩
  calc π * θ ^ 4 * ε ^ 2 = ∫ _ in ball z₀ ρ₀, (θ * A) ^ 2 := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Complex.volume_ball,
          ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
          ENNReal.coe_toReal, NNReal.coe_real_pi, hρ₀]
        field_simp
    _ ≤ ∫ z in ball z₀ ρ₀, ‖deriv u z‖ ^ 2 :=
        setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne) (hint.mono_set hsub)
          measurableSet_ball fun z hz ↦
            pow_le_pow_left₀ (by positivity) (hball z (ball_subset_ball hρ₀δ hz)).2.1 2
    _ ≤ ∫ z in U ∩ u ⁻¹' ball (u z₀) ε, ‖deriv u z‖ ^ 2 :=
        setIntegral_mono_set hint (ae_of_all _ fun _ ↦ sq_nonneg _) (ae_of_all _ hsub)

/-- The area bound at an immersed point. -/
private theorem pi_mul_sq_le_setIntegral_norm_deriv_sq_of_deriv_ne_zero (hU : IsOpen U)
    (hu : DifferentiableOn ℂ u U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hd : deriv u z₀ ≠ 0) {r : ℝ}
    (hr : 0 < r) (hK : IsCompact (U ∩ u ⁻¹' closedBall (u z₀) r)) :
    π * r ^ 2 ≤ ∫ z in U ∩ u ⁻¹' ball (u z₀) r, ‖deriv u z‖ ^ 2 := by
  have key : ∀ θ ∈ Ioo (0 : ℝ) 1,
      π * θ ^ 4 * r ^ 2 ≤ ∫ z in U ∩ u ⁻¹' ball (u z₀) r, ‖deriv u z‖ ^ 2 := by
    rintro θ ⟨hθ0, hθ1⟩
    obtain ⟨ε, hε, hlow⟩ := exists_pi_mul_pow_four_mul_sq_le hU hu hz₀ hd hr hK hθ0 hθ1
    have hε0 : 0 < ε := hε.1
    have hmono := monotoneOn_setIntegral_norm_deriv_sq_div_sq hU hu (u z₀) hK hε ⟨hr, le_rfl⟩ hε.2
    dsimp only at hmono
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hmono
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < ε ^ 2)
    calc π * θ ^ 4 * r ^ 2 * ε ^ 2 = π * θ ^ 4 * ε ^ 2 * r ^ 2 := by ring
      _ ≤ (∫ z in U ∩ u ⁻¹' ball (u z₀) ε, ‖deriv u z‖ ^ 2) * r ^ 2 :=
          mul_le_mul_of_nonneg_right hlow (by positivity)
      _ ≤ _ := hmono
  have hlim : Tendsto (fun θ : ℝ ↦ π * θ ^ 4 * r ^ 2) (𝓝[<] 1) (𝓝 (π * 1 ^ 4 * r ^ 2)) :=
    ((by fun_prop : Continuous fun θ : ℝ ↦ π * θ ^ 4 * r ^ 2).tendsto 1).mono_left
      nhdsWithin_le_nhds
  simpa using le_of_tendsto hlim
    (eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) key)

/-- **Monotonicity lower bound for holomorphic curves.** Let `u` be a holomorphic map from an open
set `U ⊆ ℂ` to a complex Hilbert space which is not constant near `z₀ ∈ U`, and let `r ≥ 0` be such
that `U ∩ u⁻¹(closedBall (u z₀) r)` is compact. Then the part of the curve inside the ball of
radius `r` about `u z₀` has area at least `π r²`. -/
theorem pi_mul_sq_le_setIntegral_norm_deriv_sq (hU : IsOpen U) (hu : DifferentiableOn ℂ u U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hnc : ∃ᶠ z in 𝓝 z₀, u z ≠ u z₀) {r : ℝ} (hr : 0 ≤ r)
    (hK : IsCompact (U ∩ u ⁻¹' closedBall (u z₀) r)) :
    π * r ^ 2 ≤ ∫ z in U ∩ u ⁻¹' ball (u z₀) r, ‖deriv u z‖ ^ 2 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  by_cases hd : deriv u z₀ ≠ 0
  · exact pi_mul_sq_le_setIntegral_norm_deriv_sq_of_deriv_ne_zero hU hu hz₀ hd hr hK
  have hcu : ContinuousOn u U := hu.continuousOn
  have hint : IntegrableOn (fun z ↦ ‖deriv u z‖ ^ 2) (U ∩ u ⁻¹' ball (u z₀) r) :=
    ((((hu.deriv hU).continuousOn.norm.pow 2).mono inter_subset_left).integrableOn_compact
      hK).mono_set (inter_subset_inter_right _ (preimage_mono ball_subset_closedBall))
  -- At a critical centre, compare with the balls about nearby immersed points.
  have key : ∀ s ∈ Ioo 0 r, π * s ^ 2 ≤ ∫ z in U ∩ u ⁻¹' ball (u z₀) r, ‖deriv u z‖ ^ 2 := by
    rintro s ⟨hs0, hsr⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
      (((hu.differentiableAt (hU.mem_nhds hz₀)).continuousAt.eventually
        (ball_mem_nhds (u z₀) (sub_pos.2 hsr))).and (hU.mem_nhds hz₀))
    have hδU : ball z₀ δ ⊆ U := fun z hz ↦ (hball z hz).2
    obtain ⟨z₁, hz₁, hd₁⟩ : ∃ z₁ ∈ ball z₀ δ, deriv u z₁ ≠ 0 := by
      by_contra! h
      have hconst : ∀ z ∈ ball z₀ δ, u z = u z₀ := fun z hz ↦
        isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ δ).isPreconnected
          (hu.mono hδU) (fun y hy ↦ h y hy) hz (mem_ball_self hδ)
      exact hnc (eventually_of_mem (ball_mem_nhds z₀ hδ) fun z hz h ↦ h (hconst z hz))
    obtain ⟨hz₁r, hz₁U⟩ := hball z₁ hz₁
    have hsub : s + dist (u z₁) (u z₀) ≤ r := by
      have : dist (u z₁) (u z₀) < r - s := hz₁r
      linarith
    have h₁ := pi_mul_sq_le_setIntegral_norm_deriv_sq_of_deriv_ne_zero hU hu hz₁U hd₁ hs0
      (isCompact_inter_preimage_closedBall_of_subset hcu hK (closedBall_subset_closedBall' hsub))
    exact h₁.trans (setIntegral_mono_set hint (ae_of_all _ fun _ ↦ sq_nonneg _)
      (ae_of_all _
        (inter_subset_inter_right _ (preimage_mono (ball_subset_ball' hsub)))))
  have hlim : Tendsto (fun s : ℝ ↦ π * s ^ 2) (𝓝[<] r) (𝓝 (π * r ^ 2)) :=
    ((by fun_prop : Continuous fun s : ℝ ↦ π * s ^ 2).tendsto r).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_of_mem (Ioo_mem_nhdsLT hr) key)

end TauCeti
