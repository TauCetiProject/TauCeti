/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.MeasureTheory.Group.Convolution.IdempotentKernel.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.Algebra.Algebra.Basic
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.EqOne
import TauCeti.MeasureTheory.Function.Lp.LeftTranslation

/-!
# Idempotents kill the functions invariant under the radical of a group of dilations

Let `G` be a second countable locally compact group with a left Haar measure `μ`, and
`ρ(e) F = (x ↦ ∫ g, e g * F (x * g) ∂μ)` the right regular representation integrated against
`e : G → ℂ` (`TauCeti.rightRegularIntegral`). The main theorem,
`TauCeti.rightRegularIntegral_apply_eq_zero`, is the vanishing of the constant terms of an
idempotent `e ⋆ e = e`. Let `H : G → ℝ` be a continuous height whose right variation
`|H (x * g) - H x|` is bounded by some `ℓ g` uniformly in `x`, and let `D` be a subgroup of
`G × ℂˣ` whose elements `(r, c)` shift the height, `H (r * g) = H g - log ‖c‖`, and which contains
dilations `(x * b * x⁻¹, c)` with `log ‖c‖ ≠ 0` and `b` in any prescribed neighbourhood of `1`,
simultaneously for all `x`. Then `ρ(e) f = 0` for every bounded continuous `f` that is left
invariant under the radical `{r | (r, 1) ∈ D}`. For an idempotent kernel
(`TauCeti.IsIdempotentKernel`) this is
`TauCeti.IsIdempotentKernel.integral_mul_comp_mul_left_eq_zero`. Applied to the dilations of a
parabolic subgroup of a unitary group
(`Matrix.unitaryGroupOf.exists_norm_sub_one_le_and_conj_dilates`) and a height `H`, this is the
analytic input of the theorem that coefficients of integrable discrete series are cusp forms.

The proof is an operator argument on the Banach space `V` of bounded continuous functions that
are invariant under the radical and reproduced by `e`. Since `e ⋆ e = e`, `ρ(e)` maps the
radical-invariant bounded continuous functions into `V`, so it suffices that `V = 0`. The twisted
operator `T = ρ(e) ∘ exp(i t H)` maps `V` to itself, and on `V` it is within
`ε(t) = ∫ ‖e g‖ * sup_z ‖exp(i t H (z * g)) - exp(i t H z)‖` of multiplication by the phase
`exp(i t H)`. The supremum is at most `min 2 (|t| ℓ g)`, so `ε(t) → 0` as `t → 0` by dominated
convergence, and `T` is injective on `V` for small `t`. Left translation by an element `(r₀, c)`
of `D` maps `V` to itself and multiplies the phase by `exp(-i t log ‖c‖)`; choosing `t` so that a
power `T ^ k` acquires the factor `-1`, left translation anticommutes with `T ^ k`. On functions
invariant under the radical, left translation by `r₀` agrees at each point `x` with left
translation by any `x * b * x⁻¹` with the same `c`, and functions reproduced by `e` are uniformly
continuous under small right translations, so left translation by `r₀` is within `1 / 2` of the
identity on `V`. An operator anticommuting with one so close to the identity vanishes
(`TauCeti.apply_eq_zero_of_mul_eq_neg_mul`), so `T ^ k = 0` on `V`, and injectivity gives
`V = 0`. Only the idempotence `e ⋆ e = e` of the kernel enters; neither its continuity nor its
symmetry nor the minimal idempotence identity of an idempotent kernel is used.

## Main results

* `TauCeti.rightRegularIntegral_apply_eq_zero`: an idempotent `e ⋆ e = e` kills the bounded
  continuous functions invariant under the radical of a group of dilations.
* `TauCeti.IsIdempotentKernel.integral_mul_comp_mul_left_eq_zero`: the same statement for an
  idempotent kernel, `∫ g, e g * f (x * g) ∂μ = 0`.

## References

* R. Godement, C. R. Acad. Sci. Paris 225 (1947), for the cuspidality of coefficients of
  integrable discrete series.
* N. R. Wallach, *Real reductive groups I*, Academic Press (1988), Chapter 7.
* B. Barnes, Proc. Edinburgh Math. Soc. 23 (1980), and A. Valette, Math. Ann. 294 (1992), for
  arguments through minimal idempotents.

## Provenance

The strategy of the proof of `TauCeti.rightRegularIntegral_apply_eq_zero` (a reproducing operator
twisted by a phase of the height, and a dilation close to the identity anticommuting with a power
of it) is that of `New.DiscreteSeries.integral_idempotentKernel_mul_eq_zero` (file
`src/Lib/DiscreteSeries/CuspKernel.lean`) in grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC). The statement here is more general: only the
idempotence `e ⋆ e = e` of the kernel is assumed, and the variation bound `ℓ` need not be
integrable against `‖e‖`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*}

section Phase

variable [TopologicalSpace G] {H : G → ℝ} (hH : Continuous H)

/-- The phase `z ↦ exp (i t H z)`, a bounded continuous function of modulus one. -/
private def phase (t : ℝ) : G →ᵇ ℂ :=
  .ofNormedAddCommGroup (fun z => Complex.exp (Complex.I * ↑(t * H z))) (by fun_prop) 1
    fun z => (Complex.norm_exp_I_mul_ofReal _).le

private theorem phase_apply (t : ℝ) (z : G) :
    phase hH t z = Complex.exp (Complex.I * ↑(t * H z)) := by
  rw [phase, BoundedContinuousFunction.coe_ofNormedAddCommGroup]

private theorem norm_phase_apply (t : ℝ) (z : G) : ‖phase hH t z‖ = 1 := by
  rw [phase_apply]
  exact Complex.norm_exp_I_mul_ofReal _

include hH in
/-- The right variation of the phase is controlled by that of `H`. -/
private theorem norm_phase_mul_sub_le [Group G] {ℓ : G → ℝ}
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g) (t : ℝ)
    (z g : G) : ‖phase hH t (z * g) - phase hH t z‖ ≤ |t| * ℓ g := by
  have h : phase hH t (z * g) - phase hH t z =
      phase hH t z * (Complex.exp (Complex.I * ↑(t * (H (z * g) - H z))) - 1) := by
    rw [phase_apply, phase_apply, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, norm_phase_apply, one_mul]
  calc _ ≤ ‖t * (H (z * g) - H z)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * |H (z * g) - H z| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ |t| * ℓ g := mul_le_mul_of_nonneg_left (hHℓ z g) (abs_nonneg t)

/-- The right variation of the phase is at most `2`. -/
private theorem norm_phase_mul_sub_le_two [Mul G] (t : ℝ) (z g : G) :
    ‖phase hH t (z * g) - phase hH t z‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_phase_apply, norm_phase_apply]
  norm_num

/-- The supremum `sup_z ‖φ (z * g) - φ z‖` of the right variation by `g` of the phase
`φ = exp (i t H)`. -/
private def phaseVar [Mul G] (t : ℝ) (g : G) : ℝ :=
  ⨆ z, ‖phase hH t (z * g) - phase hH t z‖

private theorem bddAbove_phaseVar [Mul G] (t : ℝ) (g : G) :
    BddAbove (Set.range fun z => ‖phase hH t (z * g) - phase hH t z‖) :=
  ⟨2, Set.forall_mem_range.2 fun z => norm_phase_mul_sub_le_two hH t z g⟩

private theorem norm_phase_mul_sub_le_phaseVar [Mul G] (t : ℝ) (z g : G) :
    ‖phase hH t (z * g) - phase hH t z‖ ≤ phaseVar hH t g :=
  le_ciSup (bddAbove_phaseVar hH t g) z

private theorem phaseVar_nonneg [Mul G] [Nonempty G] (t : ℝ) (g : G) : 0 ≤ phaseVar hH t g :=
  (norm_nonneg _).trans (norm_phase_mul_sub_le_phaseVar hH t (Classical.arbitrary G) g)

private theorem phaseVar_le_two [Mul G] [Nonempty G] (t : ℝ) (g : G) : phaseVar hH t g ≤ 2 :=
  ciSup_le fun z => norm_phase_mul_sub_le_two hH t z g

private theorem phaseVar_le [Group G] {ℓ : G → ℝ} (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g)
    (t : ℝ) (g : G) : phaseVar hH t g ≤ |t| * ℓ g :=
  ciSup_le fun z => norm_phase_mul_sub_le hH hHℓ t z g

/-- `phaseVar` is lower semicontinuous, as a supremum of continuous functions, hence
measurable. -/
private theorem measurable_phaseVar [Mul G] [SeparatelyContinuousMul G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (t : ℝ) : Measurable (phaseVar hH t) :=
  (lowerSemicontinuous_ciSup (bddAbove_phaseVar hH t) fun z =>
    (((phase hH t).continuous.comp (continuous_const_mul z)).sub
      continuous_const).norm.lowerSemicontinuous).measurable

/-- An element `(r, c)` of `D` multiplies the phase by `exp (-i t log ‖c‖)`. -/
private theorem phase_mul_left [Group G] {D : Subgroup (G × ℂˣ)}
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    {r : G} {c : ℂˣ} (hrc : (r, c) ∈ D) (t : ℝ) (z : G) :
    phase hH t (r * z) =
      Complex.exp (-(Complex.I * ↑(t * Real.log ‖(c : ℂ)‖))) * phase hH t z := by
  rw [phase_apply, phase_apply, ← Complex.exp_add, hD_shift _ hrc z]
  congr 1
  push_cast
  ring

variable [Group G] [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {e : G → ℂ} {μ : Measure G}

/-- The twist error `∫ ‖e g‖ * phaseVar t g` is finite. -/
private theorem integrable_norm_mul_phaseVar (he : Integrable e μ) (t : ℝ) :
    Integrable (fun g => ‖e g‖ * phaseVar hH t g) μ :=
  (he.norm.const_mul 2).mono'
    (he.norm.aestronglyMeasurable.mul (measurable_phaseVar hH t).aestronglyMeasurable)
    (Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (phaseVar_nonneg hH t g)),
        mul_comm 2]
      exact mul_le_mul_of_nonneg_left (phaseVar_le_two hH t g) (norm_nonneg _))

/-- **The twist error tends to `0` with the twist**, by dominated convergence, since
`phaseVar t g ≤ min 2 (|t| ℓ g)`. -/
private theorem tendsto_integral_norm_mul_phaseVar (he : Integrable e μ) {ℓ : G → ℝ}
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g) :
    Tendsto (fun t => ∫ g, ‖e g‖ * phaseVar hH t g ∂μ) (𝓝 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (fun g => 2 * ‖e g‖)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun t => (integrable_norm_mul_phaseVar hH he t).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (phaseVar_nonneg hH t g)),
        mul_comm 2]
      exact mul_le_mul_of_nonneg_left (phaseVar_le_two hH t g) (norm_nonneg _))
    (he.norm.const_mul 2) (Eventually.of_forall fun g => by
      have h0 : Tendsto (fun t : ℝ => ‖e g‖ * (|t| * ℓ g)) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun t : ℝ => ‖e g‖ * (|t| * ℓ g) := by fun_prop
        simpa using hc.tendsto 0
      exact squeeze_zero (fun t => mul_nonneg (norm_nonneg _) (phaseVar_nonneg hH t g))
        (fun t => mul_le_mul_of_nonneg_left (phaseVar_le hH hHℓ t g) (norm_nonneg _)) h0)
  simpa using h

end Phase

section Vanishing

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {e : G → ℂ} {μ : Measure G} [μ.IsMulLeftInvariant]
  {D : Subgroup (G × ℂˣ)} {H ℓ : G → ℝ} (hH : Continuous H)

variable (e μ D) in
/-- The bounded continuous functions `F` reproduced by `e`, `ρ(e) F = F`, and left invariant
under the radical `{r | (r, 1) ∈ D}`. -/
private def reproducing : Submodule ℂ (G →ᵇ ℂ) where
  carrier := {F | rightRegularIntegral e μ F = F ∧
    ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g, F (r * g) = F g}
  add_mem' {F F'} hF hF' :=
    ⟨by rw [map_add, hF.1, hF'.1], fun r hr g => by simp [hF.2 r hr g, hF'.2 r hr g]⟩
  zero_mem' := ⟨map_zero _, fun _ _ _ => rfl⟩
  smul_mem' c F hF := ⟨by rw [map_smul, hF.1], fun r hr g => by simp [hF.2 r hr g]⟩

/-- An idempotent `e ⋆ e = e` maps the functions invariant under the radical into `V`. -/
private theorem rightRegularIntegral_mem_reproducing [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e) {f : G →ᵇ ℂ}
    (hf : ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g, f (r * g) = f g) :
    rightRegularIntegral e μ f ∈ reproducing e μ D := by
  refine ⟨?_, fun r hr g => ?_⟩
  · rw [← mul_apply_eq_comp, (isIdempotentElem_rightRegularIntegral he_idem).eq]
  · simp only [rightRegularIntegral_apply he, mul_assoc, hf r hr]

variable (e μ) in
/-- The twisted reproducing operator `F ↦ ρ(e) (exp (i t H) * F)`. -/
private def twisted (t : ℝ) : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ :=
  rightRegularIntegral e μ ∘L ContinuousLinearMap.mul ℂ (G →ᵇ ℂ) (phase hH t)

omit [μ.IsMulLeftInvariant] in
private theorem twisted_apply (t : ℝ) (F : G →ᵇ ℂ) :
    twisted e μ hH t F = rightRegularIntegral e μ (phase hH t * F) := by
  rw [twisted, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']

/-- The twisted operator maps `V` into itself. -/
private theorem twisted_mem_reproducing [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖) (t : ℝ)
    {F : G →ᵇ ℂ} (hF : F ∈ reproducing e μ D) : twisted e μ hH t F ∈ reproducing e μ D := by
  rw [twisted_apply]
  exact rightRegularIntegral_mem_reproducing he he_idem fun r hr g => by
    simp [phase_mul_left hH hD_shift hr, hF.2 r hr g]

omit [μ.IsMulLeftInvariant] in
/-- Left translation by the first component of an element of `D` maps `V` into itself, since it
normalizes the radical. -/
private theorem compContinuous_mulLeft_mem_reproducing {r : G} {c : ℂˣ} (hrc : (r, c) ∈ D)
    {F : G →ᵇ ℂ} (hF : F ∈ reproducing e μ D) :
    F.compContinuous (ContinuousMap.mulLeft r) ∈ reproducing e μ D := by
  refine ⟨by rw [rightRegularIntegral_compContinuous_mulLeft, hF.1], fun ρ hρ g => ?_⟩
  have hmem : (r * ρ * r⁻¹, (1 : ℂˣ)) ∈ D := by
    simpa using D.mul_mem (D.mul_mem hrc hρ) (D.inv_mem hrc)
  simpa [mul_assoc] using hF.2 _ hmem (r * g)

omit [μ.IsMulLeftInvariant] in
/-- Left translation by `r` with `(r, c) ∈ D` commutes with the twisted operator up to the
factor `exp (-i t log ‖c‖)`. -/
private theorem compContinuousCLM_mul_twisted
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖) {r : G} {c : ℂˣ}
    (hrc : (r, c) ∈ D) (t : ℝ) :
    BoundedContinuousFunction.compContinuousCLM ℂ ℂ (ContinuousMap.mulLeft r) * twisted e μ hH t =
      Complex.exp (-(Complex.I * ↑(t * Real.log ‖(c : ℂ)‖))) •
        (twisted e μ hH t * BoundedContinuousFunction.compContinuousCLM ℂ ℂ
          (ContinuousMap.mulLeft r)) := by
  ext F : 1
  simp only [mul_apply_eq_comp, smul_apply, BoundedContinuousFunction.compContinuousCLM_apply,
    twisted_apply, ← rightRegularIntegral_compContinuous_mulLeft]
  have h : (phase hH t * F).compContinuous (ContinuousMap.mulLeft r) =
      Complex.exp (-(Complex.I * ↑(t * Real.log ‖(c : ℂ)‖))) •
        (phase hH t * F.compContinuous (ContinuousMap.mulLeft r)) := by
    ext z
    simp [phase_mul_left hH hD_shift hrc, mul_assoc]
  rw [h, map_smul]

/-- **Left translation by `r₀` is close to the identity on `V`.** At each point `z`, left
translation by `r₀` agrees on `V` with left translation by a conjugate `z * b * z⁻¹` carrying the
same `c`, that is with right translation by `b`, which moves functions reproduced by `e` by at
most `∫ ‖e (b⁻¹ * ·) - e‖` times their norm. -/
private theorem norm_compContinuous_mulLeft_sub_le (he : Integrable e μ) {W : Set G} {δ : ℝ}
    (hδ : 0 ≤ δ) (hW : ∀ b ∈ W, ∫ g, ‖e (b⁻¹ * g) - e g‖ ∂μ ≤ δ) {r₀ : G} {c : ℂˣ}
    (hr₀ : (r₀, c) ∈ D) (hc : ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D) {F : G →ᵇ ℂ}
    (hF : F ∈ reproducing e μ D) :
    ‖F.compContinuous (ContinuousMap.mulLeft r₀) - F‖ ≤ δ * ‖F‖ := by
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hδ (norm_nonneg F))).2 fun z => ?_
  obtain ⟨b, hbW, hb⟩ := hc z
  have hρ : (r₀ * (z * b * z⁻¹)⁻¹, (1 : ℂˣ)) ∈ D := by
    simpa using D.mul_mem hr₀ (D.inv_mem hb)
  have h₁ : F (r₀ * z) = F (z * b) := by
    rw [← hF.2 _ hρ (z * b)]
    group
  -- `F (z * b) - F z` is `ρ(e (b⁻¹ * ·) - e) F` at `z`.
  have hb' : Integrable (fun g => e (b⁻¹ * g)) μ := he.comp_mul_left b⁻¹
  have h₂ : F (z * b) - F z = rightRegularIntegral ((fun g => e (b⁻¹ * g)) - e) μ F z := by
    rw [rightRegularIntegral_sub hb' he, sub_apply, sub_apply, rightRegularIntegral_apply hb',
      ← rightRegularIntegral_apply_mul he, hF.1]
  rw [sub_apply, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mulLeft, h₁, h₂]
  calc _ ≤ ‖rightRegularIntegral ((fun g => e (b⁻¹ * g)) - e) μ F‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ z
    _ ≤ ‖rightRegularIntegral ((fun g => e (b⁻¹ * g)) - e) μ‖ * ‖F‖ :=
        ContinuousLinearMap.le_opNorm _ F
    _ ≤ δ * ‖F‖ :=
        mul_le_mul_of_nonneg_right (norm_rightRegularIntegral_le.trans (hW b hbW)) (norm_nonneg F)

omit [μ.IsMulLeftInvariant] in
/-- **The twisted operator is almost injective on reproduced functions**: it is within the twist
error `∫ ‖e g‖ * phaseVar t g` of multiplication by the phase, which preserves the norm. -/
private theorem norm_mul_one_sub_le_norm_twisted (he : Integrable e μ) (t : ℝ) {F : G →ᵇ ℂ}
    (hF : rightRegularIntegral e μ F = F) :
    ‖F‖ * (1 - ∫ g, ‖e g‖ * phaseVar hH t g ∂μ) ≤ ‖twisted e μ hH t F‖ := by
  set C := ∫ g, ‖e g‖ * phaseVar hH t g ∂μ
  have hC : 0 ≤ C := integral_nonneg fun g => mul_nonneg (norm_nonneg _) (phaseVar_nonneg hH t g)
  suffices h : ‖F‖ ≤ ‖twisted e μ hH t F‖ + C * ‖F‖ by linarith
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun z => ?_
  -- `T F - φ z • F` is `ρ(e) (φ * F - φ z • F)`.
  have hd : twisted e μ hH t F z - phase hH t z * F z =
      ∫ g, e g * ((phase hH t (z * g) - phase hH t z) * F (z * g)) ∂μ := by
    have h : twisted e μ hH t F - phase hH t z • F =
        rightRegularIntegral e μ (phase hH t * F - phase hH t z • F) := by
      rw [map_sub, map_smul, hF, twisted_apply]
    have h' := congrArg (fun F' : G →ᵇ ℂ => F' z) h
    simp only [sub_apply, smul_apply, smul_eq_mul] at h'
    rw [h', rightRegularIntegral_apply he]
    congr 1 with g
    simp only [sub_apply, smul_apply, smul_eq_mul, FunLike.coe_mul, Pi.mul_apply]
    ring
  have hpt : ∀ g, ‖e g * ((phase hH t (z * g) - phase hH t z) * F (z * g))‖ ≤
      ‖e g‖ * phaseVar hH t g * ‖F‖ := fun g => by
    rw [norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_phase_mul_sub_le_phaseVar hH t z g)
      (norm_nonneg _)) (F.norm_coe_le_norm _) (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (phaseVar_nonneg hH t g))
  have hle : ‖twisted e μ hH t F z - phase hH t z * F z‖ ≤ C * ‖F‖ := by
    rw [hd, ← integral_mul_const]
    exact norm_integral_le_of_norm_le ((integrable_norm_mul_phaseVar hH he t).mul_const _)
      (Eventually.of_forall hpt)
  calc ‖F z‖ = ‖phase hH t z * F z‖ := by rw [norm_mul, norm_phase_apply, one_mul]
    _ = ‖twisted e μ hH t F z - (twisted e μ hH t F z - phase hH t z * F z)‖ := by
        rw [sub_sub_cancel]
    _ ≤ ‖twisted e μ hH t F z‖ + ‖twisted e μ hH t F z - phase hH t z * F z‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add ((twisted e μ hH t F).norm_coe_le_norm z) hle

/-- The powers of the twisted operator map `V` into itself. -/
private theorem pow_twisted_mem_reproducing [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖) (t : ℝ) (n : ℕ)
    {F : G →ᵇ ℂ} (hF : F ∈ reproducing e μ D) :
    (twisted e μ hH t ^ n) F ∈ reproducing e μ D := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact twisted_mem_reproducing hH he he_idem hD_shift t ih

/-- On `V`, the powers of the twisted operator satisfy
`‖F‖ * (1 - ∫ ‖e‖ phaseVar t) ^ n ≤ ‖T ^ n F‖`. -/
private theorem norm_mul_pow_le_norm_pow_twisted [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    {t : ℝ} (ht : ∫ g, ‖e g‖ * phaseVar hH t g ∂μ ≤ 1) (n : ℕ) {F : G →ᵇ ℂ}
    (hF : F ∈ reproducing e μ D) :
    ‖F‖ * (1 - ∫ g, ‖e g‖ * phaseVar hH t g ∂μ) ^ n ≤ ‖(twisted e μ hH t ^ n) F‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (twisted e μ hH t) n, mul_apply_eq_comp, pow_succ, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right ih (by linarith)).trans
      (norm_mul_one_sub_le_norm_twisted hH he t
        (pow_twisted_mem_reproducing hH he he_idem hD_shift t n hF).1)

omit [μ.IsMulLeftInvariant] in
include hH in
/-- **An integrable idempotent kills the functions invariant under the radical of a group of
dilations.** Let `μ` be a left Haar measure on a second countable locally compact group `G`, and
`e : G → ℂ` with `e ⋆ e = e` almost everywhere. Let `H : G → ℝ` be continuous with
`|H (x * g) - H x| ≤ ℓ g` for all `x` and `g`, and `D` a subgroup of `G × ℂˣ` such that
`H (r * g) = H g - log ‖c‖` for `(r, c) ∈ D`, and such that every neighbourhood `W` of `1` has a
`c` with `log ‖c‖ ≠ 0` for which every `x` admits `b ∈ W` with `(x * b * x⁻¹, c) ∈ D`. Then
`ρ(e) f = 0` for every bounded continuous `f` with `f (r * g) = f g` whenever `(r, 1) ∈ D`. For
integrable `e` this says `∫ g, e g * f (x * g) ∂μ = 0` for all `x`
(`TauCeti.rightRegularIntegral_apply`); for non-integrable `e` the operator `ρ(e)` is `0` by
definition. -/
theorem rightRegularIntegral_apply_eq_zero [LocallyCompactSpace G] [μ.IsHaarMeasure]
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    (hD_near : ∀ W ∈ 𝓝 (1 : G), ∃ c : ℂˣ, Real.log ‖(c : ℂ)‖ ≠ 0 ∧
      ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D)
    {f : G →ᵇ ℂ} (hf : ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g : G, f (r * g) = f g) :
    rightRegularIntegral e μ f = 0 := by
  by_cases he : Integrable e μ
  swap
  · simp [rightRegularIntegral_of_not_integrable he]
  -- It suffices that the space `V` of reproduced radical-invariant functions is `0`.
  suffices hV : ∀ F ∈ reproducing e μ D, F = 0 from
    hV _ (rightRegularIntegral_mem_reproducing he he_idem hf)
  intro F hF
  -- A dilation `(b₀, c)` with `log ‖c‖ ≠ 0` whose conjugates `x * b * x⁻¹` carrying the same
  -- `c` have `b` so close to `1` that right translation by `b` moves `V` by at most `1 / 2`.
  obtain ⟨c, hc, hcD⟩ := hD_near _
    ((he.tendsto_integral_norm_comp_inv_mul_sub).eventually (gt_mem_nhds one_half_pos))
  obtain ⟨b₀, -, hb₀⟩ := hcD 1
  rw [one_mul, inv_one, mul_one] at hb₀
  -- A tolerance `δ` such that the twist error is `< 1` for `|t| < δ`, and a twist `t = -s / L`
  -- with `|t| < δ` for which `T ^ k` anticommutes with left translation by `b₀`.
  obtain ⟨δ, hδ, hδC⟩ := Metric.eventually_nhds_iff.1
    ((tendsto_integral_norm_mul_phaseVar hH he hHℓ).eventually (gt_mem_nhds one_pos))
  set L := Real.log ‖(c : ℂ)‖
  have hL : 0 < |L| := abs_pos.2 hc
  obtain ⟨k, s, hs, hsk⟩ := Complex.exists_abs_lt_and_exp_mul_I_pow_eq_neg_one (mul_pos hδ hL)
  have htC : ∫ g, ‖e g‖ * phaseVar hH (-s / L) g ∂μ < 1 := hδC <| by
    rwa [Real.dist_0_eq_abs, abs_div, abs_neg, div_lt_iff₀ hL]
  have hζ : Complex.exp (-(Complex.I * ↑(-s / L * L))) ^ k = -1 := by
    rw [div_mul_cancel₀ _ hc, ← hsk]
    congr 2
    push_cast
    ring
  have hST : BoundedContinuousFunction.compContinuousCLM ℂ ℂ (ContinuousMap.mulLeft b₀) *
      twisted e μ hH (-s / L) ^ k = -(twisted e μ hH (-s / L) ^ k *
        BoundedContinuousFunction.compContinuousCLM ℂ ℂ (ContinuousMap.mulLeft b₀)) := by
    rw [mul_pow_of_mul_eq_smul_mul (compContinuousCLM_mul_twisted hH hD_shift hb₀ _) k, hζ,
      neg_one_smul]
  -- So `T ^ k` vanishes on `V`, while `‖T ^ k F‖ ≥ (1 - ε(t)) ^ k ‖F‖`.
  have hzero := apply_eq_zero_of_mul_eq_neg_mul
    (fun F hF => compContinuous_mulLeft_mem_reproducing hb₀ hF)
    (fun F hF => pow_twisted_mem_reproducing hH he he_idem hD_shift _ k hF) hST one_half_lt_one
    (fun F hF => norm_compContinuous_mulLeft_sub_le he one_half_pos.le
      (fun b hb => le_of_lt hb) hb₀ hcD hF) hF
  have h := norm_mul_pow_le_norm_pow_twisted hH he he_idem hD_shift htC.le k hF
  rw [hzero, norm_zero] at h
  exact norm_eq_zero.mp <| le_antisymm
    (nonpos_of_mul_nonpos_left h (pow_pos (by linarith) k)) (norm_nonneg F)

end Vanishing

/-- **Idempotent kernels kill the bounded functions invariant under the radical of a group of
dilations**: `∫ g, e g * f (x * g) ∂μ = 0` under the hypotheses of
`TauCeti.rightRegularIntegral_apply_eq_zero`, for an idempotent kernel `e`. -/
theorem IsIdempotentKernel.integral_mul_comp_mul_left_eq_zero [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] {e : G → ℂ} (he : IsIdempotentKernel e μ)
    {H ℓ : G → ℝ} (hH : Continuous H) (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g)
    {D : Subgroup (G × ℂˣ)}
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    (hD_near : ∀ W ∈ 𝓝 (1 : G), ∃ c : ℂˣ, Real.log ‖(c : ℂ)‖ ≠ 0 ∧
      ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D)
    (f : G →ᵇ ℂ) (hf : ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g : G, f (r * g) = f g) (x : G) :
    ∫ g, e g * f (x * g) ∂μ = 0 := by
  rw [← rightRegularIntegral_apply he.integrable, rightRegularIntegral_apply_eq_zero hH
    (Eventually.of_forall he.integral_mul_inv_mul) hHℓ hD_shift hD_near hf,
    FunLike.coe_zero, Pi.zero_apply]

end TauCeti
