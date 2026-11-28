/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Incompressible.Solenoidal
public import TauCeti.MeasureTheory.Function.Lp.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Translation, convolution and mollification of solenoidal fields

The closed solenoidal subspace `Lᵖ_σ(E)` of `Lᵖ(E; E)` is invariant under translations, and
hence under convolution with an integrable scalar kernel: for `p < ∞` the convolution
`TauCeti.convolutionLp` is the `Lᵖ`-valued Bochner integral `∫ k(y) • u(· - y) dy` of
translates, and each pairing with a test gradient is a continuous linear functional, which
commutes with the Bochner integral and vanishes on every translate.

Mollification therefore maps `Lᵖ_σ` into smooth solenoidal fields: convolving with a compactly
supported `C¹` kernel produces a `C¹` field whose classical divergence vanishes everywhere.
Combined with the approximate identity `TauCeti.tendsto_normedBumpLp`, every
field of `Lᵖ_σ`, `1 ≤ p < ∞`, is an `Lᵖ` limit of solenoidal fields with smooth
representatives.

## Main declarations

* `TauCeti.translateLp_mem_solenoidalLp_iff`: translation preserves and reflects `Lᵖ_σ`.
* `TauCeti.convolutionLp_mem_solenoidalLp`: convolution with a scalar kernel preserves `Lᵖ_σ`.
* `TauCeti.isSolenoidalOn_convolution`: the pointwise convolution of a field in `Lᵖ_σ` with an
  integrable scalar kernel is weakly solenoidal.
* `TauCeti.trace_fderiv_convolution_eq_zero`: the mollification of a field in `Lᵖ_σ` by a
  compactly supported `C¹` kernel has vanishing classical divergence at every point.
* `TauCeti.mem_closure_contDiff_of_mem_solenoidalLp`: fields of `Lᵖ_σ` are `Lᵖ` limits of fields
  of `Lᵖ_σ` with smooth representatives.

## References

* T. Tao, *254A: Incompressible fluid equations*, Notes 1 (2018).
* G. P. Galdi, *An Introduction to the Mathematical Theory of the Navier–Stokes Equations*,
  2nd ed., Springer, 2011, Section III.2.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace ContinuousLinearMap Filter
open scoped ENNReal Convolution Distributions Gradient InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E}

section Translation

variable [CompleteSpace E] [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ]
  [IsLocallyFiniteMeasure μ]

/-- Translating an `Lᵖ` field preserves and reflects membership in the solenoidal subspace. -/
theorem translateLp_mem_solenoidalLp_iff {u : Lp E p μ} {a : E} :
    μ.translateLp p a u ∈ solenoidalLp E p μ ↔ u ∈ solenoidalLp E p μ := by
  suffices h : ∀ (v : Lp E p μ) (b : E), v ∈ solenoidalLp E p μ →
      μ.translateLp p b v ∈ solenoidalLp E p μ by
    refine ⟨fun hu ↦ ?_, h u a⟩
    have h' := h _ (-a) hu
    rwa [← Measure.translateLp_symm, LinearIsometryEquiv.symm_apply_apply] at h'
  intro v b hv
  rw [mem_solenoidalLp_iff] at hv ⊢
  exact (hv.comp_add_right (V := ⊤) (a := b) (mapsTo_univ _ _)).congr_ae
    (ae_restrict_of_ae (Measure.coeFn_translateLp b v).symm)

end Translation

section Convolution

variable [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

/-- **Convolution preserves solenoidality.** For `p < ∞`, convolution with a scalar kernel maps
`Lᵖ_σ(E)` into itself. The kernel is unrestricted because `TauCeti.convolutionLp` is zero for a
non-integrable kernel. -/
theorem convolutionLp_mem_solenoidalLp (hp : p ≠ ∞) (k : E → ℝ) {u : Lp E p μ}
    (hu : u ∈ solenoidalLp E p μ) : convolutionLp hp k μ u ∈ solenoidalLp E p μ := by
  by_cases hk : Integrable k μ
  swap
  · rw [convolutionLp_of_not_integrable hp hk, zero_apply]
    exact zero_mem _
  rw [mem_solenoidalLp_iff_testGradientPairingCLM_eq_zero]
  intro φ
  -- The pairing with `∇φ` is a continuous linear functional on `Lᵖ`, so it commutes with the
  -- `Lᵖ`-valued integral defining the convolution and vanishes on each translate of `u`.
  rw [convolutionLp_apply hp hk,
    ← integral_comp_comm _ (integrable_smul_translateLp hp hk u)]
  simp [fun y : E ↦ mem_solenoidalLp_iff_testGradientPairingCLM_eq_zero.mp
    (translateLp_mem_solenoidalLp_iff (a := -y) |>.mpr hu) φ]

/-- The pointwise convolution `k ⋆ u` of a field `u ∈ Lᵖ_σ(E)`, `p < ∞`, with an integrable
scalar kernel is weakly solenoidal on the whole space. -/
theorem isSolenoidalOn_convolution (hp : p ≠ ∞) {k : E → ℝ} (hk : Integrable k μ)
    {u : Lp E p μ} (hu : u ∈ solenoidalLp E p μ) :
    IsSolenoidalOn μ ⊤ (k ⋆[lsmul ℝ ℝ, μ] (u : E → E)) :=
  (mem_solenoidalLp_iff.mp (convolutionLp_mem_solenoidalLp hp k hu)).congr_ae
    (ae_restrict_of_ae (convolutionLp_ae_eq_convolution_coeFn hp hk u))

/-- **Mollification of solenoidal fields.** If `ρ` is a compactly supported `C¹` scalar kernel
and `u ∈ Lᵖ_σ(E)` with `p < ∞`, then the `C¹` field `ρ ⋆ u` has vanishing classical divergence
at every point. Its smoothness is `HasCompactSupport.contDiff_convolution_left`. -/
theorem trace_fderiv_convolution_eq_zero (hp : p ≠ ∞) {ρ : E → ℝ} (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) {u : Lp E p μ} (hu : u ∈ solenoidalLp E p μ) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] (u : E → E)) x) = 0 :=
  (hρc.contDiff_convolution_left _ hρ ((Lp.memLp u).locallyIntegrable Fact.out)).contDiffOn
    |>.isSolenoidalOn_iff.mp
      (isSolenoidalOn_convolution hp (hρ.continuous.integrable_of_hasCompactSupport hρc) hu) x
      trivial

/-- For `p < ∞`, every field of `Lᵖ_σ(E)` is an `Lᵖ` limit of fields of `Lᵖ_σ(E)` with smooth
representatives: the mollifications `ρₙ ⋆ u` of `u` by the shrinking normalized smooth bumps
`ContDiffBump.shrinking`. -/
theorem mem_closure_contDiff_of_mem_solenoidalLp (hp : p ≠ ∞) {u : Lp E p μ}
    (hu : u ∈ solenoidalLp E p μ) :
    u ∈ closure {v : Lp E p μ | v ∈ solenoidalLp E p μ ∧
      ∃ w : E → E, ContDiff ℝ (⊤ : ℕ∞) w ∧ (v : E → E) =ᵐ[μ] w} := by
  let φ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos
  refine mem_closure_of_tendsto
    (tendsto_normedBumpLp hp (ContDiffBump.tendsto_rOut_shrinking one_pos) u)
    (Eventually.of_forall fun n ↦ ?_)
  rw [normedBumpLp_eq_convolutionLp]
  exact ⟨convolutionLp_mem_solenoidalLp hp _ hu, _,
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      ((Lp.memLp u).locallyIntegrable Fact.out),
    convolutionLp_ae_eq_convolution_coeFn hp (φ n).integrable_normed u⟩

end Convolution

end TauCeti
