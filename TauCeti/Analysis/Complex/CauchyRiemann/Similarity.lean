/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Similarity
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# The similarity principle for classical solutions of linear Cauchy–Riemann equations

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` open, and `ξ : ℂ → V` a map of
class `C¹` on `Ω` solving the linear Cauchy–Riemann equation

`∂ₛξ + i ∂ₜξ + C ξ = 0`

on `Ω`, in the coordinate `z = s + i t`, for a measurable, locally bounded (for instance
continuous) field `C` of *real*-linear endomorphisms of `V`. The **similarity principle** says
that near every point `z₀ ∈ Ω` the solution factors as `ξ = Φ σ` with `Φ` a continuous family of
invertible complex-linear maps and `σ` holomorphic (`TauCeti.exists_similarity_of_contDiffOn`).
In particular `ξ` has a similarity factorization in the sense of
`TauCeti.HasSimilarityFactorizationAt` at every point of `Ω`
(`TauCeti.hasSimilarityFactorizationAt_of_contDiffOn`), so it inherits the zero structure of a
holomorphic map: unique continuation from a zero of infinite order
(`TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO`) and isolated zeros
(`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`).

The coefficient `C` need not commute with `i`, and a solution is in general not holomorphic.
These are the classical cases of the similarity principle for weak solutions
(`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn`): on a disc about `z₀` on which `C`
is bounded, a `C¹` solution is a weak solution and the bounded coefficient is locally `Lᵖ` for
every `p`, say `p = 3`.

## Main results

* `TauCeti.exists_similarity_of_contDiffOn`: the local factorization `ξ = Φ σ` on a disc.
* `TauCeti.hasSimilarityFactorizationAt_of_contDiffOn`: the factorization in the form consumed by
  `TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.
* `TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO`: unique continuation from a zero of infinite
  order.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn`: a solution that is not identically
  zero on a connected open set has isolated zeros.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and its proof.
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Set ℂ} {ξ : ℂ → V} {C : ℂ → V →L[ℝ] V}

/-- **The similarity principle** (Carleman) for classical solutions. Let `ξ` be of class `C¹` on
an open set `Ω ⊆ ℂ` and solve `∂ₛξ + i ∂ₜξ + C ξ = 0` on `Ω`, for a measurable, locally bounded
field `C` of real-linear endomorphisms of a finite-dimensional complex normed space `V` (for
instance a continuous one). Then every point `z₀ ∈ Ω` is the centre of a disc in `Ω` on which
`ξ = Φ σ`, with `Φ` a continuous family of invertible complex-linear maps and `σ` holomorphic. -/
theorem exists_similarity_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℂ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  have := FiniteDimensional.completeSpace ℂ V
  -- an open disc `B` about `z₀` in `Ω` on which `C` is bounded
  obtain ⟨M, hM⟩ := hCb z₀ hz₀
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.1 (inter_mem hM (hΩ.mem_nhds hz₀))
  let B : Opens ℂ := ⟨ball z₀ R, isOpen_ball⟩
  have hBΩ : (B : Set ℂ) ⊆ Ω := fun z hz ↦ (hRΩ hz).2
  -- there `ξ` is a weak solution, and `C` is locally `L³`
  have h : IsWeakLinearCauchyRiemannOn ((3 : ℝ≥0) : ℝ≥0∞) B
      (fun _ ↦ I • ContinuousLinearMap.id ℝ V) C ξ :=
    isWeakCauchyRiemannOn_of_contDiffOn (hξ.mono hBΩ) fun z hz ↦ by
      simpa using eq_neg_of_add_eq_zero_left (heq z (hBΩ hz))
  have hC : MemLpLoc ((3 : ℝ≥0) : ℝ≥0∞) B C := memLpLoc_iff.2 fun K hK hc ↦ by
    have := isFiniteMeasure_restrict.2 (hc.measure_lt_top (μ := volume)).ne
    exact MemLp.of_bound (hCm.mono_measure (Measure.restrict_mono (hK.trans hBΩ) le_rfl)) M
      (ae_restrict_of_forall_mem hc.measurableSet fun z hz ↦ (hRΩ (hK hz)).1)
  obtain ⟨r, hr, hrB, Φ, σ, hΦ, -, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn (by norm_num) h hC (mem_ball_self hR)
  exact ⟨r, hr, hrB.trans hBΩ, Φ, σ, hΦ, hΦu, hσ, hξσ⟩

/-- A `C¹` solution of `∂ₛξ + i ∂ₜξ + C ξ = 0` on an open set `Ω`, with measurable, locally
bounded real-linear coefficient `C`, has a similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_contDiffOn (hΩ : IsOpen Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  obtain ⟨r, hr, -, Φ, σ, hΦ, hΦu, hσ, hξσ⟩ :=
    exists_similarity_of_contDiffOn hΩ hξ hCm hCb heq hz₀
  -- restricting the scalars of the unit `Φ z₀` to `ℝ` keeps it invertible
  exact .of_eqOn_ball hr (Φ := fun z ↦ (Φ z).restrictScalars ℝ)
    ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℂ).continuous.comp_continuousOn hΦ)
    (ContinuousLinearMap.isUnit_restrictScalars (hΦu z₀ (mem_ball_self hr))) hσ hξσ

/-- **Unique continuation** for classical solutions. On a connected open set `Ω`, a `C¹` solution
of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with measurable, locally bounded real-linear coefficient `C`, that
vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_forall_isBigO (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz) hz₀ h₀

/-- **Isolated zeros** of classical solutions. On a connected open set `Ω`, the zeros of a `C¹`
solution of `∂ₛξ + i ∂ₜξ + C ξ = 0`, with measurable, locally bounded real-linear coefficient
`C`, that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I + C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  have := FiniteDimensional.completeSpace ℂ V
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc hξ.continuousOn
    (fun _ hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz) hne

end TauCeti
