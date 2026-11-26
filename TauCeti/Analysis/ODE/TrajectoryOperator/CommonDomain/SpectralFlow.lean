/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.SpectralFlow
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.IndexLocalization
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Prod
public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Prod
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The index of the trajectory operator over a common domain and the spectral flow

Let `ι : D →L[ℝ] H` be a compact operator from a Banach space into a Hilbert space, and let `A` be
a continuous path of `ι`-symmetric operators `D → H` with invertible limits at `±∞`. Over the
common domain `D`, the operator `D_A u = (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to
`L²(ℝ, H)` (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator`) is Fredholm
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`), and the index formula of
Robbin and Salamon identifies its index with the spectral flow `TauCeti.domainSpectralFlow ι A a b`
of `A` over any interval `[a, b]` outside which `A` is invertible. In the convention of the
operator `d/ds - A`, whose coefficient is `-A`, this is the formula `ind (∂ₛ - A) = -SF(A)` for
the linearized Floer operator. This file proves the formula for the paths whose crossings stay in a
finite-dimensional block.

* **The identity embedding.** Over the common domain `F` embedded in itself by the identity,
  `D_A` is the trajectory operator `u ↦ u' + A u` on `W^{1,p}(Ω, F)`
  (`TauCeti.WeakDerivStep.trajectoryOperator`) read on another realization of the same graph
  space, so the two have the same index
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_one`) and are Fredholm together
  (`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator_one_iff`).
* **Finite-dimensional paths.** For a continuous path of symmetric operators on a
  finite-dimensional real inner product space `E` with invertible limits, the index of `D_A` over
  the common domain `E` is the spectral flow `TauCeti.domainSpectralFlow 1 A a b` for all `a` far
  enough to the left and `b` far enough to the right
  (`eventually_index_familyDomainTrajectoryOperator_one_eq_domainSpectralFlow` in the namespace
  `TauCeti.WeakDerivStep`).
  This combines the index formula for bounded paths in finite dimensions,
  `TauCeti.WeakDerivStep.eventually_index_trajectoryOperator_eq_spectralFlow`, with the comparison
  `TauCeti.domainSpectralFlow_one` of the two spectral flows.
* **Splitting off an invertible block.** Let `A₁` be such a finite-dimensional path, and let `A₂`
  be a continuous path of `ι`-symmetric operators `D → H` which is invertible at every time, with
  invertible limits. Over the common domain `E ⊕ D` embedded by `1 ⊕ ι`, the index of
  `D_{A₁ ⊕ A₂}` is the spectral flow of `A₁ ⊕ A₂`
  (`eventually_index_familyDomainTrajectoryOperator_withLpProdMap_eq_domainSpectralFlow`
  in the namespace `TauCeti.WeakDerivStep`).
  Both the index and the spectral flow are additive under direct sums
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_withLpProdMap`,
  `TauCeti.domainSpectralFlow_withLpProdMap`), the invertible block contributes to neither
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible`,
  `TauCeti.domainSpectralFlow_eq_zero_of_forall_isInvertible`), and the finite-dimensional block
  is the previous case.

The block form is the local normal form of the index formula: near a crossing `B₀`, the kernel of
`B₀` is finite-dimensional, and splitting it off leaves a block on which the path stays invertible.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4.
-/

public section

namespace TauCeti.WeakDerivStep

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

/-! ### The identity embedding -/

section Identity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the graph space of the identity of `Lᵖ(Ω, F)`, the formula defining
`familyDomainTrajectoryOperator` is the trajectory operator `u ↦ u' + A u`. -/
private theorem apply_compLpL_comp_weakFDerivL_add_operatorMultiplication_comp_prevL
    (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
        (weakFDerivL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) +
      (Lp.operatorMultiplication p AL).comp
        (prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) =
      trajectoryOperator (p := p) AL := by
  refine ContinuousLinearMap.ext fun u ↦ Lp.ext ?_
  filter_upwards [trajectoryOperator_apply_ae AL u,
    Lp.coeFn_add ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p (mu.restrict Omega)
      (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u))
      (Lp.operatorMultiplication p AL
        (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)),
    (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLpL (p := p) (μ := mu.restrict Omega)
      (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u),
    Lp.operatorMultiplication_ae AL
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)] with s h₁ h₂ h₃ h₄
  rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    weakFDerivL_apply, prevL_apply, h₂, Pi.add_apply, h₃, h₄, h₁,
    ContinuousLinearMap.apply_apply]

/-- The graph space of the embedding `1 ∘ ·` of `Lᵖ(Ω, F)` is the graph space of the identity of
`Lᵖ(Ω, F)`, and along this identification the operator `u ↦ (1 ∘ u)' + A u` is the trajectory
operator `u ↦ u' + A u`. The two graph spaces are equal as sets but have different types, since
`(1 : F →L[ℝ] F).compLpL p μ` is only propositionally the identity. -/
private theorem exists_familyDomainTrajectoryOperator_one_eq_comp
    (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    ∃ e : WeakDerivStep mu Omega p ((1 : F →L[ℝ] F).compLpL p (mu.restrict Omega)) ≃L[ℝ]
        WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))),
      familyDomainTrajectoryOperator (p := p) (1 : F →L[ℝ] F) AL =
        (trajectoryOperator AL).comp (e : _ →L[ℝ] _) := by
  rw [familyDomainTrajectoryOperator_def]
  -- Replace the embedding `(1 : F →L[ℝ] F).compLpL p μ` by the identity of `Lᵖ(Ω, F)`, in the
  -- types of the graph spaces as well.
  generalize hb : (1 : F →L[ℝ] F).compLpL p (mu.restrict Omega) = base
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_compLpL] at hb
  subst hb
  exact ⟨.refl ℝ _, by
    rw [apply_compLpL_comp_weakFDerivL_add_operatorMultiplication_comp_prevL,
      ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id]⟩

/-- **The common-domain operator with the identity embedding is the trajectory operator.** Over
the common domain `F` embedded in itself by the identity, `u ↦ (1 ∘ u)' + A u` has the index of the
trajectory operator `u ↦ u' + A u` on `W^{1,p}(Ω, F)`. -/
theorem index_familyDomainTrajectoryOperator_one (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    (familyDomainTrajectoryOperator (p := p) (1 : F →L[ℝ] F) AL).index =
      (trajectoryOperator (p := p) AL).index := by
  obtain ⟨e, he⟩ := exists_familyDomainTrajectoryOperator_one_eq_comp (p := p) AL
  rw [he, ContinuousLinearMap.index_comp_equiv]

/-- Over the common domain `F` embedded in itself by the identity, `u ↦ (1 ∘ u)' + A u` is
Fredholm exactly when the trajectory operator `u ↦ u' + A u` on `W^{1,p}(Ω, F)` is. -/
theorem isFredholm_familyDomainTrajectoryOperator_one_iff
    (AL : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    (familyDomainTrajectoryOperator (p := p) (1 : F →L[ℝ] F) AL).IsFredholm ↔
      (trajectoryOperator (p := p) AL).IsFredholm := by
  obtain ⟨e, he⟩ := exists_familyDomainTrajectoryOperator_one_eq_comp (p := p) AL
  rw [he, ContinuousLinearMap.isFredholm_comp_equiv]

end Identity

/-! ### Finite-dimensional paths -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- **The index is the spectral flow, on a finite-dimensional common domain.** Let `A` be a
continuous path of symmetric operators on a finite-dimensional real inner product space `E`, with
invertible limits at `±∞`. Over the common domain `E` embedded in itself by the identity, for every
`a` far enough to the left and every `b` far enough to the right, the index of
`u ↦ (1 ∘ u)' + A u` from `L²(ℝ, E) ∩ W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is the spectral flow
`TauCeti.domainSpectralFlow 1 A a b`. -/
theorem eventually_index_familyDomainTrajectoryOperator_one_eq_domainSpectralFlow
    (hA : Continuous A) (hsym : ∀ s, (A s : E →ₗ[ℝ] E).IsSymmetric) {Bbot Btop : E →L[ℝ] E}
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hbot : Tendsto A atBot (𝓝 Bbot))
    (htop : Tendsto A atTop (𝓝 Btop)) (AL : Lp (E →L[ℝ] E) ∞ μ₀) (hAL : AL =ᵐ[μ₀] A) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) (1 : E →L[ℝ] E) AL).index =
        domainSpectralFlow 1 A ab.1 ab.2 := by
  -- Both limits are bounded below by `α = (‖Bbot⁻¹‖ + ‖Btop⁻¹‖ + 1)⁻¹`.
  have hle {B : E →L[ℝ] E} (hB : B.IsInvertible) (hle : ‖B.inverse‖ ≤ ‖Bbot.inverse‖ +
      ‖Btop.inverse‖) (v : E) : (‖Bbot.inverse‖ + ‖Btop.inverse‖ + 1)⁻¹ * ‖v‖ ≤ ‖B v‖ := by
    rw [inv_mul_le_iff₀ (by positivity)]
    exact (hB.norm_le_norm_inverse_mul_norm v).trans (by gcongr; linarith)
  filter_upwards [eventually_index_trajectoryOperator_eq_spectralFlow hA hsym (by positivity)
      (hle hBbot (le_add_of_nonneg_right (norm_nonneg _)))
      (hle hBtop (le_add_of_nonneg_left (norm_nonneg _))) hbot htop AL hAL,
    (eventually_le_atBot 0).prod_mk (eventually_ge_atTop 0)] with ⟨a, b⟩ hab ⟨ha, hb⟩
  rw [index_familyDomainTrajectoryOperator_one, hab,
    domainSpectralFlow_one (ha.trans hb) hA.continuousOn
      fun t _ ↦ ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (hsym t)]

end FiniteDimensional

/-! ### Paths splitting off an invertible block -/

section Block

variable {E D H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H} {A₁ : ℝ → E →L[ℝ] E}
  {A₂ : ℝ → D →L[ℝ] H}

/-- **The index is the spectral flow, for paths whose crossings lie in a finite-dimensional
block.** Let `ι : D → H` be a compact operator from a Banach space into a Hilbert space. Let `A₁` be
a continuous path of symmetric operators on a finite-dimensional real inner product space `E`, and
`A₂` a continuous path of `ι`-symmetric operators `D → H` which is invertible at every time. Suppose
that both have invertible limits at `±∞`, and that `A₂` differs from its limit at `∞` on every
bounded interval by operators bounded through `ι`, as in
`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`. Over the common domain `E ⊕ D`
embedded by `1 ⊕ ι`, for every `a` far enough to the left and every `b` far enough to the right,
the index of `u ↦ ((1 ⊕ ι) ∘ u)' + (A₁ ⊕ A₂) u` is the spectral flow of `A₁ ⊕ A₂` from `a` to
`b`. -/
theorem eventually_index_familyDomainTrajectoryOperator_withLpProdMap_eq_domainSpectralFlow
    (hι : IsCompactOperator ι) (hA₁ : Continuous A₁) (hA₂ : Continuous A₂)
    (hsym₁ : ∀ s, (A₁ s : E →ₗ[ℝ] E).IsSymmetric)
    (hSymm₂ : ∀ s x y, ⟪A₂ s x, ι y⟫_ℝ = ⟪ι x, A₂ s y⟫_ℝ) (hInv₂ : ∀ s, (A₂ s).IsInvertible)
    {B₁bot B₁top : E →L[ℝ] E} {B₂bot B₂top : D →L[ℝ] H} (hB₁bot : B₁bot.IsInvertible)
    (hB₁top : B₁top.IsInvertible) (hB₂bot : B₂bot.IsInvertible) (hB₂top : B₂top.IsInvertible)
    (hbot₁ : Tendsto A₁ atBot (𝓝 B₁bot)) (htop₁ : Tendsto A₁ atTop (𝓝 B₁top))
    (hbot₂ : Tendsto A₂ atBot (𝓝 B₂bot)) (htop₂ : Tendsto A₂ atTop (𝓝 B₂top))
    (hc : ∀ T, ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x, ‖(A₂ s - B₂top) x‖ ≤ c * ‖ι x‖)
    (AL : Lp (WithLp 2 (E × D) →L[ℝ] WithLp 2 (E × H)) ∞ μ₀)
    (hAL : AL =ᵐ[μ₀] fun s ↦ (A₁ s).withLpProdMap 2 (A₂ s)) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ((1 : E →L[ℝ] E).withLpProdMap 2 ι) AL).index =
        domainSpectralFlow ((1 : E →L[ℝ] E).withLpProdMap 2 ι)
          (fun s ↦ (A₁ s).withLpProdMap 2 (A₂ s)) ab.1 ab.2 := by
  -- The `L∞` classes of the two blocks.
  obtain ⟨C₁, hC₁⟩ := exists_forall_norm_le_of_tendsto hA₁ hbot₁ htop₁
  obtain ⟨C₂, hC₂⟩ := exists_forall_norm_le_of_tendsto hA₂ hbot₂ htop₂
  have hm₁ : MemLp A₁ ∞ μ₀ := memLp_top_of_bound hA₁.aestronglyMeasurable C₁ (.of_forall hC₁)
  have hm₂ : MemLp A₂ ∞ μ₀ := memLp_top_of_bound hA₂.aestronglyMeasurable C₂ (.of_forall hC₂)
  have hsplit : ∀ᵐ s ∂μ₀, AL s = (hm₁.toLp A₁ s).withLpProdMap 2 (hm₂.toLp A₂ s) := by
    filter_upwards [hAL, hm₁.coeFn_toLp, hm₂.coeFn_toLp] with s h h₁ h₂
    rw [h, h₁, h₂]
  -- The finite-dimensional block is Fredholm, and every large shift of it is invertible.
  have hι₁ : IsCompactOperator (1 : E →L[ℝ] E) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).2 inferInstance
  have hSymm₁ (s : ℝ) (x y : E) :
      ⟪A₁ s x, (1 : E →L[ℝ] E) y⟫_ℝ = ⟪(1 : E →L[ℝ] E) x, A₁ s y⟫_ℝ := by
    simpa using hsym₁ s x y
  have hF₁ : (familyDomainTrajectoryOperator (p := 2) (1 : E →L[ℝ] E) (hm₁.toLp A₁)).IsFredholm :=
    isFredholm_familyDomainTrajectoryOperator hι₁
      (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hbot₁
        (.of_forall fun s ↦ hSymm₁ s x y)) hB₁bot
      (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto htop₁
        (.of_forall fun s ↦ hSymm₁ s x y)) hB₁top hm₁.coeFn_toLp hbot₁ htop₁
      fun _ ↦ ⟨C₁ + ‖B₁top‖, .of_forall fun s _ x ↦ ((A₁ s - B₁top).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add_left (hC₁ s) _))
          (norm_nonneg x))⟩
  have h₀₁ (t : ℝ) : ∃ c₀ : ℝ, (c₀ • (1 : E →L[ℝ] E) - A₁ t).IsInvertible := by
    refine ⟨‖A₁ t‖ + 1, ContinuousLinearMap.isInvertible_iff_isUnit.2 ?_⟩
    have hnot : ‖A₁ t‖ + 1 ∉ spectrum ℝ (A₁ t) := fun hmem ↦ by
      have := spectrum.norm_le_norm_of_mem hmem
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at this
      linarith
    rwa [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one] at hnot
  -- The invertible block is Fredholm and contributes neither index nor spectral flow.
  have hF₂ := isFredholm_familyDomainTrajectoryOperator hι
    (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto hbot₂
      (.of_forall fun s ↦ hSymm₂ s x y)) hB₂bot
    (fun x y ↦ ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto htop₂
      (.of_forall fun s ↦ hSymm₂ s x y)) hB₂top hm₂.coeFn_toLp hbot₂ htop₂ hc
  have hind₂ := index_familyDomainTrajectoryOperator_eq_zero_of_forall_isInvertible hι hA₂ hSymm₂
    hInv₂ hB₂bot hB₂top hm₂.coeFn_toLp hbot₂ htop₂ hc
  filter_upwards [eventually_index_familyDomainTrajectoryOperator_one_eq_domainSpectralFlow hA₁
      hsym₁ hB₁bot hB₁top hbot₁ htop₁ (hm₁.toLp A₁) hm₁.coeFn_toLp,
    (eventually_le_atBot 0).prod_mk (eventually_ge_atTop 0)] with ⟨a, b⟩ h₁ ⟨ha, hb⟩
  have hab : a ≤ b := ha.trans hb
  rw [index_familyDomainTrajectoryOperator_withLpProdMap 1 ι hsplit hF₁ hF₂, hind₂, add_zero, h₁,
    domainSpectralFlow_withLpProdMap hab hι₁ hι hA₁.continuousOn hA₂.continuousOn
      (fun t _ ↦ hSymm₁ t) (fun t _ ↦ hSymm₂ t) (fun t _ ↦ h₀₁ t)
      (fun t _ ↦ ⟨0, by simpa [ContinuousLinearMap.isInvertible_neg_iff] using hInv₂ t⟩),
    domainSpectralFlow_eq_zero_of_forall_isInvertible hι hab hA₂.continuousOn (fun t _ ↦ hSymm₂ t)
      fun t _ ↦ hInv₂ t, add_zero]

end Block

end TauCeti.WeakDerivStep
