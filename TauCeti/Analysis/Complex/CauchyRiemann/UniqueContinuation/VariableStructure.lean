/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak
import TauCeti.Geometry.Symplectic.Complex.Module.Conjugacy

/-!
# Unique continuation for linear Cauchy–Riemann equations with a variable complex structure

Let `V` be a finite-dimensional real normed space, `Ω ⊆ ℂ` open, `J : ℂ → V →L[ℝ] V` a `C¹`
field of complex structures on `V`, `J(z)² = -1`, and `ξ : ℂ → V` a map of class `C¹` on `Ω`
solving the linear Cauchy–Riemann equation

`∂ₛξ + J(z) ∂ₜξ + C(z) ξ = 0`

on `Ω`, in the coordinate `z = s + i t`, for a measurable, locally bounded (for instance
continuous) field `C` of real-linear endomorphisms. This is the shape of the linearized operator
of a pseudoholomorphic curve or of a Floer solution, with `J` the almost complex structure along
the map and `C` collecting the zeroth-order terms. This file proves that such solutions have the
zero structure of holomorphic maps:

* a solution vanishing to infinite order at one point of a connected open `Ω` vanishes on `Ω`
  (`TauCeti.eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure`);
* so does a solution vanishing on a nonempty open subset of `Ω`
  (`TauCeti.eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure`);
* otherwise its zeros are isolated
  (`TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure`), and each of
  them has a finite positive order
  (`TauCeti.exists_isTheta_pow_of_contDiffOn_of_complexStructure`).

For a constant structure `J = i` on a complex space these are the classical statements of
`TauCeti.Analysis.Complex.CauchyRiemann.Similarity`. The variable structure is handled in two
steps.

* **The weak similarity principle.** When `V` is a complex space, a `C¹` solution is a weak
  solution in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`, the `C¹` field `J` is
  continuous and of class `W^{1,p}_loc`, and the locally bounded `C` is locally `Lᵖ` for every
  `p` (`TauCeti.memLpLoc_of_forall_eventually_norm_le`), say `p = 3`. The similarity principle for
  weak solutions with a variable structure
  (`TauCeti.hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn`)
  then gives `ξ` a similarity factorization at every point of `Ω`
  (`TauCeti.hasSimilarityFactorizationAt_of_contDiffOn_of_complexStructure`).
* **A complex model of `V`.** A real space carrying one complex structure `J(z₁)` has even
  dimension, so it is real-linearly isomorphic to `ℂⁿ`
  (`ContinuousLinearMap.exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul`).
  Conjugating `J` and `C` by such an isomorphism `T` gives the same kind of equation for
  `T⁻¹ ξ` on `ℂⁿ`, and `T⁻¹ ξ` vanishes exactly where `ξ` does.

The zero structure then follows from the factorizations by
`TauCeti.Analysis.Complex.CauchyRiemann.UniqueContinuation`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (Theorem 2.3.5, the Carleman similarity principle, and its consequences for
  unique continuation).
* T. Carleman, *Sur les systèmes linéaires aux dérivées partielles du premier ordre à deux
  variables*, C. R. Acad. Sci. Paris **197** (1933), 471–474.
-/

public noncomputable section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-! ### The local factorization on a complex space -/

section Complex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- **The similarity principle for a variable complex structure.** Let `ξ` be of class `C¹` on an
open set `Ω ⊆ ℂ` and solve `∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω`, for a `C¹` field `J` of real-linear
complex structures, `J(z)² = -1`, on a finite-dimensional complex normed space `V` and a
measurable, locally bounded field `C` of real-linear endomorphisms. Then `ξ` has a similarity
factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_contDiffOn_of_complexStructure (hΩ : IsOpen Ω)
    (hJ : ContDiffOn ℝ 1 J Ω) (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) : HasSimilarityFactorizationAt ξ z₀ := by
  have := FiniteDimensional.completeSpace ℂ V
  -- `ξ` is a weak solution on `Ω`, `J` is `W^{1,3}_loc` and the locally bounded `C` is `L³_loc`
  let B : Opens ℂ := ⟨Ω, hΩ⟩
  have h : IsWeakLinearCauchyRiemannOn ((3 : ℝ≥0) : ℝ≥0∞) B J C ξ :=
    isWeakCauchyRiemannOn_of_contDiffOn hξ fun z hz ↦ eq_neg_of_add_eq_zero_left (heq z hz)
  exact hasSimilarityFactorizationAt_of_isWeakLinearCauchyRiemannOn (Ω := B) (by norm_num)
    (hJ.memWkpLoc subset_rfl) hJ.continuousOn hJJ (memLpLoc_of_forall_eventually_norm_le hCm hCb)
    h hz₀

end Complex

/-! ### The zero structure on a real space -/

section Real

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Set ℂ} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- Under the hypotheses of the unique continuation theorems, `ξ` read in a complex model
`T : ℂⁿ ≃ V` of `V` has a similarity factorization at every point of `Ω`. -/
private theorem exists_hasSimilarityFactorizationAt_symm_comp (hΩ : IsOpen Ω)
    (hJ : ContDiffOn ℝ 1 J Ω) (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hξ : ContDiffOn ℝ 1 ξ Ω) (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) {z₁ : ℂ}
    (hz₁ : z₁ ∈ Ω) : ∃ (n : ℕ) (T : EuclideanSpace ℂ (Fin n) ≃L[ℝ] V),
      ∀ z ∈ Ω, HasSimilarityFactorizationAt (T.symm ∘ ξ) z := by
  obtain ⟨n, T, -⟩ :=
    (J z₁).exists_continuousLinearEquiv_euclideanSpace_comp_eq_comp_I_smul (hJJ z₁ hz₁)
  -- Conjugation by `T` carries the equation on `V` to the same kind of equation on `ℂⁿ`.
  let c : (V →L[ℝ] V) →L[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) :=
    (T.symm.arrowCongr T.symm : _)
  have hc (A : V →L[ℝ] V) (v : V) : c A (T.symm v) = T.symm (A v) := by simp [c]
  refine ⟨n, T, fun z hz ↦ hasSimilarityFactorizationAt_of_contDiffOn_of_complexStructure
    (J := fun z ↦ c (J z)) (C := fun z ↦ c (C z)) hΩ (c.contDiff.comp_contDiffOn hJ)
    (fun z hz ↦ ?_) (T.symm.contDiff.comp_contDiffOn hξ)
    (c.continuous.comp_aestronglyMeasurable hCm) (fun z hz ↦ ?_) (fun z hz ↦ ?_) hz⟩
  · have hJJ' (v : V) : J z (J z v) = -v := congr($(hJJ z hz) v)
    ext w
    simp [c, hJJ']
  · obtain ⟨M, hM⟩ := hCb z hz
    exact ⟨‖c‖ * M, hM.mono fun w hw ↦ (c.le_opNorm _).trans (by gcongr)⟩
  · rw [T.symm.comp_fderiv]
    simpa [hc] using congr(T.symm $(heq z hz))

/-- **Unique continuation from a zero of infinite order** for a variable complex structure. On a
connected open set `Ω`, a `C¹` solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`, for a `C¹` field `J` of
complex structures, `J(z)² = -1`, on a finite-dimensional real normed space and a measurable,
locally bounded real-linear coefficient `C`, that vanishes to infinite order at one point of `Ω`
vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_forall_isBigO_of_complexStructure (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  obtain ⟨n, T, hfac⟩ :=
    exists_hasSimilarityFactorizationAt_symm_comp hΩ hJ hJJ hξ hCm hCb heq hz₀
  have h := eqOn_zero_of_hasSimilarityFactorizationAt_of_forall_isBigO hΩ hΩc
    (T.symm.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz) hz₀
    fun k ↦ (T.symm.isBigO_comp ξ _).trans (h₀ k)
  exact fun z hz ↦ by simpa using congr(T $(h hz))

/-- **Unique continuation** for a variable complex structure. On a connected open set `Ω`, a `C¹`
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`, for a `C¹` field `J` of complex structures,
`J(z)² = -1`, on a finite-dimensional real normed space and a measurable, locally bounded
real-linear coefficient `C`, that vanishes on a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_contDiffOn_of_eqOn_zero_of_complexStructure (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0) {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨z₁, hz₁⟩ := hUne
  obtain ⟨n, T, hfac⟩ :=
    exists_hasSimilarityFactorizationAt_symm_comp hΩ hJ hJJ hξ hCm hCb heq (hUΩ hz₁)
  have h := eqOn_zero_of_hasSimilarityFactorizationAt_of_eqOn_zero hΩ hΩc
    (T.symm.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz) hU
    ⟨z₁, hz₁⟩ hUΩ fun z hz ↦ by simp [h₀ hz]
  exact fun z hz ↦ by simpa using congr(T $(h hz))

/-- **Isolated zeros** for a variable complex structure. On a connected open set `Ω`, the zeros of
a `C¹` solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`, for a `C¹` field `J` of complex structures,
`J(z)² = -1`, on a finite-dimensional real normed space and a measurable, locally bounded
real-linear coefficient `C`, that is not identically zero on `Ω` form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_contDiffOn_of_complexStructure (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) : {z | ξ z ≠ 0} ∈ codiscreteWithin Ω := by
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  obtain ⟨n, T, hfac⟩ :=
    exists_hasSimilarityFactorizationAt_symm_comp hΩ hJ hJJ hξ hCm hCb heq hz₁
  simpa using setOf_ne_zero_mem_codiscreteWithin_of_hasSimilarityFactorizationAt hΩ hΩc
    (T.symm.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz)
    ⟨z₁, hz₁, by simpa using hξz₁⟩

/-- **Positive orders** for a variable complex structure. On a connected open set `Ω`, let `ξ` be
a `C¹` solution of `∂ₛξ + J ∂ₜξ + C ξ = 0`, for a `C¹` field `J` of complex structures,
`J(z)² = -1`, on a finite-dimensional real normed space and a measurable, locally bounded
real-linear coefficient `C`, that is not identically zero on `Ω`. Then each zero `z₀ ∈ Ω` of `ξ`
has a finite positive order `m`: `‖ξ z‖` is comparable to `‖z - z₀‖ ^ m` near `z₀`. -/
theorem exists_isTheta_pow_of_contDiffOn_of_complexStructure (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (hJ : ContDiffOn ℝ 1 J Ω)
    (hJJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hCm : AEStronglyMeasurable C (volume.restrict Ω))
    (hCb : ∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M)
    (heq : ∀ z ∈ Ω, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + C z (ξ z) = 0)
    (hne : ∃ z ∈ Ω, ξ z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m := by
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  obtain ⟨n, T, hfac⟩ :=
    exists_hasSimilarityFactorizationAt_symm_comp hΩ hJ hJJ hξ hCm hCb heq hz₁
  obtain ⟨m, hm, hθ, -⟩ := exists_analyticOrderAt_eq_of_hasSimilarityFactorizationAt hΩ hΩc
    (T.symm.continuous.comp_continuousOn hξ.continuousOn) (fun z hz _ ↦ hfac z hz)
    ⟨z₁, hz₁, by simpa using hξz₁⟩ hz₀ (by simp [hξ₀])
  exact ⟨m, hm, IsTheta.trans ⟨T.symm.isBigO_comp_rev _ _, T.symm.isBigO_comp _ _⟩ hθ⟩

end Real

end TauCeti
