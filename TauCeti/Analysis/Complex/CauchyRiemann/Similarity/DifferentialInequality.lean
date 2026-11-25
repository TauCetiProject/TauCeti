/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The similarity principle for a weak Cauchy–Riemann inequality with an `Lᵖ` bound

Let `E` be a finite-dimensional complex inner product space, `Ω ⊆ ℂ` open and `p > 2`. Let
`ξ : ℂ → E` be continuous on `Ω` with weak conjugate Wirtinger derivative `G = bar∂ξ` on `Ω`
satisfying the differential inequality

`‖bar∂ξ‖ ≤ g ‖ξ‖` almost everywhere on `Ω`,

for a function `g` which is only locally `Lᵖ`. Then `ξ` solves `∂ₛξ + i ∂ₜξ + C ξ = 0` with the
rank-one coefficient `C = -2 (bar∂ξ) ξ* / ‖ξ‖²` (`TauCeti.rankOneDivNormSq`), and `‖C‖ ≤ 2 g`, so
`C` is locally `Lᵖ` and the similarity principle for `Lᵖ` coefficients
(`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn`) applies: near every point `ξ = Φ σ`
with `Φ` continuous and invertible and `σ` holomorphic
(`TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn_of_norm_le`). The zeros of `ξ` then
behave as those of a holomorphic map: unique continuation, isolated zeros and positive orders.

This is the form in which the similarity principle applies to the kernel of a real Cauchy–Riemann
operator whose zeroth-order term is only `Lᵖ`: in a holomorphic chart and a complex frame of a line
bundle the operator reads `bar∂ + Z` with `Z ∈ Lᵖ_loc`, and a kernel element `f` satisfies
`‖bar∂ f‖ = ‖Z f‖ ≤ ‖Z‖ ‖f‖`. For a scalar `f : ℂ → ℂ` the factor `Φ` is multiplication by a
complex number (`TauCeti.exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le`), so
the zeros of `f` have positive local indices. This extends the classical statements
`TauCeti.exists_similarity_of_norm_le` and
`TauCeti.exists_eventually_eq_mul_of_norm_conjWirtingerDeriv_le`, for `C¹` maps and locally bounded
`g`, to weak solutions and `Lᵖ` bounds.

## Main results

* `TauCeti.exists_similarity_of_hasWeakConjWirtingerDerivOn_of_norm_le`: the local factorization.
* `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_norm_le_of_eqOn_zero` and
  `TauCeti.eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_norm_le_of_forall_isBigO`: unique
  continuation.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn_of_norm_le`:
  isolated zeros.
* `TauCeti.exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivOn_of_norm_le`: positive orders.
* `TauCeti.exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le`: the scalar
  factorization `f = v σ` with `v` continuous and nonzero.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Carleman similarity principle) and the proof of Theorem C.1.10.
-/

public section

open Asymptotics Complex Filter Function MeasureTheory Metric Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {Ω : Opens ℂ} {p : ℝ≥0∞} {ξ G : ℂ → E} {g : ℂ → ℝ}

omit [FiniteDimensional ℂ E] in
/-- The rank-one coefficient `C = -2 G ξ* / ‖ξ‖²` turns the inequality `‖G‖ ≤ g ‖ξ‖` for the weak
derivative `G = bar∂ξ` into the equation `bar∂ξ = ½ (-C ξ)`, with `C` locally `Lᵖ` along with
`g`. -/
private theorem exists_coeff_of_norm_le (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) :
    ∃ C : ℂ → E →L[ℝ] E, MemLpLoc p Ω C ∧
      HasWeakConjWirtingerDerivOn volume Ω ξ (fun z ↦ (2 : ℂ)⁻¹ • -C z (ξ z)) := by
  set C : ℂ → E →L[ℝ] E :=
    fun z ↦ ((-2 : ℂ) • rankOneDivNormSq ℂ (G z) (ξ z)).restrictScalars ℝ with hC_def
  have hCm : AEStronglyMeasurable C (volume.restrict Ω) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℂ).continuous.comp_aestronglyMeasurable
      (by
        simpa only [Pi.smul_def] using
          (hG.locallyIntegrableOn_deriv.aestronglyMeasurable.rankOneDivNormSq (𝕜 := ℂ)
            (hξ.aestronglyMeasurable Ω.isOpen.measurableSet)).const_smul (-2 : ℂ))
  refine ⟨C, (hg.const_smul 2).of_le hCm ?_, hG.congr_ae_deriv ?_⟩
  · -- `‖C z‖ = 2 ‖G z‖ / ‖ξ z‖ ≤ 2 |g z|`
    filter_upwards [hle] with z hz
    simp only [hC_def, ContinuousLinearMap.norm_restrictScalars, norm_smul, norm_rankOneDivNormSq,
      norm_neg, Complex.norm_two, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_two]
    gcongr
    exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _)
      (hz.trans (by gcongr; exact le_abs_self _))
  · -- `½ (-C ξ) = G`, also where `ξ = 0`, since there `G = 0`
    filter_upwards [hle] with z hz
    by_cases h0 : ξ z = 0
    · rw [h0, norm_zero, mul_zero, norm_le_zero_iff] at hz
      simp [hz, h0]
    · simp [hC_def, rankOneDivNormSq_apply_self _ h0, smul_smul]

/-- **The similarity principle for a weak differential inequality.** Let `ξ` be continuous on an
open set `Ω ⊆ ℂ`, with values in a finite-dimensional complex inner product space, and have a weak
conjugate Wirtinger derivative `G = bar∂ξ` on `Ω` with `‖G‖ ≤ g ‖ξ‖` almost everywhere on `Ω`,
for a function `g` locally `Lᵖ` on `Ω` with `p > 2`. Then every point `z₀ ∈ Ω` is the centre of a
disc in `Ω` on which `ξ = Φ σ`, with `Φ` a continuous family of invertible complex-linear maps and
`σ` holomorphic. -/
theorem exists_similarity_of_hasWeakConjWirtingerDerivOn_of_norm_le (hp : 2 < p)
    (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω) (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r, 0 < r ∧ ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → E →L[ℂ] E) (σ : ℂ → E),
      ContinuousOn Φ (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧ EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r) := by
  obtain ⟨C, hC, heq⟩ := exists_coeff_of_norm_le hg hξ hG hle
  exact exists_similarity_of_hasWeakConjWirtingerDerivOn hp hC hξ heq hz₀

/-- Under a weak differential inequality `‖bar∂ξ‖ ≤ g ‖ξ‖` with `g ∈ Lᵖ_loc`, `p > 2`, a continuous
map has a similarity factorization at every point of `Ω`. -/
theorem hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn_of_norm_le (hp : 2 < p)
    (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω) (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    HasSimilarityFactorizationAt ξ z₀ := by
  obtain ⟨C, hC, heq⟩ := exists_coeff_of_norm_le hg hξ hG hle
  exact hasSimilarityFactorizationAt_of_hasWeakConjWirtingerDerivOn hp hC hξ heq hz₀

/-- **Unique continuation under a weak differential inequality.** On a connected open set `Ω`, a
continuous map with `‖bar∂ξ‖ ≤ g ‖ξ‖` almost everywhere, `g ∈ Lᵖ_loc`, `p > 2`, that vanishes on
a nonempty open subset of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_norm_le_of_eqOn_zero (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) {U : Set ℂ} (hU : IsOpen U)
    (hUne : U.Nonempty) (hUΩ : U ⊆ Ω) (h₀ : EqOn ξ 0 U) : EqOn ξ 0 Ω := by
  obtain ⟨C, hC, heq⟩ := exists_coeff_of_norm_le hg hξ hG hle
  exact eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_eqOn_zero hp hΩc hC hξ heq hU hUne hUΩ h₀

/-- **Unique continuation from a zero of infinite order under a weak differential inequality.**
On a connected open set `Ω`, a continuous map with `‖bar∂ξ‖ ≤ g ‖ξ‖` almost everywhere,
`g ∈ Lᵖ_loc`, `p > 2`, that vanishes to infinite order at one point of `Ω` vanishes on `Ω`. -/
theorem eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_norm_le_of_forall_isBigO (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (h₀ : ∀ n : ℕ, ξ =O[𝓝 z₀] fun z ↦ (z - z₀) ^ n) : EqOn ξ 0 Ω := by
  obtain ⟨C, hC, heq⟩ := exists_coeff_of_norm_le hg hξ hG hle
  exact eqOn_zero_of_hasWeakConjWirtingerDerivOn_of_forall_isBigO hp hΩc hC hξ heq hz₀ h₀

/-- **Isolated zeros under a weak differential inequality.** On a connected open set `Ω`, the
zeros of a continuous map with `‖bar∂ξ‖ ≤ g ‖ξ‖` almost everywhere, `g ∈ Lᵖ_loc`, `p > 2`, which is
not identically zero on `Ω`, form a discrete subset of `Ω`. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn_of_norm_le (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) (hne : ∃ z ∈ Ω, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin (Ω : Set ℂ) := by
  obtain ⟨C, hC, heq⟩ := exists_coeff_of_norm_le hg hξ hG hle
  exact setOf_ne_zero_mem_codiscreteWithin_of_hasWeakConjWirtingerDerivOn hp hΩc hC hξ heq hne

/-- **Positive orders of zeros under a weak differential inequality.** On a connected open set
`Ω`, let `ξ` be continuous with `‖bar∂ξ‖ ≤ g ‖ξ‖` almost everywhere, `g ∈ Lᵖ_loc`, `p > 2`, and
not identically zero. At a zero `z₀ ∈ Ω`, every similarity factorization `ξ = Φ σ` has `σ` of the
same finite positive analytic order `m`, and `‖ξ z‖` is comparable to `‖z - z₀‖ ^ m` near
`z₀`. -/
theorem exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivOn_of_norm_le (hp : 2 < p)
    (hΩc : IsPreconnected (Ω : Set ℂ)) (hg : MemLpLoc p Ω g) (hξ : ContinuousOn ξ Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω ξ G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖ξ z‖) (hne : ∃ z ∈ Ω, ξ z ≠ 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) (hξ₀ : ξ z₀ = 0) :
    ∃ m : ℕ, 0 < m ∧ (ξ =Θ[𝓝 z₀] fun z ↦ (z - z₀) ^ m) ∧
      ∀ (Φ : ℂ → E →L[ℝ] E) (σ : ℂ → E), ContinuousAt Φ z₀ → IsUnit (Φ z₀) →
        AnalyticAt ℂ σ z₀ → (∀ᶠ z in 𝓝 z₀, ξ z = Φ z (σ z)) → analyticOrderAt σ z₀ = m := by
  obtain ⟨C, hC, heq⟩ := exists_coeff_of_norm_le hg hξ hG hle
  exact exists_analyticOrderAt_eq_of_hasWeakConjWirtingerDerivOn hp hΩc hC hξ heq hne hz₀ hξ₀

/-- **Scalar similarity factorization under a weak differential inequality.** A function
`f : ℂ → ℂ`, continuous on an open set `Ω`, with weak conjugate Wirtinger derivative `G` on `Ω`
satisfying `‖G‖ ≤ g ‖f‖` almost everywhere for some `g ∈ Lᵖ_loc`, `p > 2`, is near every point
`z₀ ∈ Ω` the product `v * σ` of a function `v` continuous and nonzero at `z₀` and a function `σ`
analytic at `z₀`. The factor `v` is a complex number, so the zeros of `f` count positively, as
those of `σ` do. -/
theorem exists_eventually_eq_mul_of_hasWeakConjWirtingerDerivOn_of_norm_le (hp : 2 < p)
    {f G : ℂ → ℂ} (hg : MemLpLoc p Ω g) (hf : ContinuousOn f Ω)
    (hG : HasWeakConjWirtingerDerivOn volume Ω f G)
    (hle : ∀ᵐ z ∂volume.restrict Ω, ‖G z‖ ≤ g z * ‖f z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ v σ : ℂ → ℂ, ContinuousAt v z₀ ∧ v z₀ ≠ 0 ∧ AnalyticAt ℂ σ z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = v z * σ z := by
  obtain ⟨r, hr, -, Φ, σ, hΦ, hΦu, hσ, hfσ⟩ :=
    exists_similarity_of_hasWeakConjWirtingerDerivOn_of_norm_le hp hg hf hG hle hz₀
  have hball : ball z₀ r ∈ 𝓝 z₀ := ball_mem_nhds z₀ hr
  exact exists_eventually_eq_mul_of_eventually_eq_clm_apply (hΦ.continuousAt hball)
    (hΦu z₀ (mem_ball_self hr)) (hσ.analyticAt hball) (eventually_of_mem hball hfσ)

end TauCeti
