/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.BrownianMotion.Integral.Square
public import TauCeti.Probability.Martingale.QuadraticVariation.Covariation
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Quadratic variation and covariation of filtered Brownian motion

This file connects `TauCeti.Probability.IsFilteredPreBrownianReal` and elementary Brownian integrals
(`TauCeti.Finance.simpleGains`) to the continuous bracket predicates
`TauCeti.Probability.IsQuadraticVariation` and `TauCeti.Probability.IsCovariation`:

* **Single Brownian motion**: `IsFilteredPreBrownianReal.isQuadraticVariation` shows `[B]_t = t`
  without path-continuity or usual-conditions hypotheses, and
  `IsFilteredPreBrownianReal.indist_of_isQuadraticVariation` records uniqueness up to
  indistinguishability when `B` has almost-surely continuous paths.
* **Elementary Brownian integrals**: `IsFilteredPreBrownianReal.martingale_mul_simpleGains_sub`,
  `IsFilteredPreBrownianReal.isQuadraticVariation_simpleGains`, and
  `IsFilteredPreBrownianReal.isCovariation_simpleGains` prove the mutual martingale decomposition
  and identify the pathwise energy and mutual energy brackets of `Finance.simpleGains` for
  square-integrable left-endpoint heights.
* **Independent Brownian motions and linear combinations**:
  `IsFilteredPreBrownianReal.martingale_mul_of_indep_sub` and
  `IsFilteredPreBrownianReal.isCovariation_zero_of_indep_sub` show that two filtered pre-Brownian
  motions whose pair increments are independent of the past and mutually independent have product
  martingale `B₁ * B₂` and zero covariation. From pairwise product martingales,
  `isCovariation_sum_mul_of_martingale_mul`, `isQuadraticVariation_sum_mul_of_martingale_mul`,
  `OrthonormalBasis.isCovariation_inner_of_martingale_mul`, and
  `OrthonormalBasis.isQuadraticVariation_inner_of_martingale_mul` compute the mutual and quadratic
  brackets `[⟨u, W⟩, ⟨v, W⟩]_t = ⟨u, v⟩ t` and `[⟨u, W⟩]_t = ‖u‖² t` for arbitrary vectors `u, v`.

## References

* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.5 and §3.2.
* Daniel Revuz and Marc Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal Topology

namespace TauCeti.Probability

private theorem isStronglyProgressive_deterministic {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    IsStronglyProgressive ℱ (fun t _ ↦ f t) :=
  StronglyAdapted.isStronglyProgressive_of_continuous
    (fun _ ↦ stronglyMeasurable_const) fun _ ↦ hf

private theorem monotone_min_sub_min {a b : ℝ≥0} (hab : a ≤ b) :
    Monotone (fun t : ℝ≥0 ↦ ↑(min b t) - (↑(min a t) : ℝ)) := by
  intro s t hst
  dsimp only
  rcases le_total t a with hta | hat
  · have hsa : s ≤ a := hst.trans hta
    rw [min_eq_right hsa, min_eq_right (hsa.trans hab),
      min_eq_right hta, min_eq_right (hta.trans hab), sub_self, sub_self]
  · rcases le_total s a with hsa | has
    · rw [min_eq_right hsa, min_eq_right (hsa.trans hab), sub_self, min_eq_left hat]
      exact sub_nonneg.2 (NNReal.coe_le_coe.2 (le_min hab hat))
    · rw [min_eq_left has, min_eq_left hat]
      exact sub_le_sub_right (NNReal.coe_le_coe.2 (min_le_min_left b hst)) _

private theorem continuous_simpleGains_time {Ω : Type*} (τ : ℕ → ℝ≥0) (n : ℕ)
    (c : ℕ → Ω → ℝ) (ω : Ω) :
    Continuous (Finance.simpleGains τ n c (fun t _ ↦ (t : ℝ)) · ω) := by
  have heq : (Finance.simpleGains τ n c (fun t _ ↦ (t : ℝ)) · ω) =
      fun t ↦ ∑ i ∈ Finset.range n, c i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t)) :=
    funext fun t ↦ Finance.simpleGains_def τ n c (fun u _ ↦ (u : ℝ)) t ω
  rw [heq]
  fun_prop

private theorem isStronglyProgressive_simpleGains_time {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {τ : ℕ → ℝ≥0} {n : ℕ} {c : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hc : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (c i)) :
    IsStronglyProgressive ℱ (Finance.simpleGains τ n c (fun t _ ↦ (t : ℝ))) :=
  (Finance.stronglyAdapted_simpleGains hτ hc
    fun _ ↦ stronglyMeasurable_const).isStronglyProgressive_of_continuous
      (continuous_simpleGains_time τ n c)

private theorem monotone_simpleGains_sq_time {Ω : Type*} {τ : ℕ → ℝ≥0} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (d : ℕ → Ω → ℝ) (ω : Ω) :
    Monotone (Finance.simpleGains τ n (fun i ω ↦ d i ω ^ 2) (fun t _ ↦ (t : ℝ)) · ω) := by
  intro s t hst
  dsimp only
  rw [Finance.simpleGains_def, Finance.simpleGains_def]
  exact Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
    (monotone_min_sub_min
      (hτ (Finset.mem_range.1 hi).le (Finset.mem_range.1 hi) i.le_succ) hst)
    (sq_nonneg _)

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B B₁ B₂ W : ℝ≥0 → Ω → ℝ}

/-- The centered compensated square `B_t² - B_0² - t` of a filtered pre-Brownian motion is a true
martingale. -/
theorem martingale_sq_sub_sq_zero_sub (hB : IsFilteredPreBrownianReal ℱ B P) :
    Martingale (fun t ω ↦ (B t ω) ^ 2 - (B 0 ω) ^ 2 - (t : ℝ)) ℱ P := by
  refine hB.martingale_sq_sub.congr (fun t ↦ ?_) fun t ↦ ?_
  · exact ((((hB.adapted t).stronglyMeasurable.pow 2).sub
      (((hB.adapted 0).stronglyMeasurable.pow 2).mono (ℱ.mono bot_le))).sub
      stronglyMeasurable_const)
  · filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
    simp [h0]

/-- A real pre-Brownian motion relative to `ℱ` has quadratic variation `t ↦ t`. Neither path
continuity nor usual conditions on `ℱ` are required. -/
theorem isQuadraticVariation (hB : IsFilteredPreBrownianReal ℱ B P) :
    IsQuadraticVariation ℱ P B (fun t _ ↦ (t : ℝ)) :=
  IsQuadraticVariation.mk
    (isStronglyProgressive_deterministic ℱ NNReal.continuous_coe)
    (ae_of_all P fun _ ↦ NNReal.continuous_coe)
    (ae_of_all P fun _ ↦ NNReal.coe_mono)
    (ae_of_all P fun _ ↦ NNReal.coe_zero)
    (Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) hB.martingale_sq_sub_sq_zero_sub)

/-- Any quadratic variation of an almost-surely continuous filtered Brownian motion is
indistinguishable from `t ↦ t`. -/
theorem indist_of_isQuadraticVariation (hB : IsFilteredPreBrownianReal ℱ B P)
    (hcB : ∀ᵐ ω ∂P, Continuous (B · ω)) {A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticVariation ℱ P B A) :
    A ≡ᵐ[P] fun t _ ↦ (t : ℝ) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact hA.indist hB.isQuadraticVariation hcB

/-- **Quadratic variation of an elementary Brownian integral.** For square-integrable heights known
at the left endpoints of a monotone grid, `Finance.simpleGains τ n a W` has quadratic variation
equal to its elapsed pathwise square energy. -/
theorem isQuadraticVariation_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    IsQuadraticVariation ℱ P (Finance.simpleGains τ n a W)
      (fun t ω ↦ ∑ i ∈ Finset.range n,
        a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) := by
  let A := Finance.simpleGains τ n (fun i ω ↦ a i ω ^ 2) (fun t _ ↦ (t : ℝ))
  have hAeq : (fun t ω ↦ ∑ i ∈ Finset.range n,
      a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) = A :=
    funext₂ fun t ω ↦ (Finance.simpleGains_def τ n (fun i ω ↦ a i ω ^ 2)
      (fun u _ ↦ (u : ℝ)) t ω).symm
  rw [hAeq]
  refine IsQuadraticVariation.mk
    (isStronglyProgressive_simpleGains_time hτ fun i hi ↦ (ha i hi).pow 2)
    (ae_of_all P (continuous_simpleGains_time τ n _))
    (ae_of_all P (monotone_simpleGains_sq_time hτ a))
    (ae_of_all P fun _ ↦ by simp [A, Finance.simpleGains_def]) ?_
  have heq : (fun t ω ↦ (Finance.simpleGains τ n a W t ω) ^ 2 -
      (Finance.simpleGains τ n a W 0 ω) ^ 2 - A t ω) =
      fun t ω ↦ Finance.simpleGains τ n a W t ω ^ 2 -
        ∑ i ∈ Finset.range n, a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t)) := by
    ext t ω
    simp [A, Finance.simpleGains_def]
  rw [heq]
  exact Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P)
    (hW.martingale_sq_simpleGains_sub hτ ha ha₂)

/-- **Elementary Brownian product decomposition.** The product of two elementary Brownian integrals
on a common monotone grid with square-integrable left-endpoint heights, minus their elapsed mutual
energy, is a true martingale. -/
theorem martingale_mul_simpleGains_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a b : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (b i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P)
    (hb₂ : ∀ i < n, MemLp (b i) 2 P) :
    Martingale (fun t ω ↦ Finance.simpleGains τ n a W t ω * Finance.simpleGains τ n b W t ω -
      ∑ i ∈ Finset.range n, a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) ℱ P := by
  have hMpos := hW.martingale_sq_simpleGains_sub (a := a + b) hτ
    (fun i hi ↦ (ha i hi).add (hb i hi)) fun i hi ↦ (ha₂ i hi).add (hb₂ i hi)
  have hMneg := hW.martingale_sq_simpleGains_sub (a := a - b) hτ
    (fun i hi ↦ (ha i hi).sub (hb i hi)) fun i hi ↦ (ha₂ i hi).sub (hb₂ i hi)
  convert (hMpos.sub hMneg).smul (4⁻¹ : ℝ) using 1
  ext t ω
  have hsub_gains : Finance.simpleGains τ n (a - b) W t ω =
      Finance.simpleGains τ n a W t ω - Finance.simpleGains τ n b W t ω := by
    simp only [Finance.simpleGains_def, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finance.simpleGains_add, hsub_gains]
  simp only [Pi.add_apply]
  have hsum_id : ∑ i ∈ Finset.range n, a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t)) =
      4⁻¹ * (∑ i ∈ Finset.range n,
          (a i ω + b i ω) ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t)) -
        ∑ i ∈ Finset.range n,
          (a i ω - b i ω) ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hsum_id]
  ring

/-- **Covariation of two elementary Brownian integrals.** On a common monotone grid with
square-integrable left-endpoint heights, the covariation of `Finance.simpleGains τ n a W` and
`Finance.simpleGains τ n b W` is their elapsed mutual energy. -/
theorem isCovariation_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a b : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (b i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P)
    (hb₂ : ∀ i < n, MemLp (b i) 2 P) :
    IsCovariation ℱ P (Finance.simpleGains τ n a W) (Finance.simpleGains τ n b W)
      (fun t ω ↦ ∑ i ∈ Finset.range n,
        a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) := by
  let C := Finance.simpleGains τ n (fun i ω ↦ a i ω * b i ω) (fun t _ ↦ (t : ℝ))
  have hCeq : (fun t ω ↦ ∑ i ∈ Finset.range n,
      a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t))) = C :=
    funext₂ fun t ω ↦ (Finance.simpleGains_def τ n (fun i ω ↦ a i ω * b i ω)
      (fun u _ ↦ (u : ℝ)) t ω).symm
  rw [hCeq]
  have hbv (ω : Ω) : LocallyBoundedVariationOn (C · ω) Set.univ := by
    let Apos := Finance.simpleGains τ n (fun i ω ↦ (a + b) i ω ^ 2) (fun t _ ↦ (t : ℝ))
    let Aneg := Finance.simpleGains τ n (fun i ω ↦ (a - b) i ω ^ 2) (fun t _ ↦ (t : ℝ))
    have hCe : (C · ω) = (4⁻¹ : ℝ) • ((Apos · ω) - (Aneg · ω)) := by
      ext t
      simp only [C, Apos, Aneg, Finance.simpleGains_def, Pi.smul_apply, Pi.sub_apply,
        Pi.add_apply, smul_eq_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hCe]
    have hbv_pos : LocallyBoundedVariationOn (Apos · ω) Set.univ :=
      ((monotone_simpleGains_sq_time hτ (a + b) ω).monotoneOn Set.univ).locallyBoundedVariationOn
    have hbv_neg : LocallyBoundedVariationOn (Aneg · ω) Set.univ :=
      ((monotone_simpleGains_sq_time hτ (a - b) ω).monotoneOn Set.univ).locallyBoundedVariationOn
    exact (lipschitzWith_smul (4⁻¹ : ℝ)).comp_locallyBoundedVariationOn (hbv_pos.sub hbv_neg)
  refine IsCovariation.mk
    (isStronglyProgressive_simpleGains_time hτ fun i hi ↦ (ha i hi).mul (hb i hi))
    (ae_of_all P (continuous_simpleGains_time τ n _)) (ae_of_all P hbv)
    (ae_of_all P fun _ ↦ by simp [C, Finance.simpleGains_def]) ?_
  have heq : (fun t ω ↦ Finance.simpleGains τ n a W t ω * Finance.simpleGains τ n b W t ω -
      Finance.simpleGains τ n a W 0 ω * Finance.simpleGains τ n b W 0 ω - C t ω) =
      fun t ω ↦ Finance.simpleGains τ n a W t ω * Finance.simpleGains τ n b W t ω -
        ∑ i ∈ Finset.range n, a i ω * b i ω * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t)) := by
    ext t ω
    simp [C, Finance.simpleGains_def]
  rw [heq]
  exact Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P)
    (hW.martingale_mul_simpleGains_sub hτ ha hb ha₂ hb₂)

private theorem condExp_mul_sub_eq_zero (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P) {s t : ℝ≥0}
    (hindep_past : Indep (.comap (fun ω ↦ (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)) inferInstance)
      (ℱ s) P)
    (hindep_inc : IndepFun (B₁ t - B₁ s) (B₂ t - B₂ s) P) :
    P[fun ω ↦ (B₁ t ω - B₁ s ω) * (B₂ t ω - B₂ s ω) | ℱ s] =ᵐ[P] 0 := by
  have := hB₁.isGaussianProcess.isProbabilityMeasure
  let pair (ω : Ω) : ℝ × ℝ := (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)
  have hpair_meas : Measurable pair :=
    ((hB₁.adapted.measurable.sub hB₁.adapted.measurable).prodMk
      (hB₂.adapted.measurable.sub hB₂.adapted.measurable))
  have hcond : P[fun ω ↦ (B₁ t ω - B₁ s ω) * (B₂ t ω - B₂ s ω) | ℱ s] =ᵐ[P]
      fun _ ↦ ∫ ω, (B₁ t ω - B₁ s ω) * (B₂ t ω - B₂ s ω) ∂P :=
    condExp_indep_eq hpair_meas.comap_le (ℱ.le s)
      (((continuous_fst.mul continuous_snd).stronglyMeasurable).comp_measurable
        (comap_measurable pair)) hindep_past
  have hint_zero : ∫ ω, (B₁ t ω - B₁ s ω) * (B₂ t ω - B₂ s ω) ∂P = 0 := by
    have hprod := hindep_inc.integral_fun_mul_eq_mul_integral
      (hB₁.adapted.measurable.sub hB₁.adapted.measurable).aestronglyMeasurable
      (hB₂.adapted.measurable.sub hB₂.adapted.measurable).aestronglyMeasurable
    have hm₁ : ∫ ω, B₁ t ω - B₁ s ω ∂P = 0 := by
      rw [integral_sub (hB₁.integrable_eval t) (hB₁.integrable_eval s),
        hB₁.integral_eval, hB₁.integral_eval, sub_self]
    simpa only [Pi.sub_apply, hm₁, zero_mul] using hprod
  simpa only [hint_zero, Pi.zero_def] using hcond

/-- **Product martingale of independent filtered Brownian motions.** If two filtered pre-Brownian
motions have pair increments independent of `ℱ s` and mutually independent increments over every
`[s, t]`, then their pointwise product `B₁ * B₂` is a martingale on `ℱ`. -/
theorem martingale_mul_of_indep_sub (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P)
    (hindep_past : ∀ ⦃s t⦄, s ≤ t →
      Indep (.comap (fun ω ↦ (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)) inferInstance) (ℱ s) P)
    (hindep_inc : ∀ ⦃s t⦄, s ≤ t → IndepFun (B₁ t - B₁ s) (B₂ t - B₂ s) P) :
    Martingale (B₁ * B₂) ℱ P := by
  have := hB₁.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t ↦ ((hB₁.adapted t).mul (hB₂.adapted t)).stronglyMeasurable, fun s t hst ↦ ?_⟩
  let Δ₁ := B₁ t - B₁ s
  let Δ₂ := B₂ t - B₂ s
  have hL₁ (u : ℝ≥0) : MemLp (B₁ u) 2 P := hB₁.memLp_eval u (by simp)
  have hL₂ (u : ℝ≥0) : MemLp (B₂ u) 2 P := hB₂.memLp_eval u (by simp)
  have hi₀ : Integrable (B₁ s * B₂ s) P := (hL₁ s).integrable_mul (hL₂ s)
  have hi₁ : Integrable (Δ₁ * Δ₂) P := ((hL₁ t).sub (hL₁ s)).integrable_mul ((hL₂ t).sub (hL₂ s))
  have hi₂ : Integrable (B₁ s * Δ₂) P := (hL₁ s).integrable_mul ((hL₂ t).sub (hL₂ s))
  have hi₃ : Integrable (B₂ s * Δ₁) P := (hL₂ s).integrable_mul ((hL₁ t).sub (hL₁ s))
  have hc₁ : P[Δ₁ * Δ₂ | ℱ s] =ᵐ[P] 0 :=
    condExp_mul_sub_eq_zero hB₁ hB₂ (hindep_past hst) (hindep_inc hst)
  have hc₂ : P[B₁ s * Δ₂ | ℱ s] =ᵐ[P] 0 := by
    have hm := (hB₂.martingale_mul_sub_min hst (hB₁.adapted s).stronglyMeasurable
      (hB₁.integrable_eval s)).condExp_ae_eq hst
    simpa only [min_self, min_eq_left hst, min_eq_right hst, sub_self, mul_zero,
      Pi.mul_def, Pi.sub_def, Pi.zero_def, Δ₂] using hm
  have hc₃ : P[B₂ s * Δ₁ | ℱ s] =ᵐ[P] 0 := by
    have hm := (hB₁.martingale_mul_sub_min hst (hB₂.adapted s).stronglyMeasurable
      (hB₂.integrable_eval s)).condExp_ae_eq hst
    simpa only [min_self, min_eq_left hst, min_eq_right hst, sub_self, mul_zero,
      Pi.mul_def, Pi.sub_def, Pi.zero_def, Δ₁] using hm
  have hdecomp : (B₁ * B₂) t = B₁ s * B₂ s + (Δ₁ * Δ₂ + (B₁ s * Δ₂ + B₂ s * Δ₁)) := by
    ext ω
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Δ₁, Δ₂]
    ring
  rw [hdecomp]
  have hadd₁ := condExp_add hi₀ (hi₁.add (hi₂.add hi₃)) (ℱ s)
  have hadd₂ := condExp_add hi₁ (hi₂.add hi₃) (ℱ s)
  have hadd₃ := condExp_add hi₂ hi₃ (ℱ s)
  have hbase := condExp_of_stronglyMeasurable (ℱ.le s)
    ((hB₁.adapted s).mul (hB₂.adapted s)).stronglyMeasurable hi₀
  filter_upwards [hadd₁, hadd₂, hadd₃, hc₁, hc₂, hc₃] with ω h1 h2 h3 z1 z2 z3
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 z1 z2 z3 ⊢
  rw [h1, hbase, h2, h3, z1, z2, z3]
  simp

/-- If the pointwise product `B₁ * B₂` of two filtered pre-Brownian motions is a martingale, then
their covariation vanishes. -/
theorem isCovariation_zero_of_martingale_mul (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P) (hmul : Martingale (B₁ * B₂) ℱ P) :
    IsCovariation ℱ P B₁ B₂ 0 := by
  refine IsCovariation.mk (isStronglyProgressive_const ℱ 0)
    (ae_of_all P fun _ ↦ continuous_const)
    (ae_of_all P fun _ _ _ _ _ ↦ by simp [BoundedVariationOn, eVariationOn]) .rfl ?_
  refine Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) (hmul.congr (fun t ↦ ?_) fun t ↦ ?_)
  · exact ((((hB₁.adapted t).stronglyMeasurable.mul (hB₂.adapted t).stronglyMeasurable).sub
      (((hB₁.adapted 0).stronglyMeasurable.mul
        (hB₂.adapted 0).stronglyMeasurable).mono (ℱ.mono bot_le))).sub
      stronglyMeasurable_const)
  · filter_upwards [hB₁.eval_zero_ae_eq_zero] with ω h0
    simp [h0]

/-- Independent filtered Brownian motions (with pair increments independent of the past and
mutually independent) have zero covariation. -/
theorem isCovariation_zero_of_indep_sub (hB₁ : IsFilteredPreBrownianReal ℱ B₁ P)
    (hB₂ : IsFilteredPreBrownianReal ℱ B₂ P)
    (hindep_past : ∀ ⦃s t⦄, s ≤ t →
      Indep (.comap (fun ω ↦ (B₁ t ω - B₁ s ω, B₂ t ω - B₂ s ω)) inferInstance) (ℱ s) P)
    (hindep_inc : ∀ ⦃s t⦄, s ≤ t → IndepFun (B₁ t - B₁ s) (B₂ t - B₂ s) P) :
    IsCovariation ℱ P B₁ B₂ 0 :=
  hB₁.isCovariation_zero_of_martingale_mul hB₂
    (hB₁.martingale_mul_of_indep_sub hB₂ hindep_past hindep_inc)

end IsFilteredPreBrownianReal

section LinearCombinations

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}

open scoped Classical in
private theorem martingale_mul_sub_mul_zero_sub_ite {B : ι → ℝ≥0 → Ω → ℝ} {i j : ι}
    (hBi : IsFilteredPreBrownianReal ℱ (B i) P)
    (hBj : IsFilteredPreBrownianReal ℱ (B j) P)
    (horth : i ≠ j → Martingale (B i * B j) ℱ P) :
    Martingale (fun t ω ↦
      B i t ω * B j t ω - B i 0 ω * B j 0 ω - if i = j then (t : ℝ) else 0) ℱ P := by
  by_cases hij : i = j
  · subst hij
    simpa only [↓reduceIte, sq] using hBi.martingale_sq_sub_sq_zero_sub
  · have hadp0 : ∀ t, StronglyMeasurable[ℱ t]
        (fun ω ↦ B i t ω * B j t ω - B i 0 ω * B j 0 ω) := fun t ↦
      ((hBi.adapted t).stronglyMeasurable.mul (hBj.adapted t).stronglyMeasurable).sub
        (((hBi.adapted 0).stronglyMeasurable.mul
          (hBj.adapted 0).stronglyMeasurable).mono (ℱ.mono bot_le))
    have h0eq : ∀ t, (B i * B j) t =ᵐ[P] fun ω ↦ B i t ω * B j t ω - B i 0 ω * B j 0 ω :=
      fun t ↦ hBi.eval_zero_ae_eq_zero.mono fun _ h0 ↦ by simp [h0]
    simpa only [hij, ↓reduceIte, sub_zero] using (horth hij).congr hadp0 h0eq

/-- **Covariation of linear combinations of pairwise-orthogonal filtered Brownian motions.**
For any finite family `B` of filtered pre-Brownian motions whose distinct products `B i * B j` are
martingales, and any coefficient vectors `u, v`, the covariation of `∑ i ∈ s, u i * B i` and
`∑ j ∈ s, v j * B j` is `t ↦ (∑ i ∈ s, u i * v i) * t`. -/
theorem isCovariation_sum_mul_of_martingale_mul (s : Finset ι) (u v : ι → ℝ)
    {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i ∈ s, IsFilteredPreBrownianReal ℱ (B i) P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Martingale (B i * B j) ℱ P) :
    IsCovariation ℱ P (fun t ω ↦ ∑ i ∈ s, u i * B i t ω)
      (fun t ω ↦ ∑ j ∈ s, v j * B j t ω)
      (fun t _ ↦ (∑ i ∈ s, u i * v i) * (t : ℝ)) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · convert isCovariation_zero_left (ℱ := ℱ) (P := P) (0 : ℝ≥0 → Ω → ℝ) <;> simp
  have := (hB i₀ hi₀).isGaussianProcess.isProbabilityMeasure
  let c := ∑ i ∈ s, u i * v i
  refine IsCovariation.mk
    (isStronglyProgressive_deterministic ℱ (continuous_const.mul NNReal.continuous_coe))
    (ae_of_all P fun _ ↦ continuous_const.mul NNReal.continuous_coe)
    (ae_of_all P fun _ ↦ ((lipschitzWith_smul c).comp_locallyBoundedVariationOn
      (NNReal.coe_mono.monotoneOn Set.univ).locallyBoundedVariationOn).congr fun _ _ ↦ rfl)
    (ae_of_all P fun _ ↦ by simp) ?_
  let K (p : ι × ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
    B p.1 t ω * B p.2 t ω - B p.1 0 ω * B p.2 0 ω - if p.1 = p.2 then (t : ℝ) else 0
  have hsum_mart : Martingale (∑ p ∈ s ×ˢ s, (u p.1 * v p.2) • K p) ℱ P :=
    Finset.sum_induction _ (Martingale · ℱ P) (fun _ _ ↦ Martingale.add)
      (martingale_zero _ ℱ P) fun ⟨i, j⟩ hp ↦
        (martingale_mul_sub_mul_zero_sub_ite (hB i (Finset.mem_product.1 hp).1)
          (hB j (Finset.mem_product.1 hp).2)
          (horth i (Finset.mem_product.1 hp).1 j (Finset.mem_product.1 hp).2)).smul (u i * v j)
  have heq : (fun t ω ↦ (∑ i ∈ s, u i * B i t ω) * (∑ j ∈ s, v j * B j t ω) -
      (∑ i ∈ s, u i * B i 0 ω) * (∑ j ∈ s, v j * B j 0 ω) - c * (t : ℝ)) =
      ∑ p ∈ s ×ˢ s, (u p.1 * v p.2) • K p := by
    ext t ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, K, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_product, Finset.sum_mul_sum]
    have h1 : ∑ x ∈ s, ∑ y ∈ s, u x * v y * (B x t ω * B y t ω) =
        ∑ x ∈ s, ∑ y ∈ s, u x * B x t ω * (v y * B y t ω) :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    have h2 : ∑ x ∈ s, ∑ y ∈ s, u x * v y * (B x 0 ω * B y 0 ω) =
        ∑ x ∈ s, ∑ y ∈ s, u x * B x 0 ω * (v y * B y 0 ω) :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    have h3 : ∑ x ∈ s, ∑ y ∈ s, u x * v y * (if x = y then (t : ℝ) else 0) = c * (t : ℝ) := by
      simp only [c, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      have hite (y : ι) : u x * v y * (if x = y then (t : ℝ) else 0) =
          if x = y then u x * v y * (t : ℝ) else 0 := by
        split_ifs <;> simp
      simp [hite, hx]
    rw [h1, h2, h3]
  rw [heq]
  exact Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) hsum_mart

/-- **Quadratic variation of a linear combination of pairwise-orthogonal filtered Brownian
motions.** Under the hypotheses of `isCovariation_sum_mul_of_martingale_mul`, the process
`∑ i ∈ s, u i * B i` has quadratic variation `t ↦ (∑ i ∈ s, u i ^ 2) * t`. -/
theorem isQuadraticVariation_sum_mul_of_martingale_mul (s : Finset ι) (u : ι → ℝ)
    {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i ∈ s, IsFilteredPreBrownianReal ℱ (B i) P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Martingale (B i * B j) ℱ P) :
    IsQuadraticVariation ℱ P (fun t ω ↦ ∑ i ∈ s, u i * B i t ω)
      (fun t _ ↦ (∑ i ∈ s, u i ^ 2) * (t : ℝ)) := by
  have hcov := isCovariation_sum_mul_of_martingale_mul s u u hB horth
  have hsq : (∑ i ∈ s, u i * u i) = ∑ i ∈ s, u i ^ 2 :=
    Finset.sum_congr rfl fun _ _ ↦ (sq _).symm
  rw [hsq] at hcov
  exact hcov.isQuadraticVariation_of_ae_monotone <| ae_of_all P fun _ _ _ hst ↦
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hst)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

end LinearCombinations

end TauCeti.Probability

namespace OrthonormalBasis

open TauCeti.Probability

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Covariation of inner-product projections of vector Brownian noise.** If the coordinates of a
process `W : ℝ≥0 → Ω → E` along an orthonormal basis `b` of `E` are filtered pre-Brownian motions
whose off-diagonal products are martingales, then for every pair of vectors `u, v : E` (orthonormal
or not), `[⟨u, W⟩, ⟨v, W⟩]_t = ⟨u, v⟩ t`. -/
theorem isCovariation_inner_of_martingale_mul (b : OrthonormalBasis ι ℝ E)
    {W : ℝ≥0 → Ω → E}
    (hW : ∀ i, IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪b i, W t ω⟫_ℝ) P)
    (horth : ∀ i j, i ≠ j →
      Martingale (fun t ω ↦ ⟪b i, W t ω⟫_ℝ * ⟪b j, W t ω⟫_ℝ) ℱ P)
    (u v : E) :
    IsCovariation ℱ P (fun t ω ↦ ⟪u, W t ω⟫_ℝ) (fun t ω ↦ ⟪v, W t ω⟫_ℝ)
      (fun t _ ↦ ⟪u, v⟫_ℝ * (t : ℝ)) := by
  have hcov := isCovariation_sum_mul_of_martingale_mul Finset.univ
    (fun i ↦ ⟪u, b i⟫_ℝ) (fun j ↦ ⟪v, b j⟫_ℝ)
    (fun i _ ↦ hW i) (fun i _ j _ hij ↦ horth i j hij)
  have hexp (z : E) : (fun t ω ↦ ∑ i : ι, ⟪z, b i⟫_ℝ * ⟪b i, W t ω⟫_ℝ) =
      fun t ω ↦ ⟪z, W t ω⟫_ℝ := by
    ext t ω
    exact b.sum_inner_mul_inner z (W t ω)
  have hinner : ∑ i : ι, ⟪u, b i⟫_ℝ * ⟪v, b i⟫_ℝ = ⟪u, v⟫_ℝ := by
    simpa only [real_inner_comm (b _)] using b.sum_inner_mul_inner u v
  simpa only [hexp, hinner] using hcov

/-- **Quadratic variation of an inner-product projection of vector Brownian noise.** Under the
hypotheses of `OrthonormalBasis.isCovariation_inner_of_martingale_mul`, for any `u : E` the scalar
projection `⟨u, W⟩` has quadratic variation `t ↦ ‖u‖² t`. -/
theorem isQuadraticVariation_inner_of_martingale_mul (b : OrthonormalBasis ι ℝ E)
    {W : ℝ≥0 → Ω → E}
    (hW : ∀ i, IsFilteredPreBrownianReal ℱ (fun t ω ↦ ⟪b i, W t ω⟫_ℝ) P)
    (horth : ∀ i j, i ≠ j →
      Martingale (fun t ω ↦ ⟪b i, W t ω⟫_ℝ * ⟪b j, W t ω⟫_ℝ) ℱ P)
    (u : E) :
    IsQuadraticVariation ℱ P (fun t ω ↦ ⟪u, W t ω⟫_ℝ)
      (fun t _ ↦ ‖u‖ ^ 2 * (t : ℝ)) := by
  have hcov := b.isCovariation_inner_of_martingale_mul hW horth u u
  rw [real_inner_self_eq_norm_sq] at hcov
  exact hcov.isQuadraticVariation_of_ae_monotone <| ae_of_all P fun _ _ _ hst ↦
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hst) (sq_nonneg _)

end OrthonormalBasis
