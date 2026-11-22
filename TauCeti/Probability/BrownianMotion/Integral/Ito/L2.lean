/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy

/-!
# The L² Brownian Itô integral process

For a Brownian-integrable predictable integrand `H` (`TauCeti.BrownianIntegrable`) and a filtered
pre-Brownian motion `W`, any process satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I`
agrees almost surely at every time `t` with the finite-horizon predictable L² Brownian integral
`hW.l2Integral t` (`ae_eq_l2Integral_of_isItoIntegral`). This yields mean zero
(`integral_eq_zero_of_isItoIntegral`) and the bilinear cross-isometry
(`integral_mul_of_isItoIntegral`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The `L²(P)` distance between an elementary Brownian integral and `hW.l2Integral t` of a
`BrownianIntegrable` integrand equals the time-product `L²` distance between their integrands. -/
theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    (t : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W t ω -
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hK : MemLp (Function.uncurry (Finance.simpleHolding τ n a)) 2 (ℱ.predictableMeasure P t) :=
    Finance.memLp_simpleHolding_predictableMeasure ha ha₂ t
  exact (eLpNorm_congr_ae ((hW.coeFn_l2Integral_simpleHolding hτ ha t hK).symm.mono
    fun ω hω ↦ by simp only [Pi.sub_apply, hω])).trans
    (hW.eLpNorm_l2Integral_sub t (Finance.isStronglyPredictable_simpleHolding ha)
      hH.isStronglyPredictable hK (hH.memLp_predictableMeasure t))

/-- For a `BrownianIntegrable` integrand, every Itô integral agrees almost surely at every time `t`
with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`. Neither Brownian path
continuity nor progressive measurability of `I` is required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hKlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  exact hI.ae_eq_of_tendstoInMeasure hW (fun k ↦ (hτ k).monotoneOn) ha
    (fun _ hε ↦ TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm
      (fun k ↦ (((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (hKlim t) hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((hKlim t).congr fun k ↦ (hW.eLpNorm_simpleGains_sub_l2Integral (hτ k).monotoneOn (ha k)
        (Finance.memLp_of_bound_stronglyMeasurable (ha k) (hb k)) hH t).symm))

/-- Any Itô integral of a `BrownianIntegrable` integrand has expectation zero at every time. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) : ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Bilinear Itô cross-isometry (covariance).** For two `BrownianIntegrable` integrands and
their Itô integrals, the expected product at time `t` equals the time-product integral of the
product of the integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H₁ H₂ I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) (t : ℝ≥0) :
    ∫ ω, I₁ t ω * I₂ t ω ∂P = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P := by
  let f₁ := (hH₁.memLp_predictableMeasure t).toLp (Function.uncurry H₁)
  let f₂ := (hH₂.memLp_predictableMeasure t).toLp (Function.uncurry H₂)
  calc ∫ ω, I₁ t ω * I₂ t ω ∂P = ⟪hW.l2Integral t f₁, hW.l2Integral t f₂⟫_ℝ := by
        rw [L2.inner_def]
        exact integral_congr_ae ((hW.ae_eq_l2Integral_of_isItoIntegral hH₁ hI₁ t).mp
          ((hW.ae_eq_l2Integral_of_isItoIntegral hH₂ hI₂ t).mono fun _ h2 h1 ↦ by
            simp only [f₁, f₂, RCLike.inner_apply, conj_trivial, h1, h2, mul_comm]))
    _ = ⟪f₁, f₂⟫_ℝ := (hW.l2Integral t).inner_map_map f₁ f₂
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂ℱ.predictableMeasure P t := by
        rw [L2.inner_def]
        exact integral_congr_ae ((hH₁.memLp_predictableMeasure t).coeFn_toLp.mp
          ((hH₂.memLp_predictableMeasure t).coeFn_toLp.mono fun ⟨_, _⟩ h2 h1 ↦ by
            simp only [f₁, f₂, RCLike.inner_apply, conj_trivial, h1, h2,
              Function.uncurry_apply_pair, mul_comm]))
    _ = ∫ p, H₁ p.1 p.2 * H₂ p.1 p.2 ∂(timeMeasure t).prod P :=
        ℱ.integral_predictableMeasure P (hH₁.isStronglyPredictable.mul hH₂.isStronglyPredictable) t

end TauCeti.Probability.IsFilteredPreBrownianReal
