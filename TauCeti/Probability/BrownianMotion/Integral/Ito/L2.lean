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
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The L² Brownian Itô integral process

For a Brownian-integrable predictable integrand `H` (`TauCeti.BrownianIntegrable`) and a filtered
pre-Brownian motion `W`, any process satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I`
agrees almost surely at every time `t` with the finite-horizon predictable L² Brownian integral
`hW.l2Integral t` (`ae_eq_l2Integral_of_isItoIntegral`). This yields mean zero
(`integral_eq_zero_of_isItoIntegral`) and the bilinear cross-isometry
(`integral_mul_of_isItoIntegral`), as well as the bundled martingale and Itô isometry theorem
(`itoIntegral_isometry`) built on `Ito/Isometry.lean`.

When `W` has almost surely continuous paths, every `BrownianIntegrable` integrand also admits an
approximating sequence of bounded simple holdings whose elementary integrals converge almost
surely uniformly on every finite horizon to any Itô integral
(`exists_seq_simpleHolding_tendstoUniformlyOn`).

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

/-- Helper: `MemLp` for bounded `ℱ (τ j)`-measurable heights. -/
private theorem memLp_of_bound_stronglyMeasurable [IsFiniteMeasure P]
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    {C : ℝ} (hb : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) (j : ℕ) (hj : j < n) :
    MemLp (a j) 2 P :=
  MemLp.of_bound ((ha j hj).mono (ℱ.le _)).aestronglyMeasurable C (.of_forall (hb j hj))

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
    (fun _ hε ↦ TauCeti.tendsto_measure_lintegral_eNorm_pow_of_tendsto_eLpNorm
      (F := fun k (p : ℝ≥0 × Ω) ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
      (n := 2) (by norm_num) (hKlim t) hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((hKlim t).congr fun k ↦ (hW.eLpNorm_simpleGains_sub_l2Integral (hτ k).monotoneOn (ha k)
        (memLp_of_bound_stronglyMeasurable (ha k) (hb k)) hH t).symm))

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

/-- **Itô isometry and martingale theorem.** Any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a square-integrable martingale whose second moment at every
time `t` equals the expected square energy of `H` on `(0, t]`. Neither Brownian path continuity
nor usual filtration conditions are required. -/
theorem itoIntegral_isometry (hW : IsFilteredPreBrownianReal ℱ W P) {H I : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (hAdap : StronglyAdapted ℱ I) :
    Martingale I ℱ P ∧
      ∀ t : ℝ≥0, ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P :=
  ⟨hI.martingale hW hH hAdap, hI.integral_sq hW hH⟩

/-- Internal existence builder exposing an approximating sequence of bounded simple holdings whose
integrals converge almost surely uniformly on every finite horizon to the constructed continuous
martingale Itô integral. -/
private theorem exists_approx_continuous_martingale_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Set.Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ t : ℝ≥0, MemLp (I t) 2 P) ∧
      (∀ T : ℝ≥0, Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, Continuous (I · ω) ∧ ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun k t ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω)
          (I · ω) atTop (Set.Iic T) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hKlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hmem (m t) : MemLp (Finance.simpleGains (τ m) (n m) (a m) W t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) t
      (Finance.memLp_simpleHolding_predictableMeasure (ha m)
        (memLp_of_bound_stronglyMeasurable (ha m) (hb m)) t))
  have hcau (t : ℝ≥0) :
      CauchySeq (fun m ↦ (hmem m t).toLp (Finance.simpleGains (τ m) (n m) (a m) W t)) := by
    let Z := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
    refine Tendsto.cauchySeq (x := Z) ?_
    rw [← Lp.toLp_coeFn Z (Lp.memLp Z),
      Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (hmem · t) _ (Lp.memLp Z)]
    exact (hKlim t).congr fun m ↦ (hW.eLpNorm_simpleGains_sub_l2Integral (hτ m).monotoneOn (ha m)
      (memLp_of_bound_stronglyMeasurable (ha m) (hb m)) hH t).symm
  obtain ⟨I, hImart, hIpred, hIlim, -, φ, hφ, hpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2)
      (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m)
        fun j hj ↦ ⟨C m, .of_forall fun ω ↦ by
          simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
      (fun m ↦ hcont.mono fun _ hω ↦ Finance.continuous_simpleGains hω) hmem hcau
  exact ⟨I, fun k ↦ n (φ k), fun k ↦ τ (φ k), fun k ↦ a (φ k), fun k ↦ C (φ k),
    fun k ↦ (hτ (φ k)).monotoneOn, fun k ↦ ha (φ k), fun k ↦ hb (φ k),
    ⟨hH.isStronglyPredictable, hpath.mono fun _ h ↦ h.1, fun t ↦
      ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha, fun _ hε ↦
          TauCeti.tendsto_measure_lintegral_eNorm_pow_of_tendsto_eLpNorm
            (F := fun m (p : ℝ≥0 × Ω) ↦
              Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2)
            (n := 2) (by norm_num) (hKlim t) hε,
        tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2⟩⟩,
    hIpred, hImart, fun t ↦ (hIlim t).1, fun T ↦ (hKlim T).comp hφ.tendsto_atTop, hpath⟩

/-- Every Itô integral of a `BrownianIntegrable` integrand against an almost surely continuous
filtered pre-Brownian motion is approximated almost surely uniformly on every finite horizon by a
single sequence of bounded simple holdings whose holdings converge in `L²` on every horizon. -/
theorem exists_seq_simpleHolding_tendstoUniformlyOn
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Set.Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      (∀ T : ℝ≥0, Tendsto (fun k ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun k t ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω)
          (I · ω) atTop (Set.Iic T) := by
  obtain ⟨I₀, n, τ, a, C, hτ, ha, hb, hI₀ito, -, -, -, hKlim, hpath⟩ :=
    hW.exists_approx_continuous_martingale_of_brownianIntegrable hcont hH
  exact ⟨n, τ, a, C, hτ, ha, hb, hKlim, hpath.mp ((isItoIntegral_unique hW hI hI₀ito).mono
    fun ω heq hω T ↦ by
      simpa only [show (fun t ↦ I t ω) = fun t ↦ I₀ t ω from funext heq] using hω.2 T)⟩

end TauCeti.Probability.IsFilteredPreBrownianReal
