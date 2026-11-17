/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The L² Brownian Itô integral process

For a Brownian-integrable predictable integrand `H` (`TauCeti.BrownianIntegrable`) and a filtered
pre-Brownian motion `W`, any process satisfying `TauCeti.IsItoIntegral ℱ P W H I` agrees almost
surely at every time `t` with the finite-horizon predictable L² Brownian integral
`hW.l2Integral t` (`ae_eq_l2Integral_of_isItoIntegral`). This yields square integrability, mean
zero, the bilinear cross-isometry (`integral_mul_of_isItoIntegral`), and the Itô isometry
(`integral_sq_of_isItoIntegral`, `eLpNorm_of_isItoIntegral`). For any **strongly adapted** Itô
integral (`StronglyAdapted ℱ I`), this also yields the martingale property
(`martingale_of_isItoIntegral`, `itoIntegral_isometry`), without requiring Brownian path continuity
or usual filtration conditions.

When `W` has almost surely continuous paths, every `BrownianIntegrable` integrand admits a
strongly predictable, almost surely continuous square-integrable martingale Itô integral
(`exists_isItoIntegral_of_brownianIntegrable`), constructed via continuous L²-martingale
completion of elementary integrals, together with an elementary approximating sequence whose
integrals converge almost surely uniformly on every finite horizon
(`exists_seq_elementaryIntegrand_tendstoUniformlyOn`).

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

/-- On any elementary integrand `K`, the finite-horizon predictable L² Brownian integral agrees
almost surely with the elementary integral `K.integral W T`. -/
theorem coeFn_l2Integral_elementaryIntegrand (hW : IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) (T : ℝ≥0)
    (hmem : MemLp (Function.uncurry K.toProcess) 2 (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hmem.toLp (Function.uncurry K.toProcess)) =ᵐ[P] K.integral W T := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let g (i : ℕ) (p : ℝ≥0 × Ω) : ℝ := (Ioc (K.τ i) (K.τ (i + 1))).indicator (fun _ ↦ K.a i p.2) p.1
  have hterm (i : ℕ) (hi : i < K.n) : MemLp (g i) 2 (ℱ.predictableMeasure P T) :=
    ℱ.memLp_predictableMeasure_indicator_Ioc_mul (P := P) T (K.τ i) (K.τ (i + 1))
      (K.stronglyMeasurable i hi) (K.memLp_a hi)
  let term (i : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    if hi : i < K.n then (hterm i hi).toLp (g i) else 0
  have hsum : hmem.toLp (Function.uncurry K.toProcess) = ∑ i ∈ range K.n, term i := by
    apply Lp.ext
    have hae : ∀ᵐ p ∂ℱ.predictableMeasure P T, ∀ i ∈ range K.n,
        (term i : ℝ≥0 × Ω → ℝ) p = g i p :=
      (ae_ball_iff (range K.n).countable_toSet).mpr fun i hi ↦ by
        have hi' := Finset.mem_range.mp hi
        filter_upwards [(hterm i hi').coeFn_toLp] with p hp
        simpa only [term, hi', dite_true] using hp
    filter_upwards [hmem.coeFn_toLp, Lp.coeFn_finsetSum (range K.n) term, hae] with p h1 h2 h3
    rw [h1, h2, Finset.sum_apply, Function.uncurry_apply_pair, K.toProcess_def]
    exact Finset.sum_congr rfl fun i hi ↦ (h3 i hi).symm
  have hterm_int : ∀ᵐ ω ∂P, ∀ i ∈ range K.n, (hW.l2Integral T (term i) : Ω → ℝ) ω =
      K.a i ω * (W (min (K.τ (i + 1)) T) ω - W (min (K.τ i) T) ω) :=
    (ae_ball_iff (range K.n).countable_toSet).mpr fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      filter_upwards [hW.coeFn_l2Integral_indicator_Ioc_mul T (K.mono hi'.le hi' (Nat.le_succ i))
        (K.stronglyMeasurable i hi') (K.memLp_a hi') (hterm i hi')] with ω hω
      simpa only [term, hi', dite_true] using hω
  filter_upwards [Lp.ext_iff.mp ((congrArg (hW.l2Integral T) hsum).trans (map_sum _ _ _)),
    Lp.coeFn_finsetSum (range K.n) (fun i ↦ hW.l2Integral T (term i)), hterm_int] with ω h1 h2 h3
  rw [h1, h2, Finset.sum_apply, K.integral_def]; exact Finset.sum_congr rfl fun i hi ↦ h3 i hi

/-- Helper: extract a single sequence of `ElementaryIntegrand`s approximating a `BrownianIntegrable`
integrand in `L²((timeMeasure T).prod P)` on every finite horizon `T`. -/
private theorem exists_seq_elementaryIntegrand_tendsto_eLpNorm [IsFiniteMeasure P]
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ K : ℕ → ElementaryIntegrand ℱ, ∀ T : ℝ≥0,
      Tendsto (fun m ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦ (K m).toProcess p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P)) atTop (𝓝 0) := by
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  exact ⟨fun m ↦ ⟨n m, τ m, (hτ m).monotoneOn, a m, ha m,
      fun j hj ↦ ⟨C m, fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩⟩,
    fun T ↦ by simpa only [ElementaryIntegrand.toProcess_eq_simpleHolding] using hlim T⟩

/-- The `L²(P)` distance between an elementary integral and `hW.l2Integral t` of a
`BrownianIntegrable` integrand equals the time-product `L²` distance between their integrands. -/
theorem eLpNorm_elementaryIntegrand_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (K : ElementaryIntegrand ℱ) {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (t : ℝ≥0) :
    eLpNorm (fun ω ↦ K.integral W t ω -
        hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ K.toProcess p.1 p.2 - H p.1 p.2) 2 ((timeMeasure t).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hK := K.brownianIntegrable_toProcess (P := P)
  exact (eLpNorm_congr_ae ((hW.coeFn_l2Integral_elementaryIntegrand K t
    (hK.memLp_predictableMeasure t)).symm.mono fun ω hω ↦ by simp only [Pi.sub_apply, hω])).trans
    (hW.eLpNorm_l2Integral_sub t hK.isStronglyPredictable hH.isStronglyPredictable
      (hK.memLp_predictableMeasure t) (hH.memLp_predictableMeasure t))

/-- For a `BrownianIntegrable` integrand, every Itô integral agrees almost surely at every time `t`
with the finite-horizon predictable L² Brownian integral `hW.l2Integral t`. Neither Brownian path
continuity nor progressive measurability of `I` is required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (t : ℝ≥0) :
    I t =ᵐ[P] hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  obtain ⟨L, hLE, hLI⟩ := hI.exists_approx t
  exact hW.ae_eq_of_tendsto_lintegral_enorm_sq hH.isStronglyPredictable hLE
    (fun _ hε ↦ TauCeti.tendsto_measure_lintegral_eNorm_pow_of_tendsto_eLpNorm
      (F := fun m (p : ℝ≥0 × Ω) ↦ (K m).toProcess p.1 p.2 - H p.1 p.2)
      (n := 2) (by norm_num) (hKlim t) hε)
    hLI (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((hKlim t).congr fun m ↦ (hW.eLpNorm_elementaryIntegrand_sub_l2Integral (K m) hH t).symm))

/-- Any Itô integral of a `BrownianIntegrable` integrand is square integrable at every time. -/
theorem memLp_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {H I : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) : MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm

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

/-- **Itô isometry** for the second moment of an Itô integral of a `BrownianIntegrable`
integrand. -/
theorem integral_sq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {H I : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  simpa only [sq] using hW.integral_mul_of_isItoIntegral hH hH hI hI t

/-- **L²-seminorm Itô isometry.** The `eLpNorm` of an Itô integral at time `t` equals the
time-product `eLpNorm` of its integrand on `(0, t]`. -/
theorem eLpNorm_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {H I : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    eLpNorm (I t) 2 P = eLpNorm (Function.uncurry H) 2 ((timeMeasure t).prod P) :=
  (eLpNorm_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.eLpNorm_l2Integral t hH.isStronglyPredictable (hH.memLp_predictableMeasure t))

/-- **L²-seminorm Itô isometry for differences.** The `L²(P)` distance between two Itô integrals
at time `t` equals the time-product `L²` distance between their integrands on `(0, t]`. -/
theorem eLpNorm_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H₁ H₂ I₁ I₂ : ℝ≥0 → Ω → ℝ}
    (hH₁ : BrownianIntegrable ℱ P H₁) (hH₂ : BrownianIntegrable ℱ P H₂)
    (hI₁ : IsItoIntegral ℱ P W H₁ I₁) (hI₂ : IsItoIntegral ℱ P W H₂ I₂) (t : ℝ≥0) :
    eLpNorm (I₁ t - I₂ t) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ H₁ p.1 p.2 - H₂ p.1 p.2) 2 ((timeMeasure t).prod P) :=
  hW.eLpNorm_of_isItoIntegral (H := fun s ω ↦ H₁ s ω - H₂ s ω) (hH₁.sub hH₂) (hI₁.sub hI₂) t

/-- Any strongly adapted Itô integral of a `BrownianIntegrable` integrand is a martingale. -/
theorem martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P) {H I : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (hAdap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨K, hKlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  refine martingale_of_tendsto_eLpNorm_one (fun m ↦ (K m).martingale_integral hW.martingale)
    hAdap fun t ↦ TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm (p := 2)
      (by norm_num) ((hKlim t).congr fun m ↦ ?_)
  rw [← hW.eLpNorm_elementaryIntegrand_sub_l2Integral (K m) hH t]
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm)

/-- **Itô isometry and martingale theorem.** Any strongly adapted Itô integral of a
`BrownianIntegrable` integrand is a square-integrable martingale whose second moment at every
time `t` equals the expected square energy of `H` on `(0, t]`. Neither Brownian path continuity
nor usual filtration conditions are required. -/
theorem itoIntegral_isometry (hW : IsFilteredPreBrownianReal ℱ W P) {H I : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (hAdap : StronglyAdapted ℱ I) :
    Martingale I ℱ P ∧
      ∀ t : ℝ≥0, ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P :=
  ⟨hW.martingale_of_isItoIntegral hH hI hAdap, hW.integral_sq_of_isItoIntegral hH hI⟩

/-- Internal existence builder exposing an approximating sequence of elementary integrands whose
integrals converge almost surely uniformly on every finite horizon to the constructed continuous
martingale Itô integral. -/
private theorem exists_approx_continuous_martingale_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (K : ℕ → ElementaryIntegrand ℱ),
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ t : ℝ≥0, MemLp (I t) 2 P) ∧
      (∀ T : ℝ≥0, Tendsto (fun n ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, Continuous (I · ω) ∧ ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n t ↦ (K n).integral W t ω) (I · ω) atTop (Set.Iic T) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨L, hLlim⟩ := exists_seq_elementaryIntegrand_tendsto_eLpNorm (P := P) hH
  have hmem : ∀ m t, MemLp ((L m).integral W t) 2 P := fun m t ↦ (L m).memLp_integral hW t
  have hcau (t : ℝ≥0) : CauchySeq (fun m ↦ (hmem m t).toLp ((L m).integral W t)) := by
    let Z := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))
    refine Tendsto.cauchySeq (x := Z) ?_
    rw [← Lp.toLp_coeFn Z (Lp.memLp Z),
      Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (hmem · t) _ (Lp.memLp Z)]
    exact (hLlim t).congr fun m ↦ (hW.eLpNorm_elementaryIntegrand_sub_l2Integral (L m) hH t).symm
  obtain ⟨I, hImart, hIpred, hIlim, -, φ, hφ, hpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2)
      (fun m ↦ (L m).martingale_integral hW.martingale)
      (fun m ↦ (L m).ae_continuous_integral hcont) hmem hcau
  exact ⟨I, fun n ↦ L (φ n),
    ⟨hH.isStronglyPredictable, hpath.mono fun _ h ↦ h.1, fun t ↦
      ⟨L, fun _ hε ↦ TauCeti.tendsto_measure_lintegral_eNorm_pow_of_tendsto_eLpNorm
          (F := fun m (p : ℝ≥0 × Ω) ↦ (L m).toProcess p.1 p.2 - H p.1 p.2)
          (n := 2) (by norm_num) (hLlim t) hε,
        tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2⟩⟩,
    hIpred, hImart, fun t ↦ (hIlim t).1, fun T ↦ (hLlim T).comp hφ.tendsto_atTop, hpath⟩

/-- **Existence of the L² Brownian Itô integral process.** For a filtered pre-Brownian motion `W`
with almost surely continuous paths, every `BrownianIntegrable` integrand admits a strongly
predictable, almost surely continuous square-integrable martingale Itô integral. No usual
filtration conditions are required. -/
theorem exists_isItoIntegral_of_brownianIntegrable
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P ∧ ∀ t : ℝ≥0, MemLp (I t) 2 P :=
  let ⟨I, _, hIito, hIpred, hImart, hImem, _, _⟩ :=
    hW.exists_approx_continuous_martingale_of_brownianIntegrable hcont hH
  ⟨I, hIito, hIpred, hImart, hImem⟩

/-- Every Itô integral of a `BrownianIntegrable` integrand against an almost surely continuous
filtered pre-Brownian motion is approximated almost surely uniformly on every finite horizon by a
single sequence of elementary integrals whose integrands converge in `L²` on every horizon. -/
theorem exists_seq_elementaryIntegrand_tendstoUniformlyOn
    (hW : IsFilteredPreBrownianReal ℱ W P) (hcont : ∀ᵐ ω ∂P, Continuous (W · ω))
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    ∃ K : ℕ → ElementaryIntegrand ℱ,
      (∀ T : ℝ≥0, Tendsto (fun n ↦ eLpNorm
        (fun p : ℝ≥0 × Ω ↦ (K n).toProcess p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun n t ↦ (K n).integral W t ω) (I · ω) atTop (Set.Iic T) := by
  obtain ⟨I₀, K, hI₀ito, -, -, -, hKlim, hpath⟩ :=
    hW.exists_approx_continuous_martingale_of_brownianIntegrable hcont hH
  exact ⟨K, hKlim, hpath.mp ((hW.isItoIntegral_unique hI hI₀ito).mono fun ω heq hω T ↦ by
    simpa only [show (fun t ↦ I t ω) = fun t ↦ I₀ t ω from funext heq] using hω.2 T)⟩

end TauCeti.Probability.IsFilteredPreBrownianReal
