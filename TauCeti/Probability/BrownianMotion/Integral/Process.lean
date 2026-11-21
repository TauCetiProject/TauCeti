/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Simple
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Square
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.MaximalInequality.Basic
import TauCeti.Probability.Process.TimeIntegral

/-!
# The predictable L² Brownian integral process

For a filtration-relative Brownian motion `W` and an integrand `H` in
`TauCeti.BrownianIntegrable ℱ P H`, the finite-horizon terminal maps
`IsFilteredPreBrownianReal.l2Integral` assemble into a time-indexed stochastic integral process.

First, `eLpNorm_l2Integral_sub_l2Integral` and `eLpNorm_simpleGains_sub_l2Integral` express
sample-space `L²` distances as ambient time-product `L²` distances, and
`integral_mul_l2Integral_toPredictableLp` and `integral_sq_l2Integral_toPredictableLp` establish the
terminal isometries.

Second, any adapted modification `I` of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` inherits the
elementary-approximation `L²` error identity (`eLpNorm_simpleGains_sub_of_ae_eq_l2Integral`,
`tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral`), uniform convergence in outer probability on
finite horizons when right-continuous (`tendsto_measure_exists_le_norm_simpleGains_sub_lt`), and is
a centered `L²` martingale satisfying the Itô isometry `integral_sq_of_ae_eq_l2Integral`, the
cross-isometry `integral_mul_of_ae_eq_l2Integral`, and the square-compensation martingale property
`martingale_sq_sub_integral_of_ae_eq_l2Integral`. Predictable rectangle restriction and optional
stopping at raw stopping times are established in
`TauCeti.Probability.BrownianMotion.Integral.Locality` and
`TauCeti.Probability.BrownianMotion.Integral.OptionalStopping`.

Finally, when `W` has almost surely continuous paths, `exists_continuous_l2Integral` selects a
strongly predictable, almost surely continuous martingale modification, unique up to
indistinguishability. Neither right continuity nor completeness of the filtration is assumed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- For two `BrownianIntegrable` integrands, the sample-space `L²` distance between their
finite-horizon `l2Integral` values equals the ambient time-product `L²` distance between the
integrands. -/
theorem eLpNorm_l2Integral_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H K : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (T : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    eLpNorm (fun ω ↦ hW.l2Integral T (hH.toPredictableLp T) ω -
        hW.l2Integral T (hK.toPredictableLp T) ω) 2 P =
      eLpNorm (fun p ↦ H p.1 p.2 - K p.1 p.2) 2 ((timeMeasure T).prod P) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hsm : StronglyMeasurable[ℱ.predictable] (Function.uncurry H - Function.uncurry K) :=
    hH.isStronglyPredictable.sub hK.isStronglyPredictable
  calc
    eLpNorm (fun ω ↦ hW.l2Integral T (hH.toPredictableLp T) ω -
        hW.l2Integral T (hK.toPredictableLp T) ω) 2 P
      = edist (hW.l2Integral T (hH.toPredictableLp T))
          (hW.l2Integral T (hK.toPredictableLp T)) := (Lp.edist_def _ _).symm
    _ = edist (hH.toPredictableLp T) (hK.toPredictableLp T) := (hW.l2Integral T).edist_map _ _
    _ = eLpNorm (Function.uncurry H - Function.uncurry K) 2 (ℱ.predictableMeasure P T) := by
        rw [Lp.edist_def]
        exact eLpNorm_congr_ae ((hH.coeFn_toPredictableLp T).sub (hK.coeFn_toPredictableLp T))
    _ = eLpNorm (fun p ↦ H p.1 p.2 - K p.1 p.2) 2 ((timeMeasure T).prod P) := by
        rw [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hsm]; rfl

/-- For a `BrownianIntegrable` process and any square-integrable elementary holding on a
nondecreasing grid, the sample-space `L²` distance between `Finance.simpleGains` and `l2Integral`
equals the ambient time-product `L²` distance between `Finance.simpleHolding` and `H`. -/
theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω -
        hW.l2Integral T (hH.toPredictableLp T) ω) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hS := hW.eLpNorm_l2Integral_sub_l2Integral (BrownianIntegrable.simpleHolding ha ha₂) hH T
  rw [(BrownianIntegrable.simpleHolding ha ha₂).toPredictableLp_def T] at hS
  exact (eLpNorm_congr_ae
    ((hW.coeFn_l2Integral_simpleHolding hτ ha T
      ((BrownianIntegrable.simpleHolding ha ha₂).memLp_predictableMeasure T)).symm.sub
      .rfl)).trans hS

/-- Cross-isometry of the finite-horizon predictable `L²` Brownian integral on
`BrownianIntegrable` processes. -/
theorem integral_mul_l2Integral_toPredictableLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {H K : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (T : ℝ≥0) :
    ∫ ω, hW.l2Integral T (hH.toPredictableLp T) ω *
        hW.l2Integral T (hK.toPredictableLp T) ω ∂P =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hiso := (hW.l2Integral T).inner_map_map (hH.toPredictableLp T) (hK.toPredictableLp T)
  have hlhs : ⟪hW.l2Integral T (hH.toPredictableLp T),
      hW.l2Integral T (hK.toPredictableLp T)⟫_ℝ =
      ∫ ω, hW.l2Integral T (hH.toPredictableLp T) ω *
        hW.l2Integral T (hK.toPredictableLp T) ω ∂P := by
    rw [real_inner_comm, L2.inner_def]; simp only [RCLike.inner_apply, conj_trivial]
  have hrhs : ⟪hH.toPredictableLp T, hK.toPredictableLp T⟫_ℝ =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    rw [real_inner_comm, L2.inner_def]
    have hc := integral_congr_ae ((hH.coeFn_toPredictableLp T).mul (hK.coeFn_toPredictableLp T))
    simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply] at hc ⊢
    exact hc.trans (ℱ.integral_predictableMeasure P
      (hH.isStronglyPredictable.mul hK.isStronglyPredictable) T)
  exact hlhs.symm.trans (hiso.trans hrhs)

/-- Itô isometry of the finite-horizon predictable `L²` Brownian integral on a
`BrownianIntegrable` process. -/
theorem integral_sq_l2Integral_toPredictableLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    ∫ ω, hW.l2Integral T (hH.toPredictableLp T) ω ^ 2 ∂P =
      ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P := by
  simpa only [sq] using hW.integral_mul_l2Integral_toPredictableLp hH hH T

section Modification

variable {H K I J : ℝ≥0 → Ω → ℝ}

/-- Any modification of the predictable `L²` integral process vanishes almost surely at `0`. -/
theorem ae_eval_zero_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    I 0 =ᵐ[P] 0 := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  exact (hI 0).trans ((hW.l2Integral_zero _) ▸ Lp.coeFn_zero ℝ 2 P)

/-- Any modification of the predictable `L²` integral process is in `L²(P)` at every time. -/
theorem memLp_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) (t : ℝ≥0) :
    MemLp (I t) 2 P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  exact (Lp.memLp (hW.l2Integral t (hH.toPredictableLp t))).ae_eq (hI t).symm

/-- Cross-isometry for modifications of the predictable `L²` integral processes. -/
theorem integral_mul_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    (hJ : ∀ t, J t =ᵐ[P] hW.l2Integral t (hK.toPredictableLp t)) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P :=
  (integral_congr_ae ((hI T).mul (hJ T))).trans
    (hW.integral_mul_l2Integral_toPredictableLp hH hK T)

/-- Itô isometry for any modification of the predictable `L²` integral process. -/
theorem integral_sq_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P := by
  simpa only [sq] using hW.integral_mul_of_ae_eq_l2Integral hH hH hI hI T

/-- For any almost-everywhere representative `X` of `hW.l2Integral T (hH.toPredictableLp T)` and any
square-integrable elementary holding on a nondecreasing grid, the sample-space `L²` distance
between `Finance.simpleGains` and `X` equals the ambient time-product `L²` distance between
`Finance.simpleHolding` and `H`. -/
theorem eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    {X : Ω → ℝ} {T : ℝ≥0} (hX : X =ᵐ[P] hW.l2Integral T (hH.toPredictableLp T))
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    eLpNorm (Finance.simpleGains τ n a W T - X) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P) :=
  (eLpNorm_congr_ae (EventuallyEq.rfl.sub hX)).trans
    (hW.eLpNorm_simpleGains_sub_l2Integral hH hτ ha ha₂ T)

/-- If elementary holdings converge in ambient time-product `L²` to a family of `BrownianIntegrable`
integrands `H k`, then their Brownian simple gains converge in sample-space `L²` to any
representatives `X k` of `hW.l2Integral T ((hH k).toPredictableLp T)`. -/
theorem tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
    {ι : Type*} {l : Filter ι} (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ι → ℝ≥0 → Ω → ℝ} (hH : ∀ k, BrownianIntegrable ℱ P (H k))
    {X : ι → Ω → ℝ} {T : ℝ≥0} (hX : ∀ k, X k =ᵐ[P] hW.l2Integral T ((hH k).toPredictableLp T))
    {τ : ι → ℕ → ℝ≥0} {n : ι → ℕ} {a : ι → ℕ → Ω → ℝ} (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k, ∀ i < n k, StronglyMeasurable[ℱ (τ k i)] (a k i))
    (ha₂ : ∀ k, ∀ i < n k, MemLp (a k i) 2 P) {L : ℝ≥0∞}
    (hlim : Tendsto (fun k ↦ eLpNorm (fun p ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 -
      H k p.1 p.2) 2 ((timeMeasure T).prod P)) l (𝓝 L)) :
    Tendsto (fun k ↦ eLpNorm (Finance.simpleGains (τ k) (n k) (a k) W T - X k) 2 P) l (𝓝 L) :=
  hlim.congr fun k ↦
    (hW.eLpNorm_simpleGains_sub_of_ae_eq_l2Integral (hH k) (hX k) (hτ k) (ha k) (ha₂ k)).symm

/-- Any strongly adapted modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` is a
martingale on the original raw filtration. -/
theorem martingale_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) : Martingale I ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P := MemLp.of_bound
    ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (Eventually.of_forall (hb m j hj))
  refine martingale_of_tendsto_eLpNorm_one (fun m ↦ hW.martingale.simpleGains_of_bdd
    (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
    hI_adapt fun t ↦ TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t))

/-- If `W` has almost surely continuous paths, `I` is a strongly adapted, almost surely
right-continuous modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)`, and square-integrable
elementary holdings converge in ambient time-product `L²` to `H` on `(0, T]`, then their Brownian
simple gains converge uniformly in outer probability to `I` on `[0, T]`. -/
theorem tendsto_measure_exists_le_norm_simpleGains_sub_lt
    {ι : Type*} {l : Filter ι} (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    {T : ℝ≥0}
    (hI_rc : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ I u ω) (Ioi t) t)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    {τ : ι → ℕ → ℝ≥0} {n : ι → ℕ} {a : ι → ℕ → Ω → ℝ} (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k, ∀ i < n k, StronglyMeasurable[ℱ (τ k i)] (a k i))
    (ha₂ : ∀ k, ∀ i < n k, MemLp (a k i) 2 P)
    (hlim : Tendsto (fun k ↦ eLpNorm (fun p ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 -
      H p.1 p.2) 2 ((timeMeasure T).prod P)) l (𝓝 0))
    {ε : ℝ≥0} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ∃ t ≤ T, (ε : ℝ) < ‖Finance.simpleGains (τ k) (n k) (a k) W t ω -
      I t ω‖}) l (𝓝 0) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hM (k : ι) : Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P := by
    have hstep : ∀ m ≤ n k, Martingale (fun t ω ↦
        ∑ i ∈ range m, a k i ω * (W (min (τ k (i + 1)) t) ω - W (min (τ k i) t) ω)) ℱ P := by
      intro m hm
      induction m with
      | zero => simpa only [sum_range_zero, Pi.zero_def] using martingale_zero ℝ ℱ P
      | succ m ih =>
        have hlt : m < n k := hm
        have hle : τ k m ≤ τ k (m + 1) := hτ k (mem_Iic.mpr hlt.le) (mem_Iic.mpr hlt) m.le_succ
        convert (ih hlt.le).add (hW.martingale_mul_sub_min hle
          (ha k m hlt) ((ha₂ k m hlt).integrable one_le_two)) using 1
        ext t ω; simp only [Pi.add_apply, sum_range_succ]
    convert hstep (n k) le_rfl using 1
    ext t ω; rw [Finance.simpleGains_def]
  exact (hW.martingale_of_ae_eq_l2Integral hH hI_adapt hI).tendsto_measure_exists_le_norm_sub_lt
    hM hI_rc (fun k ↦ hcont.mono fun _ hω _ _ ↦
      (Finance.continuous_simpleGains hω).continuousWithinAt)
    (TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI T) hτ ha ha₂ hlim)) hε

/-- **Brownian square-compensation martingale.** For any `BrownianIntegrable` integrand `H` and
strongly adapted modification `I` of `l2Integral`, `I_t² - ∫_{(0, t]} H_s² ds` is a true
martingale on the original raw filtration. -/
theorem martingale_sq_sub_integral_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P := MemLp.of_bound
    ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (Eventually.of_forall (hb m j hj))
  let M (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 -
      ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t
  have hM (m : ℕ) : Martingale (M m) ℱ P := by
    convert hW.martingale_sq_simpleGains_sub (hτ m).monotoneOn (ha m) (ha₂ m) using 1
    ext t ω; dsimp only [M]
    rw [Finance.integral_sq_simpleHolding_timeMeasure (hτ m).monotoneOn t ω]
  have hcomp_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) := by
    simpa only [sq] using (hH.isStronglyPredictable.mul
      hH.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
  refine martingale_of_tendsto_eLpNorm_one hM (fun t ↦ ((hI_adapt t).pow 2).sub (hcomp_adapt t))
    fun t ↦ ?_
  have hG_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hW.memLp_of_ae_eq_l2Integral hH hI t).eLpNorm_ne_top
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t))
  have hA_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
        ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hH.memLp_timeMeasure t).eLpNorm_ne_top (herr t))
      (fun _ ↦ bot_le) fun m ↦ ?_
    have hS := BrownianIntegrable.simpleHolding (ha m) (ha₂ m)
    have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 ^ 2 - Function.uncurry H p ^ 2) :=
      ((hS.isStronglyPredictable.pow 2).sub (hH.isStronglyPredictable.pow 2)).mono
        ℱ.predictable_le_prod
    have hS_adapt : StronglyAdapted ℱ
        (fun t ω ↦ ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) := by
      simpa only [sq] using (hS.isStronglyPredictable.mul
        hS.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
    have hlhs_m : AEStronglyMeasurable
        (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
      (((hS_adapt t).sub (hcomp_adapt t)).mono (ℱ.le t)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hlhs_m,
      eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
      lintegral_prod_symm _ hdiff_sm.eNorm.aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [hS.locallyBrownianIntegrable.ae_memLp,
      hH.locallyBrownianIntegrable.ae_memLp] with ω hSω hHω
    rw [← integral_sub
      (by simpa [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hSω t).integrable_sq)
      (by simpa [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hHω t).integrable_sq)]
    exact eNorm_integral_le_lintegral_eNorm _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hG_lim.add hA_lim) (fun _ ↦ bot_le) fun m ↦ ?_
  have htri : (M m t - fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) =
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) -
        fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t := by ext ω; simp [M]; ring
  rw [htri]; exact eLpNorm_sub_le le_rfl

end Modification

/-- **Continuous martingale modification of the predictable `L²` Brownian integral.**
When `W` has almost surely continuous paths, any `BrownianIntegrable` integrand `H` admits a
strongly predictable, almost surely continuous martingale `I` on the original raw filtration
that represents `hW.l2Integral t (hH.toPredictableLp t)` at every time `t`. -/
theorem exists_continuous_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P := MemLp.of_bound
    ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (Eventually.of_forall (hb m j hj))
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) t
      ((BrownianIntegrable.simpleHolding (ha m) (ha₂ m)).memLp_predictableMeasure t))
  have htend (t : ℝ≥0) : Tendsto (fun m ↦ (hmem m t).toLp (M m t)) atTop
      (𝓝 (hW.l2Integral t (hH.toPredictableLp t))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    exact (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
      (fun _ ↦ hH) (fun _ ↦ .rfl) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t)).congr
      fun m ↦ eLpNorm_congr_ae (((hmem m t).coeFn_toLp).symm.sub .rfl)
  obtain ⟨I, hIm, hIp, hIlim, _, _, _, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2)
      (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
        ⟨C m, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
      (fun m ↦ hcont.mono fun ω hω ↦ by
        simp only [Finance.simpleGains_def]
        exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
          ((hω.comp (continuous_const.min continuous_id)).sub
            (hω.comp (continuous_const.min continuous_id))))
      hmem (fun t ↦ (htend t).cauchySeq)
  refine ⟨I, hIp, hIm, hIpath.mono fun _ hω ↦ hω.1, fun t ↦ ?_⟩
  have heq_lp : (hIlim t).1.toLp (I t) = hW.l2Integral t (hH.toPredictableLp t) :=
    tendsto_nhds_unique
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun m ↦ hmem m t) _ (hIlim t).1).mpr (hIlim t).2)
      (htend t)
  exact (hIlim t).1.coeFn_toLp.symm.trans (heq_lp ▸ EventuallyEq.rfl)

end TauCeti.Probability.IsFilteredPreBrownianReal
