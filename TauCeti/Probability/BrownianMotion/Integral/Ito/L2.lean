/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Square
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
public import TauCeti.Probability.Process.AccumulatedEnergy
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Martingale.LpLimit
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# L² theory and existence of the Itô stochastic integral

For a `TauCeti.BrownianIntegrable` integrand `H` and a filtered pre-Brownian motion `W`, any
Itô integral `I` satisfying `TauCeti.Probability.IsItoIntegral ℱ P W H I` agrees almost surely at
each finite horizon `T` with the terminal L² integral `hW.l2Integral T`. In particular, `I T` is
square integrable with mean zero, satisfies the Itô isometry and cross-isometry against the
time-product inner product, and—when strongly adapted to `ℱ`—is a true `L²` martingale whose
square minus elapsed pathwise square energy `∫ s, H s ω ^ 2 ∂timeMeasure t` is again a true
martingale on the raw filtration. None of these identification, moment, or martingale properties
require path continuity of `W` or usual conditions on `ℱ`.

When `W` also has almost surely continuous paths, approximating `H` by bounded simple holdings in
time-product `L²` and passing to the continuous martingale limit via
`MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` constructs a predictable, continuous
`L²` martingale that satisfies `IsItoIntegral ℱ P W H I`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace

namespace TauCeti.BrownianIntegrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H : ℝ≥0 → Ω → ℝ}

/-- A Brownian-integrable process belongs to `L²` of the finite-horizon predictable measure. -/
theorem memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr
    (by simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T)

end TauCeti.BrownianIntegrable

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

/-- Pathwise Bochner square energy on `timeMeasure t` equals the real part of the `nnvolume`
accumulated energy. -/
theorem integral_sq_timeMeasure_eq_toReal_accumulatedEnergy
    (hH : IsStronglyPredictable ℱ H) (t : ℝ≥0) (ω : Ω) :
    (∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) =
      (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal := by
  have hHmeas : Measurable (fun s ↦ H s ω) :=
    ((hH.mono ℱ.predictable_le_prod).comp_measurable measurable_prodMk_right).measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (hHmeas.pow_const 2).aestronglyMeasurable,
    TauCeti.nnvolume.accumulatedEnergy_eq_setLIntegral_Ioc,
    TauCeti.Probability.timeMeasure_def, ← TauCeti.nnvolume_def]
  congr 1
  refine lintegral_congr fun s ↦ ?_
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm]

/-- The elapsed pathwise Bochner square energy of a predictable process is again predictable. -/
theorem isStronglyPredictable_integral_sq_timeMeasure (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) := by
  have hpred : IsStronglyPredictable ℱ
      (fun t ω ↦ (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal) :=
    (ENNReal.measurable_toReal.comp
      (hH.isStronglyProgressive.isStronglyPredictable_accumulatedEnergy
        TauCeti.nnvolume).measurable).stronglyMeasurable
  have hfun : (fun t ω ↦ ∫ s, H s ω ^ 2 ∂TauCeti.Probability.timeMeasure t) =
      fun t ω ↦ (TauCeti.nnvolume.accumulatedEnergy H t ω).toReal :=
    funext fun t ↦ funext fun ω ↦ hH.integral_sq_timeMeasure_eq_toReal_accumulatedEnergy t ω
  rwa [hfun]

end MeasureTheory.IsStronglyPredictable

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H K I J : ℝ≥0 → Ω → ℝ}

/-! ### Private helpers for elementary L² identification and energy Markov bounds -/

private theorem lp_norm_sq {α : Type*} {_m : MeasurableSpace α} {ν : Measure α} (g : Lp ℝ 2 ν) :
    ‖g‖ ^ 2 = ∫ x, g x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, sq]

private theorem stronglyMeasurable_Ioc_prod (s u : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) :
    StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) := by
  have h := Finance.isStronglyPredictable_simpleHolding (τ := fun j ↦ if j = 0 then s else u)
    (n := 1) (a := fun _ ↦ ξ) (fun j hj ↦ by cases Nat.lt_one_iff.mp hj; simpa using hξ)
  change StronglyMeasurable[ℱ.predictable] _ at h
  convert h using 1
  ext ⟨t, ω⟩; simp [Finance.simpleHolding_def]

private theorem memLp_Ioc_prod_predictableMeasure [SFinite P] (T s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ ξ p.2) p.1) 2
      (ℱ.predictableMeasure P T) := by
  convert Finance.memLp_simpleHolding_predictableMeasure (τ := fun j ↦ if j = 0 then s else u)
    (n := 1) (a := fun _ ↦ ξ) (fun j hj ↦ by cases Nat.lt_one_iff.mp hj; simpa using hξ)
    (fun _ _ ↦ hξ₂) T using 1
  ext ⟨t, ω⟩; simp [Finance.simpleHolding_def]

private theorem coeFn_l2Integral_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s u : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T ((memLp_Ioc_prod_predictableMeasure T s u hξ hξ₂).toLp _) =ᵐ[P]
      fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  let μ := P.trim (ℱ.le s)
  have hmem (f : Lp ℝ 2 μ) : MemLp (f : Ω → ℝ) 2 P := by
    rw [memLp_iff, ← eLpNorm_trim (ℱ.le s) (Lp.stronglyMeasurable f)]
    exact (Lp.memLp f).eLpNorm_lt_top
  let lift (f : Lp ℝ 2 μ) : Lp ℝ 2 (ℱ.predictableMeasure P T) :=
    (memLp_Ioc_prod_predictableMeasure T s u (Lp.stronglyMeasurable f) (hmem f)).toLp _
  have hlift_fn (f : Lp ℝ 2 μ) : (lift f : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
      fun p ↦ (Ioc s u).indicator (fun _ ↦ f p.2) p.1 :=
    (memLp_Ioc_prod_predictableMeasure T s u (Lp.stronglyMeasurable f) (hmem f)).coeFn_toLp
  let L₁ (f : Lp ℝ 2 μ) : Lp ℝ 2 P := hW.l2Integral T (lift f)
  let L₂ (f : Lp ℝ 2 μ) : Lp ℝ 2 P :=
    (hW.memLp_mul_sub (le_max_left s (min u T)) (Lp.stronglyMeasurable f) (hmem f)).toLp
      (fun ω ↦ f ω * (W (max s (min u T)) ω - W s ω))
  have hL₂_fn (f : Lp ℝ 2 μ) : (L₂ f : Ω → ℝ) =ᵐ[P]
      fun ω ↦ f ω * (W (max s (min u T)) ω - W s ω) :=
    (hW.memLp_mul_sub (le_max_left s (min u T)) (Lp.stronglyMeasurable f) (hmem f)).coeFn_toLp
  have hdist_trim (f g : Lp ℝ 2 μ) : dist f g ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
    rw [dist_eq_norm, lp_norm_sq]
    exact (integral_trim (μ := P) (ℱ.le s) ((Lp.stronglyMeasurable (f - g)).pow 2)).symm.trans <|
      integral_congr_ae <| (ae_eq_of_ae_eq_trim (Lp.coeFn_sub f g)).mono fun _ h ↦ by
        rw [Pi.pow_apply, h, Pi.sub_apply]
  have hlift_ae {a b : Ω → ℝ} (ha : StronglyMeasurable[ℱ s] a) (hb : StronglyMeasurable[ℱ s] b)
      (hab : a =ᵐ[P] b) :
      (fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ a p.2) p.1) =ᵐ[ℱ.predictableMeasure P T]
        fun p ↦ (Ioc s u).indicator (fun _ ↦ b p.2) p.1 := by
    rw [ℱ.predictableMeasure_def]
    exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable ℱ.predictable_le_prod
      (stronglyMeasurable_Ioc_prod s u ha) (stronglyMeasurable_Ioc_prod s u hb) <|
      (hab.comp_tendsto
        (Measure.quasiMeasurePreserving_snd (μ := timeMeasure T) (ν := P)).tendsto_ae).mono
        fun p hp ↦ by dsimp only [Function.comp_apply] at hp ⊢; rw [hp]
  have hL₁_cont : Continuous L₁ := (hW.l2Integral T).continuous.comp <|
    (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (Real.sqrt (T : ℝ))) fun f g ↦
      le_of_sq_le_sq (by
        rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt T.coe_nonneg,
          hdist_trim, dist_eq_norm, lp_norm_sq]
        have hpred : IsStronglyPredictable ℱ
            (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ f ω - g ω) t ^ 2) :=
          (stronglyMeasurable_Ioc_prod s u (ξ := fun ω ↦ f ω - g ω)
            ((Lp.stronglyMeasurable f).sub (Lp.stronglyMeasurable g))).pow 2
        have hcongr : (fun p : ℝ≥0 × Ω ↦ (lift f - lift g) p ^ 2) =ᵐ[ℱ.predictableMeasure P T]
            Function.uncurry (fun t ω ↦ (Ioc s u).indicator (fun _ ↦ f ω - g ω) t ^ 2) := by
          filter_upwards [Lp.coeFn_sub (lift f) (lift g), hlift_fn f, hlift_fn g] with p hsub hf hg
          rw [hsub, Pi.sub_apply, hf, hg]; dsimp only [Function.uncurry]
          by_cases ht : p.1 ∈ Ioc s u <;> simp [ht]
        rw [integral_congr_ae hcongr, ℱ.integral_predictableMeasure P hpred T]
        have hfg_int : Integrable (fun p : ℝ≥0 × Ω ↦ (f p.2 - g p.2) ^ 2)
            ((timeMeasure T).prod P) :=
          (((hmem f).sub (hmem g)).comp_snd (timeMeasure T)).integrable_sq
        calc ∫ p, (Ioc s u).indicator (fun _ ↦ f p.2 - g p.2) p.1 ^ 2 ∂(timeMeasure T).prod P
            ≤ ∫ p, (f p.2 - g p.2) ^ 2 ∂(timeMeasure T).prod P :=
              integral_mono
                (hfg_int.mono' (hpred.mono ℱ.predictable_le_prod).aestronglyMeasurable <|
                  Eventually.of_forall fun p ↦ by
                    by_cases ht : p.1 ∈ Ioc s u <;> simp [ht, sq_nonneg])
                hfg_int (fun p ↦ by by_cases ht : p.1 ∈ Ioc s u <;> simp [ht, sq_nonneg])
          _ = (T : ℝ) * ∫ ω, (f ω - g ω) ^ 2 ∂P := by
              rw [integral_prod _ hfg_int]; simp [integral_const, smul_eq_mul, Measure.real_def])
      (by positivity)).continuous
  have hL₂_cont : Continuous L₂ := by
    let c : ℝ := (max s (min u T) : ℝ≥0) - (s : ℝ)
    have hc : 0 ≤ c := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_max_left s (min u T)))
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (Real.sqrt c)) fun f g ↦
      le_of_sq_le_sq ?_ (by positivity)).continuous
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hc, hdist_trim,
      dist_eq_norm, lp_norm_sq]
    have hcongr : (fun ω ↦ (L₂ f - L₂ g) ω ^ 2) =ᵐ[P]
        fun ω ↦ ((f ω - g ω) * (W (max s (min u T)) ω - W s ω)) ^ 2 := by
      filter_upwards [Lp.coeFn_sub (L₂ f) (L₂ g), hL₂_fn f, hL₂_fn g] with ω hsub hf hg
      rw [hsub, Pi.sub_apply, hf, hg, ← sub_mul]
    have hsm : StronglyMeasurable[ℱ s] (fun ω ↦ f ω - g ω) :=
      (Lp.stronglyMeasurable f).sub (Lp.stronglyMeasurable g)
    rw [integral_congr_ae hcongr, hW.integral_sq_mul_sub (le_max_left s (min u T)) hsm, mul_comm]
  have hL₁_add (f g : Lp ℝ 2 μ) : L₁ (f + g) = L₁ f + L₁ g := by
    change hW.l2Integral T (lift (f + g)) = hW.l2Integral T (lift f) + hW.l2Integral T (lift g)
    rw [← map_add]; refine congrArg (hW.l2Integral T) (Lp.ext ?_)
    filter_upwards [hlift_fn (f + g), Lp.coeFn_add (lift f) (lift g), hlift_fn f, hlift_fn g,
      hlift_ae (Lp.stronglyMeasurable (f + g))
        ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g))
        (ae_eq_of_ae_eq_trim (Lp.coeFn_add f g))] with p h1 h2 hf hg hadd
    rw [h1, h2, Pi.add_apply, hf, hg, hadd]; by_cases ht : p.1 ∈ Ioc s u <;> simp [ht]
  have hL₂_add (f g : Lp ℝ 2 μ) : L₂ (f + g) = L₂ f + L₂ g := Lp.ext <| by
    filter_upwards [hL₂_fn (f + g), Lp.coeFn_add (L₂ f) (L₂ g), hL₂_fn f, hL₂_fn g,
      ae_eq_of_ae_eq_trim (Lp.coeFn_add f g)] with ω h1 h2 hf hg hadd
    rw [h1, h2, Pi.add_apply, hf, hg, hadd, Pi.add_apply, add_mul]
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have heq_all : ∀ f : Lp ℝ 2 μ, L₁ f = L₂ f :=
    @Lp.induction Ω ℝ (ℱ s) _ 2 μ _ (by norm_num) (fun f ↦ L₁ f = L₂ f)
      (fun c A hA _ ↦ by
        let g : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) c
        have hgA : (g : Ω → ℝ) =ᵐ[P] A.indicator (fun _ ↦ c) :=
          ae_eq_of_ae_eq_trim (indicatorConstLp_coeFn (p := 2) (hs := hA)
            (hμs := measure_ne_top μ A) (c := c))
        have hlift : lift g = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s u hA)
            (measure_ne_top _ _) c := Lp.ext <| by
          filter_upwards [hlift_fn g,
            hlift_ae (Lp.stronglyMeasurable g) (stronglyMeasurable_const.indicator hA) hgA,
            indicatorConstLp_coeFn (p := 2) (hs := measurableSet_predictable_Ioc_prod s u hA)
              (hμs := measure_ne_top (ℱ.predictableMeasure P T) _) (c := c)] with p h1 h2 h3
          rw [h1, h2, h3]
          by_cases ht : p.1 ∈ Ioc s u <;> by_cases hω : p.2 ∈ A <;> simp [ht, hω]
        apply Lp.ext; change (hW.l2Integral T (lift g) : Ω → ℝ) =ᵐ[P] L₂ g; rw [hlift]
        filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s u hA c,
          hL₂_fn g, hgA] with ω h1 h2 h3
        rw [h1, h2, h3])
      (fun _ _ _ _ _ h1 h2 ↦ by rw [hL₁_add, hL₂_add, h1, h2])
      (isClosed_eq hL₁_cont hL₂_cont)
  have hξμ : MemLp ξ 2 μ := by
    rw [memLp_iff, eLpNorm_trim (ℱ.le s) hξ]; exact hξ₂.eLpNorm_lt_top
  let fξ : Lp ℝ 2 μ := hξμ.toLp ξ
  have hfξ : (fξ : Ω → ℝ) =ᵐ[P] ξ := ae_eq_of_ae_eq_trim hξμ.coeFn_toLp
  have hlift_eq : (memLp_Ioc_prod_predictableMeasure T s u hξ hξ₂).toLp _ = lift fξ := Lp.ext <|
    ((memLp_Ioc_prod_predictableMeasure T s u hξ hξ₂).coeFn_toLp.trans
      (hlift_ae hξ (Lp.stronglyMeasurable fξ) hfξ.symm)).trans (hlift_fn fξ).symm
  rw [hlift_eq]; change (L₁ fξ : Ω → ℝ) =ᵐ[P] _; rw [heq_all fξ]
  exact (hL₂_fn fξ).trans (hfξ.mono fun _ h ↦ by dsimp only; rw [h])

private theorem tendsto_measure_lintegral_eNorm_sq_of_tendsto_eLpNorm [SFinite P]
    {F : ℕ → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hF : ∀ k, StronglyMeasurable (Function.uncurry (F k)))
    (hlim : Tendsto (fun k ↦ eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P))
      atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T}) atTop (𝓝 0) := by
  wlog htop : ε ≠ ∞ generalizing ε
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (this zero_lt_one ENNReal.one_ne_top) (fun _ ↦ zero_le) fun k ↦
      measure_mono fun _ h ↦ (le_top : (1 : ℝ≥0∞) ≤ ∞).trans (by rwa [not_not.mp htop] at h)
  have hbound (k : ℕ) : P {ω | ε ≤ ∫⁻ s, ‖F k s ω‖ₑ ^ 2 ∂timeMeasure T} ≤
      eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P) ^ 2 / ε := by
    rw [ENNReal.le_div_iff_mul_le (.inl hε.ne') (.inl htop), mul_comm]
    refine (mul_meas_ge_le_lintegral
      ((hF k).measurable.eNorm.pow_const 2 |>.lintegral_prod_left') ε).trans_eq ?_
    have hprod := lintegral_prod_symm (fun p : ℝ≥0 × Ω ↦ ‖Function.uncurry (F k) p‖ₑ ^ 2)
      ((hF k).eNorm.pow_const 2).aemeasurable (μ := timeMeasure T) (ν := P)
    have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      (hF k).aestronglyMeasurable (μ := (timeMeasure T).prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat,
      Function.uncurry_apply_pair] at hprod hp
    exact hprod.symm.trans hp.symm
  have hsq : Tendsto (fun k ↦
      eLpNorm (Function.uncurry (F k)) 2 ((timeMeasure T).prod P) ^ 2) atTop (𝓝 0) := by
    simpa only [sq, mul_zero] using
      ENNReal.Tendsto.mul hlim (.inr ENNReal.zero_ne_top) hlim (.inr ENNReal.zero_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hsq (.inr hε.ne'))
    (fun _ ↦ zero_le) hbound

private theorem martingale_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₁ : ∀ j < n, Integrable (a j) P) :
    Martingale (Finance.simpleGains τ n a W) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  induction n with
  | zero =>
    convert martingale_zero ℝ ℱ P using 1
    ext t ω; simp [Finance.simpleGains_def]
  | succ n ih =>
    convert (ih (hτ.mono (Iic_subset_Iic.mpr n.le_succ))
        (fun j hj ↦ ha j (hj.trans n.lt_succ_self))
        (fun j hj ↦ ha₁ j (hj.trans n.lt_succ_self))).add
      (hW.martingale_mul_sub_min (hτ (by simp) (by simp) n.le_succ)
        (ha n n.lt_succ_self) (ha₁ n n.lt_succ_self)) using 1
    ext t ω; simp [Finance.simpleGains_def, Finset.sum_range_succ]

/-! ### Identification with the terminal L² integral and moments -/

/-- On a monotone deterministic grid with square-integrable left-measurable heights, the terminal
`L²` Brownian integral agrees almost surely with the elementary gains process. -/
theorem coeFn_l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp _) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hterm (j : ℕ) (hj : j < n) :=
    memLp_Ioc_prod_predictableMeasure T (τ j) (τ (j + 1)) (ha j hj) (ha₂ j hj)
  let f : ℕ → Lp ℝ 2 (ℱ.predictableMeasure P T) := fun j ↦
    if hj : j < n then (hterm j hj).toLp _ else 0
  have hsum : (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
      (Function.uncurry (Finance.simpleHolding τ n a)) = ∑ j ∈ Finset.range n, f j := Lp.ext <| by
    have hterms : ∀ j ∈ Finset.range n, (f j : ℝ≥0 × Ω → ℝ) =ᵐ[ℱ.predictableMeasure P T]
        fun p ↦ (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ a j p.2) p.1 := fun j hj ↦ by
      simp only [f, dite_eq_left (Finset.mem_range.mp hj)]
      exact (hterm j (Finset.mem_range.mp hj)).coeFn_toLp
    filter_upwards [(Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp,
      Lp.coeFn_finsetSum (s := Finset.range n) f, eventuallyEq_sum hterms] with p hp0 hp hps
    rw [hp0, hp, hps]; simp [Function.uncurry_def, Finance.simpleHolding_def]
  rw [hsum, map_sum]
  have heach : ∀ j ∈ Finset.range n, (hW.l2Integral T (f j) : Ω → ℝ) =ᵐ[P]
      fun ω ↦ a j ω * (W (min (τ (j + 1)) T) ω - W (min (τ j) T) ω) := fun j hj ↦ by
    have hj' := Finset.mem_range.mp hj
    have hle : τ j ≤ τ (j + 1) := hτ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
    simp only [f, dite_eq_left hj']
    refine (coeFn_l2Integral_Ioc hW T (τ j) (τ (j + 1)) (ha j hj') (ha₂ j hj')).mono fun ω hω ↦
      hω.trans ?_
    by_cases hT : τ j ≤ T
    · rw [min_eq_left hT, max_eq_right (le_min hle hT)]
    · have hT' : T ≤ τ j := (not_le.mp hT).le
      simp [min_eq_right hT', min_eq_right (hT'.trans hle), max_eq_left hT']
  filter_upwards [Lp.coeFn_finsetSum (s := Finset.range n) (fun j ↦ hW.l2Integral T (f j)),
    eventuallyEq_sum heach] with ω hω hsumω
  rw [hω, hsumω]; simp [Finance.simpleGains_def]

private theorem eLpNorm_simpleGains_sub_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω -
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) ω) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let fK := (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
    (Function.uncurry (Finance.simpleHolding τ n a))
  let fH := (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)
  calc eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω - hW.l2Integral T fH ω) 2 P
      = edist (hW.l2Integral T fK) (hW.l2Integral T fH) := by
        rw [Lp.edist_def]
        exact eLpNorm_congr_ae
          ((hW.coeFn_l2Integral_simpleHolding hτ ha ha₂ T).symm.sub EventuallyEq.rfl)
    _ = eLpNorm (⇑fK - ⇑fH) 2 (ℱ.predictableMeasure P T) := by
        rw [(hW.l2Integral T).isometry.edist_eq, Lp.edist_def]
    _ = eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
          (ℱ.predictableMeasure P T) :=
        eLpNorm_congr_ae ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp.sub
          (hH.memLp_predictableMeasure T).coeFn_toLp)
    _ = eLpNorm (fun p : ℝ≥0 × Ω ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure T).prod P) := by
        rw [ℱ.predictableMeasure_def]
        exact eLpNorm_trim ℱ.predictable_le_prod
          ((Finance.isStronglyPredictable_simpleHolding ha).sub hH.isStronglyPredictable)

private theorem exists_simpleHolding_approx (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      (∀ k j, j < n k → MemLp (a k j) 2 P) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦
          Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 - H p.1 p.2)
          2 ((timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      (∀ T ε, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
          ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure T})
          atTop (𝓝 0)) ∧
      (∀ T, Tendsto (fun k ↦ eLpNorm (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W T ω -
          hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) ω) 2 P)
          atTop (𝓝 0)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, -, hτ, ha, hb, hlim⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (k j : ℕ) (hj : j < n k) : MemLp (a k j) 2 P :=
    (memLp_const (C k)).mono' ((ha k j hj).mono (ℱ.le _)).aestronglyMeasurable
      (Eventually.of_forall (hb k j hj))
  refine ⟨n, τ, a, C, fun k ↦ (hτ k).monotoneOn, ha, hb, ha₂, hlim,
    fun T ε hε ↦ tendsto_measure_lintegral_eNorm_sq_of_tendsto_eLpNorm
      (F := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
      (fun k ↦ ((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod) (hlim T) hε,
    fun T ↦ by
      simpa only [fun k ↦
        hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ k).monotoneOn (ha k) (ha₂ k) T] using hlim T⟩

/-- **Agreement with the terminal L² integral.** For a Brownian-integrable integrand, any Itô
integral agrees almost surely at each finite horizon `T` with `hW.l2Integral T`. Path continuity
of `W` is not required. -/
theorem ae_eq_l2Integral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  obtain ⟨n, τ, a, -, hτ, ha, -, -, -, hE, hL2⟩ := hW.exists_simpleHolding_approx hH
  exact hW.ae_eq_of_isItoIntegral hI hτ ha (hE T)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hL2 T))

/-- **L² characterization of Itô integrals.** For a Brownian-integrable integrand `H`, an almost
surely continuous process `I` is an Itô integral of `H` if and only if `I T` agrees almost surely
with the terminal `L²` integral `hW.l2Integral T` at every horizon `T`. Path continuity of `W` is
not required. -/
theorem isItoIntegral_iff_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hIcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) :
    IsItoIntegral ℱ P W H I ↔
      ∀ T : ℝ≥0, I T =ᵐ[P]
        hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  refine ⟨fun hI T ↦ hW.ae_eq_l2Integral_of_isItoIntegral hH hI T, fun hT ↦ ?_⟩
  obtain ⟨n, τ, a, C, hτ, ha, hb, -, -, hE, hL2⟩ := hW.exists_simpleHolding_approx hH
  refine ⟨hH.isStronglyPredictable, hIcont, fun T ↦
    ⟨n, τ, a, hτ, ha, fun k j hj ↦ ⟨C k, hb k j hj⟩, hE T,
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        ((hL2 T).congr fun k ↦ eLpNorm_congr_ae (EventuallyEq.rfl.sub (hT T).symm))⟩⟩

/-- Every Itô integral of a Brownian-integrable process is square integrable at each horizon. -/
theorem memLp_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    MemLp (I t) 2 P :=
  (Lp.memLp _).ae_eq (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm

/-- Every Itô integral of a Brownian-integrable process has expectation zero at each horizon. -/
theorem integral_eq_zero_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ∂P = 0 :=
  (integral_congr_ae (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t)).trans
    (hW.integral_l2Integral t _)

/-- **Itô cross-isometry.** The covariance of two Brownian-integrable Itô integrals at horizon `t`
equals the time-product inner product of their integrands on `(0, t]`. -/
theorem integral_mul_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (t : ℝ≥0) :
    ∫ ω, I t ω * J t ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure t).prod P := by
  let f := (hH.memLp_predictableMeasure t).toLp (Function.uncurry H)
  let g := (hK.memLp_predictableMeasure t).toLp (Function.uncurry K)
  calc ∫ ω, I t ω * J t ω ∂P
      = ⟪hW.l2Integral t f, hW.l2Integral t g⟫_ℝ := by
        rw [real_inner_comm, L2.inner_def]
        exact integral_congr_ae <| (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).mp <|
          (hW.ae_eq_l2Integral_of_isItoIntegral hK hJ t).mono fun _ hJω hIω ↦ by
            simp [f, g, hIω, hJω]
    _ = ∫ p, H p.1 p.2 * K p.1 p.2 ∂ℱ.predictableMeasure P t := by
        rw [(hW.l2Integral t).inner_map_map, real_inner_comm, L2.inner_def]
        exact integral_congr_ae <| (hH.memLp_predictableMeasure t).coeFn_toLp.mp <|
          (hK.memLp_predictableMeasure t).coeFn_toLp.mono fun _ hpK hpH ↦ by
            simp only [RCLike.inner_apply, conj_trivial, f, g, hpH, hpK]; rfl
    _ = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure t).prod P :=
        ℱ.integral_predictableMeasure P
          (hH.isStronglyPredictable.mul hK.isStronglyPredictable) t

/-- **Itô isometry.** The second moment of a Brownian-integrable Itô integral at horizon `t`
equals the expected square energy of its integrand on `(0, t]`. -/
theorem integral_sq_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) :
    ∫ ω, I t ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  simpa only [sq] using hW.integral_mul_of_isItoIntegral hH hH hI hI t

/-! ### L² martingale property, square compensation, and existence -/

/-- Any strongly adapted Itô integral of a Brownian-integrable process is a true martingale on
the raw filtration. Path continuity of `W` is not required. -/
theorem martingale_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, hτ, ha, -, ha₂, -, -, hL2⟩ := hW.exists_simpleHolding_approx hH
  refine martingale_of_tendsto_eLpNorm_one
    (fun k ↦ hW.martingale_simpleGains (hτ k) (ha k)
      (fun j hj ↦ (ha₂ k j hj).integrable one_le_two))
    hI_adapt fun t ↦ TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two <|
      (hL2 t).congr fun k ↦
        eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm)

private theorem simpleHolding_energy_eq_integral_sq {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n)) (t : ℝ≥0) (ω : Ω) :
    (∑ j ∈ Finset.range n, a j ω ^ 2 * (↑(min (τ (j + 1)) t) - ↑(min (τ j) t))) =
      ∫ s, Finance.simpleHolding τ n a s ω ^ 2 ∂timeMeasure t := by
  have hKmeas : Measurable (fun s ↦ Finance.simpleHolding τ n a s ω) := by
    simp only [Finance.simpleHolding_def]
    exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ioc
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (hKmeas.pow_const 2).aestronglyMeasurable,
    lintegral_congr fun s ↦ by
      rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm],
    Finance.lintegral_enorm_sq_simpleHolding_timeMeasure hτ,
    ENNReal.toReal_sum (fun _ _ ↦
      ENNReal.mul_ne_top (ENNReal.pow_ne_top eNorm_ne_top) ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hle : τ j ≤ τ (j + 1) := hτ (mem_Iic.mpr hj'.le) (mem_Iic.mpr hj') (Nat.le_succ j)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, Real.norm_eq_abs, sq_abs]
  by_cases hT : τ j ≤ t
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_min hle hT))),
      min_eq_left hT]
  · have hT' : t ≤ τ j := (not_le.mp hT).le
    rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr
      ((min_le_right _ _).trans hT')))]
    simp [min_eq_right hT', min_eq_right (hT'.trans hle)]

/-- **L² Itô square compensation (quadratic variation bracket).** For a Brownian-integrable
integrand and a strongly adapted Itô integral `I`, the process
`I t ^ 2 - ∫ s, H s ^ 2 ∂timeMeasure t` is a true martingale on the raw filtration.
Path continuity of `W` is not required. -/
theorem martingale_sq_sub_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adapt : StronglyAdapted ℱ I) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) :=
    hH.isStronglyPredictable.isStronglyPredictable_integral_sq_timeMeasure
      |>.isStronglyProgressive.stronglyAdapted
  obtain ⟨n, τ, a, -, hτ, ha, -, ha₂, hlim, -, hL2⟩ := hW.exists_simpleHolding_approx hH
  let B (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j ∈ Finset.range (n k), a k j ω ^ 2 * (↑(min (τ k (j + 1)) t) - ↑(min (τ k j) t))
  refine martingale_of_tendsto_eLpNorm_one
    (fun k ↦ hW.martingale_sq_simpleGains_sub (hτ k) (ha k) (ha₂ k))
    (fun t ↦ (hI_adapt t).pow 2 |>.sub (hA_adapt t)) fun t ↦ ?_
  have hsq_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_sq_sub_one (hW.memLp_of_isItoIntegral hH hI t).eLpNorm_ne_top <|
      (hL2 t).congr fun k ↦
        eLpNorm_congr_ae (EventuallyEq.rfl.sub (hW.ae_eq_l2Integral_of_isItoIntegral hH hI t).symm)
  have henergy_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    have hHmem : MemLp (fun p : ℝ≥0 × Ω ↦ H p.1 p.2) 2 ((timeMeasure t).prod P) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def, Function.uncurry_def] using
        hH.memLp t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_sq_sub_one hHmem.eLpNorm_ne_top (hlim t)) (fun _ ↦ zero_le)
      fun k ↦ ?_
    simp_rw [B, simpleHolding_energy_eq_integral_sq (hτ k) t]
    have hBA_sm : AEStronglyMeasurable
        (fun ω ↦ (∫ s, Finance.simpleHolding (τ k) (n k) (a k) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha k))
        |>.isStronglyPredictable_integral_sq_timeMeasure.isStronglyProgressive.stronglyAdapted t
        |>.mono (ℱ.le t)).sub ((hA_adapt t).mono (ℱ.le t)))).aestronglyMeasurable
    have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 ^ 2 - H p.1 p.2 ^ 2) :=
      (((Finance.isStronglyPredictable_simpleHolding (ha k)).mono
        ℱ.predictable_le_prod).pow 2).sub
        ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).pow 2)
    rw [eLpNorm_one_eq_lintegral_eNorm hBA_sm,
      eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
      lintegral_prod_symm _ hdiff_sm.measurable.eNorm.aemeasurable]
    refine lintegral_mono_ae <| hH.locallyBrownianIntegrable.ae_memLp.mono fun ω hω ↦ ?_
    have hH2 : MemLp (fun s ↦ H s ω) 2 (timeMeasure t) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using hω t
    have hK2 : MemLp (fun s ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω) 2 (timeMeasure t) := by
      simp only [Finance.simpleHolding_def]
      exact memLp_finsetSum _ fun j _ ↦
        (memLp_const (a k j ω)).indicator measurableSet_Ioc.nullMeasurableSet
    rw [← integral_sub hK2.integrable_sq hH2.integrable_sq]
    exact eNorm_integral_le_lintegral_eNorm _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hsq_lim.add henergy_lim) (fun _ ↦ zero_le) fun k ↦ ?_
  have hsplit : ((fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - B k t ω) -
      (fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t)) =
      (fun ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω ^ 2 - I t ω ^ 2) -
        (fun ω ↦ B k t ω - ∫ s, H s ω ^ 2 ∂timeMeasure t) := by ext ω; simp; ring
  rw [hsplit]; exact eLpNorm_sub_le le_rfl

/-- **Existence of the L² Itô stochastic integral.** Every Brownian-integrable process against a
continuous filtered pre-Brownian motion admits a predictable, almost surely continuous `L²`
martingale that is its Itô integral. No usual conditions on the filtration are required. -/
theorem exists_isItoIntegral_of_brownianIntegrable (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ,
      IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hτ, ha, hb, ha₂, -, hE, hL2⟩ := hW.exists_simpleHolding_approx hH
  let M (k : ℕ) : ℝ≥0 → Ω → ℝ := Finance.simpleGains (τ k) (n k) (a k) W
  have hMmem (k : ℕ) (t : ℝ≥0) : MemLp (M k t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ k) (ha k) (ha₂ k) t)
  have hMcau (t : ℝ≥0) : CauchySeq (fun k ↦ (hMmem k t).toLp (M k t)) :=
    Tendsto.cauchySeq
      (x := hW.l2Integral t ((hH.memLp_predictableMeasure t).toLp (Function.uncurry H))) <| by
        rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
        exact (hL2 t).congr fun k ↦
          eLpNorm_congr_ae ((hMmem k t).coeFn_toLp.symm.sub EventuallyEq.rfl)
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨I, hImart, hIpred, hIL2, _, ⟨_, _, hIpath⟩⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp
      (fun k ↦ hW.martingale_simpleGains (hτ k) (ha k)
        (fun j hj ↦ (ha₂ k j hj).integrable one_le_two))
      (fun k ↦ (IsItoIntegral.simpleHolding hcont (hτ k) (ha k)
        fun j hj ↦ ⟨C k, hb k j hj⟩).ae_continuous)
      hMmem hMcau
  exact ⟨I, ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦
    ⟨n, τ, a, hτ, ha, fun k j hj ↦ ⟨C k, hb k j hj⟩, hE t,
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hIL2 t).2⟩⟩,
    hIpred, hImart⟩

end TauCeti.Probability.IsFilteredPreBrownianReal
