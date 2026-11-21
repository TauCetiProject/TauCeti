/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Predictable.Basic

/-!
# Itô integrals against Brownian motion and their uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings, with heights known at the left endpoints of
their intervals, approximate `H` on `(0,t]` in square energy in probability, while their
elementary integrals at `t` converge in probability to `I t`. Square energy is a lower Lebesgue
integral, so an infinite energy is never read as the default value zero of a divergent Bochner
integral. The heights need not be bounded; bounded approximants are a special case.

Against a pre-Brownian motion relative to the filtration, the predicate determines the integral
up to indistinguishability (`TauCeti.Probability.isItoIntegral_unique`). Conversely, the predicate
is invariant under indistinguishability (`TauCeti.Probability.IsItoIntegral.congr`), so it
determines its integrals exactly up to indistinguishability
(`TauCeti.Probability.isItoIntegral_iff_indist`).

The elementary integral of a simple holding is its Itô integral against every process with
almost surely continuous paths (`TauCeti.Probability.isItoIntegral_simpleGains`). Every such
integrand satisfies `LocallyBrownianIntegrable` (`IsItoIntegral.locallyBrownianIntegrable`), and
`IsItoIntegral` is closed under filtration enlargement (`IsItoIntegral.mono_filtration`),
product-a.e. replacement (`IsItoIntegral.congr_ae_prod`), linearity (`IsItoIntegral.const_mul`,
`IsItoIntegral.add`, `IsItoIntegral.sub`), sequential limits (`IsItoIntegral.of_seq`), and against
a filtered pre-Brownian motion `W`, `(s, ∞)` multiplication by `ℱ s`-measurable variables
(`IsItoIntegral.ite_lt_mul`). Against `W`, any simple holdings converging in pathwise square energy
on `(0, T]` have gains converging in probability at `v ≤ T` to `I v`
(`IsItoIntegral.tendstoInMeasure_simpleGains`, `..._of_le`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory TopologicalSpace
open Finset hiding Iic mem_Iic mem_union
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W B H K I J : ℝ≥0 → Ω → ℝ}

/-- `I` is an **Itô integral** of the integrand `H` against `W`. The integrand is predictable,
almost every path of `I` is continuous, and at every time `t` there are simple holdings with
heights known at the left endpoints of their intervals such that
`∫_(0,t] |Kₖ - H|² ds → 0` in probability while their elementary integrals at `t` converge to
`I t` in probability. The square energy is a lower Lebesgue integral, so it is infinite rather
than zero when the square error is not integrable. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W H I : ℝ≥0 → Ω → ℝ) :
    Prop where
  /-- The integrand is predictable, so its square errors are measurable in time. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- Almost every path of the integral is continuous. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous fun t ↦ I t ω
  /-- At each time `t`, simple holdings approximate the integrand on `(0,t]` in square energy
  in probability, and their elementary integrals at `t` converge to `I t` in probability. -/
  exists_approx (t : ℝ≥0) : ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
    (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
    (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-- Two sequences of predictable processes approximating the same predictable process in
square energy in probability on `(0,t]` approximate each other there. -/
private theorem tendsto_measure_le_lintegral_sub (hH : IsStronglyPredictable ℱ H)
    {K L : ℕ → ℝ≥0 → Ω → ℝ} (hK : ∀ k, IsStronglyPredictable ℱ (K k)) (t : ℝ≥0)
    (hKH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖K k s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖L k s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖K k s ω - L k s ω‖ₑ ^ 2 ∂timeMeasure t})
      atTop (𝓝 0) := by
  set η := ε / 4
  have hη : 0 < η := ENNReal.div_pos hε.ne' (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using (hKH η hη).add (hLH η hη)) (fun _ ↦ bot_le) fun k ↦ ?_
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  simp only [not_or, not_le] at hcon
  have hmeas : Measurable fun s ↦ ‖K k s ω - H s ω‖ₑ ^ 2 :=
    ((((hK k).sub hH).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2).comp
      (measurable_id.prodMk measurable_const)
  have hlt := ENNReal.add_lt_add hcon.1 hcon.2
  refine (hω.trans (lintegral_enorm_sub_sq_le_two_mul hmeas.aemeasurable)).not_gt ?_
  calc
    _ < 2 * (η + η) := by
      rw [two_mul, two_mul]
      exact ENNReal.add_lt_add hlt hlt
    _ = 4 * (ε / 4) := by ring
    _ ≤ ε := ENNReal.mul_div_le

/-- **Uniqueness of the Itô integral.** Against a pre-Brownian motion relative to the
filtration, two Itô integrals of the same integrand are indistinguishable. Neither path
continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) : I ≡ᵐ[P] J := by
  refine indist_of_forall_ae_eq hI.ae_continuous hJ.ae_continuous fun t ↦ ?_
  obtain ⟨n, τ, a, hτ, ha, hKH, hKI⟩ := hI.exists_approx t
  obtain ⟨m, σ, b, hσ, hb, hLH, hLJ⟩ := hJ.exists_approx t
  choose N ρ c _ hρ hc hhold hgain using fun k ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ k) (hσ k) (ha k) (hb k)
  -- On a common grid, the difference of the approximations has vanishing elementary integral.
  have hdiff : TendstoInMeasure P (fun k ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω -
      Finance.simpleGains (σ k) (m k) (b k) W t ω) atTop (fun _ ↦ 0) := by
    have henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (ρ k) (N k) (c k) s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0) := by
      simp_rw [hhold]
      exact tendsto_measure_le_lintegral_sub hI.isStronglyPredictable
        (fun k ↦ Finance.isStronglyPredictable_simpleHolding (ha k)) t hKH hLH
    exact (hW.tendstoInMeasure_simpleGains_of_energy (fun k ↦ (hρ k).monotoneOn) hc t
      henergy).congr_left fun k ↦ ae_of_all _ fun ω ↦ hgain k W t ω
  -- Compare almost surely convergent subsequences of the three sequences.
  obtain ⟨ns, hns, hK⟩ := hKI.exists_seq_tendsto_ae
  obtain ⟨ns', hns', hL⟩ := (hLJ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ns'', hns'', hD⟩ :=
    ((hdiff.comp hns.tendsto_atTop).comp hns'.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hK, hL, hD] with ω hKω hLω hDω
  have hsub := (hKω.comp (hns'.tendsto_atTop.comp hns''.tendsto_atTop)).sub
    (hLω.comp hns''.tendsto_atTop)
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hDω)

/-- An Itô integral may be replaced by any indistinguishable process. -/
theorem IsItoIntegral.congr (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hω hIJω
    exact hω.congr hIJω
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    exact ⟨n, τ, a, hτ, ha, hE, hG.congr_right (hIJ.ae_eq_eval t)⟩

/-- Against a pre-Brownian motion relative to the filtration, the Itô integrals of an integrand
are exactly the processes indistinguishable from one of them. -/
theorem isItoIntegral_iff_indist (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W H J ↔ I ≡ᵐ[P] J :=
  ⟨isItoIntegral_unique hW hI, hI.congr⟩

/-- The elementary integral of a simple holding with heights known at the left endpoints of its
intervals is its Itô integral against every process with almost surely continuous paths. -/
theorem isItoIntegral_simpleGains {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := by
    filter_upwards [hW] with ω hω
    exact Finance.continuous_simpleGains hω
  exists_approx t := ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha,
    fun ε hε ↦ by simp [hε.ne'], fun ε hε ↦ by simp [hε.ne']⟩

namespace IsItoIntegral

/-- Any integrand admitting an Itô integral has locally finite pathwise square energy. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat_timeMeasure.2 ⟨hI.isStronglyPredictable, fun k ↦ ?_⟩
  obtain ⟨n, τ, a, -, -, hE, -⟩ := hI.exists_approx k
  let E (m : ℕ) (ω : Ω) :=
    ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure k
  have hex : ∀ᵐ ω ∂P, ∃ m, E m ω < 1 := by
    rw [ae_iff, (by ext; simp : {ω | ¬∃ m, E m ω < 1} = ⋂ m, {ω | 1 ≤ E m ω})]
    exact le_antisymm (ge_of_tendsto' (hE 1 one_pos) fun m ↦ measure_mono (iInter_subset _ m))
      zero_le
  filter_upwards [hex] with ω ⟨m, hm⟩
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ m) (n m) (a m) s ω) 2 (timeMeasure k) := by
    simpa only [Finance.simpleHolding_def] using memLp_finsetSum _ fun j _ ↦
      (memLp_const (a m j ω)).indicator measurableSet_Ioc.nullMeasurableSet
  simpa only [Pi.sub_def, sub_sub_cancel] using hL.sub ((hL.aestronglyMeasurable.sub
    (hI.isStronglyPredictable.stronglyMeasurable_path ω).aestronglyMeasurable)
    |>.memLp_two_iff_lintegral_enorm_sq_lt_top.2 (hm.trans_le le_top))

/-- Every Itô integral against an integrator with almost-everywhere strongly measurable marginals
is almost-everywhere strongly measurable at each horizon, without assuming adaptation of `I`. -/
theorem aestronglyMeasurable (hW : ∀ s, AEStronglyMeasurable (W s) P)
    (hI : IsItoIntegral ℱ P W H I) (t : ℝ≥0) : AEStronglyMeasurable (I t) P := by
  obtain ⟨n, g, a, _, ha, _, hG⟩ := hI.exists_approx t
  refine hG.aestronglyMeasurable fun m ↦ ?_
  rw [funext (Finance.simpleGains_def (g m) (n m) (a m) W t)]
  exact Finset.aestronglyMeasurable_fun_sum _ fun j hj ↦
    ((ha m j (mem_range.1 hj)).mono (ℱ.le _)).aestronglyMeasurable.mul ((hW _).sub (hW _))

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp] theorem zero : IsItoIntegral ℱ P W 0 0 :=
  ⟨stronglyMeasurable_zero, .of_forall fun _ ↦ continuous_const, fun _ ↦
    ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0, fun _ ↦ monotoneOn_const,
      fun _ _ hj ↦ absurd hj (Nat.not_lt_zero _),
      fun _ hε ↦ by simp [Finance.simpleHolding_def, hε.ne'],
      fun _ hε ↦ by simp [Finance.simpleGains_def, hε.ne']⟩⟩

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem mono_filtration {𝒢 : Filtration ℝ≥0 mΩ} (hℱ𝒢 : ℱ ≤ 𝒢) (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral 𝒢 P W H I :=
  ⟨hI.isStronglyPredictable.mono (Filtration.predictable_mono hℱ𝒢), hI.ae_continuous, fun t ↦
    let ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    ⟨n, τ, a, hτ, fun m j hj ↦ (ha m j hj).mono (hℱ𝒢 (τ m j)), hE, hG⟩⟩

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ t, W t =ᵐ[P] B t) :
    IsItoIntegral ℱ P B H I :=
  ⟨hI.isStronglyPredictable, hI.ae_continuous, fun t ↦
    let ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    ⟨n, τ, a, hτ, ha, hE, hG.congr_left fun m ↦
      ((ae_ball_iff (Finset.countable_toSet (range (n m + 1)))).2 fun _ _ ↦ hWB _).mono fun ω hω ↦
        Finance.simpleGains_congr_price ω fun j hj ↦ hω j (mem_range.2 (Nat.lt_succ_of_le hj))⟩⟩

/-- Replacing the integrand by a predictable representative agreeing a.e. in time on a.e. path
preserves `IsItoIntegral`. -/
theorem congr_ae (hI : IsItoIntegral ℱ P W H I) (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω)) :
    IsItoIntegral ℱ P W K I :=
  ⟨hK, hI.ae_continuous, fun t ↦
    let ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
    ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hE ε hε).congr fun m ↦ measure_congr <| (hHK t).mono fun ω hω ↦
      iff_of_eq <| congrArg (ε ≤ ·) <| lintegral_congr_ae <|
        hω.mono fun s (hs : H s ω = K s ω) ↦ by rw [hs], hG⟩⟩

/-- Under an `SFinite` sample measure, replacing the integrand by a predictable representative
agreeing `(timeMeasure T).prod P`-a.e. on every finite horizon preserves `IsItoIntegral`. -/
theorem congr_ae_prod [SFinite P] (hI : IsItoIntegral ℱ P W H I) (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P W K I :=
  hI.congr_ae hK fun T ↦ Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := P) (ν := timeMeasure T))
      |>.quasiMeasurePreserving.ae_eq_comp (hHK T))

/-- For any `ℱ 0`-strongly measurable `ξ` and a.s. continuous integrator `W`,
`fun t ω ↦ ξ ω * (W t ω - W 0 ω)` is an Itô integral of `fun _ ω ↦ ξ ω`. -/
theorem const (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * (W t ω - W 0 ω)) :=
  ⟨StronglyAdapted.isStronglyPredictable_of_continuous (fun _ ↦ hξ.mono (ℱ.mono bot_le))
    fun _ ↦ continuous_const, hW.mono fun _ hω ↦ continuous_const.mul (hω.sub continuous_const),
    fun t ↦
      let τ (k : ℕ) : ℝ≥0 := if k = 0 then 0 else t
      ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ _ ↦ ξ,
        fun _ _ _ _ _ _ ↦ by dsimp [τ]; split_ifs <;> first | exact zero_le | exact le_rfl | omega,
        fun _ j hj ↦ by obtain rfl := Nat.lt_one_iff.1 hj; simpa [τ] using hξ,
        fun _ hε ↦ by
          have h0 (ω : Ω) : (∫⁻ s, ‖Finance.simpleHolding τ 1 (fun _ ↦ ξ) s ω - ξ ω‖ₑ ^ 2
              ∂timeMeasure t) = 0 := (lintegral_congr_ae
            ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by
              simp [Finance.simpleHolding_def, τ, indicator_of_mem hs])).trans lintegral_zero
          simp [h0, hε.ne'],
        fun _ hε ↦ by simp [Finance.simpleGains_def, τ, hε.ne']⟩⟩

/-- For an a.s. continuous integrator vanishing a.s. at `0`, `W` is an Itô integral of `1`. -/
theorem one (hW : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hW₀ : W 0 =ᵐ[P] 0) :
    IsItoIntegral ℱ P W 1 W :=
  (const hW (ξ := fun _ ↦ 1) stronglyMeasurable_const).congr
    (hW₀.mono fun _ hω₀ _ ↦ by simp [hω₀])

/-- Scaling an integrand scales its Itô integral. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) :=
  ⟨hI.isStronglyPredictable.const_mul c, hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω,
    fun t ↦
      let ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
      have hctop : ‖c‖ₑ ^ 2 ≠ ∞ := ENNReal.pow_ne_top eNorm_ne_top
      ⟨n, τ, fun m ↦ c • a m, hτ, fun m j hj ↦ (ha m j hj).const_smul c,
        fun _ hε ↦ (tendsto_measure_ge_zero_const_mul hctop hE hε).congr fun _ ↦ congrArg P <|
          Set.ext fun _ ↦ by simp only [mem_ofPred_eq, Finance.simpleHolding_smul, ← mul_sub,
            eNorm_mul, mul_pow, lintegral_const_mul' _ _ hctop],
        (hG.const_smul c).congr_left fun m ↦ .of_forall fun ω ↦
          (Finance.simpleGains_smul (τ m) (n m) c (a m) W t ω).symm⟩⟩

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) : IsItoIntegral ℱ P W (-H) (-I) := by
  simpa only [neg_one_mul, Pi.neg_def] using hI.const_mul (-1)

/-- Negating both the integrand and the integral process preserves `IsItoIntegral`. -/
@[simp] theorem neg_iff : IsItoIntegral ℱ P W (-H) (-I) ↔ IsItoIntegral ℱ P W H I :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

/-- The sum of two Itô integrals is an Itô integral of the sum of their integrands. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H + K) (I + J) := by
  refine ⟨hI.isStronglyPredictable.add hJ.isStronglyPredictable,
    by filter_upwards [hI.ae_continuous, hJ.ae_continuous] with _ h₁ h₂ using h₁.add h₂, fun t ↦ ?_⟩
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hG₁⟩ := hI.exists_approx t
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hJ.exists_approx t
  choose N grid height _ hgrid hgrid_le hheight _ hhold hgains using fun m ↦
    Finance.exists_simpleHolding_simpleGains_sub ℱ t (a₂ := -(a₂ m)) (hτ₁ m) (ha₁ m) (hτ₂ m)
      (fun j hj ↦ (ha₂ m j hj).neg)
  refine ⟨N, grid, height, hgrid, hheight, fun ε hε ↦
    (tendsto_measure_lintegral_enorm_sub_sq
      (f := fun m s ω ↦ Finance.simpleHolding (τ₁ m) (n₁ m) (a₁ m) s ω - H s ω)
      (g := fun m s ω ↦ K s ω - Finance.simpleHolding (τ₂ m) (n₂ m) (a₂ m) s ω)
      (h := fun _ _ _ ↦ 0)
      (.of_forall fun m ↦ .of_forall fun ω ↦ by
        simpa only [sub_zero, Pi.sub_apply] using
          (((Finance.isStronglyPredictable_simpleHolding (ha₁ m)).stronglyMeasurable_path ω).sub
            (hI.isStronglyPredictable.stronglyMeasurable_path ω)).eNorm.pow_const 2 |>.aemeasurable)
      (fun _ hδ ↦ by simpa only [sub_zero] using hE₁ _ hδ)
      (fun _ hδ ↦ by simpa only [sub_zero, eNorm_sub_rev (K _ _)] using hE₂ _ hδ) hε).congr
      fun m ↦ congrArg P <| Set.ext fun ω ↦ iff_of_eq <| congrArg (ε ≤ ·) <|
        lintegral_congr_ae <| (ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by
          rw [hhold m s hs.2 ω, Finance.simpleHolding_neg]; simp only [Pi.add_apply]; ring_nf,
    (hG₁.add hG₂).congr_left fun m ↦ .of_forall fun ω ↦ by
      rw [Finance.simpleGains_of_ge (a := height m) (hgrid m) (hgrid_le m (N m) le_rfl) W ω,
        Finance.simpleGains_apply_eq_sum (a := height m) (hgrid m) le_rfl W ω, hgains m W ω,
        Finance.simpleGains_neg, sub_neg_eq_add]⟩

/-- The difference of two Itô integrals is an Itô integral of the difference of their integrands. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-- **Sequential closure of the Itô integral.** If Itô integrals `(H_seq k, U_seq k)` approximate a
predictable `H` in pathwise square energy in probability on every finite horizon and `U_seq k t`
converges in probability to `I t` for an a.s. continuous `I`, then `I` is an Itô integral of `H`. -/
theorem of_seq {H_seq : ℕ → ℝ≥0 → Ω → ℝ} {U_seq : ℕ → ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H) (hI : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω))
    (hU : ∀ k, IsItoIntegral ℱ P W (H_seq k) (U_seq k))
    (hE : ∀ t : ℝ≥0, ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖H_seq k s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hG : ∀ t : ℝ≥0, TendstoInMeasure P (fun k ↦ U_seq k t) atTop (I t)) :
    IsItoIntegral ℱ P W H I := by
  refine ⟨hH, hI, fun t ↦ ?_⟩
  let δ (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ k
  have hδ_lim : Tendsto δ atTop (𝓝 0) := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hstep (k : ℕ) : ∃ N grid height, MonotoneOn grid (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (grid j)] (height j)) ∧
      P {ω | δ k ≤ ∫⁻ s, ‖Finance.simpleHolding grid N height s ω - H_seq k s ω‖ₑ ^ 2
        ∂timeMeasure t} ≤ δ k ∧
      P {ω | (2⁻¹ ^ k : ℝ) ≤ ‖Finance.simpleGains grid N height W t ω - U_seq k t ω‖} ≤ δ k :=
    let ⟨n, τ, a, hτ, ha, hEk, hGk⟩ := (hU k).exists_approx t
    let hδp : 0 < δ k := ENNReal.pow_pos (by simp) k
    let ⟨m, hm₁, hm₂⟩ := (((hEk (δ k) hδp).eventually (eventually_lt_nhds hδp)).and
      (((tendstoInMeasure_iff_norm.1 hGk) (2⁻¹ ^ k) (by positivity)).eventually
        (eventually_lt_nhds hδp))).exists
    ⟨n m, τ m, a m, hτ m, ha m, hm₁.le, hm₂.le⟩
  choose N grid height hgrid hheight hE_diag hG_diag using hstep
  refine ⟨N, grid, height, hgrid, hheight, fun _ hε ↦
    tendsto_measure_lintegral_enorm_sub_sq (h := H_seq)
      (.of_forall fun k ↦ .of_forall fun ω ↦
        (((Finance.isStronglyPredictable_simpleHolding (hheight k)).stronglyMeasurable_path
          ω).sub ((hU k).isStronglyPredictable.stronglyMeasurable_path ω)).eNorm.pow_const 2
          |>.aemeasurable)
      (fun _ hδ ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ_lim
        (.of_forall fun _ ↦ zero_le) ((hδ_lim.eventually (eventually_lt_nhds hδ)).mono fun k hk ↦
          (measure_mono fun _ hω ↦ hk.le.trans hω).trans (hE_diag k)))
      (fun _ hδ ↦ by simpa only [eNorm_sub_rev (H _ _)] using hE t _ hδ) hε, ?_⟩
  simpa only [sub_add_cancel, Pi.zero_apply, zero_add] using
    (tendstoInMeasure_of_tendsto_measure_rate_lt_dist
      (f := fun k ω ↦ Finance.simpleGains (grid k) (N k) (height k) W t ω - U_seq k t ω) (g := 0)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by positivity) (by norm_num))
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ_lim (fun _ ↦ zero_le)
        fun k ↦ (measure_mono fun _ hω ↦ by
          rw [mem_ofPred_eq, Pi.zero_apply, dist_zero_right] at hω; exact hω.le).trans
          (hG_diag k))).add (hG t)

/-- Against a filtered pre-Brownian motion, **every** family of left-measurable simple holdings
whose pathwise square-energy error on `(0, t]` tends to zero in probability along `l` has
elementary gains at `t` converging in probability along `l` to `I t`. -/
theorem tendstoInMeasure_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {ι : Type*} {l : Filter ι} {t : ℝ≥0}
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure t}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ↦ Finance.simpleGains (τ i) (n i) (a i) W t) l (I t) := by
  obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hG₂⟩ := hI.exists_approx t
  choose N grid height _ hgrid hgrid_le hheight _ hhold hgains using fun p : ι × ℕ ↦
    Finance.exists_simpleHolding_simpleGains_sub ℱ t (hτ p.1) (ha p.1) (hτ₂ p.2) (ha₂ p.2)
  let lp : Filter (ι × ℕ) := l ×ˢ (atTop : Filter ℕ)
  have henergy : TendstoInMeasure P
      (fun p : ι × ℕ ↦ elementaryEnergy (grid p) (height p) (N p)) lp (fun _ ↦ 0) :=
    tendstoInMeasure_iff_norm.2 fun δ hδ ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (tendsto_measure_lintegral_enorm_sub_sq (l := lp)
        (f := fun p ↦ Finance.simpleHolding (τ p.1) (n p.1) (a p.1))
        (g := fun p ↦ Finance.simpleHolding (τ₂ p.2) (n₂ p.2) (a₂ p.2)) (h := fun _ ↦ H)
        (.of_forall fun p ↦ .of_forall fun ω ↦
          (((Finance.isStronglyPredictable_simpleHolding (ha p.1)).stronglyMeasurable_path
            ω).sub (hI.isStronglyPredictable.stronglyMeasurable_path ω)).eNorm.pow_const 2
            |>.aemeasurable)
        (fun _ hε ↦ (hE _ hε).comp tendsto_fst) (fun _ hε ↦ (hE₂ _ hε).comp tendsto_snd)
        (ENNReal.ofReal_pos.2 hδ))
      (fun _ ↦ zero_le) fun p ↦ measure_mono fun ω hω ↦ by
        simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
          abs_of_nonneg (elementaryEnergy_nonneg (hgrid p) ω)] at hω ⊢
        exact (ENNReal.ofReal_le_ofReal hω).trans_eq <|
          (lintegral_enorm_sq_simpleHolding_eq_ofReal_elementaryEnergy (hgrid p)
            (hgrid_le p _ le_rfl) ω).symm.trans <|
            lintegral_congr_ae ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by
              dsimp only; rw [hhold p s hs.2 ω])
  have htot : TendstoInMeasure P
      (fun p : ι × ℕ ↦ Finance.simpleGains (τ p.1) (n p.1) (a p.1) W t) lp (I t) := by
    simpa only [sub_add_cancel, zero_add] using
      ((hW.tendstoInMeasure_sum_mul_sub_of_energy hgrid hheight henergy).congr_left
        fun p ↦ .of_forall (hgains p W)).add
        (fun ε hε ↦ (hG₂ ε hε).comp tendsto_snd : TendstoInMeasure P _ lp (I t))
  intro ε hε; rw [← Filter.map_fst_prod l (atTop : Filter ℕ), tendsto_map'_iff]; exact htot ε hε

/-- Against a filtered pre-Brownian motion, elementary holdings whose pathwise square-energy error
on `(0, T]` tends to zero in probability along `l` have gains converging in probability at every
earlier horizon `v ≤ T` to `I v`. -/
theorem tendstoInMeasure_simpleGains_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {ι : Type*} {l : Filter ι} {v T : ℝ≥0} (hv : v ≤ T)
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ i, MonotoneOn (τ i) (Iic (n i)))
    (ha : ∀ i j, j < n i → StronglyMeasurable[ℱ (τ i j)] (a i j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ i) (n i) (a i) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure T}) l (𝓝 0)) :
    TendstoInMeasure P (fun i ↦ Finance.simpleGains (τ i) (n i) (a i) W v) l (I v) :=
  hI.tendstoInMeasure_simpleGains hW hτ ha fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE ε hε) (fun _ ↦ zero_le)
      fun _ ↦ measure_mono fun _ hω ↦ hω.trans <| lintegral_mono' (by
        rw [← min_eq_left hv, ← timeMeasure_restrict]; exact Measure.restrict_le_self)
        le_rfl

/-- **Predictable `ℱ s`-multiplier rule on `(s, ∞)`.** Against a filtered pre-Brownian motion,
multiplying `H` on `(s, ∞)` by an `ℱ s`-measurable `ξ` yields the Itô integral
`t ↦ ξ * (I t - I (min s t))`, with no path continuity on `W` or moment bounds on `ξ`. -/
theorem ite_lt_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (s : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if s < t then ξ ω * H t ω else 0)
      (fun t ω ↦ ξ ω * (I t ω - I (min s t) ω)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨by
      convert hξ.isStronglyPredictable_indicator_Ioi.mul hI.isStronglyPredictable using 2 with t ω
      simp only [indicator_apply, Set.mem_Ioi]; split_ifs <;> simp,
    hI.ae_continuous.mono fun _ hc ↦
      continuous_const.mul (hc.sub (hc.comp (continuous_const.min continuous_id))), fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hE, hG⟩ := hI.exists_approx t
  let τ' (m j : ℕ) := max s (τ m j); let a' (m j : ℕ) (ω : Ω) := ξ ω * a m j ω
  have hhold (m : ℕ) (u : ℝ≥0) (ω : Ω) : Finance.simpleHolding (τ' m) (n m) (a' m) u ω =
      if s < u then ξ ω * Finance.simpleHolding (τ m) (n m) (a m) u ω else 0 := by
    rw [Finance.simpleHolding_def, Finance.simpleHolding_def]; split_ifs with hu
    · rw [mul_sum]; refine sum_congr rfl fun j _ ↦ ?_
      have hmem : u ∈ Set.Ioc (τ' m j) (τ' m (j + 1)) ↔ u ∈ Set.Ioc (τ m j) (τ m (j + 1)) := by
        simp only [τ', Set.mem_Ioc, max_lt_iff, le_max_iff, hu, true_and, hu.not_ge, false_or]
      by_cases hj : u ∈ Set.Ioc (τ m j) (τ m (j + 1)) <;> simp [hmem, hj, a']
    · exact sum_eq_zero fun j _ ↦ indicator_of_notMem
        (fun (h : u ∈ Set.Ioc _ _) ↦ hu ((le_max_left s (τ m j)).trans_lt h.1)) _
  refine ⟨n, τ', a', fun m _ hi _ hj hij ↦ max_le_max_left s (hτ m hi hj hij),
    fun m j hj ↦ (hξ.mono (ℱ.mono (le_max_left _ _))).mul
      ((ha m j hj).mono (ℱ.mono (le_max_right _ _))), fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_ge_zero_mul_of_ae_lt_top ((hξ.mono (ℱ.le s)).aemeasurable.eNorm.pow_const 2)
        (.of_forall fun _ ↦ ENNReal.pow_lt_top eNorm_lt_top) hE hε)
      (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω (hω : ε ≤ _) ↦ Set.mem_ofPred.2 <| hω.trans <| by
        rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)]
        exact lintegral_mono fun u ↦ by
          rw [hhold m u ω]; by_cases hu : s < u <;> simp [hu, ← mul_sub, eNorm_mul, mul_pow], ?_⟩
  refine ((hξ.mono (ℱ.le s)).aestronglyMeasurable.tendstoInMeasure_smul
    (hG.sub (hI.tendstoInMeasure_simpleGains_of_le hW (min_le_right s t) hτ ha hE))).congr_left
    fun m ↦ .of_forall fun ω ↦ ?_
  rw [smul_eq_mul, Finance.simpleGains_def, Finance.simpleGains_def, Finance.simpleGains_def,
    ← sum_sub_distrib, mul_sum]
  have hpt (z : ℝ≥0) : W (min (max s z) t) ω + W (min z (min s t)) ω =
      W (min z t) ω + W (min s t) ω := by
    rcases le_total z s with h | h <;>
      simp only [max_eq_left, max_eq_right, ← min_assoc, min_eq_left, min_eq_right, h, add_comm]
  refine sum_congr rfl fun j _ ↦ by
    dsimp only [a', τ']; rw [← mul_sub, mul_assoc]; congr 2
    linarith [hpt (τ m (j + 1)), hpt (τ m j)]

/-- Every Itô integral vanishes almost surely at time zero. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 :=
  let ⟨_, _, _, hτ, _, _, hG⟩ := hI.exists_approx 0
  tendstoInMeasure_ae_unique
    (hG.congr_left fun m ↦ .of_forall fun ω ↦ Finance.simpleGains_of_le (hτ m) zero_le W ω)
    fun _ hε ↦ tendsto_const_nhds.congr fun _ ↦ by simp [hε.ne']

/-- **Filtration invariance.** If `ℱ ≤ 𝒢` and `W` remains filtered pre-Brownian on `𝒢`, any Itô
integral of `H` on `ℱ` is indistinguishable from any Itô integral of `H` on `𝒢`. -/
theorem indist_of_le {𝒢 : Filtration ℝ≥0 mΩ} (hW : IsFilteredPreBrownianReal 𝒢 W P)
    (hℱ𝒢 : ℱ ≤ 𝒢) (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral 𝒢 P W H J) : I ≡ᵐ[P] J :=
  isItoIntegral_unique hW (hI.mono_filtration hℱ𝒢) hJ

/-- Two Itô integrals whose integrands agree a.e. in time on a.e. path are indistinguishable. -/
theorem indist_of_ae_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω)) :
    I ≡ᵐ[P] J :=
  isItoIntegral_unique hW (hI.congr_ae hJ.isStronglyPredictable hHK) hJ

/-- **Product-a.e. congruence.** Itô integrals of integrands agreeing `(timeMeasure T).prod P`-a.e.
on every finite horizon are indistinguishable. -/
theorem indist_of_ae_eq_prod (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    I ≡ᵐ[P] J :=
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  isItoIntegral_unique hW (hI.congr_ae_prod hJ.isStronglyPredictable hHK) hJ

end IsItoIntegral

/-- For an a.s. continuous filtered pre-Brownian motion `W`, `W` is an Itô integral of `1`. -/
theorem IsFilteredPreBrownianReal.isItoIntegral_one
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) : IsItoIntegral ℱ P W 1 W :=
  IsItoIntegral.one hcont hW.toIsPreBrownianReal.eval_zero_ae_eq_zero

end TauCeti.Probability
