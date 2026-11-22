/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Process.Indistinguishable
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Integral.Lebesgue.Norm
import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Process.Predictable.Basic
import TauCeti.Probability.Process.ContinuousAE

/-!
# Itô integrals against Brownian motion and their uniqueness

`TauCeti.Probability.IsItoIntegral ℱ P W H I` says that `I` is an Itô integral of the integrand
`H` against `W`. The integrand is predictable and the paths of `I` are almost surely continuous.
Moreover, for every time `t` some simple holdings, with heights known at the left endpoints of
their intervals, approximate `H` on `(0,t]` in square energy in probability, while their
elementary integrals at `t` converge in probability to `I t`. Square energy is a lower Lebesgue
integral, so an infinite energy is never read as the default value zero of a divergent Bochner
integral. The heights need not be bounded; bounded approximants are a special case. Every Itô
integral integrand belongs to the pathwise domain `TauCeti.LocallyBrownianIntegrable`
(`TauCeti.Probability.IsItoIntegral.locallyBrownianIntegrable`), giving one direction of the domain
characterization without extra hypotheses on `P` or `W`.

Against a pre-Brownian motion relative to the filtration, any limit in probability of the
elementary integrals of simple holdings approximating the integrand on `(0,t]` in square energy
in probability agrees almost surely with the Itô integral at `t`
(`TauCeti.Probability.IsItoIntegral.ae_eq_of_tendstoInMeasure`). Such a sequence and the one
witnessing the Itô integral are compared on one common grid. Their difference has square energy
converging to zero in probability, so its elementary integral at `t` converges to zero in
probability by the energy estimate
`TauCeti.Probability.IsFilteredPreBrownianReal.tendstoInMeasure_simpleGains_of_energy`. Hence
the predicate determines the integral up to indistinguishability
(`TauCeti.Probability.isItoIntegral_unique`), and predictable integrands that agree
`(timeMeasure T).prod P`-almost everywhere on every finite horizon have indistinguishable Itô
integrals (`TauCeti.Probability.IsFilteredPreBrownianReal.itoIntegral_local_congr`): two integrals
agree almost surely at each time, and continuity of their paths makes them indistinguishable.
Neither path continuity of `W` nor usual conditions on the filtration are needed. Conversely, the
predicate is invariant under indistinguishability (`TauCeti.Probability.IsItoIntegral.congr`), so it
determines its integrals exactly up to indistinguishability
(`TauCeti.Probability.isItoIntegral_iff_indist`).

The helper `TauCeti.Probability.tendsto_measure_le_lintegral_enorm_sq_sub` converts `L²`
convergence on `(0, t] × Ω` between two strongly predictable families into convergence in
probability of their pathwise square energies. The elementary integral of a simple holding with
heights known at the left endpoints of its intervals is its Itô integral against every process
with almost surely continuous paths (`TauCeti.Probability.isItoIntegral_simpleGains`), and
`IsItoIntegral` is closed under scaling, negation, addition, subtraction, and a.e. congruence
of the integrand or integrator. Existence of the integral for general L² and locally
square-integrable integrands is proved in `Ito/Isometry.lean`, `Ito/L2.lean`, and `Ito/Local.lean`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W B H H₁ H₂ K I I₁ I₂ J : ℝ≥0 → Ω → ℝ}

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

/-- If the difference of two strongly predictable families converges to zero in
`L²((timeMeasure t).prod P)`, then their pathwise square energies on `(0, t]` converge to zero
in `P`-measure. -/
theorem tendsto_measure_le_lintegral_enorm_sq_sub [SFinite P] {ι : Type*} {l : Filter ι}
    {K L : ι → ℝ≥0 → Ω → ℝ}
    (hK : ∀ k, IsStronglyPredictable ℱ (K k)) (hL : ∀ k, IsStronglyPredictable ℱ (L k))
    {t : ℝ≥0} (hKL : Tendsto (fun k ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ K k p.1 p.2 - L k p.1 p.2) 2 ((timeMeasure t).prod P)) l (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖K k s ω - L k s ω‖ₑ ^ 2 ∂timeMeasure t}) l (𝓝 0) :=
  TauCeti.tendsto_measure_le_lintegral_enorm_sq_of_tendsto_eLpNorm
    (fun k ↦ (((hK k).sub (hL k)).mono ℱ.predictable_le_prod).aestronglyMeasurable) hKL hε

/-- Every Itô integral integrand has finite pathwise square energy on every finite horizon almost
surely (`TauCeti.LocallyBrownianIntegrable`). Neither s-finiteness of `P` nor Brownian assumptions
on `W` are required. -/
theorem IsItoIntegral.locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun n ↦ ?_⟩
  rw [← NNReal.coe_natCast n, NNReal.comap_volume_restrict_Ioc, ← timeMeasure_def]
  obtain ⟨m, τ, a, hτ, ha, hE, _⟩ := hI.exists_approx n
  have hsub (ω : Ω) : ¬ MemLp (fun t ↦ H t ω) 2 (timeMeasure n) →
      ∀ k, 1 ≤ ∫⁻ s, ‖Finance.simpleHolding (τ k) (m k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂timeMeasure n := by
    intro hnot k
    by_contra! hlt
    apply hnot
    have hK_fin :
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (m k) (a k) s ω‖ₑ ^ 2 ∂timeMeasure n < ∞ := by
      let C := ∑ j ∈ Finset.range (m k), ‖a k j ω‖
      have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      have hle (s : ℝ≥0) : ‖Finance.simpleHolding (τ k) (m k) (a k) s ω‖ₑ ^ 2 ≤ ‖C‖ₑ ^ 2 := by
        gcongr
        rw [eNorm_le_iff_norm_le, Real.norm_of_nonneg hC]
        exact (Finance.norm_simpleHolding_le (hτ k) s ω (a := a k) fun j hj ↦
          Finset.single_le_sum (f := fun i ↦ ‖a k i ω‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_range.mpr hj)).trans_eq (max_eq_left hC)
      refine (lintegral_mono hle).trans_lt ?_
      rw [lintegral_const, timeMeasure_univ]
      finiteness
    have hpred : IsStronglyPredictable ℱ
        (fun s ω ↦ H s ω - Finance.simpleHolding (τ k) (m k) (a k) s ω) :=
      hI.isStronglyPredictable.sub (Finance.isStronglyPredictable_simpleHolding (ha k))
    have hmeas : AEMeasurable
        (fun s ↦ ‖H s ω - Finance.simpleHolding (τ k) (m k) (a k) s ω‖ₑ ^ 2) (timeMeasure n) :=
      (hpred.measurable_eNorm_pow ω 2).aemeasurable
    have hH_fin : ∫⁻ s, ‖H s ω‖ₑ ^ 2 ∂timeMeasure n < ∞ := by
      have htri := lintegral_enorm_sub_sq_le_two_mul (g := (0 : ℝ≥0 → ℝ)) hmeas
      simp only [Pi.zero_apply, sub_zero, zero_sub, eNorm_neg] at htri
      refine htri.trans_lt (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨?_, hK_fin⟩))
      simpa only [eNorm_sub_rev] using hlt.trans ENNReal.one_lt_top
    have hH_eLp : eLpNorm (fun t ↦ H t ω) 2 (timeMeasure n) < ∞ := by
      rw [← TauCeti.eLpNorm_two_sq_eq_lintegral
        (hI.isStronglyPredictable.stronglyMeasurable_section ω).aestronglyMeasurable] at hH_fin
      exact lt_of_not_ge fun htop ↦ by simp [top_le_iff.mp htop] at hH_fin
    exact hH_eLp
  rw [ae_iff]
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds (hE 1 one_pos)
      (Eventually.of_forall fun k ↦ measure_mono fun ω hω ↦ hsub ω hω k))
    zero_le

/-- **Identification of the Itô integral at a time.** Against a pre-Brownian motion relative
to the filtration, if simple holdings with heights known at the left endpoints of their
intervals approximate the integrand on `(0,t]` in square energy in probability, then every
limit in probability of their elementary integrals at `t` agrees almost surely with the Itô
integral at `t`. -/
theorem IsItoIntegral.ae_eq_of_tendstoInMeasure (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {m : ℕ → ℕ} {σ : ℕ → ℕ → ℝ≥0}
    {b : ℕ → ℕ → Ω → ℝ} {X : Ω → ℝ} (hσ : ∀ k, MonotoneOn (σ k) (Iic (m k)))
    (hb : ∀ k j, j < m k → StronglyMeasurable[ℱ (σ k j)] (b k j))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t})
        atTop (𝓝 0))
    (hLX : TendstoInMeasure P (fun k ↦ Finance.simpleGains (σ k) (m k) (b k) W t) atTop X) :
    I t =ᵐ[P] X := by
  obtain ⟨n, τ, a, hτ, ha, hKH, hKI⟩ := hI.exists_approx t
  choose N ρ c _ hρ hc hhold hgain using fun k ↦
    Finance.exists_simpleHolding_simpleGains_eq_sub ℱ (hτ k) (hσ k) (ha k) (hb k)
  -- On a common grid, the difference of the approximations has vanishing elementary integral.
  have hdiff : TendstoInMeasure P (fun k ω ↦ Finance.simpleGains (τ k) (n k) (a k) W t ω -
      Finance.simpleGains (σ k) (m k) (b k) W t ω) atTop (fun _ ↦ 0) := by
    have henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (ρ k) (N k) (c k) s ω‖ₑ ^ 2 ∂timeMeasure t})
          atTop (𝓝 0) := by
      intro ε hε
      simp_rw [hhold]
      have hpred (k : ℕ) : IsStronglyPredictable ℱ
          (fun s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω) :=
        (Finance.isStronglyPredictable_simpleHolding (ha k)).sub hI.isStronglyPredictable
      exact TauCeti.tendsto_measure_le_lintegral_enorm_sub_sq
        (Eventually.of_forall fun k ω ↦ ((hpred k).measurable_eNorm_pow ω 2).aemeasurable)
        hKH hLH hε
    exact (hW.tendstoInMeasure_simpleGains_of_energy (fun k ↦ (hρ k).monotoneOn) hc t
      henergy).congr_left fun k ↦ ae_of_all _ fun ω ↦ hgain k W t ω
  -- Compare almost surely convergent subsequences of the three sequences.
  obtain ⟨ns, hns, hK⟩ := hKI.exists_seq_tendsto_ae
  obtain ⟨ns', hns', hL⟩ := (hLX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ns'', hns'', hD⟩ :=
    ((hdiff.comp hns.tendsto_atTop).comp hns'.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hK, hL, hD] with ω hKω hLω hDω
  have hsub := (hKω.comp (hns'.tendsto_atTop.comp hns''.tendsto_atTop)).sub
    (hLω.comp hns''.tendsto_atTop)
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hDω)

/-- **Uniqueness of the Itô integral.** Against a pre-Brownian motion relative to the
filtration, two Itô integrals of the same integrand are indistinguishable. Neither path
continuity of the integrator nor usual conditions on the filtration are needed. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) : I ≡ᵐ[P] J := by
  refine indist_of_forall_ae_eq hI.ae_continuous hJ.ae_continuous fun t ↦ ?_
  obtain ⟨m, σ, b, hσ, hb, hLH, hLJ⟩ := hJ.exists_approx t
  exact hI.ae_eq_of_tendstoInMeasure hW hσ hb hLH hLJ

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

/-- The zero process is an Itô integral of the zero integrand. -/
theorem zero (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) :
    IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_zero
  ae_continuous := .of_forall fun _ ↦ continuous_const
  exists_approx _ := ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ ↦ 0,
    fun _ _ _ _ _ _ ↦ le_rfl,
    fun _ _ hj ↦ (Nat.not_lt_zero _ hj).elim,
    fun _ hε ↦ by simp [Finance.simpleHolding_def, hε.not_ge],
    fun _ hε ↦ by simp [Finance.simpleGains_def, hε.not_ge]⟩

/-- For an almost surely continuous process starting at zero almost surely, `W` itself is an Itô
integral of the constant integrand `1`. -/
theorem const_one (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) (h0 : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsItoIntegral ℱ P W (fun _ _ ↦ 1) W where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := hcont
  exists_approx t := by
    let τ : ℕ → ℝ≥0 := fun j ↦ if j = 0 then 0 else t
    let a : ℕ → Ω → ℝ := fun _ _ ↦ 1
    have hτ : MonotoneOn τ (Iic 1) := fun i hi j hj hij ↦ by
      simp only [mem_Iic] at hi hj
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [τ] at hij ⊢
    have ha : ∀ j < 1, StronglyMeasurable[ℱ (τ j)] (a j) := fun _ _ ↦ stronglyMeasurable_const
    refine ⟨fun _ ↦ 1, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha, fun ε hε ↦ ?_,
      TendstoInMeasure.congr_left (f := fun _ ↦ W t)
        (fun _ ↦ h0.mono fun ω hω ↦ by simp [Finance.simpleGains_def, τ, a, hω])
        (fun _ hε ↦ by simp [hε.not_ge])⟩
    have hzero (ω : Ω) : ∫⁻ s, ‖Finance.simpleHolding τ 1 a s ω - 1‖ₑ ^ 2 ∂timeMeasure t = 0 := by
      have hsub : IsStronglyPredictable ℱ (fun s ω ↦ Finance.simpleHolding τ 1 a s ω - 1) :=
        (Finance.isStronglyPredictable_simpleHolding ha).sub stronglyMeasurable_const
      have hmeas : Measurable fun s ↦ ‖Finance.simpleHolding τ 1 a s ω - 1‖ₑ ^ 2 :=
        hsub.measurable_eNorm_pow ω 2
      refine (lintegral_eq_zero_iff' hmeas.aemeasurable).2
        ((ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ ?_)
      simp [Finance.simpleHolding_def, τ, a, hs]
    simp [hzero, hε.not_ge]

/-- Replacing the integrand by a predictable process agreeing `(timeMeasure T).prod P`-almost
everywhere on every finite horizon preserves `IsItoIntegral`. -/
theorem congr_integrand_ae [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hE, hM⟩ := hI.exists_approx t
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[timeMeasure t] (fun s ↦ K s ω) :=
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (hHK t))
    refine ⟨n, τ, a, hτ, ha, fun ε hε ↦ (hE ε hε).congr fun m ↦ measure_congr ?_, hM⟩
    exact hsec.mono fun ω hω ↦ Iff.of_eq (congrArg (ε ≤ ·) (lintegral_congr_ae
      (hω.mono fun s hs ↦
        congrArg (fun x ↦ ‖Finance.simpleHolding (τ m) (n m) (a m) s ω - x‖ₑ ^ 2) hs)))

/-- Replacing the integrator by a process equal almost surely at each fixed time preserves
`IsItoIntegral`. -/
theorem congr_integrator_ae (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ t : ℝ≥0, W t =ᵐ[P] B t) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_approx t :=
    let ⟨n, τ, a, hτ, ha, hE, hM⟩ := hI.exists_approx t
    ⟨n, τ, a, hτ, ha, hE, hM.congr_left fun m ↦
      (ae_all_iff.mpr fun i : ℕ ↦ hWB (min (τ m i) t)).mono
        fun ω hω ↦ Finance.simpleGains_congr_price ω fun i _ ↦ hω i⟩

/-- Every Itô integral vanishes almost surely at time zero. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 :=
  let ⟨n, τ, a, _, _, _, hM⟩ := hI.exists_approx 0
  tendstoInMeasure_ae_unique hM fun _ hε ↦ by
    simp [Finance.simpleGains_def, hε.not_ge]

/-- Scaling both the integrand and the integral by a real constant preserves `IsItoIntegral`. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.const_mul c
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω
  exists_approx t := by
    rcases eq_or_ne c 0 with rfl | hc
    · obtain ⟨n, τ, a, hτ, ha, hE, hM⟩ := (zero ℱ P W).exists_approx t
      exact ⟨n, τ, a, hτ, ha,
        fun ε hε ↦ by simpa only [zero_mul, Pi.zero_apply] using hE ε hε,
        by simpa only [zero_mul, Pi.zero_def] using hM⟩
    · obtain ⟨n, τ, a, hτ, ha, hE, hM⟩ := hI.exists_approx t
      · refine ⟨n, τ, fun m ↦ c • a m, hτ, fun m j hj ↦ (ha m j hj).const_smul c,
          fun ε hε ↦ ?_, (hM.const_smul c).congr_left fun m ↦
            .of_forall fun ω ↦ (Finance.simpleGains_smul (τ m) (n m) c (a m) W t ω).symm⟩
        have hc₂_pos : 0 < ‖c‖ₑ ^ 2 := pos_iff_ne_zero.mpr (pow_ne_zero 2 (eNorm_pos.mpr hc).ne')
        have hc₂_ne_top : ‖c‖ₑ ^ 2 ≠ ∞ := by finiteness
        refine (hE (ε / ‖c‖ₑ ^ 2) (ENNReal.div_pos hε.ne' hc₂_ne_top)).congr fun m ↦ congrArg P ?_
        ext ω
        have hlint : (∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (c • a m) s ω -
            c * H s ω‖ₑ ^ 2 ∂timeMeasure t) =
            ‖c‖ₑ ^ 2 * ∫⁻ s, ‖Finance.simpleHolding (τ m) (n m) (a m) s ω -
              H s ω‖ₑ ^ 2 ∂timeMeasure t := by
          rw [← lintegral_const_mul' _ _ hc₂_ne_top]
          exact lintegral_congr fun s ↦ by
            rw [Finance.simpleHolding_smul, ← mul_sub, eNorm_mul, mul_pow]
        simp only [mem_ofPred_eq, hlint, ENNReal.div_le_iff_le_mul (.inl hc₂_pos.ne')
          (.inl hc₂_ne_top), mul_comm]

/-- Negating both the integrand and the integral preserves `IsItoIntegral`. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

/-- Adding two integrands and their Itô integrals preserves `IsItoIntegral`. -/
theorem add (h₁ : IsItoIntegral ℱ P W H₁ I₁) (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω + H₂ t ω) (fun t ω ↦ I₁ t ω + I₂ t ω) where
  isStronglyPredictable := h₁.isStronglyPredictable.add h₂.isStronglyPredictable
  ae_continuous := h₁.ae_continuous.mp (h₂.ae_continuous.mono fun _ hω₂ hω₁ ↦ hω₁.add hω₂)
  exists_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hE₁, hM₁⟩ := h₁.exists_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hE₂, hM₂⟩ := h₂.exists_approx t
    choose N ρ c _ hρ hc hhold hgain using fun k ↦
      Finance.exists_simpleHolding_simpleGains_eq_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    refine ⟨N, ρ, c, fun k ↦ (hρ k).monotoneOn, hc, fun ε hε ↦ ?_,
      (hM₁.add hM₂).congr_left fun k ↦ .of_forall fun ω ↦ (hgain k W t ω).symm⟩
    have hEq (k s ω) : ‖Finance.simpleHolding (ρ k) (N k) (c k) s ω -
          (H₁ s ω + H₂ s ω)‖ₑ =
          ‖(Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H₁ s ω) -
            (H₂ s ω - Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω)‖ₑ := by
      rw [hhold]; congr 1; ring
    simp_rw [hEq]
    have hK (k : ℕ) : IsStronglyPredictable ℱ
        (fun s ω ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H₁ s ω) :=
      (Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub h₁.isStronglyPredictable
    exact TauCeti.tendsto_measure_le_lintegral_enorm_sub_sq
      (H := (0 : ℝ≥0 → Ω → ℝ))
      (K := fun k s ω ↦ Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω - H₁ s ω)
      (L := fun k s ω ↦ H₂ s ω - Finance.simpleHolding (τ₂ k) (n₂ k) (a₂ k) s ω)
      (Eventually.of_forall fun k ω ↦ by
        simpa only [Pi.zero_apply, sub_zero] using ((hK k).measurable_eNorm_pow ω 2).aemeasurable)
      (fun δ hδ ↦ by simpa only [Pi.zero_apply, sub_zero] using hE₁ δ hδ)
      (fun δ hδ ↦ by simpa only [Pi.zero_apply, sub_zero, eNorm_sub_rev] using hE₂ δ hδ) hε

/-- Subtracting two integrands and their Itô integrals preserves `IsItoIntegral`. -/
theorem sub (h₁ : IsItoIntegral ℱ P W H₁ I₁) (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω - H₂ t ω) (fun t ω ↦ I₁ t ω - I₂ t ω) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

end IsItoIntegral

/-- Representative independence of the Brownian Itô integral: Itô integrals of predictable
integrands that agree `(timeMeasure T).prod P`-almost everywhere on every finite horizon are
indistinguishable. Neither local square integrability nor Brownian path continuity is required. -/
theorem IsFilteredPreBrownianReal.itoIntegral_local_congr
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    I ≡ᵐ[P] J := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact isItoIntegral_unique hW (hI.congr_integrand_ae hJ.isStronglyPredictable hHK) hJ

end TauCeti.Probability
