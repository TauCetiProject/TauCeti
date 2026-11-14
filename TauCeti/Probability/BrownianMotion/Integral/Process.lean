/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.Probability.BrownianMotion.Integral.Square
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.StochasticInterval
import TauCeti.Probability.Process.TimeIntegral

/-!
# The predictable L² Brownian integral process

For a filtration-relative Brownian motion `W` and an integrand `H` in
`TauCeti.BrownianIntegrable ℱ P H`, the finite-horizon terminal maps
`IsFilteredPreBrownianReal.l2Integral` assemble into a time-indexed stochastic integral process.

First, `coeFn_l2Integral_simpleHolding` identifies `l2Integral` on any finite-grid elementary
holding with its Brownian gain `Finance.simpleGains`, yielding the exact `L²` norm identity
`eLpNorm_simpleGains_sub_l2Integral`. Together with predictable rectangle restriction
(`coeFn_l2Integral_indicator_Ioc_prod`), this connects horizon truncation and `ℱ_u`-event
multiplication.

Second, any adapted modification `I` of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` is a
centered `L²` martingale satisfying the Itô isometry `integral_sq_of_ae_eq_l2Integral`, the
cross-isometry `integral_mul_of_ae_eq_l2Integral`, and the square-compensation martingale
property `martingale_sq_sub_integral_of_ae_eq_l2Integral`. Optional stopping at raw stopping times
is established in `TauCeti.Probability.BrownianMotion.Integral.Stopping`.

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

namespace TauCeti.BrownianIntegrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {H K : ℝ≥0 → Ω → ℝ}

/-- The zero process belongs to the expected-square-energy integrand domain. -/
theorem zero : BrownianIntegrable ℱ P (0 : ℝ≥0 → Ω → ℝ) :=
  ⟨stronglyMeasurable_const, fun _ ↦ .zero⟩

/-- Negation preserves finite expected square energy. -/
theorem neg (h : BrownianIntegrable ℱ P H) : BrownianIntegrable ℱ P (fun t ω ↦ -H t ω) := by
  simpa only [neg_one_mul] using h.const_mul (-1)

/-- Subtraction preserves finite expected square energy. -/
theorem sub (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K) :
    BrownianIntegrable ℱ P (fun t ω ↦ H t ω - K t ω) := by
  simpa only [sub_eq_add_neg] using hH.add hK.neg

/-- Stopping an expected-square-integrable predictable integrand at a raw stopping time
preserves `BrownianIntegrable`. -/
theorem ite_le (hH : BrownianIntegrable ℱ P H) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) :
    BrownianIntegrable ℱ P (fun t : ℝ≥0 ↦ fun ω ↦
      if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) := by
  refine ⟨hH.isStronglyPredictable.ite_le hτ, fun T ↦ ?_⟩
  have hS : MeasurableSet {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) ≤ τ p.2} :=
    ℱ.predictable_le_prod _ hτ.measurableSet_predictable_ge
  have hfun : Function.uncurry (fun t : ℝ≥0 ↦ fun ω ↦
      if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0) =
      {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator (Function.uncurry H) := by
    ext ⟨t, ω⟩
    simp only [Function.uncurry_apply_pair, indicator_apply, mem_ofPred_eq]
  rw [hfun]
  exact (hH.memLp T).indicator hS.nullMeasurableSet

/-- Restricting an expected-square-integrable predictable integrand to a predictable rectangle
`(u, v] × E` preserves `BrownianIntegrable`. -/
theorem indicator_Ioc_prod (hH : BrownianIntegrable ℱ P H) (u v : ℝ≥0)
    {E : Set Ω} (hE : MeasurableSet[ℱ u] E) :
    BrownianIntegrable ℱ P (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ E.indicator (H t) ω) t) := by
  have hfun : Function.uncurry (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ E.indicator (H t) ω) t) =
      (Ioc u v ×ˢ E).indicator (Function.uncurry H) := by
    ext ⟨t, ω⟩
    by_cases ht : t ∈ Ioc u v <;> by_cases hω : ω ∈ E <;> simp [ht, hω]
  have hp : IsStronglyPredictable ℱ
      (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ E.indicator (H t) ω) t) := by
    rw [IsStronglyPredictable, hfun]
    exact hH.isStronglyPredictable.indicator (measurableSet_predictable_Ioc_prod u v hE)
  refine ⟨hp, fun T ↦ ?_⟩
  rw [hfun]
  exact (hH.memLp T).indicator (measurableSet_Ioc.prod (ℱ.le u E hE)).nullMeasurableSet

/-- Finite-horizon expected square energy written against `Probability.timeMeasure`. -/
theorem memLp_timeMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P) := by
  simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using hH.memLp T

/-- Finite-horizon membership in the trimmed predictable `L²` space. -/
theorem memLp_predictableMeasure (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    MemLp (Function.uncurry H) 2 (ℱ.predictableMeasure P T) :=
  (ℱ.memLp_predictableMeasure_iff P hH.isStronglyPredictable T 2).mpr (hH.memLp_timeMeasure T)

/-- The finite-horizon predictable `L²` class of a `BrownianIntegrable` process. -/
def toPredictableLp (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    Lp ℝ 2 (ℱ.predictableMeasure P T) :=
  (hH.memLp_predictableMeasure T).toLp (Function.uncurry H)

/-- Almost-everywhere representative of `toPredictableLp` under the predictable measure. -/
theorem coeFn_toPredictableLp (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    hH.toPredictableLp T =ᵐ[ℱ.predictableMeasure P T] Function.uncurry H :=
  (hH.memLp_predictableMeasure T).coeFn_toLp

/-- Almost-everywhere representative of `toPredictableLp` under the ambient product measure. -/
theorem coeFn_toPredictableLp_prod (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    (hH.toPredictableLp T : ℝ≥0 × Ω → ℝ) =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry H := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  exact (ℱ.ae_eq_predictableMeasure_iff P (Lp.stronglyMeasurable _).measurable
    hH.isStronglyPredictable.measurable T).mp (hH.coeFn_toPredictableLp T)

/-- Embedding the zero integrand into `Lp ℝ 2 (ℱ.predictableMeasure P T)` yields `0`. -/
@[simp]
theorem toPredictableLp_zero (T : ℝ≥0) :
    (zero : BrownianIntegrable ℱ P 0).toPredictableLp T = 0 := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  apply Lp.ext
  filter_upwards [(zero (ℱ := ℱ) (P := P)).coeFn_toPredictableLp T,
    Lp.coeFn_zero ℝ 2 (ℱ.predictableMeasure P T)] with ⟨t, ω⟩ hp h0
  rw [hp, h0]
  rfl

/-- `BrownianIntegrable.toPredictableLp` commutes with pointwise addition of integrands. -/
theorem toPredictableLp_add (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (T : ℝ≥0) :
    (hH.add hK).toPredictableLp T = hH.toPredictableLp T + hK.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  apply Lp.ext
  filter_upwards [(hH.add hK).coeFn_toPredictableLp T, hH.coeFn_toPredictableLp T,
    hK.coeFn_toPredictableLp T,
    Lp.coeFn_add (hH.toPredictableLp T) (hK.toPredictableLp T)] with ⟨t, ω⟩ hp h1 h2 hadd
  rw [hp, hadd, Pi.add_apply, h1, h2]
  rfl

/-- `BrownianIntegrable.toPredictableLp` commutes with multiplication by a real constant. -/
theorem toPredictableLp_const_mul (hH : BrownianIntegrable ℱ P H) (c : ℝ) (T : ℝ≥0) :
    (hH.const_mul c).toPredictableLp T = c • hH.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  apply Lp.ext
  filter_upwards [(hH.const_mul c).coeFn_toPredictableLp T, hH.coeFn_toPredictableLp T,
    Lp.coeFn_smul c (hH.toPredictableLp T)] with ⟨t, ω⟩ hp h1 hsmul
  rw [hp, hsmul, Pi.smul_apply, h1, smul_eq_mul]
  rfl

/-- Two `BrownianIntegrable` integrands that agree almost everywhere under `(timeMeasure T).prod P`
have equal predictable `L²` embeddings on `[0, T]`. -/
theorem toPredictableLp_congr (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    {T : ℝ≥0}
    (hHK : Function.uncurry H =ᵐ[(Probability.timeMeasure T).prod P] Function.uncurry K) :
    hH.toPredictableLp T = hK.toPredictableLp T := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  apply Lp.ext
  have htrim := (ℱ.ae_eq_predictableMeasure_iff P hH.isStronglyPredictable.measurable
    hK.isStronglyPredictable.measurable T).mpr hHK
  exact (hH.coeFn_toPredictableLp T).trans (htrim.trans (hK.coeFn_toPredictableLp T).symm)

/-- A finite-grid elementary holding with square-integrable left-measurable heights belongs to
`BrownianIntegrable`. -/
theorem simpleHolding [SFinite P] {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    BrownianIntegrable ℱ P (Finance.simpleHolding τ n a) :=
  ⟨Finance.isStronglyPredictable_simpleHolding ha, fun T ↦ by
    simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def] using
      (ℱ.memLp_predictableMeasure_iff P (Finance.isStronglyPredictable_simpleHolding ha) T 2).mp
        (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T)⟩

end TauCeti.BrownianIntegrable

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

private theorem stronglyMeasurable_predictable_indicator_Ioc (s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    StronglyMeasurable[ℱ.predictable]
      ((Ioc s u ×ˢ (univ : Set Ω)).indicator fun p ↦ ξ p.2) := by
  have hp := Finance.isStronglyPredictable_simpleHolding (ℱ := ℱ)
    (τ := fun i ↦ if i = 0 then s else u) (n := 1) (a := fun _ ↦ ξ)
    (fun i hi ↦ by obtain rfl : i = 0 := Nat.lt_one_iff.mp hi; simpa using hξ)
  have heq : Function.uncurry (Finance.simpleHolding (fun i ↦ if i = 0 then s else u) 1
      (fun _ ↦ ξ)) = (Ioc s u ×ˢ (univ : Set Ω)).indicator fun p ↦ ξ p.2 := by
    ext ⟨t, ω⟩
    simp only [Function.uncurry_apply_pair, Finance.simpleHolding_def, range_one, sum_singleton]
    by_cases ht : t ∈ Ioc s u <;> simp [ht]
  exact heq ▸ hp

/-- An `ℱ s`-measurable `L²` height held on `(s, u]` belongs to predictable `L²` on `(0, T]`. -/
theorem memLp_indicator_Ioc_predictableMeasure [SFinite P] (T s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    MemLp ((Ioc s u ×ˢ (univ : Set Ω)).indicator fun p ↦ ξ p.2) 2 (ℱ.predictableMeasure P T) := by
  rw [ℱ.memLp_predictableMeasure_iff P (stronglyMeasurable_predictable_indicator_Ioc s u hξ) T 2]
  exact (hξ₂.comp_snd (timeMeasure T)).indicator
    (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet

private theorem innerSL_comp_l2Integral_indicator_Ioc [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownianReal ℱ W P) (T s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    (innerSL ℝ ((hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).toLp
        (fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω)))).comp
      (hW.l2Integral T).toContinuousLinearMap =
      innerSL ℝ ((memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).toLp _) := by
  apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
  intro a b hab hbT A hA
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    innerSL_apply_apply]
  rw [L2.inner_def]
  have hi := integral_congr_ae
    ((hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hab.le hbT hA 1).mul
      (hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).coeFn_toLp)
  simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply] at hi ⊢
  rw [hi, hW.integral_mul_sub_mul_mul_sub hab.le (le_max_left s (min u T))
    (stronglyMeasurable_const.indicator hA) hξ
    ((memLp_const (1 : ℝ)).indicator (ℱ.le a A hA).nullMeasurableSet) hξ₂]
  rw [real_inner_comm, L2.inner_indicatorConstLp_one]
  have hrect_int : ∫ x in Ioc a b ×ˢ A,
      ((memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).toLp _) x
        ∂ℱ.predictableMeasure P T =
      ∫ p, ((Ioc a b ×ˢ A).indicator
        ((Ioc s u ×ˢ (univ : Set Ω)).indicator fun q ↦ ξ q.2)) p
        ∂(timeMeasure T).prod P := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    rw [setIntegral_congr_ae (measurableSet_predictable_Ioc_prod a b hA)
        ((memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).coeFn_toLp.mono fun _ h _ ↦ h),
      ← integral_indicator (measurableSet_predictable_Ioc_prod a b hA)]
    exact ℱ.integral_predictableMeasure P
      ((stronglyMeasurable_predictable_indicator_Ioc s u hξ).indicator
        (measurableSet_predictable_Ioc_prod a b hA)) T
  rw [hrect_int]
  have hprod_eq : ((Ioc a b ×ˢ A).indicator
      ((Ioc s u ×ˢ (univ : Set Ω)).indicator fun p ↦ ξ p.2)) =
      fun p : ℝ≥0 × Ω ↦ (Ioc (max a s) (min b u)).indicator (fun _ ↦ (1 : ℝ)) p.1 *
        (A.indicator (fun _ ↦ (1 : ℝ)) p.2 * ξ p.2) := by
    ext ⟨t, ω⟩
    rw [← Set.Ioc_inter_Ioc]
    by_cases ht₁ : t ∈ Ioc a b <;> by_cases ht₂ : t ∈ Ioc s u <;> by_cases hω : ω ∈ A <;>
      simp [ht₁, ht₂, hω]
  rw [hprod_eq, integral_prod_mul (L := ℝ)
      (fun x : ℝ≥0 ↦ (Ioc (max a s) (min b u)).indicator (fun _ ↦ (1 : ℝ)) x)
      (fun y : Ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) y * ξ y),
    integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
    mul_one, measureReal_def, timeMeasure_Ioc, ENNReal.toReal_ofReal', mul_comm]
  congr 1
  simp only [NNReal.coe_sub_def, NNReal.coe_min, NNReal.coe_max]
  have : (b : ℝ) ≤ T := by exact_mod_cast hbT
  grind only [min_def, max_def]

private theorem norm_sq_indicator_Ioc_predictableMeasure [IsProbabilityMeasure P]
    (hW : IsFilteredPreBrownianReal ℱ W P) (T s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    ‖(hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).toLp
      (fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω))‖ ^ 2 =
      ‖(memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).toLp _‖ ^ 2 := by
  let rLp := (memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).toLp _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi₁ := integral_congr_ae
    ((hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).coeFn_toLp.mul
      (hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).coeFn_toLp)
  simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply, ← sq] at hi₁ ⊢
  rw [hi₁, hW.integral_sq_mul_sub (le_max_left s (min u T)) hξ,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi₂ : ∫ a, rLp a ^ 2 ∂ℱ.predictableMeasure P T =
      ∫ p, ((Ioc s u ×ˢ (univ : Set Ω)).indicator (fun q ↦ ξ q.2) p) ^ 2
        ∂(timeMeasure T).prod P := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    have hcongr := integral_congr_ae
      ((memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).coeFn_toLp.mul
        (memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).coeFn_toLp)
    simp only [Pi.mul_apply, ← sq] at hcongr
    exact hcongr.trans (ℱ.integral_predictableMeasure P
      ((stronglyMeasurable_predictable_indicator_Ioc s u hξ).pow 2) T)
  simp only [RCLike.inner_apply, conj_trivial, ← sq]
  have hsq_eq : (fun p : ℝ≥0 × Ω ↦
      ((Ioc s u ×ˢ (univ : Set Ω)).indicator (fun q ↦ ξ q.2) p) ^ 2) =
      fun p : ℝ≥0 × Ω ↦ (Ioc s u).indicator (fun _ ↦ (1 : ℝ)) p.1 * (ξ p.2 ^ 2) := by
    ext ⟨t, ω⟩; by_cases ht : t ∈ Ioc s u <;> simp [ht]
  rw [hi₂, hsq_eq, integral_prod_mul (L := ℝ)
      (fun x : ℝ≥0 ↦ (Ioc s u).indicator (fun _ ↦ (1 : ℝ)) x) (fun y : Ω ↦ ξ y ^ 2),
    integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
    mul_one, measureReal_def, timeMeasure_Ioc, ENNReal.toReal_ofReal', mul_comm]
  congr 1
  simp only [NNReal.coe_min, NNReal.coe_max]
  grind only [min_def, max_def]

/-- On a single time interval `(s, u]`, the predictable `L²` integral of an `ℱ s`-measurable
square-integrable height multiplies that height by the horizon-clipped Brownian increment. -/
theorem coeFn_l2Integral_indicator_Ioc
    (hW : IsFilteredPreBrownianReal ℱ W P) (T s u : ℝ≥0)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).toLp _) =ᵐ[P]
      fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let rLp := (memLp_indicator_Ioc_predictableMeasure T s u hξ hξ₂).toLp _
  let uLp := hW.l2Integral T rLp
  let vLp := (hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).toLp
    (fun ω ↦ ξ ω * (W (max s (min u T)) ω - W s ω))
  have huv_inner : ⟪uLp, vLp⟫_ℝ = ‖rLp‖ ^ 2 := by
    rw [real_inner_comm]
    have h := congrArg (fun L : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] ℝ ↦ L rLp)
      (hW.innerSL_comp_l2Integral_indicator_Ioc T s u hξ hξ₂)
    dsimp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      innerSL_apply_apply] at h
    exact h.trans (real_inner_self_eq_norm_sq rLp)
  have hsub_zero : uLp = vLp := by
    have hsq : ‖uLp - vLp‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, (hW.l2Integral T).norm_map, huv_inner,
        hW.norm_sq_indicator_Ioc_predictableMeasure T s u hξ hξ₂]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  change (uLp : Ω → ℝ) =ᵐ[P] _
  rw [hsub_zero]
  exact (hW.memLp_mul_sub (le_max_left s (min u T)) hξ hξ₂).coeFn_toLp

/-- On any nondecreasing finite grid, `l2Integral` of `Finance.simpleHolding` equals
`Finance.simpleGains` almost everywhere. -/
theorem coeFn_l2Integral_simpleHolding
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
      (Function.uncurry (Finance.simpleHolding τ n a))) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  induction n with
  | zero =>
    have hz : (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
        (Function.uncurry (Finance.simpleHolding τ 0 a)) = 0 := by
      apply Lp.ext
      filter_upwards [(Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp,
        Lp.coeFn_zero ℝ 2 (ℱ.predictableMeasure P T)] with ⟨t, ω⟩ hp h0
      rw [hp, h0]; simp [Finance.simpleHolding_def]
    rw [hz, map_zero]
    exact (Lp.coeFn_zero ℝ 2 P).mono fun ω h0 ↦ by rw [h0]; simp [Finance.simpleGains_def]
  | succ n ih =>
    have han (i : ℕ) (hi : i < n) := ha i (hi.trans n.lt_succ_self)
    have han₂ (i : ℕ) (hi : i < n) := ha₂ i (hi.trans n.lt_succ_self)
    have hstep : τ n ≤ τ (n + 1) := hτ (mem_Iic.mpr n.le_succ) (mem_Iic.mpr le_rfl) n.le_succ
    let fPrev := (Finance.memLp_simpleHolding_predictableMeasure han han₂ T).toLp
      (Function.uncurry (Finance.simpleHolding τ n a))
    let fLast := (memLp_indicator_Ioc_predictableMeasure T (τ n) (τ (n + 1))
      (ha n n.lt_succ_self) (ha₂ n n.lt_succ_self)).toLp _
    have hsplit : (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
        (Function.uncurry (Finance.simpleHolding τ (n + 1) a)) = fPrev + fLast := by
      apply Lp.ext
      filter_upwards [(Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp,
        Lp.coeFn_add fPrev fLast,
        (Finance.memLp_simpleHolding_predictableMeasure han han₂ T).coeFn_toLp,
        (memLp_indicator_Ioc_predictableMeasure T (τ n) (τ (n + 1))
          (ha n n.lt_succ_self) (ha₂ n n.lt_succ_self)).coeFn_toLp] with ⟨t, ω⟩ hp hadd hp₁ hp₂
      rw [hp, hadd, Pi.add_apply, hp₁, hp₂]
      by_cases ht : t ∈ Ioc (τ n) (τ (n + 1)) <;>
        simp [ht, Finance.simpleHolding_def, sum_range_succ]
    rw [hsplit, map_add]
    filter_upwards [Lp.coeFn_add (hW.l2Integral T fPrev) (hW.l2Integral T fLast),
      ih (hτ.mono (Iic_subset_Iic.mpr n.le_succ)) han han₂,
      hW.coeFn_l2Integral_indicator_Ioc T (τ n) (τ (n + 1))
        (ha n n.lt_succ_self) (ha₂ n n.lt_succ_self)] with ω hadd hprev hlast
    rw [hadd, Pi.add_apply, hprev, hlast]
    simp only [Finance.simpleGains_def, sum_range_succ]
    suffices W (max (τ n) (min (τ (n + 1)) T)) ω - W (τ n) ω =
        W (min (τ (n + 1)) T) ω - W (min (τ n) T) ω by rw [this]
    by_cases hnT : τ n ≤ T
    · rw [min_eq_left hnT, max_eq_right (le_min hstep hnT)]
    · have hTn : T ≤ τ n := (not_le.mp hnT).le
      rw [min_eq_right hTn, min_eq_right (hTn.trans hstep), max_eq_left hTn, sub_self, sub_self]

/-- For a `BrownianIntegrable` process and any square-integrable elementary holding on a
nondecreasing grid, the sample-space `L²` distance between `Finance.simpleGains` and `l2Integral`
equals the ambient time-product `L²` distance between `Finance.simpleHolding` and `H`. -/
theorem eLpNorm_simpleGains_sub_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω -
        hW.l2Integral T (hH.toPredictableLp T) ω) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let gLp := (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
    (Function.uncurry (Finance.simpleHolding τ n a))
  have hlhs : eLpNorm (fun ω ↦ Finance.simpleGains τ n a W T ω -
        hW.l2Integral T (hH.toPredictableLp T) ω) 2 P =
      edist (hW.l2Integral T gLp) (hW.l2Integral T (hH.toPredictableLp T)) := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hW.coeFn_l2Integral_simpleHolding hτ ha ha₂ T).symm.sub .rfl)
  have hrhs : edist gLp (hH.toPredictableLp T) =
      eLpNorm (fun p ↦ Finance.simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P) := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    have hsm : StronglyMeasurable[ℱ.predictable]
        (Function.uncurry (Finance.simpleHolding τ n a) - Function.uncurry H) :=
      (Finance.isStronglyPredictable_simpleHolding ha).sub hH.isStronglyPredictable
    rw [Lp.edist_def, eLpNorm_congr_ae
      (((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).coeFn_toLp).sub
        (hH.coeFn_toPredictableLp T)),
      ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hsm]
    rfl
  rw [hlhs, (hW.l2Integral T).edist_map, hrhs]

/-- Cross-isometry of the finite-horizon predictable `L²` Brownian integral on
`BrownianIntegrable` processes. -/
theorem integral_mul_l2Integral_toPredictableLp
    (hW : IsFilteredPreBrownianReal ℱ W P)
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
    rw [real_inner_comm, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
  have hrhs : ⟪hH.toPredictableLp T, hK.toPredictableLp T⟫_ℝ =
      ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    rw [real_inner_comm, L2.inner_def]
    have hc := integral_congr_ae ((hH.coeFn_toPredictableLp T).mul (hK.coeFn_toPredictableLp T))
    simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply] at hc ⊢
    have hsm : StronglyMeasurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 * K p.1 p.2) :=
      hH.isStronglyPredictable.mul hK.isStronglyPredictable
    exact hc.trans (ℱ.integral_predictableMeasure P hsm T)
  exact hlhs.symm.trans (hiso.trans hrhs)

/-- Itô isometry of the finite-horizon predictable `L²` Brownian integral on a
`BrownianIntegrable` process. -/
theorem integral_sq_l2Integral_toPredictableLp
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (T : ℝ≥0) :
    ∫ ω, hW.l2Integral T (hH.toPredictableLp T) ω ^ 2 ∂P =
      ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P := by
  simpa only [sq] using hW.integral_mul_l2Integral_toPredictableLp hH hH T

private theorem sub_max_min_eq_sub_sub_of_le {a b u v T : ℝ≥0}
    (hab : a ≤ b) (huv : u ≤ v) (hvT : v ≤ T) (f : ℝ≥0 → ℝ) :
    f (max (max a u) (min (min b v) T)) - f (max a u) =
      (f (min b v) - f (min a v)) - (f (min b u) - f (min a u)) := by
  rw [min_assoc, min_eq_left hvT]
  by_cases hbu : b ≤ u
  · rw [max_eq_right (hab.trans hbu), min_eq_left (hbu.trans huv), max_eq_left hbu,
      min_eq_left (hab.trans (hbu.trans huv)), min_eq_left hbu, min_eq_left (hab.trans hbu)]
    ring
  · by_cases hva : v ≤ a
    · rw [max_eq_left (huv.trans hva), min_eq_right (hva.trans hab), max_eq_left hva,
        min_eq_right hva, min_eq_right (huv.trans (hva.trans hab)), min_eq_right (huv.trans hva)]
      ring
    · have hub : u ≤ b := (not_le.mp hbu).le
      have hav : a ≤ v := (not_le.mp hva).le
      rw [max_eq_right (max_le (le_min hab hav) (le_min hub huv)), min_eq_left hav,
        min_eq_right hub]
      by_cases hau : a ≤ u
      · rw [max_eq_right hau, min_eq_left hau]; ring
      · rw [max_eq_left (not_le.mp hau).le, min_eq_right (not_le.mp hau).le]; ring

private theorem coeFn_l2Integral_indicator_Ioc_prod_simpleHolding
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {u v T : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) {E : Set Ω} (hE : MeasurableSet[ℱ u] E)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (((BrownianIntegrable.simpleHolding ha ha₂).indicator_Ioc_prod u v
        hE).toPredictableLp T) =ᵐ[P]
      E.indicator (fun ω ↦ Finance.simpleGains τ n a W v ω - Finance.simpleGains τ n a W u ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  induction n with
  | zero =>
    let hS := BrownianIntegrable.simpleHolding ha ha₂
    rw [show (hS.indicator_Ioc_prod u v hE).toPredictableLp T = 0 by
      let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
      exact Lp.ext_iff.mpr (((hS.indicator_Ioc_prod u v hE).coeFn_toPredictableLp T).trans
        ((Lp.coeFn_zero ℝ 2 (ℱ.predictableMeasure P T)).mono fun ⟨t, ω⟩ h0 ↦ by
          rw [h0]; simp [Finance.simpleHolding_def])), map_zero]
    exact (Lp.coeFn_zero ℝ 2 P).mono fun ω h0 ↦ by rw [h0]; simp [Finance.simpleGains_def]
  | succ n ih =>
    have han (i : ℕ) (hi : i < n) := ha i (hi.trans n.lt_succ_self)
    have han₂ (i : ℕ) (hi : i < n) := ha₂ i (hi.trans n.lt_succ_self)
    have hstep : τ n ≤ τ (n + 1) := hτ (mem_Iic.mpr n.le_succ) (mem_Iic.mpr le_rfl) n.le_succ
    let hS := BrownianIntegrable.simpleHolding ha ha₂
    let hSn := BrownianIntegrable.simpleHolding han han₂
    have hξm : StronglyMeasurable[ℱ (max (τ n) u)] (E.indicator (a n)) :=
      ((ha n n.lt_succ_self).mono (ℱ.mono (le_max_left _ _))).indicator
        (ℱ.mono (le_max_right _ _) E hE)
    have hξ₂ : MemLp (E.indicator (a n)) 2 P :=
      (ha₂ n n.lt_succ_self).indicator (ℱ.le u E hE).nullMeasurableSet
    let fPrev := (hSn.indicator_Ioc_prod u v hE).toPredictableLp T
    let fLast := (memLp_indicator_Ioc_predictableMeasure T (max (τ n) u) (min (τ (n + 1)) v)
      hξm hξ₂).toLp _
    have hsplit : (hS.indicator_Ioc_prod u v hE).toPredictableLp T = fPrev + fLast := by
      let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
      apply Lp.ext
      filter_upwards [(hS.indicator_Ioc_prod u v hE).coeFn_toPredictableLp T,
        Lp.coeFn_add fPrev fLast, (hSn.indicator_Ioc_prod u v hE).coeFn_toPredictableLp T,
        (memLp_indicator_Ioc_predictableMeasure T (max (τ n) u) (min (τ (n + 1)) v)
          hξm hξ₂).coeFn_toLp] with ⟨t, ω⟩ hp hadd hp₁ hp₂
      rw [hp, hadd, Pi.add_apply, hp₁, hp₂]
      simp only [Function.uncurry_apply_pair, ← Set.Ioc_inter_Ioc]
      by_cases ht : t ∈ Ioc u v <;> by_cases htn : t ∈ Ioc (τ n) (τ (n + 1)) <;>
        by_cases hω : ω ∈ E <;> simp [ht, htn, hω, Finance.simpleHolding_def, sum_range_succ]
    rw [hsplit, map_add]
    filter_upwards [Lp.coeFn_add (hW.l2Integral T fPrev) (hW.l2Integral T fLast),
      ih (hτ.mono (Iic_subset_Iic.mpr n.le_succ)) han han₂,
      hW.coeFn_l2Integral_indicator_Ioc T (max (τ n) u) (min (τ (n + 1)) v) hξm hξ₂]
      with ω hadd hprev hlast
    rw [hadd, Pi.add_apply, hprev, hlast]
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω, Finance.simpleGains_def, sum_range_succ,
        sub_max_min_eq_sub_sub_of_le hstep huv hvT (W · ω)]
      ring
    · simp [hω]

private theorem edist_indicator_Ioc_prod_toPredictableLp_le
    {H K : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (u v T : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[ℱ u] E) :
    edist ((hH.indicator_Ioc_prod u v hE).toPredictableLp T)
        ((hK.indicator_Ioc_prod u v hE).toPredictableLp T) ≤
      eLpNorm (fun p ↦ H p.1 p.2 - K p.1 p.2) 2 ((timeMeasure T).prod P) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hsm_ind : StronglyMeasurable[ℱ.predictable]
      (Function.uncurry (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ E.indicator (H t) ω) t) -
        Function.uncurry (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ E.indicator (K t) ω) t)) :=
    (hH.indicator_Ioc_prod u v hE).isStronglyPredictable.sub
      (hK.indicator_Ioc_prod u v hE).isStronglyPredictable
  rw [Lp.edist_def, eLpNorm_congr_ae
    (((hH.indicator_Ioc_prod u v hE).coeFn_toPredictableLp T).sub
      ((hK.indicator_Ioc_prod u v hE).coeFn_toPredictableLp T)),
    ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hsm_ind]
  exact eLpNorm_mono_eNorm (hsm_ind.mono ℱ.predictable_le_prod).aestronglyMeasurable
    fun ⟨t, ω⟩ ↦ by by_cases ht : t ∈ Ioc u v <;> by_cases hω : ω ∈ E <;> simp [ht, hω]

private theorem eLpNorm_l2Integral_indicator_Ioc_prod_sub_le
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {u v T : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) {E : Set Ω} (hE : MeasurableSet[ℱ u] E)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    eLpNorm ((hW.l2Integral T ((hH.indicator_Ioc_prod u v hE).toPredictableLp T) : Ω → ℝ) -
        E.indicator (fun ω ↦ hW.l2Integral v (hH.toPredictableLp v) ω -
          hW.l2Integral u (hH.toPredictableLp u) ω)) 2 P ≤ ε := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let lhs : Ω → ℝ := hW.l2Integral T ((hH.indicator_Ioc_prod u v hE).toPredictableLp T)
  let rhs : Ω → ℝ := E.indicator (fun ω ↦ hW.l2Integral v (hH.toPredictableLp v) ω -
    hW.l2Integral u (hH.toPredictableLp u) ω)
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ :=
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P T hH.isStronglyPredictable
      (hH.memLp_timeMeasure T) (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ∞))
  have ha₂ (j : ℕ) (hj : j < n) : MemLp (a j) 2 P :=
    MemLp.of_bound ((ha j hj).mono (ℱ.le _)).aestronglyMeasurable C (Eventually.of_forall (hb j hj))
  let hS := BrownianIntegrable.simpleHolding ha ha₂
  let mid : Ω → ℝ := E.indicator (fun ω ↦
    Finance.simpleGains τ n a W v ω - Finance.simpleGains τ n a W u ω)
  have herr_lhs : eLpNorm (lhs - mid) 2 P ≤ ε / 3 := by
    rw [show eLpNorm (lhs - mid) 2 P = edist ((hH.indicator_Ioc_prod u v hE).toPredictableLp T)
      ((hS.indicator_Ioc_prod u v hE).toPredictableLp T) by
        rw [← (hW.l2Integral T).edist_map, Lp.edist_def]
        exact eLpNorm_congr_ae (EventuallyEq.rfl.sub
          (hW.coeFn_l2Integral_indicator_Ioc_prod_simpleHolding huv hvT hE hτ.monotoneOn ha
            ha₂).symm), edist_comm]
    exact (edist_indicator_Ioc_prod_toPredictableLp_le hS hH u v T hE).trans herr.le
  have hmeas_le (s : ℝ≥0) (hs : s ≤ T) : (timeMeasure s).prod P ≤ (timeMeasure T).prod P :=
    Measure.prod_mono (by rw [timeMeasure_def, timeMeasure_def]; exact
      Measure.restrict_mono_set _ (Ioc_subset_Ioc_right hs)) le_rfl
  have hsm : AEStronglyMeasurable (mid - rhs) P :=
    ((((Finance.stronglyAdapted_simpleGains hτ.monotoneOn ha hW.adapted.stronglyAdapted v).mono
      (ℱ.le v)).sub ((Finance.stronglyAdapted_simpleGains hτ.monotoneOn ha
        hW.adapted.stronglyAdapted u).mono (ℱ.le u))).aestronglyMeasurable.indicator
      (ℱ.le u E hE)).sub
      (((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).indicator (ℱ.le u E hE))
  have herr_rhs : eLpNorm (mid - rhs) 2 P ≤ ε / 3 + ε / 3 := by
    refine (eLpNorm_mono_eNorm hsm fun ω ↦ ?_).trans ((eLpNorm_sub_le
      (f := fun ω ↦ Finance.simpleGains τ n a W v ω - hW.l2Integral v (hH.toPredictableLp v) ω)
      (g := fun ω ↦ Finance.simpleGains τ n a W u ω - hW.l2Integral u (hH.toPredictableLp u) ω)
      one_le_two).trans ?_)
    · by_cases hω : ω ∈ E <;> simp only [mid, rhs, Pi.sub_apply, hω, not_false_eq_true,
        indicator_of_mem, indicator_of_notMem, sub_zero, eNorm_zero, zero_le]
      exact le_of_eq (congrArg (‖·‖ₑ) (by ring))
    · gcongr <;> rw [hW.eLpNorm_simpleGains_sub_l2Integral hH hτ.monotoneOn ha ha₂]
      · exact (eLpNorm_mono_measure _ (hmeas_le v hvT)).trans herr.le
      · exact (eLpNorm_mono_measure _ (hmeas_le u (huv.trans hvT))).trans herr.le
  calc
    eLpNorm (lhs - rhs) 2 P = eLpNorm ((lhs - mid) + (mid - rhs)) 2 P := by congr 1; ext ω; simp
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := (eLpNorm_add_le one_le_two).trans (add_le_add herr_lhs herr_rhs)
    _ = ε := by
      rw [show ε / 3 + (ε / 3 + ε / 3) = 3 * (ε / 3) by ring]
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- Restricting a `BrownianIntegrable` integrand to a predictable rectangle `(u, v] × E` within
the horizon `T` evaluates to the `E`-gated increment of `l2Integral` from `u` to `v`. -/
theorem coeFn_l2Integral_indicator_Ioc_prod
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {u v T : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) {E : Set Ω} (hE : MeasurableSet[ℱ u] E) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((hH.indicator_Ioc_prod u v hE).toPredictableLp T) =ᵐ[P]
      E.indicator (fun ω ↦ hW.l2Integral v (hH.toPredictableLp v) ω -
        hW.l2Integral u (hH.toPredictableLp u) ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hzero : eLpNorm
      ((hW.l2Integral T ((hH.indicator_Ioc_prod u v hE).toPredictableLp T) : Ω → ℝ) -
        E.indicator (fun ω ↦ hW.l2Integral v (hH.toPredictableLp v) ω -
          hW.l2Integral u (hH.toPredictableLp u) ω)) 2 P = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) bot_le
    rw [zero_add]
    exact hW.eLpNorm_l2Integral_indicator_Ioc_prod_sub_le hH huv hvT hE hε
  exact ((eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero).mono
    fun _ hω ↦ sub_eq_zero.mp hω

section Modification

variable {H K I J : ℝ≥0 → Ω → ℝ}

/-- Any modification of the predictable `L²` integral process vanishes almost surely at `0`. -/
theorem ae_eval_zero_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    I 0 =ᵐ[P] 0 := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  refine (hI 0).trans ?_
  rw [hW.l2Integral_zero]
  exact Lp.coeFn_zero ℝ 2 P

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

/-- Any strongly adapted modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` is a
martingale on the original raw filtration. -/
theorem martingale_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    Martingale I ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have hM (m : ℕ) : Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  refine martingale_of_tendsto_eLpNorm_one hM hI_adapt fun t ↦ ?_
  apply TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
  have heq (m : ℕ) :
      eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W t - I t) 2 P =
        eLpNorm (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure t).prod P) := by
    have ha₂ (j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
      MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
        (Eventually.of_forall (hb m j hj))
    exact (eLpNorm_congr_ae (EventuallyEq.rfl.sub (hI t))).trans
      (hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ m).monotoneOn (ha m) ha₂ t)
  simpa only [heq] using herr t

private theorem integral_sq_simpleHolding_timeMeasure
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Iic n)) (t : ℝ≥0) (ω : Ω) :
    ∫ s, Finance.simpleHolding τ n a s ω ^ 2 ∂timeMeasure t =
      ∑ i ∈ range n, a i ω ^ 2 * (↑(min (τ (i + 1)) t) - ↑(min (τ i) t)) := by
  have hsq (s : ℝ≥0) : Finance.simpleHolding τ n a s ω ^ 2 =
      ∑ i ∈ range n, (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ a i ω ^ 2) s := by
    by_cases hs : ∃ j < n, s ∈ Ioc (τ j) (τ (j + 1))
    · obtain ⟨j, hj, hjs⟩ := hs
      rw [Finance.simpleHolding_of_mem_Ioc hτ hj hjs,
        sum_eq_single_of_mem j (mem_range.mpr hj), indicator_of_mem hjs]
      intro i hi hij
      exact indicator_of_notMem
        (hτ.notMem_Ioc_of_mem_Ioc_of_ne (mem_range.mp hi) hj hij hjs) _
    · have hz {M : Type} [AddCommMonoid M] (b : ℕ → M) :
          ∑ i ∈ range n, (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ b i) s = 0 :=
        sum_eq_zero fun i hi ↦ indicator_of_notMem (fun his ↦ hs ⟨i, mem_range.mp hi, his⟩) _
      rw [Finance.simpleHolding_def, hz (fun i ↦ a i ω), hz (fun i ↦ a i ω ^ 2),
        zero_pow (by decide)]
  simp_rw [hsq]
  rw [integral_finsetSum _ (fun i _ ↦ (integrable_indicator_iff measurableSet_Ioc).mpr
    integrableOn_const)]
  refine sum_congr rfl fun i hi ↦ ?_
  have hstep : τ i ≤ τ (i + 1) :=
    hτ (mem_Iic.mpr (mem_range.mp hi).le) (mem_Iic.mpr (mem_range.mp hi)) i.le_succ
  rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, measureReal_def,
    timeMeasure_Ioc, ENNReal.toReal_ofReal', mul_comm]
  congr 1
  by_cases hit : τ i ≤ t
  · rw [min_eq_left hit, max_eq_left (sub_nonneg.mpr (by exact_mod_cast le_min hstep hit))]
  · have hti : t ≤ τ i := (not_le.mp hit).le
    rw [min_eq_right (hti.trans hstep), min_eq_right hti, sub_self,
      max_eq_right (sub_nonpos.mpr (by exact_mod_cast hti))]

private theorem tendsto_eLpNorm_one_sq_sub_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ}
    (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun m ↦ eLpNorm (f m - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ f m x ^ 2 - g x ^ 2) 1 μ) atTop (𝓝 0) := by
  let : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  have hbound (m : ℕ) : eLpNorm (fun x ↦ f m x ^ 2 - g x ^ 2) 1 μ ≤
      eLpNorm (f m - g) 2 μ * (eLpNorm (f m - g) 2 μ + (eLpNorm g 2 μ + eLpNorm g 2 μ)) := by
    have hfac : (fun x ↦ f m x ^ 2 - g x ^ 2) = (f m - g) • ((f m - g) + (g + g)) := by
      ext x; dsimp; ring
    rw [hfac]
    refine (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) zero_lt_one).trans ?_
    gcongr
    exact (eLpNorm_add_le one_le_two).trans (add_le_add le_rfl (eLpNorm_add_le one_le_two))
  have hrhs : Tendsto (fun m ↦ eLpNorm (f m - g) 2 μ *
      (eLpNorm (f m - g) 2 μ + (eLpNorm g 2 μ + eLpNorm g 2 μ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul hlim
      (Or.inr (ENNReal.add_ne_top.mpr ⟨ENNReal.zero_ne_top,
        ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩⟩))
      (by simpa only [zero_add] using hlim.add tendsto_const_nhds)
      (Or.inr ENNReal.zero_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun _ ↦ bot_le) hbound

private theorem stronglyAdapted_integral_sq_timeMeasure (hH : IsStronglyPredictable ℱ H) :
    StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) := by
  have hp : IsStronglyProgressive ℱ (fun s ω ↦ H s ω ^ 2) :=
    IsStronglyPredictable.isStronglyProgressive (by simpa only [sq] using hH.mul hH)
  simpa only [timeMeasure_def, ← TauCeti.nnvolume_def] using
    (hp.integral_Ioc TauCeti.nnvolume 0).stronglyAdapted

private theorem eLpNorm_one_integral_timeMeasure_sub_le [SFinite P]
    {S : ℝ≥0 → Ω → ℝ} (hS : BrownianIntegrable ℱ P S) (hH : BrownianIntegrable ℱ P H)
    (t : ℝ≥0) :
    eLpNorm (fun ω ↦ (∫ s, S s ω ^ 2 ∂timeMeasure t) - ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P ≤
      eLpNorm (fun p ↦ S p.1 p.2 ^ 2 - H p.1 p.2 ^ 2) 1 ((timeMeasure t).prod P) := by
  have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ S p.1 p.2 ^ 2 - H p.1 p.2 ^ 2) :=
    ((hS.isStronglyPredictable.pow 2).sub (hH.isStronglyPredictable.pow 2)).mono
      ℱ.predictable_le_prod
  have hlhs_m : AEStronglyMeasurable
      (fun ω ↦ (∫ s, S s ω ^ 2 ∂timeMeasure t) - ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
    (((stronglyAdapted_integral_sq_timeMeasure hS.isStronglyPredictable t).sub
      (stronglyAdapted_integral_sq_timeMeasure hH.isStronglyPredictable t)).mono
        (ℱ.le t)).aestronglyMeasurable
  have hdom : ∀ᵐ ω ∂P,
      ‖(∫ s, S s ω ^ 2 ∂timeMeasure t) - ∫ s, H s ω ^ 2 ∂timeMeasure t‖ₑ ≤
        ∫⁻ s, ‖S s ω ^ 2 - H s ω ^ 2‖ₑ ∂timeMeasure t := by
    filter_upwards [hS.locallyBrownianIntegrable.ae_memLp,
      hH.locallyBrownianIntegrable.ae_memLp] with ω hSω hHω
    have hSi : Integrable (fun s ↦ S s ω ^ 2) (timeMeasure t) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hSω t).integrable_sq
    have hHi : Integrable (fun s ↦ H s ω ^ 2) (timeMeasure t) := by
      simpa only [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hHω t).integrable_sq
    rw [← integral_sub hSi hHi]
    exact eNorm_integral_le_lintegral_eNorm _
  rw [eLpNorm_one_eq_lintegral_eNorm hlhs_m,
    eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
    lintegral_prod_symm _ hdiff_sm.eNorm.aemeasurable]
  exact lintegral_mono_ae hdom

/-- **Brownian square-compensation martingale.** For any `BrownianIntegrable` integrand `H` and
strongly adapted modification `I` of `l2Integral`, `I_t² - ∫_{(0, t]} H_s² ds` is a true
martingale on the original raw filtration. -/
theorem martingale_sq_sub_integral_of_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (Eventually.of_forall (hb m j hj))
  let M (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 -
      ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t
  have hM (m : ℕ) : Martingale (M m) ℱ P := by
    convert hW.martingale_sq_simpleGains_sub (hτ m).monotoneOn (ha m) (ha₂ m) using 1
    ext t ω; dsimp only [M]; rw [integral_sq_simpleHolding_timeMeasure (hτ m).monotoneOn t ω]
  have hcomp_adapt := stronglyAdapted_integral_sq_timeMeasure hH.isStronglyPredictable
  refine martingale_of_tendsto_eLpNorm_one hM (fun t ↦ ((hI_adapt t).pow 2).sub (hcomp_adapt t))
    fun t ↦ ?_
  have hS (m : ℕ) := BrownianIntegrable.simpleHolding (ha m) (ha₂ m)
  have hG_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_one_sq_sub_sq (hW.memLp_of_ae_eq_l2Integral hH hI t) ?_
    have heq (m : ℕ) : eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W t - I t) 2 P =
        eLpNorm (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((timeMeasure t).prod P) :=
      (eLpNorm_congr_ae (EventuallyEq.rfl.sub (hI t))).trans
        (hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ m).monotoneOn (ha m) (ha₂ m) t)
    simpa only [heq] using herr t
  have hA_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
        ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_one_sq_sub_sq (hH.memLp_timeMeasure t) (herr t))
      (fun _ ↦ bot_le) fun m ↦ eLpNorm_one_integral_timeMeasure_sub_le (hS m) hH t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hG_lim.add hA_lim) (fun _ ↦ bot_le) fun m ↦ ?_
  have htri : (M m t - fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) =
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) -
        fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t := by ext ω; simp [M]; ring
  rw [htri]
  exact eLpNorm_sub_le le_rfl

end Modification

/-- **Continuous martingale modification of the predictable `L²` Brownian integral.**
When `W` has almost surely continuous paths, any `BrownianIntegrable` integrand `H` admits a
strongly predictable, almost surely continuous martingale `I` on the original raw filtration
that represents `hW.l2Integral t (hH.toPredictableLp t)` at every time `t`. -/
theorem exists_continuous_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have hM (m : ℕ) : Martingale (M m) ℱ P :=
    hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩
  have hc (m : ℕ) : ∀ᵐ ω ∂P, Continuous (fun t ↦ M m t ω) :=
    hcont.mono fun ω hω ↦ by
      simp only [M, Finance.simpleGains_def]
      exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
        ((hω.comp (continuous_const.min continuous_id)).sub
          (hω.comp (continuous_const.min continuous_id)))
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m)
      (Eventually.of_forall (hb m j hj))
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) (ha₂ m) t)
  have htend (t : ℝ≥0) : Tendsto (fun m ↦ (hmem m t).toLp (M m t)) atTop
      (𝓝 (hW.l2Integral t (hH.toPredictableLp t))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have heq (m : ℕ) :
        eLpNorm (((hmem m t).toLp (M m t) : Ω → ℝ) -
            (hW.l2Integral t (hH.toPredictableLp t) : Ω → ℝ)) 2 P =
          eLpNorm (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
            ((timeMeasure t).prod P) :=
      (eLpNorm_congr_ae (((hmem m t).coeFn_toLp).sub .rfl)).trans
        (hW.eLpNorm_simpleGains_sub_l2Integral hH (hτ m).monotoneOn (ha m) (ha₂ m) t)
    simpa only [heq] using herr t
  obtain ⟨I, hIm, hIp, hIlim, _, _, _, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2) hM hc hmem
      (fun t ↦ (htend t).cauchySeq)
  refine ⟨I, hIp, hIm, hIpath.mono fun _ hω ↦ hω.1, fun t ↦ ?_⟩
  have hItend : Tendsto (fun m ↦ (hmem m t).toLp (M m t)) atTop
      (𝓝 ((hIlim t).1.toLp (I t))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun m ↦ hmem m t) _ (hIlim t).1).mpr (hIlim t).2
  have heq_lp : (hIlim t).1.toLp (I t) = hW.l2Integral t (hH.toPredictableLp t) :=
    tendsto_nhds_unique hItend (htend t)
  exact (hIlim t).1.coeFn_toLp.symm.trans (heq_lp ▸ EventuallyEq.rfl)

end TauCeti.Probability.IsFilteredPreBrownianReal

