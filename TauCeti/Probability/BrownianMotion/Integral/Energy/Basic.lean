/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
public import Mathlib.Probability.Martingale.Basic
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.Order.Monotone.Basic
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# Elementary Brownian isometry in the predictable energy measure

The second moment of an elementary Brownian gain equals the lower square-energy integral of its
holding against the trimmed predictable measure at the last grid date `τ n`
(`TauCeti.Probability.IsFilteredPreBrownianReal.lintegral_enorm_sq_simpleGains`), and, at an
arbitrary observation time `t`, its `L²(P)` norm equals the `L²` norm of its holding against
`(timeMeasure t).prod P` (`TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_simpleGains`),
even when the grid extends beyond `t`. Together these identify the finite-grid isometry with the
native predictable `L²` norm used for completion, without introducing an integral operator or
assuming that the general stochastic integral exists.

At an arbitrary observation time `t`, the `L²(P)` norm of the elementary integral equals the
`L²` norm of its holding for Lebesgue time on `(0,t]` times `P`
(`TauCeti.Probability.IsFilteredPreBrownianReal.eLpNorm_simpleGains`, and for two grids
`eLpNorm_simpleGains_sub`); the grid may extend beyond `t`. This is the form used to show that
elementary integrals of `L²`-approximating holdings are Cauchy in `L²(P)` at every time.

Both isometries require a nondecreasing grid (`MonotoneOn τ (Set.Iic n)`), which may be empty or
have repeated dates; heights need only be square integrable and measurable at their left endpoints,
and Brownian path regularity and usual conditions on the filtration are not needed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory Finset Set TauCeti.Finance
open scoped ENNReal NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ}

/-- An elementary Brownian integral with square-integrable left-measurable heights is square
integrable at every time. -/
theorem memLp_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (t : ℝ≥0) :
    MemLp (simpleGains τ n a W t) 2 P := by
  rw [show simpleGains τ n a W t = _ from funext (simpleGains_def τ n a W t)]
  exact hW.memLp_sum_mul_sub_min (range n)
    (fun i hi ↦ hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i))
    (fun i hi ↦ ha i (mem_range.mp hi)) (fun i hi ↦ ha₂ i (mem_range.mp hi)) t

/-- **The elementary Brownian isometry at an observation time.** The `L²(P)` norm of an
elementary Brownian integral at time `t` is the `L²` norm of its holding for Lebesgue time on
`(0,t]` times `P`. The grid may extend beyond `t`, and square-integrable left-measurable
heights suffice; no boundedness assumption is imposed. -/
theorem eLpNorm_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) (t : ℝ≥0) :
    eLpNorm (simpleGains τ n a W t) 2 P =
      eLpNorm (Function.uncurry (simpleHolding τ n a)) 2
        ((TauCeti.Probability.timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hle (i : ℕ) (hi : i ∈ range n) : τ i ≤ τ (i + 1) :=
    hτ (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i)
  have hdisj : ((range n : Finset ℕ) : Set ℕ).Pairwise
      fun i j ↦ τ (i + 1) ≤ τ j ∨ τ (j + 1) ≤ τ i := by
    simpa only [coe_range] using hτ.pairwise_succ_le_or_succ_le
  have hG : simpleGains τ n a W t = fun ω ↦ ∑ i ∈ range n,
      a i ω * (W (min (τ (i + 1)) t) ω - W (min (τ i) t) ω) :=
    funext (simpleGains_def τ n a W t)
  have hmem := hW.memLp_simpleGains hτ ha ha₂ t
  have hmeasa (i : ℕ) (hi : i < n) : Measurable (fun ω ↦ ENNReal.ofReal (a i ω ^ 2)) :=
    (((ha i hi).mono (ℱ.le _)).measurable.pow_const 2).ennreal_ofReal
  -- Compare the squares of both norms as lower integrals.
  refine ENNReal.rpow_left_injective (x := 2) two_ne_zero ?_
  simp only [ENNReal.rpow_two]
  rw [eLpNorm_two_sq_eq_lintegral hmem.aestronglyMeasurable,
    ← lintegral_lintegral_enorm_sq_eq_eLpNorm_prod_sq
      ((isStronglyPredictable_simpleHolding ha).mono ℱ.predictable_le_prod).aestronglyMeasurable]
  simp_rw [Function.uncurry_apply_pair, lintegral_enorm_sq_simpleHolding_timeMeasure hτ,
    Real.enorm_sq_eq_ofReal_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq (ae_of_all _ fun _ ↦ sq_nonneg _)]
  simp only [hG]
  rw [hW.integral_sq_sum_mul_sub_min (range n) hle hdisj (fun i hi ↦ ha i (mem_range.mp hi))
      (fun i hi ↦ ha₂ i (mem_range.mp hi)) t,
    lintegral_finsetSum _ (fun i hi ↦ (hmeasa i (mem_range.mp hi)).mul_const _),
    ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast min_le_min_right t (hle i hi))))]
  refine sum_congr rfl fun i hi ↦ ?_
  -- An interval starting after `t` has no elapsed length on either side.
  have hlen : ENNReal.ofReal ((min (τ (i + 1)) t : ℝ≥0) - (τ i : ℝ)) =
      ENNReal.ofReal ((min (τ (i + 1)) t : ℝ≥0) - (min (τ i) t : ℝ≥0)) := by
    by_cases hit : τ i ≤ t
    · rw [min_eq_left hit]
    · have hti : t ≤ τ i := (not_le.mp hit).le
      rw [min_eq_right hti, min_eq_right (hti.trans (hle i hi)), sub_self,
        ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hti)),
        ENNReal.ofReal_zero]
  rw [lintegral_mul_const _ (hmeasa i (mem_range.mp hi)), hlen,
    ← ofReal_integral_eq_lintegral_ofReal (ha₂ i (mem_range.mp hi)).integrable_sq
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ sq_nonneg _)]

/-- **The two-grid elementary Brownian isometry at an observation time.** The `L²(P)` distance
between two elementary Brownian integrals at time `t` is the `L²` distance between their holdings
for Lebesgue time on `(0,t]` times `P`. -/
theorem eLpNorm_simpleGains_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ₁ τ₂ : ℕ → ℝ≥0} {n₁ n₂ : ℕ} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Set.Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Set.Iic n₂))
    (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j))
    (ha₁₂ : ∀ j < n₁, MemLp (a₁ j) 2 P) (ha₂₂ : ∀ j < n₂, MemLp (a₂ j) 2 P) (t : ℝ≥0) :
    eLpNorm (simpleGains τ₁ n₁ a₁ W t - simpleGains τ₂ n₂ a₂ W t) 2 P =
      eLpNorm (Function.uncurry (simpleHolding τ₁ n₁ a₁) -
        Function.uncurry (simpleHolding τ₂ n₂ a₂)) 2
        ((TauCeti.Probability.timeMeasure t).prod P) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨N, ρ, c, -, hρ, hc, hhold, hgain⟩ :=
    exists_simpleHolding_simpleGains_eq_sub ℱ hτ₁ hτ₂ ha₁ ha₂
  have memLp_eval {ρ' : ℕ → ℝ≥0} {N' : ℕ} {d : ℕ → Ω → ℝ}
      (hd : ∀ j < N', MemLp (d j) 2 P) (u : ℝ≥0) :
      MemLp (fun ω ↦ simpleHolding ρ' N' d u ω) 2 P := by
    simp only [simpleHolding_def]
    refine memLp_finsetSum _ fun j hj ↦ ?_
    by_cases hu : u ∈ Ioc (ρ' j) (ρ' (j + 1))
    · simpa only [indicator_of_mem hu] using hd j (mem_range.mp hj)
    · simpa only [indicator_of_notMem hu] using (memLp_const (0 : ℝ) : MemLp (fun _ ↦ (0 : ℝ)) 2 P)
  -- Each height on the common grid is a value of the difference of the two holdings.
  have hc₂ (j : ℕ) (hj : j < N) : MemLp (c j) 2 P := by
    have hmem : ρ (j + 1) ∈ Ioc (ρ j) (ρ (j + 1)) :=
      ⟨hρ (mem_Iic.mpr hj.le) (mem_Iic.mpr hj) (Nat.lt_succ_self j), le_rfl⟩
    have hceq : c j = fun ω ↦
        simpleHolding τ₁ n₁ a₁ (ρ (j + 1)) ω - simpleHolding τ₂ n₂ a₂ (ρ (j + 1)) ω :=
      funext fun ω ↦ by
        rw [← simpleHolding_of_mem_Ioc (a := c) hρ.monotoneOn hj hmem ω, hhold]
    rw [hceq]
    exact (memLp_eval ha₁₂ _).sub (memLp_eval ha₂₂ _)
  have hG : simpleGains τ₁ n₁ a₁ W t - simpleGains τ₂ n₂ a₂ W t = simpleGains ρ N c W t :=
    funext fun ω ↦ (hgain W t ω).symm
  have hK : Function.uncurry (simpleHolding τ₁ n₁ a₁) -
      Function.uncurry (simpleHolding τ₂ n₂ a₂) = Function.uncurry (simpleHolding ρ N c) :=
    funext fun p ↦ (hhold p.1 p.2).symm
  rw [hG, hK]
  exact hW.eLpNorm_simpleGains hρ.monotoneOn hc hc₂ t

/-- The elementary Brownian isometry with its actual predictable lower-integral energy.
Square-integrable left-measurable heights suffice; no boundedness assumption is imposed. -/
theorem lintegral_enorm_sq_simpleGains (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (ha₂ : ∀ i < n, MemLp (a i) 2 P) :
    ∫⁻ ω, ‖simpleGains τ n a W (τ n) ω‖ₑ ^ 2 ∂P =
      ∫⁻ p, ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2 ∂ℱ.predictableMeasure P (τ n) := by
  have hholding := isStronglyPredictable_simpleHolding ha
  have hm : Measurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ ‖simpleHolding τ n a p.1 p.2‖ₑ ^ 2) :=
    hholding.eNorm.pow_const 2
  rw [ℱ.predictableMeasure_def, lintegral_trim ℱ.predictable_le_prod hm,
    ← eLpNorm_two_sq_eq_lintegral (hW.memLp_simpleGains hτ ha ha₂ _).aestronglyMeasurable,
    hW.eLpNorm_simpleGains hτ ha ha₂,
    eLpNorm_two_sq_eq_lintegral (hholding.mono ℱ.predictable_le_prod).aestronglyMeasurable]
  simp only [Function.uncurry_def]

/-- The gains of a left-measurable simple holding in `L²((timeMeasure T).prod P)` agree on
`[0, T]` with an almost surely continuous martingale, realized as the gains of a clipped holding
whose heights are all square integrable. -/
theorem exists_martingale_simpleGains_eq_on_Iic
    (hW : IsFilteredPreBrownianReal ℱ W P) (hWc : ∀ᵐ ω ∂P, Continuous fun t ↦ W t ω)
    {T : ℝ≥0} (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hK : MemLp (Function.uncurry (simpleHolding τ n a)) 2 ((timeMeasure T).prod P)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M ℱ P ∧ (∀ᵐ ω ∂P, Continuous fun t ↦ M t ω) ∧
      ∀ t ≤ T, ∀ ω, M t ω = simpleGains τ n a W t ω := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨a', ha', ha'₂, -, hgain⟩ :=
    exists_memLp_simpleHolding_simpleGains_eq_on_Iic hτ ha hK
  refine ⟨simpleGains τ n a' W, hW.martingale.simpleGains hτ ha' fun j hj t ↦ ?_,
    hWc.mono fun _ hω ↦ continuous_simpleGains hω, hgain W⟩
  by_cases hjt : τ j ≤ t
  · rw [min_eq_left hjt]
    exact (hW.memLp_mul_sub (le_min (hτ hj.le hj (Nat.le_succ j)) hjt)
      (ha' j hj) (ha'₂ j hj)).integrable one_le_two
  · have htj : t ≤ τ j := (not_le.1 hjt).le
    simp only [min_eq_right htj, min_eq_right (htj.trans (hτ hj.le hj (Nat.le_succ j))),
      sub_self, mul_zero]
    exact integrable_zero _ _ _

end TauCeti.Probability.IsFilteredPreBrownianReal
