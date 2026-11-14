/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight.Normed
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# The method of moments

If probability measures `μₙ` on `ℝ` have moments that are eventually integrable and the moments
converge to those of a probability measure `μ`, and `μ` is determined by its moments among
probability measures with all moments, then `μₙ → μ` weakly (the method of moments).

Unlike `TauCeti.Probability.Moments.MethodOfMoments.CompactSupport`, this version does not require
compact support; it assumes moment determinacy instead. Determinacy criteria for supplying `hdet`
are available in `TauCeti.Probability.Moments.Determinacy`.

## Main results

* `MeasureTheory.ProbabilityMeasure.integrable_pow_and_integral_pow_eq_of_mapClusterPt`:
  moments of a weak cluster point equal the limits of the moments.
* `ProbabilityMeasure.integrable_pow_and_integral_pow_eq_of_mapClusterPt_of_integral_pow_le`:
  the single-moment version, needing only a bounded twice-order moment.
* `ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_forall_integral_pow_eq_imp_eq`: weak
  convergence when the limit is determined by its moments.

## Implementation notes

Bounded second moments give tightness, and Prokhorov's theorem gives compactness of an eventual
family. Closed sublevel sets of lower-semicontinuous integrals, applied to `x ^ (2 * k)` and
`(x ^ k - c) ^ 2`, show that every cluster point has the required `k`th moment.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

open TauCeti

/-- A weak cluster point inherits an eventual integral bound for a continuous nonnegative
function. -/
private theorem integrable_and_integral_le_of_mapClusterPt_of_eventually_le
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {M : ℝ}
    (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (hint : ∀ᶠ i in l, Integrable f (μn i : Measure ℝ))
    (hbound : ∀ᶠ i in l, ∫ x, f x ∂(μn i : Measure ℝ) ≤ M)
    (hν : MapClusterPt ν l μn) :
    Integrable f (ν : Measure ℝ) ∧ ∫ x, f x ∂(ν : Measure ℝ) ≤ M := by
  have hlintegral :
      ∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal M := by
    have hclosed := isClosed_setOfPred_lintegral_le_probabilityMeasure
      ((ENNReal.continuous_ofReal.comp hf).lowerSemicontinuous) (ENNReal.ofReal M)
    have hevent : ∀ᶠ i in l, μn i ∈
        {ρ : ProbabilityMeasure ℝ |
          ∫⁻ x, ENNReal.ofReal (f x) ∂(ρ : Measure ℝ) ≤ ENNReal.ofReal M} := by
      filter_upwards [hint, hbound] with i hi hBi
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnonneg)]
      exact ENNReal.ofReal_le_ofReal hBi
    exact hclosed.mem_of_mapClusterPt hν hevent
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlintegral
  have hνint : Integrable f (ν : Measure ℝ) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (ae_of_all _ hnonneg)).1 hfinite
  have hneBot : l.NeBot := (map_neBot_iff μn).1 (hν.clusterPt.neBot.mono inf_le_right)
  have hM : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hbound.exists
    exact (integral_nonneg_of_ae (ae_of_all _ hnonneg)).trans hi
  rw [← ofReal_integral_eq_lintegral_ofReal hνint (ae_of_all _ hnonneg)] at hlintegral
  exact ⟨hνint, (ENNReal.ofReal_le_ofReal_iff hM).mp hlintegral⟩

/-- A weak cluster point inherits a fixed moment if that moment converges and the moments
of twice its order are eventually integrable and uniformly bounded. -/
theorem integrable_pow_and_integral_pow_eq_of_mapClusterPt_of_integral_pow_le
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {m B : ℝ} (k : ℕ)
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ (2 * k)) (μn i : Measure ℝ))
    (hB : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μn i : Measure ℝ) ≤ B)
    (hlimk : Tendsto (fun i => ∫ x, x ^ k ∂(μn i : Measure ℝ)) l (𝓝 m))
    (hν : MapClusterPt ν l μn) :
    Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) ∧
      ∫ x, x ^ k ∂(ν : Measure ℝ) = m := by
  have hnonneg : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := by
    intro x
    rw [show 2 * k = k * 2 by omega, pow_mul]
    exact sq_nonneg (x ^ k)
  have h2k : Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) :=
    (integrable_and_integral_le_of_mapClusterPt_of_eventually_le (continuous_id.pow (2 * k))
      hnonneg hint hB hν).1
  have hk : Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) :=
    integrable_pow_of_le aestronglyMeasurable_id (by omega) h2k
  let a : ℝ := ∫ x, x ^ k ∂(ν : Measure ℝ)
  let q : ℝ := ∫ x, x ^ (2 * k) ∂(ν : Measure ℝ)
  have hpow (x : ℝ) : x ^ (2 * k) = (x ^ k) ^ 2 := by
    calc
      x ^ (2 * k) = x ^ (k * 2) := by rw [Nat.mul_comm]
      _ = (x ^ k) ^ 2 := by rw [pow_mul]
  have hsquare_identity (c x : ℝ) :
      (x ^ k - c) ^ 2 = x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2 := by
    rw [hpow x]
    ring
  have square_info {ρ : ProbabilityMeasure ℝ}
      (h2 : Integrable (fun x : ℝ => x ^ (2 * k)) (ρ : Measure ℝ)) (c : ℝ) :
      Integrable (fun x : ℝ => (x ^ k - c) ^ 2) (ρ : Measure ℝ) ∧
      ∫ x, (x ^ k - c) ^ 2 ∂(ρ : Measure ℝ) =
        (∫ x, x ^ (2 * k) ∂(ρ : Measure ℝ)) -
          (2 * c) * ∫ x, x ^ k ∂(ρ : Measure ℝ) + c ^ 2 := by
    have hk : Integrable (fun x : ℝ => x ^ k) (ρ : Measure ℝ) :=
      integrable_pow_of_le aestronglyMeasurable_id (by omega : k ≤ 2 * k) h2
    have hpoly : Integrable
        (fun x : ℝ => x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2) (ρ : Measure ℝ) :=
      (h2.sub (hk.const_mul (2 * c))).add (integrable_const _)
    refine ⟨hpoly.congr (ae_of_all _ fun x => (hsquare_identity c x).symm), ?_⟩
    simp_rw [hsquare_identity c]
    calc
      _ = (∫ x, x ^ (2 * k) - (2 * c) * x ^ k ∂(ρ : Measure ℝ)) +
          ∫ _ : ℝ, c ^ 2 ∂(ρ : Measure ℝ) :=
        integral_add (h2.sub (hk.const_mul (2 * c))) (integrable_const _)
      _ = _ := by
        rw [integral_sub h2 (hk.const_mul (2 * c))]
        simp [integral_const_mul]
  have hνsquare (c : ℝ) :
      ∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) = q - (2 * c) * a + c ^ 2 := by
    simpa [a, q] using (square_info h2k c).2
  -- The twice-order moment need only be bounded, since the remaining term has a limit.
  have hbound_square (c : ℝ) :
      ∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) ≤
        B - (2 * c) * m + c ^ 2 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hcomb : Tendsto
        (fun i => B - (2 * c) * ∫ x, x ^ k ∂(μn i : Measure ℝ) + c ^ 2) l
        (𝓝 (B - (2 * c) * m + c ^ 2)) :=
      (tendsto_const_nhds.sub (hlimk.const_mul (2 * c))).add_const (c ^ 2)
    have hevent : ∀ᶠ i in l,
        ∫ x, (x ^ k - c) ^ 2 ∂(μn i : Measure ℝ) ≤
          B - (2 * c) * m + c ^ 2 + ε := by
      filter_upwards [hint, hB, hcomb.eventually
        (Iio_mem_nhds (show B - (2 * c) * m + c ^ 2 <
          B - (2 * c) * m + c ^ 2 + ε by linarith))] with i h2 hi hlim
      rw [(square_info h2 c).2]
      linarith
    exact (integrable_and_integral_le_of_mapClusterPt_of_eventually_le
      (((continuous_id.pow k).sub continuous_const).pow 2)
      (fun x => sq_nonneg (x ^ k - c))
      (hint.mono fun _ h2 => (square_info h2 c).1) hevent hν).2
  -- This quadratic inequality holds for every `c`, forcing the linear coefficients to agree.
  have hmoment : a = m := by
    by_contra hne
    let c : ℝ := (B - q + 1) / (2 * (m - a))
    have hden : 2 * (m - a) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      apply sub_ne_zero.mpr
      intro heq
      exact hne heq.symm
    have hc : 2 * c * (m - a) = B - q + 1 := by
      dsimp [c]
      field_simp [hden]
    have hineq := hbound_square c
    rw [hνsquare c] at hineq
    dsimp [c] at hc
    dsimp [a, q] at hineq hc
    nlinarith
  exact ⟨hk, hmoment⟩

/-- A weak cluster point of probability measures with converging moments has finite moments,
equal to the limits. -/
theorem integrable_pow_and_integral_pow_eq_of_mapClusterPt
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ}
    {m : ℕ → ℝ} (hint : ∀ k, ∀ᶠ n in l,
      Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) l (𝓝 (m k)))
    (hν : MapClusterPt ν l μn) :
    (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) ∧
      ∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = m k := by
  have h k := integrable_pow_and_integral_pow_eq_of_mapClusterPt_of_integral_pow_le
    (B := m (2 * k) + 1) k (hint (2 * k))
    ((hlim (2 * k)).eventually (Iio_mem_nhds (by linarith)) |>.mono fun _ hi => hi.le)
    (hlim k) hν
  exact ⟨fun k => (h k).1, fun k => (h k).2⟩

/-- **The method of moments.** Let `μn` be probability measures on `ℝ` whose moments are
eventually finite and converge to those of `μ`. If `μ` is determined by its moments among
probability measures with finite moments, then `μn` converges weakly to `μ`. -/
theorem tendsto_of_tendsto_integral_pow_of_forall_integral_pow_eq_imp_eq
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ}
    (hint : ∀ k, ∀ᶠ n in l, Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) l
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))))
    (hdet : ∀ ν : ProbabilityMeasure ℝ, (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) →
      (∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = ∫ x, x ^ k ∂(μ : Measure ℝ)) → ν = μ) :
    Tendsto μn l (𝓝 μ) := by
  let B : ℝ := (∫ x, x ^ 2 ∂(μ : Measure ℝ)) + 1
  let s : Set ι := {n | Integrable (fun x : ℝ => x ^ 2) (μn n : Measure ℝ) ∧
    ∫ x, x ^ 2 ∂(μn n : Measure ℝ) ≤ B}
  have hμ2_lt_B : ∫ x, x ^ 2 ∂(μ : Measure ℝ) < B := by
    dsimp [B]
    linarith
  have hs : s ∈ l := by
    filter_upwards [hint 2, (hlim 2).eventually
      (Iio_mem_nhds hμ2_lt_B)] with n hi hb
    exact ⟨hi, hb.le⟩
  have htight : IsTightMeasureSet
      ((fun p : ProbabilityMeasure ℝ => (p : Measure ℝ)) '' (μn '' s)) := by
    refine TauCeti.isTightMeasureSet_of_integral_sq_le (B := B) ?_
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact hn
  have hevent : ∀ᶠ n in l, μn n ∈ closure (μn '' s) := by
    filter_upwards [hs] with n hn
    exact subset_closure ⟨n, hn, rfl⟩
  refine (isCompact_closure_of_isTightMeasureSet htight).tendsto_nhds_of_unique_mapClusterPt
    hevent fun ν _ hν => ?_
  obtain ⟨h1, h2⟩ := integrable_pow_and_integral_pow_eq_of_mapClusterPt hint hlim hν
  exact hdet ν h1 h2

end MeasureTheory.ProbabilityMeasure
