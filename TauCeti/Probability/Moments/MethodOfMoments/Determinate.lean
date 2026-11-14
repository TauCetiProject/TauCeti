/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight.Basic
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# The method of moments

If probability measures `μₙ` on `ℝ` have moments that are eventually integrable and the moments
converge to those of a probability measure `μ`, and `μ` is determined by its moments among
probability measures with all moments, then `μₙ → μ` weakly (the method of moments).

The proof is the standard one: bounded moments give tightness, Prokhorov's theorem gives compactness
of an eventual family, and uniform integrability of the monomials (from the bounds on higher
moments) identifies the moments of every weak limit point with those of `μ`.

## Main results

* `MeasureTheory.ProbabilityMeasure.integrable_pow_and_integral_pow_eq_of_mapClusterPt`:
  moments of a weak cluster point equal the limits of the moments.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_unique`: weak
  convergence when the limit is determined by its moments.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.MethodOfMoments

/-- A weak cluster point inherits a fixed moment from convergence of the moments up to twice
its order. -/
private theorem integrable_pow_and_integral_pow_eq_of_mapClusterPt_fixed
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {m : ℕ → ℝ} (k : ℕ)
    (hint : ∀ n ≤ 2 * k, ∀ᶠ i in l,
      Integrable (fun x : ℝ => x ^ n) (μn i : Measure ℝ))
    (hlim : ∀ n ≤ 2 * k,
      Tendsto (fun i => ∫ x, x ^ n ∂(μn i : Measure ℝ)) l (𝓝 (m n)))
    (hν : MapClusterPt ν l μn) :
    Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) ∧
      ∫ x, x ^ k ∂(ν : Measure ℝ) = m k := by
  let B : ℝ := m (2 * k) + 1
  have hB : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μn i : Measure ℝ) ≤ B := by
    have hlim2 := hlim (2 * k) le_rfl
    have hlt : m (2 * k) < B := by dsimp [B]; linarith
    exact (hlim2.eventually (Iio_mem_nhds hlt)).mono fun _ h => le_of_lt h
  have hnonneg : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := by
    intro x
    rw [show 2 * k = k * 2 by omega, pow_mul]
    exact sq_nonneg (x ^ k)
  have hf : LowerSemicontinuous (fun x : ℝ => ENNReal.ofReal (x ^ (2 * k))) := by
    exact (ENNReal.continuous_ofReal.comp (continuous_id.pow (2 * k))).lowerSemicontinuous
  have hclosed := isClosed_setOfPred_lintegral_le_probabilityMeasure hf (ENNReal.ofReal B)
  have hbound :
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal B := by
    have hevent : ∀ᶠ i in l, μn i ∈
        {ρ : ProbabilityMeasure ℝ |
          ∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ρ : Measure ℝ) ≤ ENNReal.ofReal B} := by
      filter_upwards [hint (2 * k) le_rfl, hB] with i hi hBi
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ hnonneg)]
      exact ENNReal.ofReal_le_ofReal hBi
    simpa using hclosed.mem_of_mapClusterPt hν hevent
  have hfinite :
      (∫⁻ x, ENNReal.ofReal (x ^ (2 * k)) ∂(ν : Measure ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have h2k : Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) (ae_of_all _ hnonneg)).1 hfinite
  have hlow : ∀ n ≤ k, Integrable (fun x : ℝ => x ^ n) (ν : Measure ℝ) := by
    intro n hn
    exact integrable_pow_of_le (by omega) h2k
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
  have hνsquare_integrable (c : ℝ) :
      Integrable (fun x : ℝ => (x ^ k - c) ^ 2) (ν : Measure ℝ) := by
    have hpoly : Integrable
        (fun x : ℝ => x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2) (ν : Measure ℝ) :=
      (h2k.sub ((hlow k le_rfl).const_mul (2 * c))).add (integrable_const _)
    exact hpoly.congr (ae_of_all _ fun x => (hsquare_identity c x).symm)
  have integral_expansion {ρ : ProbabilityMeasure ℝ}
      (h2 : Integrable (fun x : ℝ => x ^ (2 * k)) (ρ : Measure ℝ))
      (hk : Integrable (fun x : ℝ => x ^ k) (ρ : Measure ℝ)) (c : ℝ) :
      ∫ x, x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2 ∂(ρ : Measure ℝ) =
        (∫ x, x ^ (2 * k) ∂(ρ : Measure ℝ)) -
          (2 * c) * ∫ x, x ^ k ∂(ρ : Measure ℝ) + c ^ 2 := by
    let f : ℝ → ℝ := fun x => x ^ (2 * k) - (2 * c) * x ^ k
    let g : ℝ → ℝ := fun _ => c ^ 2
    have hf : Integrable f (ρ : Measure ℝ) := h2.sub (hk.const_mul (2 * c))
    have hg : Integrable g (ρ : Measure ℝ) := integrable_const _
    have hsplit : (fun x : ℝ => x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2) = f + g := by
      funext x
      rfl
    calc
      ∫ x, x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2 ∂(ρ : Measure ℝ) =
          ∫ x, (f + g) x ∂(ρ : Measure ℝ) := by rw [hsplit]
      _ = (∫ x, f x ∂(ρ : Measure ℝ)) + ∫ x, g x ∂(ρ : Measure ℝ) :=
        integral_add hf hg
      _ = (∫ x, x ^ (2 * k) ∂(ρ : Measure ℝ)) -
          (2 * c) * ∫ x, x ^ k ∂(ρ : Measure ℝ) + c ^ 2 := by
        rw [integral_sub h2 (hk.const_mul (2 * c))]
        simp [g, integral_const_mul]
  have hνsquare (c : ℝ) :
      ∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) = q - (2 * c) * a + c ^ 2 := by
    calc
      ∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) =
          ∫ x, x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2 ∂(ν : Measure ℝ) :=
        integral_congr_ae (ae_of_all _ (hsquare_identity c))
      _ = q - (2 * c) * a + c ^ 2 := by
        simpa [a, q] using integral_expansion h2k (hlow k le_rfl) c
  have hsquare_limit (c : ℝ) :
      Tendsto (fun i => ∫ x, (x ^ k - c) ^ 2 ∂(μn i : Measure ℝ)) l
        (𝓝 (m (2 * k) - (2 * c) * m k + c ^ 2)) := by
    have heq : ∀ᶠ i in l,
        ∫ x, (x ^ k - c) ^ 2 ∂(μn i : Measure ℝ) =
          (∫ x, x ^ (2 * k) ∂(μn i : Measure ℝ)) -
            (2 * c) * ∫ x, x ^ k ∂(μn i : Measure ℝ) + c ^ 2 := by
      filter_upwards [hint (2 * k) le_rfl, hint k (by omega)] with i h2 hk
      calc
        ∫ x, (x ^ k - c) ^ 2 ∂(μn i : Measure ℝ) =
            ∫ x, x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2 ∂(μn i : Measure ℝ) :=
          integral_congr_ae (ae_of_all _ (hsquare_identity c))
        _ = _ := integral_expansion h2 hk c
    have hcomb :
        Tendsto
          (fun i => (∫ x, x ^ (2 * k) ∂(μn i : Measure ℝ)) -
            (2 * c) * ∫ x, x ^ k ∂(μn i : Measure ℝ) + c ^ 2) l
          (𝓝 (m (2 * k) - (2 * c) * m k + c ^ 2)) := by
      exact ((hlim (2 * k) le_rfl).sub ((hlim k (by omega)).const_mul (2 * c)))
        |>.add_const (c ^ 2)
    exact hcomb.congr' (heq.mono fun i hi => hi.symm)
  have hbound_square (c : ℝ) :
      ∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) ≤
        m (2 * k) - (2 * c) * m k + c ^ 2 := by
    let M : ℝ := m (2 * k) - (2 * c) * m k + c ^ 2
    have hM_nonneg : 0 ≤ M := by
      have hnonneg : ∀ i, 0 ≤ ∫ x, (x ^ k - c) ^ 2 ∂(μn i : Measure ℝ) :=
        fun i => integral_nonneg_of_ae (ae_of_all _ fun _ => sq_nonneg _)
      have hneBot : l.NeBot :=
        (map_neBot_iff μn).1 (hν.clusterPt.neBot.mono inf_le_right)
      exact ge_of_tendsto_of_frequently (hsquare_limit c)
        (@Frequently.of_forall ι l hneBot _ hnonneg)
    have hε_bound (ε : ℝ) (hε : 0 < ε) :
        ∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) ≤ M + ε := by
      have hMlt : M < M + ε := by linarith
      have hB : 0 ≤ M + ε := by linarith
      have hB_event : ∀ᶠ i in l,
          ∫ x, (x ^ k - c) ^ 2 ∂(μn i : Measure ℝ) ≤ M + ε :=
        (hsquare_limit c).eventually (Iio_mem_nhds hMlt) |>.mono fun _ h => le_of_lt h
      have hcont : Continuous fun x : ℝ => (x ^ k - c) ^ 2 :=
        ((continuous_id.pow k).sub continuous_const).pow 2
      have hclosed := isClosed_setOfPred_lintegral_le_probabilityMeasure
        ((ENNReal.continuous_ofReal.comp hcont).lowerSemicontinuous)
        (ENNReal.ofReal (M + ε))
      have hevent : ∀ᶠ i in l, μn i ∈
          {ρ : ProbabilityMeasure ℝ |
            ∫⁻ x, ENNReal.ofReal ((x ^ k - c) ^ 2) ∂(ρ : Measure ℝ) ≤
              ENNReal.ofReal (M + ε)} := by
        filter_upwards [hint (2 * k) le_rfl, hint k (by omega), hB_event]
          with i h2 hk hBi
        have hsq : Integrable (fun x : ℝ => (x ^ k - c) ^ 2) (μn i : Measure ℝ) := by
          have hpoly : Integrable
              (fun x : ℝ => x ^ (2 * k) - (2 * c) * x ^ k + c ^ 2) (μn i : Measure ℝ) :=
            (h2.sub (hk.const_mul (2 * c))).add (integrable_const _)
          exact hpoly.congr (ae_of_all _ fun x => (hsquare_identity c x).symm)
        rw [← ofReal_integral_eq_lintegral_ofReal hsq
          (ae_of_all _ fun x => sq_nonneg (x ^ k - c))]
        exact ENNReal.ofReal_le_ofReal hBi
      have hlintegral := hclosed.mem_of_mapClusterPt hν hevent
      have hlintegral' :
          ∫⁻ x, ENNReal.ofReal ((x ^ k - c) ^ 2) ∂(ν : Measure ℝ) ≤
            ENNReal.ofReal (M + ε) := by
        exact hlintegral
      have hreal : ENNReal.ofReal
          (∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ)) ≤ ENNReal.ofReal (M + ε) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hνsquare_integrable c)
          (ae_of_all _ fun x => sq_nonneg (x ^ k - c))] at hlintegral'
        exact hlintegral'
      exact (ENNReal.ofReal_le_ofReal_iff hB).mp hreal
    by_contra hnot
    have hε : 0 < (∫ x, (x ^ k - c) ^ 2 ∂(ν : Measure ℝ) - M) / 2 :=
      div_pos (sub_pos.mpr (lt_of_not_ge hnot)) (by norm_num)
    have hle := hε_bound _ hε
    linarith
  have hmoment : a = m k := by
    by_contra hne
    let c : ℝ := (m (2 * k) - q + 1) / (2 * (m k - a))
    have hden : 2 * (m k - a) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      apply sub_ne_zero.mpr
      intro heq
      exact hne heq.symm
    have hc : 2 * c * (m k - a) = m (2 * k) - q + 1 := by
      dsimp [c]
      field_simp [hden]
    have hineq := hbound_square c
    rw [hνsquare c] at hineq
    dsimp [c] at hc
    dsimp [a, q] at hineq hc
    nlinarith
  exact ⟨hlow k le_rfl, hmoment⟩

/-- A weak cluster point of probability measures with converging moments has finite moments,
equal to the limits. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.integrable_pow_and_integral_pow_eq_of_mapClusterPt
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ}
    {m : ℕ → ℝ} (hint : ∀ k, ∀ᶠ n in l,
      Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) l (𝓝 (m k)))
    (hν : MapClusterPt ν l μn) :
    (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) ∧
      ∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = m k := by
  have h k := integrable_pow_and_integral_pow_eq_of_mapClusterPt_fixed k
    (fun n _ => hint n) (fun n _ => hlim n) hν
  exact ⟨fun k => (h k).1, fun k => (h k).2⟩
end MethodOfMoments

end TauCeti

namespace MeasureTheory.ProbabilityMeasure

open TauCeti.MethodOfMoments

/-- **The method of moments.** Let `μn` be probability measures on `ℝ` whose moments are
eventually finite and converge to those of `μ`. If `μ` is determined by its moments among
probability measures with finite moments, then `μn` converges weakly to `μ`. -/
theorem tendsto_of_tendsto_integral_pow_of_unique
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
