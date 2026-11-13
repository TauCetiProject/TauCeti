/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Improper-integral asymptotics and logarithmic decay

This file extends Mathlib's improper-integral estimates with an asymptotic estimate for weighted
integrals, an Abelian limit for the averages `ε ∫_1^∞ t ^ (-ε - 1) g t`, integrability of
`(x ^ 2 + c ^ 2)⁻¹` for `c ≠ 0`, integrability at infinity of `(t (1 + log t) ^ 2)⁻¹`, and the
closed form `∫_A^∞ dy / y² = 1 / A` as a Lebesgue integral.

## Main declarations

* `TauCeti.integrable_inv_sq_add_sq`: `(x ^ 2 + c ^ 2)⁻¹` is integrable for `c ≠ 0`.

* `TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_of_log_growth`: sufficient logarithmic
  growth makes an exponentially weighted polynomial integrable.
* `TauCeti.eventually_quadratic_div_log_abs_gt`: quadratic growth dominates logarithmic growth
  as `|x| → ∞`.

* `TauCeti.lintegral_Ioi_inv_sq`: `∫⁻ y in Ioi A, (1 / ‖y‖₊) ^ 2 = ofReal A⁻¹` for `0 < A`, the
  integrand being the density of the hyperbolic area measure.

* `TauCeti.integrableAtFilter_inv_mul_one_add_log_sq`: the function
  `t ↦ (t (1 + log t) ^ 2)⁻¹` is integrable at infinity.
* `TauCeti.isLittleO_integral_rpow_sub_one_mul`: a remainder `E t = o(t)` has
  `∫ t in 1..x, t ^ (τ - 1) * E t = o(x ^ (τ + 1))`.
* `TauCeti.tendsto_smul_integral_Ioi_rpow_smul_nhdsGT_zero`: if `g t → L` as `t → ∞`, then
  `ε ∫_1^∞ t ^ (-ε - 1) g t → L` as `ε → 0⁺`. Through Mathlib's `LSeries_eq_mul_integral` this
  is the Abelian theorem for Dirichlet series.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Real Set
open scoped Topology

/-- A continuous potential with sufficient logarithmic growth dominates a
polynomial factor and makes the resulting exponential weight integrable. -/
theorem integrable_one_add_abs_rpow_mul_exp_neg_of_log_growth {p a c : ℝ} {V : ℝ → ℝ}
    (hp : 0 ≤ p) (ha : 0 < a) (hq : p - a * c < -1)
    (hV : Continuous V)
    (hGrowth : ∀ᶠ x in Filter.comap abs Filter.atTop, c * log |x| ≤ V x) :
    Integrable (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x)) volume := by
  let q : ℝ := p - a * c
  have hq' : q < -1 := hq
  have hTail : ∀ᶠ x in Filter.comap abs Filter.atTop, c * log |x| ≤ V x := hGrowth
  rw [Filter.eventually_comap] at hTail
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hTail
  let R' : ℝ := max R 1
  have hR' : 1 ≤ R' := le_max_right _ _
  have hRbound (x : ℝ) (hx : R' ≤ |x|) : c * log |x| ≤ V x := by
    exact hR _ (le_trans (le_max_left _ _) hx) x rfl
  have hpoint (x : ℝ) (hx : 1 ≤ |x|) (hVx : c * log |x| ≤ V x) :
      (1 + |x|) ^ p * exp (-a * V x) ≤ 2 ^ p * |x| ^ q := by
    have hxabs : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
    have hpoly : (1 + |x|) ^ p ≤ (2 * |x|) ^ p :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hp
    have hexp : exp (-a * V x) ≤ |x| ^ (-a * c) := by
      rw [Real.rpow_def_of_pos hxabs]
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonpos_left hVx (by linarith : -a ≤ 0)
      nlinarith [hmul]
    calc
      _ ≤ (2 * |x|) ^ p * |x| ^ (-a * c) :=
        mul_le_mul hpoly hexp (by positivity) (by positivity)
      _ = 2 ^ p * |x| ^ q := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [mul_assoc, ← Real.rpow_add hxabs]
        congr 2
        dsimp [q]
        ring
  have hpowPos : IntegrableOn (fun x : ℝ => x ^ q) (Ioi R') volume :=
    integrableOn_Ioi_rpow_of_lt hq' (lt_of_lt_of_le zero_lt_one hR')
  have hpowNeg : IntegrableOn (fun x : ℝ => (-x) ^ q) (Iio (-R')) volume := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iio, neg_neg]
    exact hpowPos
  have hg : Continuous (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x)) := by
    have hbase : Continuous (fun x : ℝ => 1 + |x|) := by fun_prop
    have hexp : Continuous (fun x : ℝ => exp (-a * V x)) := by fun_prop
    exact (hbase.rpow_const (fun x => Or.inl (by positivity))).mul hexp
  have hneg : (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x)) =O[Filter.atBot]
      (fun x : ℝ => (-x) ^ q) := by
    apply Asymptotics.IsBigO.of_bound (2 ^ p)
    filter_upwards [Filter.eventually_lt_atBot (-R')] with x hx
    have hnegx : R' < -x := by linarith
    have habs : |x| = -x := abs_of_nonpos (by linarith)
    have hnonneg : 0 ≤ (1 + |x|) ^ p * exp (-a * V x) := by positivity
    have hbound := hpoint x (by rw [habs]; linarith [hnegx, hR'])
      (hRbound x (by rw [habs]; exact le_of_lt hnegx))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ -x) q)]
    simpa only [habs] using hbound
  have hpos : (fun x : ℝ => (1 + |x|) ^ p * exp (-a * V x)) =O[Filter.atTop]
      (fun x : ℝ => x ^ q) := by
    apply Asymptotics.IsBigO.of_bound (2 ^ p)
    filter_upwards [Filter.eventually_gt_atTop R'] with x hx
    have hxge1 : 1 ≤ x := le_of_lt (lt_of_le_of_lt hR' hx)
    have habs : |x| = x := abs_of_nonneg (by linarith)
    have hnonneg : 0 ≤ (1 + |x|) ^ p * exp (-a * V x) := by positivity
    have hbound := hpoint x (by rw [habs]; exact hxge1)
      (hRbound x (by rw [habs]; exact le_of_lt hx))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) q)]
    simpa only [habs] using hbound
  exact hg.locallyIntegrable.integrable_of_isBigO_atBot_atTop hneg
    ⟨Iio (-R'), Filter.Iio_mem_atBot _, hpowNeg⟩ hpos
    ⟨Ioi R', Filter.Ioi_mem_atTop _, hpowPos⟩

/-- Every fixed positive threshold is eventually below `x² / (2 log |x|)`
as `|x|` tends to infinity. -/
theorem eventually_quadratic_div_log_abs_gt (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      c < (x ^ 2 / 2) / log |x| := by
  rw [Filter.eventually_comap]
  apply Filter.eventually_atTop.2
  refine ⟨max (2 * c + 1) 2, ?_⟩
  intro t ht x hxt
  have htA : 2 * c + 1 ≤ t := le_trans (le_max_left _ _) ht
  have htB : 2 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  have htgt : 1 < t := lt_of_lt_of_le one_lt_two htB
  have hlogpos : 0 < log t := Real.log_pos htgt
  have hlogle : log t ≤ t :=
    (Real.log_le_sub_one_of_pos htpos).trans (by linarith)
  have hmargin : 0 < t / 2 - c := by linarith
  have hquad : c * t < t ^ 2 / 2 := by
    have := mul_pos htpos hmargin
    nlinarith
  rw [← sq_abs, hxt, lt_div_iff₀ hlogpos]
  exact (mul_le_mul_of_nonneg_left hlogle hc.le).trans_lt hquad

/-- The inverse quadratic `x ↦ (x ^ 2 + c ^ 2)⁻¹` is integrable when `c ≠ 0`. -/
theorem integrable_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun x : ℝ ↦ (x ^ 2 + c ^ 2)⁻¹) := by
  have hscale (x : ℝ) : (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ = (x ^ 2 + c ^ 2)⁻¹ := by
    field_simp [hc]
    ring
  exact ((integrable_inv_one_add_sq.comp_div hc).const_mul (c ^ 2)⁻¹).congr
    (Eventually.of_forall hscale)

/-- **A remainder `o(t)` integrates to `o(x ^ (τ + 1))` against `t ^ (τ - 1)`.** If `E` is
interval integrable above `1` and `E t = o(t)`, then for every exponent `τ > -1` the weighted
integral `∫ t in 1..x, t ^ (τ - 1) * E t` is `o(x ^ (τ + 1))`. -/
theorem isLittleO_integral_rpow_sub_one_mul {E : ℝ → ℝ} {τ : ℝ} (hτ : -1 < τ)
    (hE_int : ∀ x, 1 ≤ x → IntervalIntegrable E volume 1 x) (hE : E =o[atTop] id) :
    (fun x : ℝ ↦ ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * E t) =o[atTop] fun x ↦ x ^ (τ + 1) := by
  have hτ1 : 0 < τ + 1 := by linarith
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t ↦ t ^ (τ - 1) * E t) volume a b := by
    have hE' : IntervalIntegrable E volume a b := (hE_int b (ha.trans hab)).mono_set <| by
      rw [uIcc_of_le (ha.trans hab), uIcc_of_le hab]
      exact Icc_subset_Icc ha le_rfl
    refine hE'.continuousOn_mul fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
  rw [isLittleO_iff]
  intro ε hε
  -- Beyond a cutoff `T`, `|E t| ≤ ε' t` with `ε' = ε (τ + 1) / 2`.
  set ε' := ε * (τ + 1) / 2 with hε'
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((isLittleO_iff.mp hE (by positivity : 0 < ε')).and (eventually_ge_atTop (1 : ℝ)))
  have hT1 : 1 ≤ T := (hT T le_rfl).2
  have hbound (t : ℝ) (ht : T ≤ t) : |E t| ≤ ε' * t := by
    have h := (hT t ht).1
    have ht0 : 0 ≤ t := by linarith [(hT t ht).2]
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg ht0] at h
  -- The initial segment `∫ t in 1..T` is a constant, eventually below `ε / 2 * x ^ (τ + 1)`.
  set M := |∫ t in (1 : ℝ)..T, t ^ (τ - 1) * E t|
  filter_upwards [eventually_ge_atTop T,
    (tendsto_rpow_atTop hτ1).eventually_ge_atTop (2 * M / ε)] with x hx hxM
  have hxpow : 0 ≤ x ^ (τ + 1) := Real.rpow_nonneg (by linarith) _
  have hTpow : 0 ≤ T ^ (τ + 1) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxpow,
    ← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hT1) (hint hT1 hx)]
  have htail : |∫ t in T..x, t ^ (τ - 1) * E t| ≤
      ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) := by
    calc |∫ t in T..x, t ^ (τ - 1) * E t|
        ≤ ∫ t in T..x, |t ^ (τ - 1) * E t| := intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in T..x, ε' * t ^ τ := by
          refine intervalIntegral.integral_mono_on hx (hint hT1 hx).abs
            ((intervalIntegral.intervalIntegrable_rpow' hτ).const_mul ε') fun t ht ↦ ?_
          have ht0 : 0 < t := by linarith [ht.1]
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
          calc t ^ (τ - 1) * |E t| ≤ t ^ (τ - 1) * (ε' * t) := by
                gcongr
                exact hbound t ht.1
            _ = ε' * t ^ τ := by
                rw [Real.rpow_sub_one ht0.ne']
                field_simp
      _ = ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hτ)]
  have hM : M ≤ ε / 2 * x ^ (τ + 1) := by
    rw [div_le_iff₀ hε] at hxM
    linarith
  have hε'x : ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) ≤ ε / 2 * x ^ (τ + 1) := by
    have : ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) =
        ε / 2 * (x ^ (τ + 1) - T ^ (τ + 1)) := by
      rw [hε']
      field_simp
    rw [this]
    nlinarith
  calc |(∫ t in (1 : ℝ)..T, t ^ (τ - 1) * E t) + ∫ t in T..x, t ^ (τ - 1) * E t|
      ≤ M + |∫ t in T..x, t ^ (τ - 1) * E t| := abs_add_le _ _
    _ ≤ ε * x ^ (τ + 1) := by linarith

/-- **An Abelian limit for the weights `ε t ^ (-ε - 1)`.** If `g` is locally integrable on
`[1, ∞)` and `g t → L` as `t → ∞`, then the averages `ε ∫_1^∞ t ^ (-ε - 1) g t` of `g` against
the probability densities `ε t ^ (-ε - 1)` on `(1, ∞)` tend to `L` as `ε → 0⁺`. -/
theorem tendsto_smul_integral_Ioi_rpow_smul_nhdsGT_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} {L : E}
    (hg : LocallyIntegrableOn g (Ici 1)) (hlim : Tendsto g atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ ↦ ε • ∫ t in Ioi 1, t ^ (-ε - 1) • g t) (𝓝[>] 0) (𝓝 L) := by
  have hw {ε : ℝ} (hε : 0 < ε) : IntegrableOn (fun t : ℝ ↦ t ^ (-ε - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hw_eq {ε : ℝ} (hε : 0 < ε) : ε * ∫ t in Ioi (1 : ℝ), t ^ (-ε - 1) = 1 := by
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow, sub_add_cancel]
    field_simp
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- Beyond `T'` the function `g` is within `δ / 2` of `L`; the part over `(1, T']` is weighted
  -- by at most `ε`, so it contributes at most `ε K`.
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hlim.eventually (Metric.closedBall_mem_nhds L (half_pos hδ)))
  set T' := max T 1
  set K := ∫ t in Ioc 1 T', ‖g t - L‖
  have hgL : IntegrableOn (fun t ↦ g t - L) (Ioc 1 T') :=
    ((hg.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).mono_set
      Ioc_subset_Icc_self).sub (integrableOn_const (by simp))
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * K < δ / 2 := by
    have : Tendsto (fun ε : ℝ ↦ ε * K) (𝓝[>] 0) (𝓝 (0 * K)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul_const K
    exact this.eventually_lt_const (by simpa using half_pos hδ)
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hεK (hε : 0 < ε)
  -- An integrable majorant `b` of `t ^ (-ε - 1) • (g t - L)` on `(1, ∞)`.
  set b : ℝ → ℝ := fun t ↦ (Ioc 1 T').indicator (fun t ↦ ‖g t - L‖) t + δ / 2 * t ^ (-ε - 1)
  have hb_ind : IntegrableOn ((Ioc 1 T').indicator fun t ↦ ‖g t - L‖) (Ioi 1) :=
    (IntegrableOn.integrable_indicator hgL.norm measurableSet_Ioc).integrableOn
  have hb : IntegrableOn b (Ioi 1) := hb_ind.add ((hw hε).const_mul _)
  have hbound : ∀ t ∈ Ioi (1 : ℝ), ‖t ^ (-ε - 1) • (g t - L)‖ ≤ b t := by
    intro t (ht : 1 < t)
    have hw0 : 0 ≤ t ^ (-ε - 1) := Real.rpow_nonneg (by linarith) _
    have hw1 : t ^ (-ε - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le (by linarith)
    rw [norm_smul, Real.norm_of_nonneg hw0]
    by_cases htT : t ≤ T'
    · have hmem : t ∈ Ioc 1 T' := ⟨ht, htT⟩
      have hbt : b t = ‖g t - L‖ + δ / 2 * t ^ (-ε - 1) := by simp [b, indicator_of_mem hmem]
      rw [hbt]
      nlinarith [norm_nonneg (g t - L)]
    · have hmem : t ∉ Ioc 1 T' := fun h ↦ htT h.2
      have hbt : b t = δ / 2 * t ^ (-ε - 1) := by simp [b, indicator_of_notMem hmem]
      rw [hbt]
      have : ‖g t - L‖ ≤ δ / 2 := by
        simpa [dist_eq_norm] using hT t ((le_max_left T 1).trans (not_le.mp htT).le)
      nlinarith
  have hbound_ae : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), ‖t ^ (-ε - 1) • (g t - L)‖ ≤ b t :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hbound)
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-ε - 1) • (g t - L))
      (volume.restrict (Ioi 1)) := by
    refine AEStronglyMeasurable.smul ?_ ?_
    · exact (ContinuousOn.rpow_const continuousOn_id fun t ht ↦
        Or.inl (zero_lt_one.trans ht).ne').aestronglyMeasurable measurableSet_Ioi
    · exact (hg.aestronglyMeasurable.mono_set Ioi_subset_Ici_self).sub
        aestronglyMeasurable_const
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (-ε - 1) • (g t - L)) (Ioi 1) :=
    hb.mono' hmeas hbound_ae
  -- Since the weights have total mass one, subtracting `L` subtracts `L` from the average.
  have hsplit : ε • ∫ t in Ioi 1, t ^ (-ε - 1) • g t =
      ε • (∫ t in Ioi 1, t ^ (-ε - 1) • (g t - L)) + L := by
    have : (fun t : ℝ ↦ t ^ (-ε - 1) • g t) =
        fun t ↦ t ^ (-ε - 1) • (g t - L) + t ^ (-ε - 1) • L := by
      ext t
      rw [← smul_add, sub_add_cancel]
    rw [this, integral_add hint ((hw hε).smul_const L), integral_smul_const, smul_add,
      smul_smul, hw_eq hε, one_smul]
  have hb_eq : ∫ t in Ioi 1, b t = K + δ / 2 * ∫ t in Ioi (1 : ℝ), t ^ (-ε - 1) := by
    rw [integral_add hb_ind ((hw hε).const_mul _), integral_const_mul,
      setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self]
  rw [dist_eq_norm, hsplit, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hε.le]
  calc ε * ‖∫ t in Ioi 1, t ^ (-ε - 1) • (g t - L)‖
      ≤ ε * ∫ t in Ioi 1, b t := by
        gcongr
        exact norm_integral_le_of_norm_le hb hbound_ae
    _ = ε * K + δ / 2 := by rw [hb_eq, mul_add, mul_left_comm, hw_eq hε, mul_one]
    _ < δ := by linarith

/-- The function `(t (1 + log t) ^ 2)⁻¹` is integrable at infinity. On `Ioi 1` it is dominated
by Mathlib's log-Cauchy density `(t (1 + (log t) ^ 2))⁻¹`. -/
theorem integrableAtFilter_inv_mul_one_add_log_sq :
    IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + Real.log u) ^ 2)⁻¹) atTop := by
  refine ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  have hmaj : IntegrableOn (fun u : ℝ ↦ (u * (1 + Real.log u ^ 2))⁻¹) (Ioi (1 : ℝ)) :=
    ((integrableOn_Ioi_zero_inv_mul_one_add_log_sq (b := 1) one_ne_zero).congr_fun
      (fun u _ ↦ by rw [one_mul]) measurableSet_Ioi).mono_set (Ioi_subset_Ioi zero_le_one)
  refine MeasureTheory.Integrable.mono hmaj (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := hu
  have hL : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1.le
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  nlinarith

/-- **The improper integral of `1 / y²`**: `∫_A^∞ dy / y² = 1 / A` for `0 < A`, as a Lebesgue
integral of the nonnegative function `(1 / ‖y‖₊) ^ 2`. -/
theorem lintegral_Ioi_inv_sq {A : ℝ} (hA : 0 < A) :
    ∫⁻ y in Ioi A, (((1 / ‖y‖₊) ^ 2 : NNReal) : ENNReal) = ENNReal.ofReal A⁻¹ := by
  have hint := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hA
  have hval : ∫ y in Ioi A, y ^ (-2 : ℝ) = A⁻¹ := by
    convert integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hA using 1
    norm_num [Real.rpow_neg_one]
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦
      Real.rpow_nonneg (hA.trans hy).le _)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy : 0 < y := hA.trans hy
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [Real.rpow_neg hy.le, Real.nnnorm_of_nonneg hy.le]

end TauCeti
