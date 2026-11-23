/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.RingTheory.Valuation.AddValuation
import TauCeti.RingTheory.Valuation.NormNormalization

/-!
# Exact coefficients of the principal-minor series from a dominant minor

The row bounds `‖A i j‖ ≤ r i` only bound the coefficients of the principal-minor series
`det (1 - T A) = ∑ cₙ Tⁿ` from above, by `‖cₙ‖ ≤ sup_{#s = n} ∏ i ∈ s, r i`
(`Matrix.norm_charCoeff_le`). This file gives a criterion under which that bound is attained and
the norm of each coefficient is known exactly.

Let `A : Matrix ℕ ℕ K` over a complete ultrametric normed field, and let `d : ℕ → K` have
strictly decreasing norms tending to zero, with `‖A i j‖ ≤ ‖d i‖`. Write `B` for the normalised
matrix with entries `(d i)⁻¹ * A i j`. If the leading principal minor of `B` on
`range n = {0, …, n - 1}` has norm one, then

`‖cₙ‖ = ∏ i ∈ range n, ‖d i‖` (`Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one`).

The leading principal minor of `A` on `range n` has exactly this norm
(`Matrix.norm_principalMinor_eq_prod`), while every other principal minor of size `n` is
bounded by `(∏ i ∈ range (n - 1), ‖d i‖) * ‖d n‖`
(`Matrix.norm_principalMinor_le_prod_range_mul`), which is strictly smaller because the norms
decrease strictly. By the ultrametric inequality the leading minor dominates the convergent sum
defining `cₙ`.

Over a dense value group strict decrease does not force the norms to tend to zero, and the decay
hypothesis is needed for the minors to be summable at all. For a row-compact operator on
`C₀(ℕ, K)` the decay follows from the normalisation of the leading minors; see
`TauCeti.Analysis.Normed.Operator.Nonarchimedean.DominantMinor`.

In valuation terms, with `‖x‖ = b ^ (-v x)` for a real additive valuation `v` and a base
`b > 1`, the conclusion reads `v (cₙ) = ∑ i < n, v (d i)`
(`Matrix.addValuation_charCoeff_eq_sum_of_norm_principalMinor_eq_one`). The valuations `v (d i)`
increase strictly, so these partial sums are already convex: when every leading minor is
normalised, the Newton polygon of `det (1 - T A)` is `n ↦ ∑ i < n, v (d i)`
(`Matrix.newtonPolygon_charPowerSeries_eq_sum_of_norm_principalMinor_eq_one`). Its slopes are the
valuations `v (d i)`, each with multiplicity one: the multiplicity of `σ` is the number of indices
`i` with `v (d i) = σ`
(`Matrix.newtonSlopeMultiplicity_charPowerSeries_eq_ncard_of_norm_principalMinor_eq_one`).

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §5.
* K. S. Kedlaya, *A little p-adic numerical analysis*, MIT 18.787 notes (2007), §3.
-/

public section

open Filter Finset Topology

namespace Matrix

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {A : Matrix ℕ ℕ K} {d : ℕ → K}

/-- **Exact coefficients from a dominant minor.** Let `‖A i j‖ ≤ ‖d i‖`, where the norms of `d`
decrease strictly and tend to zero. If the normalised matrix with entries `(d i)⁻¹ * A i j` has
a principal minor of norm one on `range n`, then the `n`-th coefficient of the principal-minor
series `det (1 - T A)` has norm exactly `∏ i ∈ range n, ‖d i‖`. -/
theorem norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one [CompleteSpace K]
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hd₀ : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0))
    (hA : ∀ i j, ‖A i j‖ ≤ ‖d i‖) {n : ℕ}
    (hminor : ‖(of fun i j ↦ (d i)⁻¹ * A i j).principalMinor (range n)‖ = 1) :
    ‖A.charCoeff n‖ = ∏ i ∈ range n, ‖d i‖ := by
  -- Strictly decreasing nonnegative norms are positive.
  have hpos (i : ℕ) : 0 < ‖d i‖ := norm_pos_iff.2 (TauCeti.ne_zero_of_strictAnti_norm hdec i)
  rcases n with _ | n
  · simp
  let f : {s : Finset ℕ // #s = n + 1} → K := fun s ↦ A.principalMinor s
  let s₀ : {s : Finset ℕ // #s = n + 1} := ⟨range (n + 1), card_range _⟩
  have hsum : Summable f :=
    summable_principalMinor hA (by rwa [Nat.cofinite_eq_atTop]) (n + 1)
  have hdom : ‖f s₀‖ = ∏ i ∈ range (n + 1), ‖d i‖ :=
    norm_principalMinor_eq_prod (fun i _ ↦ norm_pos_iff.1 (hpos i)) hminor
  -- The remaining minors are bounded by a constant strictly below the leading one.
  set C := (∏ i ∈ range n, ‖d i‖) * ‖d (n + 1)‖
  have hC₀ : 0 ≤ C := mul_nonneg (prod_nonneg fun i _ ↦ norm_nonneg _) (norm_nonneg _)
  have hrest : ‖∑' s, if s = s₀ then 0 else f s‖ ≤ C := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC₀ fun s ↦ ?_
    split_ifs with h
    · simpa using hC₀
    · exact norm_principalMinor_le_prod_range_mul hdec.antitone hA s.property
        fun h' ↦ h (Subtype.ext h')
  have hlt : C < ∏ i ∈ range (n + 1), ‖d i‖ := by
    rw [prod_range_succ]
    exact mul_lt_mul_of_pos_left (hdec n.lt_succ_self) (prod_pos fun i _ ↦ hpos i)
  rw [charCoeff_def, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    hsum.tsum_eq_add_tsum_ite s₀, ← hdom]
  rw [← hdom] at hlt
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (hrest.trans_lt hlt).ne',
    max_eq_left (hrest.trans hlt.le)]

section Valuation

variable (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Exact coefficient valuations from a dominant minor.** Under the hypotheses of
`Matrix.norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one`, if the norm is recovered from a
real additive valuation `v` by `‖x‖ = b ^ (-v x)`, the `n`-th coefficient of `det (1 - T A)` has
valuation `∑ i ∈ range n, v (d i)`. -/
theorem addValuation_charCoeff_eq_sum_of_norm_principalMinor_eq_one [CompleteSpace K]
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hd₀ : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0))
    (hA : ∀ i j, ‖A i j‖ ≤ ‖d i‖) {n : ℕ}
    (hminor : ‖(of fun i j ↦ (d i)⁻¹ * A i j).principalMinor (range n)‖ = 1) :
    v (A.charCoeff n) = ∑ i ∈ range n, v (d i) := by
  have hprod : ∏ i ∈ range n, d i ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ ↦ TauCeti.ne_zero_of_strictAnti_norm hdec i
  -- The coefficient has the norm of the product `∏ i ∈ range n, d i`, hence its valuation.
  have hc : ‖A.charCoeff n‖ = b ^ (-(v (∏ i ∈ range n, d i)).untop₀) := by
    rw [norm_charCoeff_eq_prod_of_norm_principalMinor_eq_one hdec hd₀ hA hminor, ← norm_prod,
      hv _ hprod]
  rw [(v.norm_eq_rpow_iff hb hv).1 hc, neg_neg, WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.2 hprod),
    AddValuation.map_prod]

omit [IsUltrametricDist K] in
/-- If the norms of `d` decrease strictly, the partial sums of the valuations `v (d i)` are the
heights of the infinite slope data starting at the origin with slopes `v (d i)`. -/
private theorem exists_infiniteSlopeData_heights_eq_sum (hdec : StrictAnti fun i ↦ ‖d i‖) :
    ∃ D : TauCeti.InfiniteSlopeData ℝ, (∀ i, D.slope i = (v (d i)).untop₀) ∧
      D.heights = fun n ↦ ∑ i ∈ range n, v (d i) := by
  have hd := TauCeti.ne_zero_of_strictAnti_norm hdec
  -- Strictly decreasing norms `b ^ (-v (d i))` mean strictly increasing valuations.
  have hmono : Monotone fun i ↦ (v (d i)).untop₀ := by
    refine StrictMono.monotone fun i j hij ↦ ?_
    have h : ‖d j‖ < ‖d i‖ := hdec hij
    rw [hv _ (hd i), hv _ (hd j), Real.rpow_lt_rpow_left_iff hb] at h
    exact neg_lt_neg_iff.1 h
  refine ⟨⟨0, 0, fun i ↦ (v (d i)).untop₀, hmono⟩, fun _ ↦ rfl, funext fun n ↦ ?_⟩
  rw [TauCeti.InfiniteSlopeData.heights_def]
  simp only [zero_le, ite_true, Nat.sub_zero, zero_add, WithTop.coe_sum]
  exact sum_congr rfl fun i _ ↦ WithTop.coe_untop₀_of_ne_top (v.ne_top_iff.2 (hd i))

/-- **Exact Newton polygon from dominant minors.** Let `‖A i j‖ ≤ ‖d i‖`, where the norms of `d`
decrease strictly and tend to zero, and let every leading principal minor of the normalised
matrix `(d i)⁻¹ * A i j` have norm one. If the norm is recovered from a real additive valuation
`v` by `‖x‖ = b ^ (-v x)`, the Newton polygon of `det (1 - T A)` is `n ↦ ∑ i ∈ range n, v (d i)`. -/
theorem newtonPolygon_charPowerSeries_eq_sum_of_norm_principalMinor_eq_one [CompleteSpace K]
    (hdec : StrictAnti fun i ↦ ‖d i‖) (hd₀ : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0))
    (hA : ∀ i j, ‖A i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(of fun i j ↦ (d i)⁻¹ * A i j).principalMinor (range n)‖ = 1) :
    A.charPowerSeries.newtonPolygon v = fun n ↦ ∑ i ∈ range n, v (d i) := by
  obtain ⟨D, -, hD⟩ := exists_infiniteSlopeData_heights_eq_sum v hb hv hdec
  -- The coefficient heights are the partial sums, which are already convex.
  have hcoeff : (fun n ↦ v (PowerSeries.coeff n A.charPowerSeries)) = D.heights := by
    rw [hD]
    funext n
    rw [coeff_charPowerSeries,
      addValuation_charCoeff_eq_sum_of_norm_principalMinor_eq_one v hb hv hdec hd₀ hA (hminor n)]
  rw [PowerSeries.newtonPolygon_def, hcoeff, D.isConvexSeq_heights.lowerConvexEnvelope_eq, hD]

/-- **Exact slopes from dominant minors.** Under the hypotheses of
`Matrix.newtonPolygon_charPowerSeries_eq_sum_of_norm_principalMinor_eq_one`, the multiplicity of
a slope `σ` in the Newton polygon of `det (1 - T A)` is the number of indices `i` with
`v (d i) = σ`. As the valuations `v (d i)` increase strictly, each of them is a slope of
multiplicity one, and no other real number is a slope. -/
theorem newtonSlopeMultiplicity_charPowerSeries_eq_ncard_of_norm_principalMinor_eq_one
    [CompleteSpace K] (hdec : StrictAnti fun i ↦ ‖d i‖)
    (hd₀ : Tendsto (fun i ↦ ‖d i‖) atTop (𝓝 0)) (hA : ∀ i j, ‖A i j‖ ≤ ‖d i‖)
    (hminor : ∀ n, ‖(of fun i j ↦ (d i)⁻¹ * A i j).principalMinor (range n)‖ = 1) (σ : ℝ) :
    A.charPowerSeries.newtonSlopeMultiplicity v σ = {i | v (d i) = σ}.ncard := by
  obtain ⟨D, hslope, hD⟩ := exists_infiniteSlopeData_heights_eq_sum v hb hv hdec
  rw [PowerSeries.newtonSlopeMultiplicity_eq_ncard_of_heights_eq (hD.trans
    (newtonPolygon_charPowerSeries_eq_sum_of_norm_principalMinor_eq_one v hb hv hdec hd₀ hA
      hminor).symm)]
  congr 1
  ext i
  have hd : v (d i) ≠ ⊤ := v.ne_top_iff.2 (TauCeti.ne_zero_of_strictAnti_norm hdec i)
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hslope, ← WithTop.coe_eq_coe,
    WithTop.coe_untop₀_of_ne_top hd]

end Valuation

end Matrix
