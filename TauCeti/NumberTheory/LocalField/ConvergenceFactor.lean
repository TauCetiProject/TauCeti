/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# Form measures on the multiplicative group need convergence factors

Let `K` be a nonarchimedean local field whose residue field has `q` elements, and let `μ` be the
additive Haar measure on `K` with `μ 𝒪[K] = 1`. The invariant form `ω = dx/x` on `𝔾_m` defines the
local measure `|ω| = |x|_K⁻¹ μ`, the measure with density `|x|_K⁻¹` with respect to `μ`. On the
units `𝒪[K]ˣ = {x | v(x) = 1}` the density is `1`, and the maximal ideal `ϖ 𝒪[K]` has mass `q⁻¹`,
so the units have mass `1 - q⁻¹` for both `μ` and `|ω|`
(`MeasureTheory.Measure.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one`).

For `K = ℚ_[p]` this mass is `1 - p⁻¹`. The partial products `∏_{p < N} (1 - p⁻¹)` tend to `0`,
because the sum of the reciprocals of the primes diverges (`TauCeti.tendsto_prod_primesBelow`).
So the family of local measures `|ω|_p` does not give the units `ℤ_p^×` mass `1` at all but
finitely many primes, which is the normalization hypothesis of the restricted product of Haar
measures (`TauCeti.restrictedHaar`), and no single rescaling `c • |ω|_p` repairs
this (`TauCeti.not_eventually_smul_withDensity_setOf_valuation_eq_one`). The Tamagawa measure
of `𝔾_m` uses the convergence factors `(1 - p⁻¹)⁻¹` instead.

## Main declarations

* `MeasureTheory.Measure.addHaar_setOf_valuation_eq_one`: the units of `𝒪[K]` have Haar mass
  `(1 - q⁻¹) μ 𝒪[K]`.
* `MeasureTheory.Measure.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one`: the same
  for the form measure `|x|_K⁻¹ μ`.
* `TauCeti.padicFormMeasure_setOf_norm_eq_one`: over `ℚ_[p]`, the form measure of `ℤ_p^×` is
  `1 - p⁻¹`.
* `TauCeti.tendsto_prod_primesBelow`: `∏_{p < N} (1 - p⁻¹) → 0`.
* `TauCeti.not_eventually_smul_withDensity_setOf_valuation_eq_one`: for local fields with
  pairwise distinct residue cardinalities, such as the `ℚ_[p]`, no rescaling of the form measures
  gives the units mass one at all but finitely many places.

## References

* Z. Rosengarten, *Tamagawa numbers and other invariants of pseudo-reductive groups over global
  function fields*, arXiv:1806.10723v3, §1, p. 2.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §5.5, p. 21.
-/

public section

open MeasureTheory Measure Filter Topology TauCeti ValuativeRel
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory.Measure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

omit [MeasurableSpace K] [BorelSpace K] in
/-- The elements of valuation one are the complement in `𝒪[K]` of the maximal ideal
`ϖ • 𝒪[K]`, for any irreducible element `ϖ` of `𝒪[K]`. -/
private theorem setOf_valuation_eq_one_eq_sdiff {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    {x : K | valuation K x = 1} = (𝒪[K] : Set K) \ (ϖ : K) • (𝒪[K] : Set K) := by
  have hm : ((↑) : 𝒪[K] → K) '' ↑𝓂[K] = (ϖ : K) • (𝒪[K] : Set K) := by
    simpa using hϖ.image_maximalIdeal_pow_eq_smul (A := K) 1
  rw [← hm]
  have hint := Valuation.integer.integers (valuation K)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_image,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_exists, not_and]
  refine ⟨fun hx ↦ ⟨(Valuation.mem_integer_iff _ x).2 hx.le, fun y hy hyx ↦
    hy (hint.isUnit_iff_valuation_eq_one.2 (hyx.symm ▸ hx :))⟩, fun ⟨hx, h⟩ ↦ ?_⟩
  by_contra hne
  exact h ⟨x, hx⟩ (fun hu ↦ hne (hint.isUnit_iff_valuation_eq_one.1 hu)) rfl

omit [MeasurableSpace K] [BorelSpace K] in
private theorem isCompact_integer : IsCompact (𝒪[K] : Set K) := by
  simpa using (integerPositiveCompacts K).isCompact

/-- The units of the ring of integers, the elements of valuation one, form a measurable set. -/
theorem measurableSet_setOf_valuation_eq_one : MeasurableSet {x : K | valuation K x = 1} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [setOf_valuation_eq_one_eq_sdiff hϖ]
  exact isCompact_integer.isClosed.measurableSet.diff
    (isCompact_integer.smul (ϖ : K)).isClosed.measurableSet

/-- The units of the ring of integers of a nonarchimedean local field, the elements of valuation
one, have Haar mass `(1 - q⁻¹) μ 𝒪[K]`, where `q` is the cardinality of the residue field: they are
the complement in `𝒪[K]` of the maximal ideal `ϖ 𝒪[K]`, of mass `q⁻¹ μ 𝒪[K]`. -/
theorem addHaar_setOf_valuation_eq_one :
    μ {x : K | valuation K x = 1} = (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) * μ 𝒪[K] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have habs : (normalizedAbsoluteValue K (ϖ : K) : ℝ≥0) = (Nat.card 𝓀[K] : ℝ≥0)⁻¹ := by
    have h := distribHaarChar_of_isUniformizer (K := K) (π := Units.mk0 _ hϖ0)
      ((isUniformizer_iff_exists_irreducible K _).2 ⟨ϖ, hϖ, rfl⟩)
    rwa [distribHaarChar_eq_normalizedAbsoluteValue, Units.val_mk0] at h
  have hsub : (ϖ : K) • (𝒪[K] : Set K) ⊆ 𝒪[K] := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem ϖ.property hy
  have hcpt := (isCompact_integer (K := K)).smul (ϖ : K)
  rw [setOf_valuation_eq_one_eq_sdiff hϖ, measure_sdiff hsub
    hcpt.isClosed.measurableSet.nullMeasurableSet hcpt.measure_lt_top.ne,
    addHaar_smul_eq_normalizedAbsoluteValue_mul, habs,
    ENNReal.sub_mul fun _ _ ↦ isCompact_integer.measure_lt_top.ne, one_mul]
  simp

/-- **The form measure of the units.** The measure `|dx/x|_K`, with density `|x|_K⁻¹` with respect
to an additive Haar measure `μ`, gives the units of `𝒪[K]` the mass `(1 - q⁻¹) μ 𝒪[K]`, since the
density is `1` there. -/
theorem withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one :
    (μ.withDensity fun x ↦ ((normalizedAbsoluteValue K x : ℝ≥0) : ℝ≥0∞)⁻¹)
        {x : K | valuation K x = 1} =
      (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) * μ 𝒪[K] := by
  rw [withDensity_apply _ measurableSet_setOf_valuation_eq_one,
    setLIntegral_congr_fun (g := fun _ ↦ 1) measurableSet_setOf_valuation_eq_one fun x hx ↦ by
      simp [(normalizedAbsoluteValue_eq_one_iff x).2 hx],
    setLIntegral_one, addHaar_setOf_valuation_eq_one]

end MeasureTheory.Measure

namespace TauCeti

section Padic

variable (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]

/-- **The form measure of `ℤ_p^×`.** For the additive Haar measure `μ` on `ℚ_[p]` with
`μ ℤ_[p] = 1`, the measure `|dx/x|_p` with density `‖x‖⁻¹` gives the units `‖x‖ = 1` the mass
`1 - p⁻¹`. -/
theorem withDensity_inv_nnnorm_setOf_norm_eq_one (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (hμ : μ 𝒪[ℚ_[p]] = 1) :
    (μ.withDensity fun x ↦ (‖x‖₊ : ℝ≥0∞)⁻¹) {x : ℚ_[p] | ‖x‖ = 1} = 1 - (p : ℝ≥0∞)⁻¹ := by
  have hset : {x : ℚ_[p] | ‖x‖ = 1} = {x : ℚ_[p] | valuation ℚ_[p] x = 1} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← normalizedAbsoluteValue_eq_one_iff,
      ← NNRat.cast_inj (α := ℝ≥0), NNRat.cast_one, Padic.normalizedAbsoluteValue_eq_nnnorm,
      ← NNReal.coe_eq_one,
      coe_nnNorm]
  have h := μ.withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one
  simp only [Padic.normalizedAbsoluteValue_eq_nnnorm, Padic.natCard_residueField, hμ, mul_one] at h
  rwa [hset]

end Padic

/-- **Form measures need convergence factors.** Let `K i` be a family of nonarchimedean local
fields, indexed by an infinite type, whose residue fields have pairwise distinct cardinalities
`q i`, such as the `ℚ_[p]` (`Padic.natCard_residueField`), and let `μ i` be the additive Haar
measure on `K i` with `μ i 𝒪[K i] = 1`. No single rescaling `c • |dx/x|_i` of the form measures
gives the units of `𝒪[K i]` mass one for all but finitely many `i`: their masses are
`c (1 - q_i⁻¹)`, which take the value `1` for at most one `i`. With `c = 1` this says that the
family `|dx/x|_i` fails the normalization hypothesis of the restricted product of Haar measures
(`TauCeti.restrictedHaar`). -/
theorem not_eventually_smul_withDensity_setOf_valuation_eq_one {ι : Type*} [Infinite ι]
    {K : ι → Type*} [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)]
    [∀ i, IsNonarchimedeanLocalField (K i)] [∀ i, MeasurableSpace (K i)]
    [∀ i, BorelSpace (K i)] (μ : ∀ i, Measure (K i)) [∀ i, (μ i).IsAddHaarMeasure]
    (hμ : ∀ i, μ i 𝒪[K i] = 1) (hq : Function.Injective fun i ↦ Nat.card 𝓀[K i]) (c : ℝ≥0∞) :
    ¬ ∀ᶠ i in cofinite,
      (c • (μ i).withDensity fun x ↦ ((normalizedAbsoluteValue (K i) x : ℝ≥0) : ℝ≥0∞)⁻¹)
        {x : K i | valuation (K i) x = 1} = 1 := by
  intro h
  simp only [smul_apply, withDensity_inv_normalizedAbsoluteValue_setOf_valuation_eq_one, hμ,
    mul_one, smul_eq_mul] at h
  obtain ⟨i, hi, j, hj, hij⟩ := (Set.infinite_of_finite_compl (Filter.mem_cofinite.1 h)).nontrivial
  have hpos (k : ι) : 0 < Nat.card 𝓀[K k] := Nat.card_pos
  have hle (k : ι) : (Nat.card 𝓀[K k] : ℝ≥0∞)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (by exact_mod_cast hpos k)
  have hne (k : ι) : (Nat.card 𝓀[K k] : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (by exact_mod_cast (hpos k).ne')
  have h' := (ENNReal.eq_inv_of_mul_eq_one_left hi).symm.trans
    (ENNReal.eq_inv_of_mul_eq_one_left hj)
  rw [inv_inj, (ENNReal.cancel_of_ne ENNReal.one_ne_top).tsub_right_inj (ENNReal.cancel_of_ne
    (hne i)) (ENNReal.cancel_of_ne (hne j)) (hle i) (hle j), inv_inj, Nat.cast_inj] at h'
  exact hij (hq h')

/-- **The Euler product of `1 - p⁻¹` diverges to `0`.** The partial products
`∏_{p < N} (1 - p⁻¹)` over the primes tend to `0`, because the sum of the reciprocals of the
primes diverges (Mathlib's `not_summable_one_div_on_primes`). -/
theorem tendsto_prod_primesBelow :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ N.primesBelow, (1 - (p : ℝ)⁻¹)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N : ℕ ↦ ∑ p ∈ N.primesBelow, (p : ℝ)⁻¹) atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦
      Set.indicator_nonneg (fun n _ ↦ by positivity) n).1 not_summable_one_div_on_primes
    refine h.congr fun N ↦ ?_
    rw [Finset.sum_indicator_eq_sum_filter, Nat.primesBelow_eq_filter_range]
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsum) (fun N ↦ ?_) (fun N ↦ ?_)
  · refine Finset.prod_nonneg fun p hp ↦ sub_nonneg.2 (inv_le_one_of_one_le₀ ?_)
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le
  · simp only [Function.comp_apply, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p hp ↦ sub_nonneg.2 (inv_le_one_of_one_le₀ ?_))
      fun p _ ↦ Real.one_sub_le_exp_neg _
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le

end TauCeti
