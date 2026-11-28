/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GeneralizedIndex
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Denominator
import TauCeti.NumberTheory.NumberField.FrequencySum

/-!
# Frequency bounds for finite sets of places

In a Fourier bound over the infinite places and a finite set `S` of finite places, the
positive power of the finite index is cancelled by the decay at infinity. The denominator
index retains the full denominator norm if the frequency is integral away from `S`.
We use the splitting of the finite adeles to read a tuple of local coordinates as an adele
with coordinate `1` away from `S`.

The frequency estimate follows `New.Filling.sum_frequencies_le` in
`grh/src/New/Spanning/MainTerm/GlobalSieve.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField
open scoped NumberField.AdeleRing nonZeroDivisors

namespace NumberField.FiniteAdeleRing

variable {K : Type*} [Field K] [NumberField K]

/-- For a nonzero `S`-integer, the generalised index at `S` is bounded by the absolute field
norm: the omitted coordinates form an integral finite idele, of index at least `1`. -/
theorem genIndex_awayEquiv_symm_one_le {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    {x : K} (hx0 : x ≠ 0) (hx : x ∈ S.integer K) :
    genIndex K ((awayEquiv (𝓞 K) K hS).symm ((fun v : S ↦ (x : v.val.adicCompletion K)), 1)) ≤
      |Algebra.norm ℚ x| := by
  let e := awayEquiv (𝓞 K) K hS
  let a := algebraMap K 𝔸ᶠ[K] x
  let b := e.symm (1, (e a).2)
  let c := e.symm ((e a).1, 1)
  have hu : IsUnit (e a) := (hx0.isUnit.map (algebraMap K 𝔸ᶠ[K])).map e
  have hb' : IsUnit ((1 : ∀ v : S, v.val.adicCompletion K), (e a).2) :=
    Prod.isUnit_iff.mpr ⟨isUnit_one, (Prod.isUnit_iff.mp hu).2⟩
  have hb : IsUnit b := hb'.map e.symm
  have hxi := mem_sIntegralAdeles.mp ((algebraMap_mem_sIntegralAdeles_iff S x).mpr hx)
  have hbi : b ∈ integralAdeles (𝓞 K) K := by
    rw [mem_integralAdeles]
    intro v
    by_cases hv : v ∈ S
    · simp [b, e, awayEquiv_symm_apply_of_mem _ _ _ _ _ hv]
    · simpa [b, e, a, awayEquiv_symm_apply_of_notMem _ _ _ _ _ hv] using hxi v hv
  have hmul : c * b = a := by simp [b, c, ← map_mul]
  have hc : c = (awayEquiv (𝓞 K) K hS).symm ((fun v : S ↦ (x : v.val.adicCompletion K)), 1) :=
    congrArg (fun t ↦ e.symm (t, 1)) (funext fun v ↦ by simp [e, a])
  calc
    _ = genIndex K c := by rw [hc]
    _ ≤ genIndex K c * genIndex K b :=
      le_mul_of_one_le_right (genIndex_nonneg c) (one_le_genIndex_of_mem_integralAdeles hb hbi)
    _ = _ := by
      rw [← map_mul, hmul]
      exact genIndex_algebraMap x

end NumberField.FiniteAdeleRing

namespace NumberField

open Finset Real

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

/-- The weight at one infinite place, after the `k`-th power of the place norm cancels. -/
private theorem frequency_weight_mul_pow_le {k : ℕ} {u c r B : ℝ} (hu : 0 < u) (hc : 0 ≤ c)
    (hB : 1 ≤ B) (hcr : c ≤ |r|) (hr : |r| ≤ B) :
    (c * u⁻¹) ^ k * min 1 (c * u⁻¹) ^ 6 * u ^ k ≤
      (|r| ^ k * B ^ 6) * (max 1 u)⁻¹ ^ 6 := by
  have hmin : min 1 (c * u⁻¹) ≤ B * (max 1 u)⁻¹ := by
    rcases le_total u 1 with h | h
    · simpa [max_eq_left h] using (min_le_left 1 (c * u⁻¹)).trans hB
    · rw [max_eq_right h]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (hcr.trans hr) (by positivity))
  calc
    _ = c ^ k * min 1 (c * u⁻¹) ^ 6 := by
      rw [mul_right_comm, ← mul_pow, inv_mul_cancel_right₀ hu.ne']
    _ ≤ |r| ^ k * (B * (max 1 u)⁻¹) ^ 6 := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

/-- The finite-place multiplier at `S`, together with the infinite-place factors, is dominated
by the inverse cube of the height, with an explicit scale factor. The local tuple is represented
by the adele `z` with the same coordinates on `S` and `1` off `S`. -/
theorem frequency_term_le {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (k : ℕ) {B : ℝ} (hB : 1 ≤ B) {c : InfinitePlace K → ℂ} {r : InfinitePlace K → ℝ}
    (hcr : ∀ v, ‖c v‖⁻¹ ≤ |r v|) (hr : ∀ v, |r v| ≤ B) {y : K} (hy0 : y ≠ 0)
    (hy : y ∈ S.integer K) :
    let z := (awayEquiv (𝓞 K) K hS).symm ((fun v : S ↦ (y : v.val.adicCompletion K)), 1)
    (∏ v, (‖c v‖⁻¹ * (v y)⁻¹) ^ k * min 1 (‖c v‖⁻¹ * (v y)⁻¹) ^ 6) *
      (√(FiniteAdeleRing.genIndex K z : ℝ) ^ k /
        ((Algebra.denIdeal (R := integralAdeles (𝓞 K) K) 𝔸ᶠ[K] z).cardQuot : ℝ) ^ 3) ≤
    (∏ v, |r v| ^ k * B ^ 6) * ((∏ v : InfinitePlace K, (max 1 (v y))⁻¹ ^ 6) *
      (Ideal.absNorm (Algebra.denIdeal (R := 𝓞 K) K y) : ℝ)⁻¹ ^ 3) := by
  dsimp only
  rw [denIdeal_awayEquiv_symm_one hS hy]
  have hI : Algebra.denIdeal (R := 𝓞 K) K y ≠ ⊥ := Algebra.denIdeal_ne_bot K (𝓞 K)⁰ y
  have hd : (completedIdeal K (Algebra.denIdeal (R := 𝓞 K) K y)).cardQuot =
      Ideal.absNorm (Algebra.denIdeal (R := 𝓞 K) K y) := by
    simpa only [Submodule.cardQuot_apply, Ideal.absNorm_apply] using
      (Nat.card_congr (quotientEquivQuotientCompletedIdeal K hI).toEquiv).symm
  rw [hd, div_eq_mul_inv, ← inv_pow]
  have hg : √(FiniteAdeleRing.genIndex K
      ((awayEquiv (𝓞 K) K hS).symm ((fun v : S ↦ (y : v.val.adicCompletion K)), 1)) : ℝ) ≤
      ∏ v : InfinitePlace K, v y := by
    have hn : (FiniteAdeleRing.genIndex K
        ((awayEquiv (𝓞 K) K hS).symm ((fun v : S ↦ (y : v.val.adicCompletion K)), 1)) : ℝ) ≤
        |(Algebra.norm ℚ y : ℝ)| := by
      exact_mod_cast FiniteAdeleRing.genIndex_awayEquiv_symm_one_le hS hy0 hy
    have hp := InfinitePlace.prod_eq_abs_norm y
    rw [Rat.cast_abs] at hp
    simp_rw [IsTotallyComplex.mult_eq] at hp
    rw [prod_pow] at hp
    rw [← hp] at hn
    exact (sqrt_le_sqrt hn).trans_eq (sqrt_sq (prod_nonneg fun v _ ↦ apply_nonneg v y))
  grw [hg, ← mul_assoc, ← prod_pow, ← prod_mul_distrib]
  rw [← mul_assoc, ← prod_mul_distrib]
  refine mul_le_mul_of_nonneg_right (prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ ?_)
    (by positivity)
  exact frequency_weight_mul_pow_le (v.pos_iff.mpr hy0) (by positivity) hB (hcr v) (hr v)

/-- The sum of the joint frequency weights over a finite set of nonzero `S`-integers is at most
`∏ v, |r v|^k * (b * B²)^3`. The estimate applies for `b ≥ 1000`; it does not require filling data
or a choice of CM type. -/
theorem sum_frequencies_le {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (k : ℕ) {b B : ℝ} (hb : 64 * 38 * exp 4 ≤ b ^ 3) (hB : 1 ≤ B)
    {c : InfinitePlace K → ℂ} {r : InfinitePlace K → ℝ}
    (hcr : ∀ v, ‖c v‖⁻¹ ≤ |r v|) (hr : ∀ v, |r v| ≤ B)
    (X : Finset K) (hX0 : ∀ y ∈ X, y ≠ 0) (hX : ∀ y ∈ X, y ∈ S.integer K) :
    (∑ y ∈ X,
      let z := (awayEquiv (𝓞 K) K hS).symm ((fun v : S ↦ (y : v.val.adicCompletion K)), 1)
      (∏ v, (‖c v‖⁻¹ * (v y)⁻¹) ^ k * min 1 (‖c v‖⁻¹ * (v y)⁻¹) ^ 6) *
        (√(FiniteAdeleRing.genIndex K z : ℝ) ^ k /
          ((Algebra.denIdeal (R := integralAdeles (𝓞 K) K) 𝔸ᶠ[K] z).cardQuot : ℝ) ^ 3)) ≤
      ∏ v, |r v| ^ k * (b * B ^ 2) ^ 3 := by
  calc
    _ ≤ ∑ y ∈ X, (∏ v, |r v| ^ k * B ^ 6) *
          ((∏ v : InfinitePlace K, (max 1 (v y))⁻¹ ^ 6) *
            (Ideal.absNorm (Algebra.denIdeal (R := 𝓞 K) K y) : ℝ)⁻¹ ^ 3) :=
      sum_le_sum fun y hy ↦ frequency_term_le hS k hB hcr hr (hX0 y hy) (hX y hy)
    _ ≤ (∏ v, |r v| ^ k * B ^ 6) * (64 * 38 * exp 4) ^ Fintype.card (InfinitePlace K) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_prod_inv_max_one_pow_six_mul_inv_absNorm_denIdeal_pow_three_le X) (by positivity)
    _ ≤ (∏ v, |r v| ^ k * B ^ 6) * (b ^ 3) ^ Fintype.card (InfinitePlace K) := by gcongr
    _ = _ := by
      rw [← card_univ, ← prod_const, ← prod_mul_distrib]
      exact prod_congr rfl fun v _ ↦ by ring

end NumberField
