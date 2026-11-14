/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Law.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Moment series, free cumulants, and R-series of real measures

Every Borel measure `μ` on `ℝ` has a formal moment series, free cumulant sequence, free cumulant
series, and formal R-series obtained by applying the one-variable combinatorics of
`TauCeti.Probability.FreeProbability.Cumulant.Series` to the identity coordinate `id : ℝ → ℝ`
under the expectation `f ↦ ∫ x, f x ∂μ`:

`M_μ(z) = ∑_{n ≥ 0} (∫ x ^ n dμ) z ^ n`,
`C_μ(z) = 1 + ∑_{n ≥ 1} κ_n(μ) z ^ n = 1 + z R_μ(z)`,
`R_μ(z) = ∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n`.

For a probability measure `μ`, the expectation sends `1` to `1`, so `M_μ`, `C_μ`, and `R_μ`
satisfy the moment–cumulant functional equations `C_μ(z M_μ(z)) = M_μ(z)` and
`M_μ(z) = 1 + z M_μ(z) R_μ(z M_μ(z))`, and two probability measures have the same moment series
if and only if they have the same R-series. When both probability measures are compactly
supported, Stone–Weierstrass moment determinacy upgrades this to measure equality: a compactly
supported probability measure on `ℝ` is uniquely determined by its R-series (equivalently, by its
free cumulants `κ_n(μ)` for `n ≥ 1`).

For any selfadjoint element `a` of a C⋆-algebra and positive functional `φ : A →ₚ[ℂ] ℂ`, the
real power series `M_{μ_a}`, `C_{μ_a}`, and `R_{μ_a}` of its scalar law `μ_a = φ.law a` map under
`ℝ →+* ℂ` to the algebraic series `TauCeti.momentSeries φ a`, `TauCeti.freeCumulantSeries φ a`,
and `TauCeti.rSeries φ a`.

## Main definitions

* `MeasureTheory.Measure.momentSeries μ`: formal moment series `M_μ(z) ∈ ℝ⟦X⟧`.
* `MeasureTheory.Measure.freeCumulant μ n`: `n`-th free cumulant `κ_n(μ) ∈ ℝ` (with `κ_0(μ) = 1`).
* `MeasureTheory.Measure.freeCumulantSeries μ`: formal free cumulant series `C_μ(z) ∈ ℝ⟦X⟧`.
* `MeasureTheory.Measure.rSeries μ`: formal R-series `R_μ(z) ∈ ℝ⟦X⟧`.

## Main results

* `MeasureTheory.Measure.freeCumulantSeries_subst_X_mul_momentSeries`,
  `MeasureTheory.Measure.momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst`: the
  functional equations relating `M_μ`, `C_μ`, and `R_μ` for a probability measure `μ`.
* `MeasureTheory.Measure.eq_iff_rSeries_eq`, `MeasureTheory.Measure.eq_iff_forall_freeCumulant_eq`:
  compactly supported probability measures on `ℝ` are determined by their R-series and by their
  free cumulants of order `n ≥ 1`.
* `PositiveLinearMap.map_ofReal_momentSeries_law`,
  `PositiveLinearMap.map_ofReal_freeCumulantSeries_law`,
  `PositiveLinearMap.map_ofReal_rSeries_law`, `PositiveLinearMap.ofReal_freeCumulant_law`:
  compatibility between the series of `φ.law a` and the algebraic series of `(φ, a)`.
* `MeasureTheory.Measure.rSeries_dirac`, `MeasureTheory.Measure.rSeries_map_mul_left`,
  `MeasureTheory.Measure.rSeries_map_add_right`: R-series of Dirac masses, dilations, and
  translations.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 12 and 16.
* D. V. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66
  (1986), 323–346.
-/

public section

noncomputable section

open Finset MeasureTheory PowerSeries
open scoped ComplexOrder

namespace MeasureTheory.Measure

/-- The formal **moment series** `M_μ(z) = ∑_{n ≥ 0} (∫ x ^ n dμ) z ^ n` of a Borel measure `μ` on
`ℝ`. When a power `x ^ n` is not `μ`-integrable, its coefficient vanishes by the Bochner integral
convention. -/
def momentSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.momentSeries (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) id

/-- The `n`-th **free cumulant** `κ_n(μ)` of a Borel measure `μ` on `ℝ`, defined via Möbius
inversion on the lattice of noncrossing partitions from the Bochner moments `∫ x ^ k dμ`. At
`n = 0` this takes the empty-block value `1`, matching `C_μ(z) = ∑_{n ≥ 0} κ_n(μ) z ^ n`. -/
def freeCumulant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  TauCeti.freeCumulant (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) (fun _ : Fin n ↦ (id : ℝ → ℝ)) univ

/-- The formal **free cumulant series** `C_μ(z) = 1 + ∑_{n ≥ 1} κ_n(μ) z ^ n` of a Borel measure
`μ` on `ℝ`. -/
def freeCumulantSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.freeCumulantSeries (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) id

/-- The formal **R-series** `R_μ(z) = ∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n` of a Borel measure `μ` on `ℝ`,
the formal counterpart of Voiculescu's R-transform satisfying `C_μ(z) = 1 + z R_μ(z)`. -/
def rSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.rSeries (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) id

/-- The `n`-th coefficient of `μ.momentSeries` is the moment `∫ x ^ n dμ`. -/
@[simp]
theorem coeff_momentSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.momentSeries = ∫ x, x ^ n ∂μ := by
  simp [momentSeries]

/-- The constant coefficient of `μ.momentSeries` is the real total mass `μ.real Set.univ`. -/
@[simp]
theorem constantCoeff_momentSeries (μ : Measure ℝ) :
    constantCoeff μ.momentSeries = μ.real Set.univ := by
  simp [momentSeries]

/-- The `n`-th coefficient of `μ.freeCumulantSeries` is `μ.freeCumulant n`. -/
@[simp]
theorem coeff_freeCumulantSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.freeCumulantSeries = μ.freeCumulant n := by
  rw [freeCumulantSeries, TauCeti.coeff_freeCumulantSeries, freeCumulant]

/-- The constant coefficient of `μ.freeCumulantSeries` is `1`. -/
@[simp]
theorem constantCoeff_freeCumulantSeries (μ : Measure ℝ) :
    constantCoeff μ.freeCumulantSeries = 1 :=
  TauCeti.constantCoeff_freeCumulantSeries _ _

/-- By the empty-partition convention, the zeroth free cumulant of any measure is `1`. -/
@[simp]
theorem freeCumulant_zero (μ : Measure ℝ) : μ.freeCumulant 0 = 1 := by
  rw [← coeff_freeCumulantSeries, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_freeCumulantSeries]

/-- The first free cumulant of `μ` is its Bochner mean `∫ x, x ∂μ`. -/
theorem freeCumulant_one (μ : Measure ℝ) : μ.freeCumulant 1 = ∫ x, x ∂μ := by
  rw [← coeff_freeCumulantSeries, freeCumulantSeries, TauCeti.coeff_one_freeCumulantSeries]
  rfl

/-- The second free cumulant of `μ` is its variance `(∫ x ^ 2 dμ) - (∫ x dμ) ^ 2`. -/
theorem freeCumulant_two (μ : Measure ℝ) :
    μ.freeCumulant 2 = (∫ x, x ^ 2 ∂μ) - (∫ x, x ∂μ) ^ 2 := by
  simpa [← coeff_freeCumulantSeries, freeCumulantSeries] using
    TauCeti.coeff_two_freeCumulantSeries (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) id

/-- The `n`-th coefficient of `μ.rSeries` is `μ.freeCumulant (n + 1)`. -/
@[simp]
theorem coeff_rSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.rSeries = μ.freeCumulant (n + 1) := by
  rw [rSeries, TauCeti.coeff_rSeries, freeCumulant]

/-- The constant coefficient of `μ.rSeries` is the Bochner mean `∫ x, x ∂μ`. -/
@[simp]
theorem constantCoeff_rSeries (μ : Measure ℝ) :
    constantCoeff μ.rSeries = ∫ x, x ∂μ := by
  rw [rSeries, TauCeti.constantCoeff_rSeries]
  rfl

/-- The free cumulant series and the R-series are related by `C_μ(z) = 1 + z R_μ(z)`. -/
theorem freeCumulantSeries_eq_one_add_X_mul_rSeries (μ : Measure ℝ) :
    μ.freeCumulantSeries = 1 + X * μ.rSeries :=
  TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries _ _

/-- Shifting indices by `1` identifies coefficients of `μ.freeCumulantSeries` and `μ.rSeries`. -/
theorem coeff_succ_freeCumulantSeries (μ : Measure ℝ) (n : ℕ) :
    coeff (n + 1) μ.freeCumulantSeries = coeff n μ.rSeries := by
  rw [coeff_freeCumulantSeries, coeff_rSeries]

/-! ### Zero measure and congruence -/

/-- The moment series of the zero measure is `0`. -/
@[simp]
theorem zero_momentSeries : (0 : Measure ℝ).momentSeries = 0 := by
  ext n
  simp

/-- Every free cumulant of positive order of the zero measure vanishes. -/
@[simp]
theorem zero_freeCumulant_succ (n : ℕ) : (0 : Measure ℝ).freeCumulant (n + 1) = 0 := by
  rw [freeCumulant, TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine Finset.sum_eq_zero fun π _ ↦ ?_
  have hne : π.1.parts.Nonempty := Finpartition.parts_nonempty π.1 univ_nonempty.ne_empty
  obtain ⟨B, hB⟩ := hne
  have hprod : TauCeti.partitionMoment (fun f : ℝ → ℝ ↦ ∫ x, f x ∂(0 : Measure ℝ))
      (fun _ : Fin (n + 1) ↦ id) π.1 = 0 := by
    rw [TauCeti.partitionMoment_def]
    exact prod_eq_zero hB (by simp)
  rw [hprod, mul_zero]

/-- Free cumulants of nonzero order of the zero measure vanish. -/
theorem zero_freeCumulant_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (0 : Measure ℝ).freeCumulant n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact zero_freeCumulant_succ k

/-- The R-series of the zero measure is `0`. -/
@[simp]
theorem zero_rSeries : (0 : Measure ℝ).rSeries = 0 := by
  ext n
  simp

/-- The free cumulant series of the zero measure is `1`. -/
@[simp]
theorem zero_freeCumulantSeries : (0 : Measure ℝ).freeCumulantSeries = 1 := by
  rw [freeCumulantSeries_eq_one_add_X_mul_rSeries, zero_rSeries, mul_zero, add_zero]

/-- Equal moment series imply equal free cumulant series, without any normalisation hypothesis. -/
theorem freeCumulantSeries_congr {μ ν : Measure ℝ} (h : μ.momentSeries = ν.momentSeries) :
    μ.freeCumulantSeries = ν.freeCumulantSeries :=
  TauCeti.freeCumulantSeries_congr _ _ h

/-- Equal moment series imply equal R-series, without any normalisation hypothesis. -/
theorem rSeries_congr {μ ν : Measure ℝ} (h : μ.momentSeries = ν.momentSeries) :
    μ.rSeries = ν.rSeries :=
  TauCeti.rSeries_congr _ _ h

/-- Two measures have the same R-series if and only if they have the same free cumulant series. -/
theorem rSeries_eq_iff_freeCumulantSeries_eq {μ ν : Measure ℝ} :
    μ.rSeries = ν.rSeries ↔ μ.freeCumulantSeries = ν.freeCumulantSeries :=
  TauCeti.rSeries_eq_iff_freeCumulantSeries_eq _

/-- Two measures have the same R-series if and only if they have the same free cumulants of every
positive order. -/
theorem rSeries_eq_iff_forall_freeCumulant_eq {μ ν : Measure ℝ} :
    μ.rSeries = ν.rSeries ↔ ∀ n ≠ 0, μ.freeCumulant n = ν.freeCumulant n := by
  rw [PowerSeries.ext_iff]
  simp only [coeff_rSeries]
  exact ⟨fun h n hn ↦ by obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn; exact h k,
    fun h k ↦ h (k + 1) (Nat.succ_ne_zero k)⟩

/-! ### Moment–cumulant functional equations for probability measures -/

/-- **Moment–cumulant formula for probability measures.** Each moment `∫ x ^ n dμ` of a probability
measure `μ` is the sum over `π ∈ NC(n)` of `∏_{B ∈ π} κ_{|B|}(μ)`. -/
theorem integral_pow_eq_sum_prod_freeCumulant (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∫ x, x ^ n ∂μ =
      ∑ π : TauCeti.NoncrossingPartition (univ : Finset (Fin n)),
        ∏ B ∈ π.1.parts, μ.freeCumulant #B := by
  have h1 : (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) 1 = 1 := by simp
  have h := TauCeti.apply_pow_eq_sum_prod_coeff_freeCumulantSeries (id : ℝ → ℝ) h1
    (univ : Finset (Fin n))
  have hc (k : ℕ) :
      coeff k (TauCeti.freeCumulantSeries (fun f : ℝ → ℝ ↦ ∫ x, f x ∂μ) id) =
        μ.freeCumulant k :=
    coeff_freeCumulantSeries μ k
  simp_rw [hc] at h
  simpa [Pi.pow_def] using h

/-- **Moment–cumulant functional equation** for a probability measure: `C_μ(z M_μ(z)) = M_μ(z)`. -/
theorem freeCumulantSeries_subst_X_mul_momentSeries (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.freeCumulantSeries.subst (X * μ.momentSeries) = μ.momentSeries :=
  TauCeti.freeCumulantSeries_subst_X_mul_momentSeries id (by simp)

/-- **R-series functional equation** for a probability measure:
`M_μ(z) = 1 + z M_μ(z) R_μ(z M_μ(z))`. -/
theorem momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    μ.momentSeries = 1 + X * μ.momentSeries * μ.rSeries.subst (X * μ.momentSeries) :=
  TauCeti.momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst id (by simp)

/-- Two probability measures on `ℝ` have the same free cumulant series if and only if they have the
same moment series. -/
theorem freeCumulantSeries_eq_iff_momentSeries_eq (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ.freeCumulantSeries = ν.freeCumulantSeries ↔ μ.momentSeries = ν.momentSeries :=
  TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq id (by simp) (by simp)

/-- Two probability measures on `ℝ` have the same R-series if and only if they have the same moment
series. -/
theorem rSeries_eq_iff_momentSeries_eq (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ.rSeries = ν.rSeries ↔ μ.momentSeries = ν.momentSeries :=
  TauCeti.rSeries_eq_iff_momentSeries_eq id (by simp) (by simp)

/-! ### Determinacy on compactly supported probability measures -/

/-- Compactly supported finite measures on `ℝ` are determined by their formal moment series. -/
theorem eq_iff_momentSeries_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ μ.momentSeries = ν.momentSeries := by
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ?_⟩
  refine TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (hμ.union hν) ?_ ?_ fun n ↦ ?_
  · exact measure_mono_null (Set.compl_subset_compl.2 Set.subset_union_left)
      Measure.measure_compl_support
  · exact measure_mono_null (Set.compl_subset_compl.2 Set.subset_union_right)
      Measure.measure_compl_support
  · simpa using congrArg (coeff n) h

/-- **R-series determinacy.** Compactly supported probability measures on `ℝ` are uniquely
determined by their formal R-series. -/
theorem eq_iff_rSeries_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ μ.rSeries = ν.rSeries :=
  (eq_iff_momentSeries_eq hμ hν).trans (rSeries_eq_iff_momentSeries_eq μ ν).symm

/-- Compactly supported probability measures on `ℝ` are uniquely determined by their formal free
cumulant series. -/
theorem eq_iff_freeCumulantSeries_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ μ.freeCumulantSeries = ν.freeCumulantSeries :=
  (eq_iff_rSeries_eq hμ hν).trans rSeries_eq_iff_freeCumulantSeries_eq

/-- Compactly supported probability measures on `ℝ` are uniquely determined by their free cumulants
of positive order. -/
theorem eq_iff_forall_freeCumulant_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ ∀ n ≠ 0, μ.freeCumulant n = ν.freeCumulant n :=
  (eq_iff_rSeries_eq hμ hν).trans rSeries_eq_iff_forall_freeCumulant_eq

/-! ### Dilations -/

/-- Pushing `μ` forward along `x ↦ r * x` rescales its moment series:
`M_{μ.map (r * ·)}(z) = M_μ(r z)`. No finiteness or support assumption on `μ` is needed. -/
theorem momentSeries_map_mul_left (μ : Measure ℝ) (r : ℝ) :
    (μ.map (r * ·)).momentSeries = rescale r μ.momentSeries := by
  ext n
  rw [coeff_momentSeries, coeff_rescale, coeff_momentSeries,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow, integral_const_mul]

/-- Pushing `μ` forward along `x ↦ r * x` multiplies its `n`-th free cumulant by `r ^ n`. -/
theorem freeCumulant_map_mul_left (μ : Measure ℝ) (r : ℝ) (n : ℕ) :
    (μ.map (r * ·)).freeCumulant n = r ^ n * μ.freeCumulant n := by
  simp_rw [freeCumulant, TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment,
    TauCeti.partitionMoment_const]
  have hmom (g : Measure ℝ) (k : ℕ) :
      (fun f : ℝ → ℝ ↦ ∫ x, f x ∂g) (id ^ k) = coeff k g.momentSeries := by
    simp
  simp_rw [hmom, momentSeries_map_mul_left, coeff_rescale]
  rw [mul_sum]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, π.1.sum_card_parts, card_univ, Fintype.card_fin]
  ring

/-- Pushing `μ` forward along `x ↦ r * x` rescales its free cumulant series:
`C_{μ.map (r * ·)}(z) = C_μ(r z)`. -/
theorem freeCumulantSeries_map_mul_left (μ : Measure ℝ) (r : ℝ) :
    (μ.map (r * ·)).freeCumulantSeries = rescale r μ.freeCumulantSeries := by
  ext n
  rw [coeff_freeCumulantSeries, coeff_rescale, coeff_freeCumulantSeries,
    freeCumulant_map_mul_left]

/-- Pushing `μ` forward along `x ↦ r * x` transforms its R-series by
`R_{μ.map (r * ·)}(z) = r R_μ(r z)`. -/
theorem rSeries_map_mul_left (μ : Measure ℝ) (r : ℝ) :
    (μ.map (r * ·)).rSeries = r • rescale r μ.rSeries := by
  ext n
  rw [coeff_rSeries, freeCumulant_map_mul_left, pow_succ', mul_assoc, ← coeff_rSeries,
    ← coeff_rescale, coeff_smul, smul_eq_mul]

end MeasureTheory.Measure

/-! ### Compatibility with C⋆-algebraic laws -/

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- Mapping the moment series of the law `φ.law a` along `ℝ →+* ℂ` recovers the algebraic moment
series `TauCeti.momentSeries φ a` of a selfadjoint element `a`. -/
theorem map_ofReal_momentSeries_law (ha : IsSelfAdjoint a) :
    (φ.law a).momentSeries.map Complex.ofRealHom = TauCeti.momentSeries φ a := by
  ext n
  simpa using ofReal_integral_pow_law φ ha n

/-- Mapping the free cumulant series of the law `φ.law a` along `ℝ →+* ℂ` recovers the algebraic
free cumulant series `TauCeti.freeCumulantSeries φ a` of a selfadjoint element `a`. -/
theorem map_ofReal_freeCumulantSeries_law (ha : IsSelfAdjoint a) :
    (φ.law a).freeCumulantSeries.map Complex.ofRealHom = TauCeti.freeCumulantSeries φ a := by
  rw [Measure.freeCumulantSeries, TauCeti.map_freeCumulantSeries]
  refine TauCeti.freeCumulantSeries_congr _ _ ?_
  rw [← TauCeti.map_momentSeries, ← Measure.momentSeries, map_ofReal_momentSeries_law φ ha]

/-- Mapping the R-series of the law `φ.law a` along `ℝ →+* ℂ` recovers the algebraic R-series
`TauCeti.rSeries φ a` of a selfadjoint element `a`. -/
theorem map_ofReal_rSeries_law (ha : IsSelfAdjoint a) :
    (φ.law a).rSeries.map Complex.ofRealHom = TauCeti.rSeries φ a := by
  rw [Measure.rSeries, TauCeti.map_rSeries]
  refine TauCeti.rSeries_congr _ _ ?_
  rw [← TauCeti.map_momentSeries, ← Measure.momentSeries, map_ofReal_momentSeries_law φ ha]

/-- Each free cumulant of `φ.law a` embeds in `ℂ` as the algebraic free cumulant
`κ_n(a, …, a)` of a selfadjoint element `a`. -/
theorem ofReal_freeCumulant_law (ha : IsSelfAdjoint a) (n : ℕ) :
    (((φ.law a).freeCumulant n : ℝ) : ℂ) =
      TauCeti.freeCumulant φ (fun _ : Fin n ↦ a) univ := by
  have h := congrArg (coeff n) (map_ofReal_freeCumulantSeries_law φ ha)
  simpa using h

/-- For states `φ` and `ψ`, two selfadjoint elements have the same law if and only if they have
the same algebraic R-series. -/
theorem law_eq_law_iff_rSeries_eq {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (ψ : B →ₚ[ℂ] ℂ) {b : B} (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    φ.law a = ψ.law b ↔ TauCeti.rSeries φ a = TauCeti.rSeries ψ b := by
  have := isProbabilityMeasure_law φ hφ ha
  have := isProbabilityMeasure_law ψ hψ hb
  rw [Measure.eq_iff_rSeries_eq (isCompact_support_law φ a) (isCompact_support_law ψ b),
    ← map_ofReal_rSeries_law φ ha, ← map_ofReal_rSeries_law ψ hb]
  exact (PowerSeries.map_injective Complex.ofRealHom Complex.ofReal_injective).eq_iff.symm

end PositiveLinearMap

/-! ### Dirac masses and translations on compactly supported laws -/

namespace MeasureTheory.Measure

/-- The R-series of the point mass `Measure.dirac c` is the constant power series `c`. -/
@[simp]
theorem rSeries_dirac (c : ℝ) : (Measure.dirac c).rSeries = PowerSeries.C c := by
  have hlaw : (PositiveLinearMap.id ℂ ℂ).law (algebraMap ℝ ℂ c) = Measure.dirac c :=
    PositiveLinearMap.law_algebraMap _ rfl c
  apply PowerSeries.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [← hlaw, PositiveLinearMap.map_ofReal_rSeries_law _ (IsSelfAdjoint.all c |>.algebraMap ℂ),
    ← PositiveLinearMap.coe_toLinearMap, IsScalarTower.algebraMap_apply ℝ ℂ ℂ c,
    TauCeti.rSeries_algebraMap (φ := (PositiveLinearMap.id ℂ ℂ).toLinearMap) rfl
      (algebraMap ℝ ℂ c),
    map_C]
  rfl

/-- The free cumulant series of `Measure.dirac c` is `1 + c z`. -/
theorem freeCumulantSeries_dirac (c : ℝ) :
    (Measure.dirac c).freeCumulantSeries = 1 + PowerSeries.C c * X := by
  rw [freeCumulantSeries_eq_one_add_X_mul_rSeries, rSeries_dirac, mul_comm]

/-- The first free cumulant of `Measure.dirac c` is `c`. -/
@[simp]
theorem freeCumulant_dirac_one (c : ℝ) : (Measure.dirac c).freeCumulant 1 = c := by
  rw [← coeff_rSeries, rSeries_dirac, coeff_zero_eq_constantCoeff_apply, constantCoeff_C]

/-- All free cumulants of order `n ≥ 2` of `Measure.dirac c` vanish. -/
theorem freeCumulant_dirac_of_two_le (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (Measure.dirac c).freeCumulant n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [← coeff_rSeries, rSeries_dirac, coeff_succ_C]

/-- Translating a compactly supported probability measure `μ` by `c : ℝ` adds the constant `c` to
its R-series: `R_{μ.map (· + c)}(z) = R_μ(z) + c`. Neither `IsProbabilityMeasure μ` nor
`IsCompact μ.support` can be omitted: the zero measure fixes `R_0 = 0`, and heavy-tailed
probability measures need not have integrable moments. -/
theorem rSeries_map_add_right (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (c : ℝ) : (μ.map (· + c)).rSeries = μ.rSeries + PowerSeries.C c := by
  have : CompactSpace μ.support := isCompact_iff_compactSpace.mp hμ
  let ν := μ.comap ((↑) : μ.support → ℝ)
  have : IsProbabilityMeasure ν :=
    MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet
      |>.isProbabilityMeasure_comap (Subtype.range_coe ▸ Measure.support_mem_ae)
  let φ : C(μ.support, ℂ) →ₚ[ℂ] ℂ := ContinuousMap.integralPositiveLinearMap ν
  let g : C(μ.support, ℝ) := ContinuousMap.restrict μ.support (ContinuousMap.id ℝ)
  let a : C(μ.support, ℂ) := g.realToRCLike ℂ
  have ha : IsSelfAdjoint a := ContinuousMap.isSelfAdjoint_realToRCLike ℂ
  have hφ : φ 1 = 1 := by simp [φ]
  have hlaw : φ.law a = μ :=
    PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id Measure.measure_compl_support
  let gc : C(μ.support, ℝ) := g + ContinuousMap.const μ.support c
  have hgc_eq : gc.realToRCLike ℂ = a + algebraMap ℂ C(μ.support, ℂ) (c : ℂ) := by
    ext x
    simp [gc, a, Algebra.algebraMap_eq_smul_one]
  have hshift : φ.law (a + algebraMap ℂ C(μ.support, ℂ) (c : ℂ)) = μ.map (· + c) := by
    rw [← hgc_eq, PositiveLinearMap.law_integralPositiveLinearMap_realToRCLike]
    have hcomp : (gc : μ.support → ℝ) = (· + c) ∘ ((↑) : μ.support → ℝ) := rfl
    rw [hcomp, ← Measure.map_map (measurable_add_const c) measurable_subtype_coe]
    congr 1
    exact (map_comap_subtype_coe hμ.measurableSet μ).trans
      (Measure.restrict_eq_self_of_ae_mem Measure.support_mem_ae)
  have hsa' : IsSelfAdjoint (a + algebraMap ℂ C(μ.support, ℂ) (c : ℂ)) :=
    hgc_eq ▸ ContinuousMap.isSelfAdjoint_realToRCLike ℂ
  have hr : μ.rSeries = (φ.law a).rSeries := congrArg Measure.rSeries hlaw.symm
  apply PowerSeries.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [← hshift, hr, PositiveLinearMap.map_ofReal_rSeries_law φ hsa', map_add,
    PositiveLinearMap.map_ofReal_rSeries_law φ ha, map_C]
  exact TauCeti.rSeries_add_algebraMap (φ := φ.toLinearMap) hφ a (c : ℂ)

/-- Pushing a compactly supported probability measure `μ` forward along an affine map
`x ↦ r * x + c` transforms its R-series by `R(z) ↦ r R_μ(r z) + c`. -/
theorem rSeries_map_affine (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (r c : ℝ) :
    (μ.map (fun x ↦ r * x + c)).rSeries = r • rescale r μ.rSeries + PowerSeries.C c := by
  have hm_mul : Measurable (r * · : ℝ → ℝ) := measurable_const_mul r
  have hm_add : Measurable (· + c : ℝ → ℝ) := measurable_add_const c
  have hcomp : μ.map (fun x ↦ r * x + c) = (μ.map (r * ·)).map (· + c) :=
    (Measure.map_map hm_add hm_mul).symm
  have : IsProbabilityMeasure (μ.map (r * ·)) :=
    ⟨by rw [Measure.map_apply hm_mul MeasurableSet.univ]; simp⟩
  have hsupp : IsCompact (μ.map (r * ·)).support := by
    rw [Measure.support_map_eq_closure_image μ Measure.support_mem_ae (continuous_const_mul r)]
    exact (hμ.image (continuous_const_mul r)).closure
  rw [hcomp, rSeries_map_add_right _ hsupp c, rSeries_map_mul_left]

end MeasureTheory.Measure
