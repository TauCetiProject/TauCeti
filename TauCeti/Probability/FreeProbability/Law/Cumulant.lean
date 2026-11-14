/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Exponential
public import TauCeti.Probability.FreeProbability.Semicircular.Law
import TauCeti.MeasureTheory.Function.PolynomialMemLp
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Moments, free cumulants, and formal R-series of Borel measures on the line

For a Borel measure `μ` on `ℝ`, evaluating the single-variable combinatorics of
`TauCeti.Probability.FreeProbability.Cumulant.Series` on the moment functional `f ↦ ∫ f dμ` at the
coordinate `x ↦ x` attaches to `μ` its formal moment series, free cumulant series, free cumulants
`κ_n(μ)`, and formal R-series `R_μ(z) = ∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n`:

`M_μ(z) = ∑_{n ≥ 0} (∫ x ^ n dμ) z ^ n` and `C_μ(z) = 1 + z R_μ(z)`.

When `μ` is a probability measure, `M_μ` and `C_μ` satisfy the formal functional equations
`C_μ(z M_μ(z)) = M_μ(z)` and `M_μ(z) = 1 + z M_μ(z) R_μ(z M_μ(z))`, so two probability measures
have the same moment series if and only if they have the same R-series. When `μ` and `ν` also have
compact topological support, moment determinacy upgrades this formal equivalence to equality of
measures: `μ = ν ↔ μ.rSeries = ν.rSeries`.

For a selfadjoint element `a` of a C⋆-algebra and a positive linear functional `φ`, the scalar
extension from `ℝ` to `ℂ` identifies these series for `φ.law a` with the algebraic series
`TauCeti.momentSeries φ a`, `TauCeti.freeCumulantSeries φ a`, and `TauCeti.rSeries φ a`. In
particular, the semicircle law `semicircleReal a v` has R-series `a + v z`.

## Main definitions

* `MeasureTheory.Measure.momentSeries μ`: the formal moment series `∑_{n ≥ 0} (∫ x ^ n dμ) z ^ n`.
* `MeasureTheory.Measure.freeCumulantSeries μ`: the formal free cumulant series `C_μ(z)`.
* `MeasureTheory.Measure.freeCumulant μ n`: the `n`-th free cumulant `κ_n(μ)`.
* `MeasureTheory.Measure.rSeries μ`: the formal R-series `R_μ(z) = ∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n`.

## Main results

* `MeasureTheory.Measure.freeCumulantSeries_subst_X_mul_momentSeries` and
  `MeasureTheory.Measure.momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst`: the
  moment–cumulant functional equations for probability measures on `ℝ`.
* `MeasureTheory.Measure.rSeries_map_mul_left`, `MeasureTheory.Measure.rSeries_map_add_left`, and
  `MeasureTheory.Measure.rSeries_map_affine`: dilation, translation, and affine transport of the
  R-series.
* `MeasureTheory.Measure.eq_iff_momentSeries_eq`,
  `MeasureTheory.Measure.eq_iff_freeCumulantSeries_eq`, `MeasureTheory.Measure.eq_iff_rSeries_eq`,
  and `MeasureTheory.Measure.eq_iff_forall_freeCumulant_eq`: determinacy of compactly supported
  measures by their moments and free cumulants.
* `MeasureTheory.Measure.abs_freeCumulant_le_pow`,
  `MeasureTheory.Measure.summable_norm_coeff_freeCumulantSeries_mul_pow`, and
  `MeasureTheory.Measure.summable_norm_coeff_rSeries_mul_pow`: exponential cumulant bounds and
  convergence disks for probability measures supported in `[-C, C]`.
* `PositiveLinearMap.map_momentSeries_law`, `PositiveLinearMap.map_freeCumulantSeries_law`,
  `PositiveLinearMap.map_rSeries_law`, and `PositiveLinearMap.ofReal_freeCumulant_law`:
  compatibility with `PositiveLinearMap.law`.
* `TauCeti.Probability.rSeries_semicircleReal` and
  `TauCeti.Probability.freeCumulant_semicircleReal`: the R-series and free cumulants of
  `semicircleReal a v`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Math. Soc.
  Lecture Note Ser. 335, Cambridge University Press (2006), Lectures 11, 12, and 16.
* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
-/

public section

noncomputable section

open Finset MeasureTheory Polynomial PowerSeries TauCeti TauCeti.Probability
open scoped ComplexOrder NNReal

namespace MeasureTheory.Measure

/-- The formal moment series `M_μ(z) = ∑_{n ≥ 0} (∫ x ^ n dμ) z ^ n` of a Borel measure `μ` on
`ℝ`. -/
def momentSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.momentSeries (integral μ) id

/-- The formal free cumulant series `C_μ(z) = 1 + ∑_{n ≥ 1} κ_n(μ) z ^ n` of a Borel measure `μ`
on `ℝ`, obtained by noncrossing Möbius inversion from the moments `∫ x ^ n dμ`. -/
def freeCumulantSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.freeCumulantSeries (integral μ) id

/-- The `n`-th free cumulant `κ_n(μ)` of a Borel measure `μ` on `ℝ`, defined as the `n`-th
coefficient of `μ.freeCumulantSeries` (`κ₀(μ) = 1`, `κ₁(μ) = ∫ x dμ`, and
`κ₂(μ) = ∫ x ^ 2 dμ - (∫ x dμ) ^ 2`). -/
def freeCumulant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  coeff n μ.freeCumulantSeries

/-- The formal R-series `R_μ(z) = ∑_{n ≥ 0} κ_{n + 1}(μ) z ^ n` of a Borel measure `μ` on `ℝ`,
the formal counterpart of Voiculescu's R-transform, so that `C_μ(z) = 1 + z R_μ(z)`. -/
def rSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.rSeries (integral μ) id

private lemma integral_id_pow (μ : Measure ℝ) (n : ℕ) :
    integral μ ((id : ℝ → ℝ) ^ n) = ∫ x, x ^ n ∂μ := by
  rw [Pi.pow_def]
  rfl

private lemma integral_id_eq (μ : Measure ℝ) :
    integral μ (id : ℝ → ℝ) = ∫ x, x ∂μ := (rfl)

private lemma integral_const_one (μ : Measure ℝ) :
    integral μ (1 : ℝ → ℝ) = μ.real Set.univ := by
  rw [Pi.one_def]
  simp

/-- The `n`-th coefficient of `μ.momentSeries` is the raw moment `∫ x ^ n dμ`. -/
@[simp]
theorem coeff_momentSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.momentSeries = ∫ x, x ^ n ∂μ := by
  rw [momentSeries, TauCeti.coeff_momentSeries, integral_id_pow]

/-- The constant coefficient of `μ.momentSeries` is the real total mass `μ.real Set.univ`. -/
@[simp]
theorem constantCoeff_momentSeries (μ : Measure ℝ) :
    constantCoeff μ.momentSeries = μ.real Set.univ := by
  rw [momentSeries, TauCeti.constantCoeff_momentSeries, integral_const_one]

/-- The `n`-th coefficient of `μ.freeCumulantSeries` is `μ.freeCumulant n`. -/
@[simp]
theorem coeff_freeCumulantSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.freeCumulantSeries = μ.freeCumulant n := (rfl)

/-- Unfolding of `μ.freeCumulant n` as the free cumulant of the constant word on `Fin n`. -/
theorem freeCumulant_eq_tauCetiFreeCumulant (μ : Measure ℝ) (n : ℕ) :
    μ.freeCumulant n = TauCeti.freeCumulant (integral μ) (fun _ : Fin n ↦ id) univ := by
  rw [freeCumulant, freeCumulantSeries, TauCeti.coeff_freeCumulantSeries]

/-- The zeroth coefficient of `μ.freeCumulantSeries` is `1`. -/
@[simp]
theorem freeCumulant_zero (μ : Measure ℝ) : μ.freeCumulant 0 = 1 := by
  simp [freeCumulant_eq_tauCetiFreeCumulant]

/-- The constant coefficient of `μ.freeCumulantSeries` is `1`. -/
@[simp]
theorem constantCoeff_freeCumulantSeries (μ : Measure ℝ) :
    constantCoeff μ.freeCumulantSeries = 1 := by
  simp [freeCumulantSeries]

/-- The first free cumulant `κ₁(μ)` is the mean `∫ x dμ`. -/
@[simp]
theorem freeCumulant_one (μ : Measure ℝ) : μ.freeCumulant 1 = ∫ x, x ∂μ := by
  rw [freeCumulant, freeCumulantSeries, TauCeti.coeff_one_freeCumulantSeries, integral_id_eq]

/-- The second free cumulant `κ₂(μ)` is `∫ x ^ 2 dμ - (∫ x dμ) ^ 2` (the variance for probability
measures). -/
theorem freeCumulant_two (μ : Measure ℝ) :
    μ.freeCumulant 2 = (∫ x, x ^ 2 ∂μ) - (∫ x, x ∂μ) ^ 2 := by
  rw [freeCumulant, freeCumulantSeries, TauCeti.coeff_two_freeCumulantSeries, integral_id_pow,
    integral_id_eq]

/-- The `n`-th coefficient of `μ.rSeries` is `μ.freeCumulant (n + 1)`. -/
@[simp]
theorem coeff_rSeries (μ : Measure ℝ) (n : ℕ) :
    coeff n μ.rSeries = μ.freeCumulant (n + 1) := by
  rw [rSeries, ← TauCeti.coeff_succ_freeCumulantSeries, ← freeCumulantSeries,
    coeff_freeCumulantSeries]

/-- The constant coefficient of `μ.rSeries` is the mean `∫ x dμ`. -/
@[simp]
theorem constantCoeff_rSeries (μ : Measure ℝ) : constantCoeff μ.rSeries = ∫ x, x ∂μ := by
  rw [rSeries, TauCeti.constantCoeff_rSeries, integral_id_eq]

/-- The free cumulant series and R-series are related by `C_μ(z) = 1 + z R_μ(z)`. -/
theorem freeCumulantSeries_eq_one_add_X_mul_rSeries (μ : Measure ℝ) :
    μ.freeCumulantSeries = 1 + PowerSeries.X * μ.rSeries :=
  TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries _ _

/-- Equal moment series give equal free cumulant series, without normalization. -/
theorem freeCumulantSeries_congr {μ ν : Measure ℝ} (h : μ.momentSeries = ν.momentSeries) :
    μ.freeCumulantSeries = ν.freeCumulantSeries :=
  TauCeti.freeCumulantSeries_congr _ _ h

/-- Equal moment series give equal R-series, without normalization. -/
theorem rSeries_congr {μ ν : Measure ℝ} (h : μ.momentSeries = ν.momentSeries) :
    μ.rSeries = ν.rSeries :=
  TauCeti.rSeries_congr _ _ h

/-- Two measures have the same R-series if and only if they have the same free cumulant series. -/
theorem rSeries_eq_iff_freeCumulantSeries_eq {μ ν : Measure ℝ} :
    μ.rSeries = ν.rSeries ↔ μ.freeCumulantSeries = ν.freeCumulantSeries := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [freeCumulantSeries_eq_one_add_X_mul_rSeries,
      freeCumulantSeries_eq_one_add_X_mul_rSeries, h]
  · ext n
    simpa using congrArg (coeff (n + 1)) h

/-- Two measures have the same R-series if and only if all their positive-order free cumulants
agree. -/
theorem rSeries_eq_iff_forall_freeCumulant_eq {μ ν : Measure ℝ} :
    μ.rSeries = ν.rSeries ↔ ∀ n ≠ 0, μ.freeCumulant n = ν.freeCumulant n := by
  refine ⟨fun h n hn ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa using congrArg (coeff k) h
  · ext n
    simpa using h (n + 1) (Nat.succ_ne_zero n)

private lemma integral_const_one_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    integral μ (1 : ℝ → ℝ) = 1 := by
  rw [integral_const_one, probReal_univ]

/-- *Moment–cumulant formula for a probability measure*: `∫ x ^ #s dμ` is the sum over noncrossing
partitions of `s` of the products of `μ.freeCumulant #B` along their blocks. -/
theorem integral_pow_eq_sum_prod_freeCumulant (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : Type*} [LinearOrder α] (s : Finset α) :
    ∫ x, x ^ #s ∂μ = ∑ π : NoncrossingPartition s, ∏ B ∈ π.1.parts, μ.freeCumulant #B := by
  rw [← integral_id_pow, TauCeti.apply_pow_eq_sum_prod_coeff_freeCumulantSeries id
    (integral_const_one_prob μ) s]
  rfl

/-- *Moment–cumulant functional equation*: for a probability measure `μ` on `ℝ`,
`C_μ(z M_μ(z)) = M_μ(z)`. -/
theorem freeCumulantSeries_subst_X_mul_momentSeries (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    μ.freeCumulantSeries.subst (PowerSeries.X * μ.momentSeries) = μ.momentSeries :=
  TauCeti.freeCumulantSeries_subst_X_mul_momentSeries id (integral_const_one_prob μ)

/-- *R-series functional equation*: for a probability measure `μ` on `ℝ`,
`M_μ(z) = 1 + z M_μ(z) R_μ(z M_μ(z))`. -/
theorem momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    μ.momentSeries =
      1 + PowerSeries.X * μ.momentSeries * μ.rSeries.subst (PowerSeries.X * μ.momentSeries) :=
  TauCeti.momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst id
    (integral_const_one_prob μ)

/-- Two probability measures on `ℝ` have the same free cumulant series if and only if they have the
same moment series. -/
theorem freeCumulantSeries_eq_iff_momentSeries_eq (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ.freeCumulantSeries = ν.freeCumulantSeries ↔ μ.momentSeries = ν.momentSeries :=
  TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq id (integral_const_one_prob μ)
    (integral_const_one_prob ν)

/-- Two probability measures on `ℝ` have the same R-series if and only if they have the same moment
series. -/
theorem rSeries_eq_iff_momentSeries_eq (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    μ.rSeries = ν.rSeries ↔ μ.momentSeries = ν.momentSeries :=
  rSeries_eq_iff_freeCumulantSeries_eq.trans (freeCumulantSeries_eq_iff_momentSeries_eq μ ν)

/-! ### Zero and Dirac measures -/

/-- The moment series of the zero measure vanishes. -/
@[simp]
theorem momentSeries_zero : (0 : Measure ℝ).momentSeries = 0 := by
  ext n
  simp

/-- The free cumulant series of the zero measure is the constant `1`. -/
@[simp]
theorem freeCumulantSeries_zero : (0 : Measure ℝ).freeCumulantSeries = 1 := by
  ext (_ | n)
  · simp
  · rw [coeff_freeCumulantSeries, freeCumulant_eq_tauCetiFreeCumulant,
      TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment, PowerSeries.coeff_one,
      ite_eq_right (Nat.succ_ne_zero n)]
    refine Finset.sum_eq_zero fun π _ ↦ mul_eq_zero_of_right _ ?_
    obtain ⟨B, hB⟩ := Finpartition.parts_nonempty (P := π.1) univ_nonempty.ne_empty
    rw [TauCeti.partitionMoment_const]
    exact Finset.prod_eq_zero hB (by rw [integral_id_pow, integral_zero_measure])

/-- Every positive-order free cumulant of the zero measure vanishes, so its R-series is `0`. -/
@[simp]
theorem rSeries_zero : (0 : Measure ℝ).rSeries = 0 := by
  ext n
  rw [coeff_rSeries, ← coeff_freeCumulantSeries, freeCumulantSeries_zero, PowerSeries.coeff_one,
    ite_eq_right (Nat.succ_ne_zero n), map_zero]

/-! ### Compatibility with C⋆-algebraic laws -/

end MeasureTheory.Measure

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- Extending scalars from `ℝ` to `ℂ` sends `(φ.law a).momentSeries` to `TauCeti.momentSeries φ a`
for every selfadjoint `a`. -/
theorem map_momentSeries_law (ha : IsSelfAdjoint a) :
    PowerSeries.map (algebraMap ℝ ℂ) (φ.law a).momentSeries = TauCeti.momentSeries φ a := by
  ext n
  simp [ofReal_integral_pow_law φ ha]

/-- Extending scalars from `ℝ` to `ℂ` sends `(φ.law a).freeCumulantSeries` to
`TauCeti.freeCumulantSeries φ a` for every selfadjoint `a`. -/
theorem map_freeCumulantSeries_law (ha : IsSelfAdjoint a) :
    PowerSeries.map (algebraMap ℝ ℂ) (φ.law a).freeCumulantSeries =
      TauCeti.freeCumulantSeries φ a := by
  rw [Measure.freeCumulantSeries, TauCeti.map_freeCumulantSeries]
  refine TauCeti.freeCumulantSeries_congr _ _ ?_
  rw [← TauCeti.map_momentSeries]
  exact map_momentSeries_law φ ha

/-- Extending scalars from `ℝ` to `ℂ` sends `(φ.law a).rSeries` to `TauCeti.rSeries φ a` for every
selfadjoint `a`. -/
theorem map_rSeries_law (ha : IsSelfAdjoint a) :
    PowerSeries.map (algebraMap ℝ ℂ) (φ.law a).rSeries = TauCeti.rSeries φ a := by
  rw [Measure.rSeries, TauCeti.map_rSeries]
  refine TauCeti.rSeries_congr _ _ ?_
  rw [← TauCeti.map_momentSeries]
  exact map_momentSeries_law φ ha

/-- The `n`-th free cumulant of `φ.law a`, cast to `ℂ`, is `κ_n(a, …, a)` for `φ`. -/
theorem ofReal_freeCumulant_law (ha : IsSelfAdjoint a) (n : ℕ) :
    (((φ.law a).freeCumulant n : ℝ) : ℂ) = TauCeti.freeCumulant φ (fun _ : Fin n ↦ a) univ := by
  simpa using congrArg (coeff n) (map_freeCumulantSeries_law φ ha)

end PositiveLinearMap

namespace MeasureTheory.Measure

/-- The formal R-series of a Dirac mass `δ_c` is the constant power series `c`: its mean is `c` and
all cumulants of order at least two vanish. -/
@[simp]
theorem rSeries_dirac (c : ℝ) : (Measure.dirac c).rSeries = PowerSeries.C c := by
  have h : (Measure.dirac c).rSeries =
      TauCeti.rSeries (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (algebraMap ℝ ℝ c) := by
    refine TauCeti.rSeries_congr _ _ ?_
    ext n
    rw [TauCeti.coeff_momentSeries, integral_id_pow]
    simp
  rw [h, TauCeti.rSeries_algebraMap (LinearMap.id_apply 1) c]

/-- The formal free cumulant series of a Dirac mass `δ_c` is `1 + c z`. -/
@[simp]
theorem freeCumulantSeries_dirac (c : ℝ) :
    (Measure.dirac c).freeCumulantSeries = 1 + PowerSeries.C c * PowerSeries.X := by
  rw [freeCumulantSeries_eq_one_add_X_mul_rSeries, rSeries_dirac, mul_comm]

/-- The free cumulants of `δ_c` are `κ₁ = c` and `κ_n = 0` for `n ≥ 2`. -/
theorem freeCumulant_dirac (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (Measure.dirac c).freeCumulant n = if n = 1 then c else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← coeff_rSeries, rSeries_dirac]
  rcases k with _ | k <;> simp

/-! ### Dilation, translation, and affine transport -/

/-- Pushing a measure forward by `x ↦ r * x` rescales its moment series:
`M_{r_* μ}(z) = M_μ(r z)`. -/
theorem momentSeries_map_mul_left (μ : Measure ℝ) (r : ℝ) :
    (μ.map (r * ·)).momentSeries = rescale r μ.momentSeries := by
  ext n
  rw [coeff_momentSeries, coeff_rescale, coeff_momentSeries,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, mul_comm]

/-- Pushing a measure forward by `x ↦ r * x` rescales its free cumulant series:
`C_{r_* μ}(z) = C_μ(r z)`. -/
theorem freeCumulantSeries_map_mul_left (μ : Measure ℝ) (r : ℝ) :
    (μ.map (r * ·)).freeCumulantSeries = rescale r μ.freeCumulantSeries := by
  ext n
  rw [coeff_freeCumulantSeries, coeff_rescale, coeff_freeCumulantSeries,
    freeCumulant_eq_tauCetiFreeCumulant, freeCumulant_eq_tauCetiFreeCumulant,
    TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment,
    TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [TauCeti.partitionMoment_const, TauCeti.partitionMoment_const]
  have hpart (B : Finset (Fin n)) :
      integral (μ.map (r * ·)) ((id : ℝ → ℝ) ^ #B) = r ^ #B * integral μ ((id : ℝ → ℝ) ^ #B) := by
    simpa [integral_id_pow, mul_comm (r ^ #B)] using
      congrArg (coeff #B) (momentSeries_map_mul_left μ r)
  simp_rw [hpart, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, π.1.sum_card_parts,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- Pushing a measure forward by `x ↦ r * x` multiplies its `n`-th free cumulant by `r ^ n`. -/
theorem freeCumulant_map_mul_left (μ : Measure ℝ) (r : ℝ) (n : ℕ) :
    (μ.map (r * ·)).freeCumulant n = r ^ n * μ.freeCumulant n := by
  simpa [mul_comm] using congrArg (coeff n) (freeCumulantSeries_map_mul_left μ r)

/-- Pushing a measure forward by `x ↦ r * x` transforms its R-series by
`R_{r_* μ}(z) = r R_μ(r z)`. -/
theorem rSeries_map_mul_left (μ : Measure ℝ) (r : ℝ) :
    (μ.map (r * ·)).rSeries = r • rescale r μ.rSeries := by
  ext n
  simp [freeCumulant_map_mul_left, pow_succ', mul_assoc]

/-- Every power `x ↦ x ^ n` is integrable against a finite measure on `ℝ` with compact support. -/
theorem integrable_pow_of_isCompact_support {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) μ := by
  have hres : μ.restrict μ.support = μ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr Measure.measure_compl_support)
  rw [← hres]
  exact (continuous_pow n).continuousOn.integrableOn_compact hμ

/-- For a probability measure on `ℝ` with finite moments, translating by `a` adds the constant `a`
to the R-series: only the mean `κ₁` changes, while higher free cumulants are translation-invariant.
-/
theorem rSeries_map_add_left {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) μ) (a : ℝ) :
    (μ.map (a + ·)).rSeries = μ.rSeries + PowerSeries.C a := by
  let L : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun p := ∫ x, p.eval x ∂μ
      map_add' p q := by
        simpa only [Polynomial.eval_add] using
          integral_add (TauCeti.integrable_eval_of_forall_integrable_pow hμ p)
            (TauCeti.integrable_eval_of_forall_integrable_pow hμ q)
      map_smul' c p := by
        simpa only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply] using
          integral_const_mul c fun x ↦ p.eval x }
  have hL1 : L 1 = 1 := by simp [L]
  have hX : μ.rSeries = TauCeti.rSeries L Polynomial.X := by
    refine TauCeti.rSeries_congr _ _ ?_
    ext n
    rw [TauCeti.coeff_momentSeries, integral_id_pow, TauCeti.coeff_momentSeries]
    simp [L]
  have hXa : (μ.map (a + ·)).rSeries = TauCeti.rSeries L (Polynomial.X + Polynomial.C a) := by
    refine TauCeti.rSeries_congr _ _ ?_
    ext n
    rw [TauCeti.coeff_momentSeries, integral_id_pow, TauCeti.coeff_momentSeries,
      integral_map (by fun_prop) (by fun_prop)]
    simp [L, add_comm a]
  rw [hXa, hX, ← Polynomial.algebraMap_eq]
  exact TauCeti.rSeries_add_algebraMap hL1 Polynomial.X a

/-- For a probability measure on `ℝ` with finite moments, translating on the right by `a` adds `a`
to the R-series. -/
theorem rSeries_map_add_right {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) μ) (a : ℝ) :
    (μ.map (· + a)).rSeries = μ.rSeries + PowerSeries.C a := by
  simpa only [add_comm a] using rSeries_map_add_left hμ a

/-- For a probability measure on `ℝ` with finite moments, pushing forward along `x ↦ a + b * x`
transforms the R-series by `R(z) ↦ b R(b z) + a`. -/
theorem rSeries_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ n) μ) (a b : ℝ) :
    (μ.map fun x ↦ a + b * x).rSeries = b • rescale b μ.rSeries + PowerSeries.C a := by
  have hcomp : μ.map (fun x ↦ a + b * x) = (μ.map (b * ·)).map (a + ·) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hint (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (μ.map (b * ·)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    have hfun : ((fun x : ℝ ↦ x ^ n) ∘ (b * ·)) = fun x : ℝ ↦ b ^ n * x ^ n := by
      ext x
      exact mul_pow b x n
    rw [hfun]
    exact (hμ n).const_mul (b ^ n)
  rw [hcomp, rSeries_map_add_left hint a, rSeries_map_mul_left]

/-! ### Determinacy and exponential cumulant bounds for compactly supported measures -/

/-- Two finite Borel measures on `ℝ` with compact support are equal if and only if they have the
same formal moment series. -/
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

/-- Two compactly supported probability measures on `ℝ` are equal if and only if they have the same
free cumulant series. -/
theorem eq_iff_freeCumulantSeries_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ μ.freeCumulantSeries = ν.freeCumulantSeries :=
  (eq_iff_momentSeries_eq hμ hν).trans (freeCumulantSeries_eq_iff_momentSeries_eq μ ν).symm

/-- Two compactly supported probability measures on `ℝ` are equal if and only if they have the same
formal R-series. -/
theorem eq_iff_rSeries_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ μ.rSeries = ν.rSeries :=
  (eq_iff_momentSeries_eq hμ hν).trans (rSeries_eq_iff_momentSeries_eq μ ν).symm

/-- Two compactly supported probability measures on `ℝ` are equal if and only if all their
positive-order free cumulants agree. -/
theorem eq_iff_forall_freeCumulant_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ ∀ n ≠ 0, μ.freeCumulant n = ν.freeCumulant n :=
  (eq_iff_rSeries_eq hμ hν).trans rSeries_eq_iff_forall_freeCumulant_eq

private lemma nonneg_of_support_subset_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {C : ℝ}
    (hsupp : μ.support ⊆ Set.Icc (-C) C) : 0 ≤ C := by
  obtain ⟨x, hx⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero μ)
  have hx' := hsupp hx
  linarith [hx'.1, hx'.2]

private lemma norm_integral_id_pow_le_of_support_subset_Icc {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {C : ℝ} (hsupp : μ.support ⊆ Set.Icc (-C) C) (k : ℕ) :
    ‖integral μ ((id : ℝ → ℝ) ^ k)‖ ≤ C ^ k := by
  rw [integral_id_pow]
  have hae : ∀ᵐ x ∂μ, ‖x ^ k‖ ≤ C ^ k := by
    filter_upwards [Measure.support_mem_ae] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr (hsupp hx)) k
  have hint : Integrable (fun x : ℝ ↦ x ^ k) μ :=
    integrable_pow_of_isCompact_support
      (isCompact_Icc.of_isClosed_subset Measure.isClosed_support hsupp) k
  calc
    ‖∫ x, x ^ k ∂μ‖ ≤ ∫ x, ‖x ^ k‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _, C ^ k ∂μ := integral_mono_ae hint.norm (integrable_const _) hae
    _ = C ^ k := by simp

/-- If a probability measure `μ` on `ℝ` has support in `[-C, C]`, then
`|κ_n(μ)| ≤ (16 * C) ^ n` for every `n`. -/
theorem abs_freeCumulant_le_pow {μ : Measure ℝ} [IsProbabilityMeasure μ] {C : ℝ}
    (hsupp : μ.support ⊆ Set.Icc (-C) C) (n : ℕ) :
    |μ.freeCumulant n| ≤ (16 * C) ^ n := by
  rw [freeCumulant_eq_tauCetiFreeCumulant, ← Real.norm_eq_abs]
  simpa using TauCeti.norm_freeCumulant_const_le_pow (integral μ) id
    (s := (univ : Finset (Fin n))) (nonneg_of_support_subset_Icc hsupp) fun k _ _ ↦
      norm_integral_id_pow_le_of_support_subset_Icc hsupp k

/-- For a probability measure `μ` supported in `[-C, C]`, the formal free cumulant series converges
absolutely on the open disk `16 * C * |z| < 1`. -/
theorem summable_norm_coeff_freeCumulantSeries_mul_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {C : ℝ} (hsupp : μ.support ⊆ Set.Icc (-C) C) {z : ℝ} (hz : 16 * C * |z| < 1) :
    Summable fun n ↦ ‖coeff n μ.freeCumulantSeries * z ^ n‖ :=
  TauCeti.summable_norm_coeff_freeCumulantSeries_mul_pow
    (fun k _ ↦ norm_integral_id_pow_le_of_support_subset_Icc hsupp k)
    (by simpa [Real.norm_eq_abs] using hz)

/-- For a probability measure `μ` supported in `[-C, C]`, the formal R-series converges absolutely
on the open disk `16 * C * |z| < 1`. -/
theorem summable_norm_coeff_rSeries_mul_pow {μ : Measure ℝ} [IsProbabilityMeasure μ] {C : ℝ}
    (hsupp : μ.support ⊆ Set.Icc (-C) C) {z : ℝ} (hz : 16 * C * |z| < 1) :
    Summable fun n ↦ ‖coeff n μ.rSeries * z ^ n‖ :=
  TauCeti.summable_norm_coeff_rSeries_mul_pow
    (fun k _ ↦ norm_integral_id_pow_le_of_support_subset_Icc hsupp k)
    (by simpa [Real.norm_eq_abs] using hz)

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- The formal R-series of the semicircle law `semicircleReal a v` with centre `a` and variance `v`
is `a + v z`. -/
@[simp]
theorem rSeries_semicircleReal (a : ℝ) (v : ℝ≥0) :
    (semicircleReal a v).rSeries = PowerSeries.C a + PowerSeries.C (v : ℝ) * PowerSeries.X := by
  have h0 : (semicircleReal 0 v).rSeries = PowerSeries.C (v : ℝ) * PowerSeries.X := by
    let K := Set.Icc (-(2 * √(v : ℝ))) (2 * √(v : ℝ))
    let φ : C(K, ℂ) →ₚ[ℂ] ℂ :=
      ContinuousMap.integralPositiveLinearMap ((semicircleReal 0 v).comap ((↑) : K → ℝ))
    let x : C(K, ℂ) := (ContinuousMap.restrict K (ContinuousMap.id ℝ)).realToRCLike ℂ
    have hlaw : φ.law x = semicircleReal 0 v :=
      PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
        (by simpa only [zero_sub, zero_add, Set.ofPred_mem_eq] using
          mem_ae_iff.1 (ae_mem_Icc_semicircleReal 0 v))
    have hsc : IsSemicircular φ.toLinearMap x ((v : ℝ) : ℂ) :=
      isSemicircular_integralPositiveLinearMap_semicircleReal v
    ext n
    apply Complex.ofReal_injective
    rw [Measure.coeff_rSeries, ← hlaw,
      PositiveLinearMap.ofReal_freeCumulant_law φ (ContinuousMap.isSelfAdjoint_realToRCLike ℂ)]
    -- `PositiveLinearMap.toLinearMap` coerces to the same underlying function as `φ`.
    have hκ := hsc.freeCumulant_const (s := (univ : Finset (Fin (n + 1)))) univ_nonempty
    change TauCeti.freeCumulant φ (fun _ : Fin (n + 1) ↦ x) univ = _ at hκ
    rw [hκ, card_univ, Fintype.card_fin]
    rcases n with _ | _ | n <;> simp [PowerSeries.coeff_X]
  have hshift : semicircleReal a v = (semicircleReal 0 v).map (a + ·) := by
    simpa using (map_affine_semicircleReal 0 a 1 v).symm
  rw [hshift, Measure.rSeries_map_add_left (integrable_pow_semicircleReal 0 v) a, h0, add_comm]

/-- The free cumulants of `semicircleReal a v` are `κ₀ = 1`, `κ₁ = a`, `κ₂ = v`, and `κ_n = 0` for
`n ≥ 3`. -/
theorem freeCumulant_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    (semicircleReal a v).freeCumulant n =
      if n = 0 then 1 else if n = 1 then a else if n = 2 then (v : ℝ) else 0 := by
  rcases n with _ | _ | _ | k
  · simp
  all_goals rw [← Measure.coeff_rSeries, rSeries_semicircleReal]; simp

end TauCeti.Probability
