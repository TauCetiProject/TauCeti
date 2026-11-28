/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Derivative
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Polynomial
import Mathlib.Analysis.Normed.Algebra.Ultra
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Polynomial.Ultra

/-!
# Baker's auxiliary series on the diagonal

For each frequency index `t`, a polynomial `Q t` in the distinguished coordinate is
multiplied by an exponential in all coordinates. The series
`TauCeti.Baker.diagonalAuxiliarySeries` is a formal extension of the diagonal mixed derivatives
that allows the frequencies `ψ t` to vary independently of the coordinate multipliers
`a t` and `c t i`. When `ψ t = a t + ∑ i, c t i` for every `t`, the series gives the mixed
derivatives of the multivariate sum restricted to the diagonal. For the Baker argument, take
`ψ t = ∑ o, t o * λ o`, `a t = t 0 * θ` and `c t i = (t i + t 0 * b i) * λ i`,
where `o` includes coordinate `0` and `i` ranges over the remaining coordinates. These satisfy
`ψ t = a t + ∑ i, c t i` for all grid indices `t` exactly when the relation to be refuted,
`λ 0 = θ + ∑ i, b i * λ i`, holds. The frequency difference is `t 0` times
`λ 0 - (θ + ∑ i, b i * λ i)`, and for degree bound at least one the grid contains the unit vector
in coordinate `0`. The definition assumes no such relation.

The relation `ψ t = a t + ∑ i, c t i` gives
`TauCeti.Baker.derivative_diagonalAuxiliarySeries`: the derivative on the diagonal is the sum
of the mixed derivatives with one coordinate order increased. Iterating this identity turns
vanishing of mixed derivatives into a univariate zero with multiplicity. The proof uses
`PowerSeries.derivative_coe_mul_of_derivative_eq_C_mul` and `Polynomial.expDerivFactor_succ`.
`TauCeti.Baker.hasSum_coeff_diagonalAuxiliarySeries` evaluates the series wherever all its
exponential arguments `ψ t * x` lie in the open `p`-adic convergence disc, using
`PowerSeries.hasSum_coeff_coe_mul_rescale_exp`.

`TauCeti.Baker.norm_coeff_diagonalAuxiliarySeries_mul_pow_le` bounds the coefficients
at a common radius, using `Polynomial.norm_coeff_expDerivFactor_le`,
`Polynomial.norm_coeff_mul_pow_le_of_natDegree_le`, and
`PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le`. The bound supplies the input
to the ultrametric Schwarz estimate in Baker's extrapolation.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2.
* B. Rousseau, *Théorème de Baker–Brumer sur les unités d'un corps de nombres algébriques*,
  Séminaire de théorie des nombres de Bordeaux (1968–1969), exposé 11, Lemmes 1–2.
-/

public section

open scoped Polynomial PowerSeries

namespace TauCeti.Baker

variable {A T ι : Type*} [CommRing A] [Algebra ℚ A] [Fintype T] [Fintype ι]

/-- The diagonal series at orders `m₀` and `m`, linear in the polynomial family `Q`.
Its term at `t` is `((D + a t)^m₀ (Q t)) * exp (ψ t * X)` scaled by
`∏ i, (c t i) ^ (m i)`. -/
noncomputable def diagonalAuxiliarySeries (ψ a : T → A) (c : T → ι → A)
    (m₀ : ℕ) (m : ι → ℕ) : (T → A[X]) →ₗ[A] A⟦X⟧ := by
  classical
  exact LinearMap.lsum A (fun _ : T ↦ A[X]) A fun t ↦ (∏ i, c t i ^ m i) •
    ((LinearMap.mulRight A (PowerSeries.rescale (ψ t) (PowerSeries.exp A))).comp
      ((Polynomial.coeToPowerSeries.algHom A).toLinearMap.comp
        (Polynomial.expDerivFactor (a t) m₀)))

-- The full expansion stays out of the simp set so identities for the diagonal series can apply.
/-- The explicit expansion of `diagonalAuxiliarySeries` applied to `Q`, for arbitrary `ψ`.
The mixed-derivative interpretation in the module overview requires `ψ t = a t + ∑ i, c t i`
for every `t`. -/
theorem diagonalAuxiliarySeries_apply (ψ a : T → A) (c : T → ι → A) (m₀ : ℕ)
    (m : ι → ℕ) (Q : T → A[X]) :
    diagonalAuxiliarySeries ψ a c m₀ m Q =
      ∑ t, (∏ i, c t i ^ m i) •
        ((Polynomial.expDerivFactor (a t) m₀ (Q t) : A⟦X⟧) *
          PowerSeries.rescale (ψ t) (PowerSeries.exp A)) := by
  classical
  rw [diagonalAuxiliarySeries]
  simp only [LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, Polynomial.coeToPowerSeries.algHom_apply,
    LinearMap.proj_apply, Algebra.algebraMap_self, PowerSeries.map_id, id_eq]

/-- At orders zero the diagonal series is the original sum of exponential polynomials. -/
@[simp]
theorem diagonalAuxiliarySeries_zero_orders (ψ a : T → A) (c : T → ι → A) (Q : T → A[X]) :
    diagonalAuxiliarySeries ψ a c 0 0 Q =
      ∑ t, (Q t : A⟦X⟧) * PowerSeries.rescale (ψ t) (PowerSeries.exp A) := by
  simp only [diagonalAuxiliarySeries_apply, Pi.zero_apply, pow_zero, Finset.prod_const_one,
    one_smul, Polynomial.expDerivFactor_zero]

/-- When the diagonal frequency equals the sum of the coordinate multipliers at each index,
differentiating the diagonal series raises each coordinate order in turn and sums the results. -/
theorem derivative_diagonalAuxiliarySeries [DecidableEq ι] {ψ a : T → A}
    {c : T → ι → A} (hψ : ∀ t, ψ t = a t + ∑ i, c t i) (m₀ : ℕ) (m : ι → ℕ)
    (Q : T → A[X]) :
    PowerSeries.derivative (diagonalAuxiliarySeries ψ a c m₀ m Q) =
      diagonalAuxiliarySeries ψ a c (m₀ + 1) m Q +
        ∑ i, diagonalAuxiliarySeries ψ a c m₀ (Function.update m i (m i + 1)) Q := by
  simp only [diagonalAuxiliarySeries_apply, map_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hprod (i : ι) :
      (∏ j, c t j ^ Function.update m i (m i + 1) j) =
        c t i * ∏ j, c t j ^ m j := by
    have heq : (fun j ↦ c t j ^ Function.update m i (m i + 1) j) =
        Function.update (fun j ↦ c t j ^ m j) i (c t i ^ (m i + 1)) := by
      exact funext (Function.apply_update (fun j n ↦ c t j ^ n) m i (m i + 1))
    rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i), pow_succ', mul_assoc,
      ← Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j ↦ c t j ^ m j)]
  simp only [hprod, ← Finset.sum_smul, ← Finset.sum_mul, Derivation.map_smul,
    PowerSeries.derivative_coe_mul_of_derivative_eq_C_mul (PowerSeries.derivative_rescale_exp _)]
  rw [Polynomial.expDerivFactor_one, Polynomial.expDerivFactor_succ, hψ t]
  push_cast [PowerSeries.smul_eq_C_mul, map_add, map_mul]
  ring

/-- Evaluation on the common convergence disc of the exponential factors in the diagonal series. -/
theorem hasSum_coeff_diagonalAuxiliarySeries {p : ℕ} [Fact p.Prime] {L : Type*}
    [NormedField L] [Algebra ℚ L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]
    {ψ : T → L} (a : T → L) (c : T → ι → L) (m₀ : ℕ) (m : ι → ℕ) (Q : T → L[X])
    {x : L} (hx : ∀ t, ‖ψ t * x‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    HasSum (fun n ↦ PowerSeries.coeff n (diagonalAuxiliarySeries ψ a c m₀ m Q) * x ^ n)
      (∑ t, (∏ i, c t i ^ m i) * ((Polynomial.expDerivFactor (a t) m₀ (Q t)).eval x *
        NormedSpace.exp (ψ t * x))) := by
  have h := hasSum_sum (s := (Finset.univ : Finset T)) fun t _ ↦
    (PowerSeries.hasSum_coeff_coe_mul_rescale_exp
      (Polynomial.expDerivFactor (a t) m₀ (Q t)) (hx t)).mul_left (∏ i, c t i ^ m i)
  refine h.congr_fun fun n ↦ ?_
  simp only [diagonalAuxiliarySeries_apply, map_sum, map_smul, Finset.sum_mul, smul_eq_mul,
    mul_assoc]

/-- At a radius `r ≥ 1`, suppose the frequencies satisfy
`‖ψ t‖ * r ≤ p ^ (-1 / (p - 1))`. If the polynomials have degrees at most `D` and
coefficients of norm at most `M`, and the coordinate multipliers have norms at most `B ≥ 1`,
then the weighted coefficients of the diagonal series are bounded by
`B ^ (m₀ + ∑ i, m i) * M * r ^ D`. This is the coefficient estimate used in Baker's
extrapolation (Baker, *Transcendental Number Theory*, Chapter 2). -/
theorem norm_coeff_diagonalAuxiliarySeries_mul_pow_le {p : ℕ} [Fact p.Prime] {L : Type*}
    [NormedField L] [Algebra ℚ L] [NormedAlgebra ℚ_[p] L]
    {ψ a : T → L} {c : T → ι → L} {Q : T → L[X]} {r B M : ℝ} {D : ℕ}
    (hr : 1 ≤ r) (hB : 1 ≤ B) (hM : 0 ≤ M)
    (hψ : ∀ t, ‖ψ t‖ * r ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹))
    (ha : ∀ t, ‖a t‖ ≤ B) (hc : ∀ t i, ‖c t i‖ ≤ B)
    (hD : ∀ t, (Q t).natDegree ≤ D) (hQ : ∀ t j, ‖(Q t).coeff j‖ ≤ M)
    (m₀ : ℕ) (m : ι → ℕ) (k : ℕ) :
    ‖PowerSeries.coeff k (diagonalAuxiliarySeries ψ a c m₀ m Q)‖ * r ^ k ≤
      B ^ (m₀ + ∑ i, m i) * M * r ^ D := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hr₀ : 0 ≤ r := zero_le_one.trans hr
  simp only [diagonalAuxiliarySeries_apply, map_sum, map_smul]
  refine IsUltrametricDist.norm_sum_mul_le_of_forall_le (pow_nonneg hr₀ _) (by positivity)
    fun t _ ↦ ?_
  have hpoly (j : ℕ) :
      ‖(Polynomial.expDerivFactor (a t) m₀ (Q t)).coeff j‖ * r ^ j ≤ B ^ m₀ * M * r ^ D := by
    have hdeg := (Polynomial.natDegree_expDerivFactor_le (a t) m₀ (Q t)).trans (hD t)
    have hcoeff :
        ‖(Polynomial.expDerivFactor (a t) m₀ (Q t)).coeff j‖ ≤ B ^ m₀ * M := by
      refine (Polynomial.norm_coeff_expDerivFactor_le (a t) (hQ t) m₀ j).trans ?_
      gcongr
      exact max_le hB (ha t)
    simpa only [div_one] using
      Polynomial.norm_coeff_mul_pow_le_of_natDegree_le zero_lt_one hr hdeg
        (by simpa only [one_pow, mul_one] using hcoeff)
  have hscale : ‖∏ i, c t i ^ m i‖ ≤ B ^ ∑ i, m i := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    simp only [norm_pow]
    exact Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg (norm_nonneg _) _)
      (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hc t i) _)
  have hterm := PowerSeries.norm_coeff_coe_mul_rescale_exp_mul_pow_le hr₀ hpoly (hψ t) k
  rw [smul_eq_mul, norm_mul, mul_assoc, pow_add]
  calc
    _ ≤ B ^ (∑ i, m i) * (B ^ m₀ * M * r ^ D) :=
      mul_le_mul hscale hterm (by positivity) (by positivity)
    _ = _ := by ring

end TauCeti.Baker
