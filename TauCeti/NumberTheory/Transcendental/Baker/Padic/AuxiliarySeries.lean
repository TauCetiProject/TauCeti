/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Derivative
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Polynomial

/-!
# Baker's auxiliary series on the diagonal

For each frequency index `t`, a polynomial `Q t` in the distinguished coordinate is
multiplied by an exponential in all coordinates. The series
`TauCeti.Baker.diagonalAuxiliarySeries` is a formal extension of the diagonal mixed derivatives
that allows the frequencies `ψ t` to vary independently of the coordinate multipliers
`a t` and `c t i`. When `ψ t = a t + ∑ i, c t i` for every `t`, the series gives the mixed
derivatives of the multivariate sum restricted to the diagonal. For the Baker argument, take
`ψ t = ∑ i, t i * λ i`, `a t = t 0 * θ` and `c t i = (t i + t 0 * b i) * λ i`
for the remaining coordinates.

The relation `ψ t = a t + ∑ i, c t i` gives
`TauCeti.Baker.derivative_diagonalAuxiliarySeries`: the derivative on the diagonal is the sum
of the mixed derivatives with one coordinate order increased. It uses
`PowerSeries.derivative_rescale_exp` and `Polynomial.expDerivFactor_succ`.
`TauCeti.Baker.hasSum_coeff_diagonalAuxiliarySeries` evaluates the series wherever all its
exponential factors converge on their open `p`-adic discs, using
`PowerSeries.hasSum_coeff_coe_mul_rescale_exp`.

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
    (m₀ : ℕ) (m : ι → ℕ) : (T → A[X]) →ₗ[A] A⟦X⟧ :=
  ∑ t, (∏ i, c t i ^ m i) •
    ((LinearMap.mulRight A (PowerSeries.rescale (ψ t) (PowerSeries.exp A))).comp
      ((Polynomial.coeToPowerSeries.algHom A).toLinearMap.comp
        ((Polynomial.expDerivFactor (a t) m₀).comp (LinearMap.proj t))))

-- The full expansion stays out of the simp set so identities for the diagonal series can apply.
/-- The exponential-polynomial expansion with frequencies `ψ` independent of `a` and `c`.
It gives the mixed derivative of Baker's multivariate sum restricted to the diagonal when
`ψ t = a t + ∑ i, c t i` for every `t`, and is a formal extension for arbitrary `ψ`. -/
theorem diagonalAuxiliarySeries_apply (ψ a : T → A) (c : T → ι → A) (m₀ : ℕ)
    (m : ι → ℕ) (Q : T → A[X]) :
    diagonalAuxiliarySeries ψ a c m₀ m Q =
      ∑ t, (∏ i, c t i ^ m i) •
        ((Polynomial.expDerivFactor (a t) m₀ (Q t) : A⟦X⟧) *
          PowerSeries.rescale (ψ t) (PowerSeries.exp A)) := by
  rw [diagonalAuxiliarySeries]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
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
    calc
      _ = c t i ^ (m i + 1) * ∏ j ∈ Finset.univ.erase i, c t j ^ m j := by
        rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
      _ = _ := by
        rw [pow_succ', mul_assoc, Finset.mul_prod_erase _ (fun j ↦ c t j ^ m j) (Finset.mem_univ i)]
  simp only [hprod, ← Finset.sum_smul, ← Finset.sum_mul, Derivation.map_smul,
    Derivation.leibniz, PowerSeries.derivative_rescale_exp, PowerSeries.derivative_coe,
    Polynomial.expDerivFactor_succ, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C]
  simp only [smul_eq_mul, Algebra.smul_def, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, map_mul]
  rw [hψ t, map_add]
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

end TauCeti.Baker
