/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Interval
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Function.Lp.Integral.L2NormSq

/-!
# The second Neumann eigenvalue of the unit interval

On `(0, 1)`, realized as the open subset `TauCeti.PDE.intervalDomain 0 1` of the Euclidean line,
the weak Neumann eigenvalues of `-Δ` are `m² π²`, `m ≥ 0`, with eigenfunctions `cos (m π x)`.
The second one, `λ₂ = π²`, is the minimum of the Rayleigh quotient `‖∇u‖² / ‖u‖²` over the nonzero
`u ∈ H¹(0, 1)` of mean zero (`isLeast_rayleigh_meanZero_unitInterval`), and `cos (π x)`, which has
mean zero, attains it.

The mean-zero function `x - 1/2` is a competitor that does not attain it: `∫_0^1 (x - 1/2)² = 1/12`
and `∫_0^1 1² = 1`, so its quotient is `12 > π²`
(`setIntegral_eq_zero_and_rayleigh_eq_twelve_of_value_ae_eq_sub_half`). Since the eigenfunctions
of `λ₂` are exactly the mean-zero minimizers, `x - 1/2` is not one of them
(`not_forall_inner_gradient_eq_of_value_ae_eq_sub_half`).

## Main declarations

All declarations are in the namespace `TauCeti.Examples.NeumannUnitInterval`.

* `isLeast_rayleigh_meanZero_unitInterval`: `λ₂ = π²` is the least Rayleigh quotient of mean zero
  on `(0, 1)`.
* `exists_value_ae_eq_cos_and_setIntegral_eq_zero_and_rayleigh_eq_unitInterval`: `cos (π x)` has
  mean zero and quotient `π²`.
* `exists_value_ae_eq_sub_half` and
  `setIntegral_eq_zero_and_rayleigh_eq_twelve_of_value_ae_eq_sub_half`: `x - 1/2` lies in
  `H¹(0, 1)`, has mean zero and quotient `12`.
* `not_forall_inner_gradient_eq_of_value_ae_eq_sub_half`: `x - 1/2` is not an eigenfunction of
  `λ₂ = π²`.

## References

* R. Courant and D. Hilbert, *Methods of Mathematical Physics*, Vol. I, Chapter VI, §1
  (eigenvalues as minima of the Rayleigh quotient, with natural boundary conditions when no
  boundary condition is imposed).
-/

public section

noncomputable section

namespace TauCeti.Examples.NeumannUnitInterval

open MeasureTheory Set TopologicalSpace TauCeti.PDE
open scoped Real InnerProductSpace

/-- **The second Neumann eigenvalue of `(0, 1)` is `π²`**: it is the minimum of the Rayleigh
quotient `‖∇u‖² / ‖u‖²` over the nonzero `u ∈ H¹(0, 1)` with `∫_0^1 u = 0`. -/
theorem isLeast_rayleigh_meanZero_unitInterval :
    IsLeast {r | ∃ u : W1p volume (intervalDomain 0 1) 2, W1p.value u ≠ 0 ∧
        ∫ x in intervalDomain 0 1, W1p.value u x = 0 ∧
        r = ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2} (π ^ 2) := by
  simpa using isLeast_rayleigh_meanZero_intervalDomain (a := 0) (b := 1) zero_lt_one

/-- **`cos (π x)` attains the second Neumann eigenvalue of `(0, 1)`**: some `u ∈ H¹(0, 1)` with
value `x ↦ cos (π x)` has mean zero and Rayleigh quotient `π²`. -/
theorem exists_value_ae_eq_cos_and_setIntegral_eq_zero_and_rayleigh_eq_unitInterval :
    ∃ u : W1p volume (intervalDomain 0 1) 2,
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => Real.cos (π * x 0)) ∧
      ∫ x in intervalDomain 0 1, W1p.value u x = 0 ∧
      ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2 = π ^ 2 := by
  simpa using exists_value_ae_eq_cos_and_setIntegral_eq_zero_and_rayleigh_eq (a := 0) (b := 1)
    zero_lt_one

/-- Some `u ∈ H¹(0, 1)` has value `x - 1/2` and constant gradient `e₀`. -/
private theorem exists_value_ae_eq_sub_half_and_gradient_ae_eq :
    ∃ u : W1p volume (intervalDomain 0 1) 2,
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => x 0 - 1 / 2) ∧
      W1p.gradient u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun _ => EuclideanSpace.single 0 1) := by
  obtain ⟨v, hv, hg⟩ := W1p.exists_value_gradient_ae_eq_apply (mu := volume)
    (Omega := intervalDomain 0 1) (p := 2) isBounded_intervalDomain 0
  refine ⟨v - W1p.const (1 / 2), ?_, ?_⟩
  · filter_upwards [W1p.value_sub_ae v (W1p.const (1 / 2)), W1p.value_const_ae (mu := volume)
      (Omega := intervalDomain 0 1) (p := 2) (1 / 2), hv] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  · rwa [W1p.gradient_sub, W1p.gradient_const, sub_zero]

/-- **`x - 1/2` lies in `H¹(0, 1)`.** -/
theorem exists_value_ae_eq_sub_half :
    ∃ u : W1p volume (intervalDomain 0 1) 2,
      W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
        (fun x => x 0 - 1 / 2) :=
  exists_value_ae_eq_sub_half_and_gradient_ae_eq.imp fun _ h => h.1

/-- `∫_0^1 (t - 1/2)² = 1/12`. -/
private theorem setIntegral_Ioo_sub_half_sq :
    ∫ t in Ioo (0 : ℝ) 1, (t - 1 / 2) ^ 2 = 1 / 12 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right (fun t => t ^ 2), integral_pow]
  norm_num

/-- **`x - 1/2` has mean zero and Rayleigh quotient `12` on `(0, 1)`.** Every `u ∈ H¹(0, 1)` with
value `x - 1/2` has `∫_0^1 u = 0` and `‖∇u‖² / ‖u‖² = 1 / (1/12) = 12`, which exceeds the second
Neumann eigenvalue `π²` (`isLeast_rayleigh_meanZero_unitInterval`). -/
theorem setIntegral_eq_zero_and_rayleigh_eq_twelve_of_value_ae_eq_sub_half
    {u : W1p volume (intervalDomain 0 1) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
      (fun x => x 0 - 1 / 2)) :
    ∫ x in intervalDomain 0 1, W1p.value u x = 0 ∧
      ‖W1p.gradient u‖ ^ 2 / ‖W1p.value u‖ ^ 2 = 12 := by
  obtain ⟨w, hwv, hwg⟩ := exists_value_ae_eq_sub_half_and_gradient_ae_eq
  -- A Sobolev class is determined by its value.
  obtain rfl : u = w := W1p.ext_value (Lp.ext (hu.trans hwv.symm))
  have hnorm : ‖W1p.value u‖ ^ 2 = 1 / 12 := by
    rw [L2.norm_sq_eq_integral_sq_of_ae_eq hu, setIntegral_intervalDomain_eq_setIntegral_Ioo]
    simpa using setIntegral_Ioo_sub_half_sq
  have hgrad : ‖W1p.gradient u‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def,
      integral_congr_ae (g := fun _ => (1 : ℝ)) (by
        filter_upwards [hwg] with x hx
        simp [hx]),
      setIntegral_intervalDomain_eq_setIntegral_Ioo]
    simp
  refine ⟨?_, by rw [hnorm, hgrad]; norm_num⟩
  rw [integral_congr_ae hu, setIntegral_intervalDomain_eq_setIntegral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  simp [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const]

/-- **`x - 1/2` is not an eigenfunction of the second Neumann eigenvalue `π²` of `(0, 1)`.** The
eigenfunctions of `π²` are exactly the mean-zero `u` with `‖∇u‖² = π² ‖u‖²`
(`TauCeti.PDE.forall_inner_gradient_eq_iff_intervalDomain`), while `x - 1/2` has
`‖∇u‖² = 12 ‖u‖²` and `π² < 12`. -/
theorem not_forall_inner_gradient_eq_of_value_ae_eq_sub_half
    {u : W1p volume (intervalDomain 0 1) 2}
    (hu : W1p.value u =ᵐ[volume.restrict (intervalDomain 0 1 : Set (EuclideanSpace ℝ (Fin 1)))]
      (fun x => x 0 - 1 / 2)) :
    ¬ ∀ v : W1p volume (intervalDomain 0 1) 2,
      ⟪W1p.gradient u, W1p.gradient v⟫_ℝ = π ^ 2 * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  intro h
  have h1 := ((forall_inner_gradient_eq_iff_intervalDomain u).1
    (by simpa using h)).2
  have h12 := (setIntegral_eq_zero_and_rayleigh_eq_twelve_of_value_ae_eq_sub_half hu).2
  have hne : ‖W1p.value u‖ ≠ 0 := by
    rintro h0
    norm_num [h0] at h12
  rw [h1] at h12
  field_simp at h12
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

end TauCeti.Examples.NeumannUnitInterval
