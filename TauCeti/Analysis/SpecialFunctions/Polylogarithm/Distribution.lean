/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.RootsOfUnity.SlitPlane
import TauCeti.RingTheory.RootsOfUnity.PartialFractions

/-!
# Distribution of nonpositive-weight polylogarithms

In every nonpositive integer weight `n ≤ 0`, the polylogarithm `Li_n(z)` is a rational function
with sole pole at `z = 1`, so its multiplicative distribution relation holds on the full
complement `{z : ℂ | z ^ m ≠ 1}` of the `m`-th roots of unity—strictly larger than the `m`-ray
star-slit domain `Ω_m = {z : ℂ | 1 - z ^ m ∈ Complex.slitPlane}` required in positive weights:
`polylog n (z ^ m) = m ^ (n - 1) * ∑ j ∈ Finset.range m, polylog n (ζ ^ j * z)`
for any primitive `m`-th root of unity `ζ`.

In weight zero, this is the root-of-unity partial-fraction identity
`IsPrimitiveRoot.sum_pow_mul_div_one_sub`, carrying the normalization factor `m ^ (-1) = 1 / m`.
Higher negative weights `n = -r` follow by induction on `r` on the open set `{w : ℂ | w ^ m ≠ 1}`:
applying the Euler operator `z ↦ z * deriv · z` scales the left-hand side by `m`
(`mul_deriv_polylog_neg_nat_comp_pow`) and commutes with each rotation `w ↦ ζ ^ j * w` on the
right-hand side (`mul_deriv_polylog_neg_nat_comp_const_mul`), shifting the prefactor from
`m ^ (-r - 1)` to `m ^ (-(r + 1) - 1)`.

## Main declarations

* `TauCeti.Polylog.polylog_distribution_of_nonpos_of_isPrimitiveRoot`: distribution in weight
  `n ≤ 0` over powers of any primitive `m`-th root of unity on `{z | z ^ m ≠ 1}`.
* `TauCeti.Polylog.polylog_distribution_of_nonpos`: distribution in weight `n ≤ 0` with the
  standard roots `exp (2 * π * I * j / m)` on `{z | z ^ m ≠ 1}`.
* `TauCeti.Polylog.polylog_distribution_of_nonpos_of_slitPlane`: specialization to the `m`-ray
  principal domain `∀ j ∈ Finset.range m, 1 - exp (2 * π * I * j / m) * z ∈ Complex.slitPlane`.
* `TauCeti.Polylog.polylog_sq_of_nonpos`: duplication (`m = 2`) in weight `n ≤ 0` on
  `{z | z ^ 2 ≠ 1}`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.2, `(4_r)`, p. 50.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics,
  and Geometry II (2007), Part I, §2, p. 9.
-/

public section

namespace TauCeti.Polylog

/-- Distribution in weight zero over the translates of `z` by a primitive `m`-th root of unity,
valid wherever `z ^ m ≠ 1`. The prefactor is `m⁻¹`, not `m`. -/
theorem polylog_zero_weight_pow_of_isPrimitiveRoot {m : ℕ} {ζ z : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hz : z ^ m ≠ 1) :
    polylog 0 (z ^ m) = (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m, polylog 0 (ζ ^ j * z) := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hz (pow_zero z)
  have hm_cast : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simp only [polylog_zero_weight]
  rw [hζ.sum_pow_mul_div_one_sub hz, mul_div_assoc, inv_mul_cancel_left₀ hm_cast]

/-- Distribution in weight `-r` (`r : ℕ`) over a primitive `m`-th root of unity on
`{z : ℂ | z ^ m ≠ 1}`. -/
theorem polylog_neg_nat_pow_of_isPrimitiveRoot (r : ℕ) {m : ℕ} {ζ z : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hz : z ^ m ≠ 1) :
    polylog (-(r : ℤ)) (z ^ m) =
      (m : ℂ) ^ (-(r : ℤ) - 1) * ∑ j ∈ Finset.range m, polylog (-(r : ℤ)) (ζ ^ j * z) := by
  induction r generalizing z with
  | zero =>
    simpa using polylog_zero_weight_pow_of_isPrimitiveRoot hζ hz
  | succ r ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      exact hz (pow_zero z)
    have hm_cast : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hU : IsOpen {w : ℂ | w ^ m ≠ 1} := isOpen_ne.preimage (continuous_pow m)
    have heq :
        (fun w : ℂ => polylog (-(r : ℤ)) (w ^ m)) =ᶠ[nhds z]
          fun w : ℂ =>
            (m : ℂ) ^ (-(r : ℤ) - 1) * ∑ j ∈ Finset.range m, polylog (-(r : ℤ)) (ζ ^ j * w) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) fun w hw => ih hw
    have hderiv := congrArg (z * ·) heq.deriv_eq
    rw [mul_deriv_polylog_neg_nat_comp_pow r m hz] at hderiv
    have hζz_ne (j : ℕ) : ζ ^ j * z ≠ 1 :=
      sub_ne_zero.mp <| TauCeti.mul_sub_one_ne_zero_of_pow_eq_one
        (by simp [pow_right_comm ζ j m, hζ.pow_eq_one] : (ζ ^ j) ^ m = 1) hz
    have hdiff (j : ℕ) : DifferentiableAt ℂ (fun w => polylog (-(r : ℤ)) (ζ ^ j * w)) z := by
      simpa only [Function.comp_def] using
        (analyticAt_polylog_neg_nat r (hζz_ne j)).differentiableAt.comp z
          (differentiableAt_id.const_mul (ζ ^ j))
    have hdiff_sum :
        DifferentiableAt ℂ (fun w => ∑ j ∈ Finset.range m, polylog (-(r : ℤ)) (ζ ^ j * w)) z :=
      DifferentiableAt.fun_sum fun j _ => hdiff j
    rw [deriv_const_mul _ hdiff_sum, deriv_fun_sum fun j _ => hdiff j] at hderiv
    have hrhs :
        z * ((m : ℂ) ^ (-(r : ℤ) - 1) *
            ∑ j ∈ Finset.range m, deriv (fun w => polylog (-(r : ℤ)) (ζ ^ j * w)) z) =
          (m : ℂ) ^ (-(r : ℤ) - 1) *
            ∑ j ∈ Finset.range m, polylog (-((r + 1 : ℕ) : ℤ)) (ζ ^ j * z) := by
      rw [← mul_assoc, mul_comm z, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      exact mul_deriv_polylog_neg_nat_comp_const_mul r (ζ ^ j) (hζz_ne j)
    rw [hrhs] at hderiv
    have hexp :
        (m : ℂ)⁻¹ * (m : ℂ) ^ (-(r : ℤ) - 1) = (m : ℂ) ^ (-((r + 1 : ℕ) : ℤ) - 1) := by
      rw [← zpow_neg_one, ← zpow_add₀ hm_cast]
      congr 1
      push_cast
      ring
    calc
      polylog (-((r + 1 : ℕ) : ℤ)) (z ^ m)
          = (m : ℂ)⁻¹ * ((m : ℂ) * polylog (-((r + 1 : ℕ) : ℤ)) (z ^ m)) := by
        rw [inv_mul_cancel_left₀ hm_cast]
      _ = (m : ℂ)⁻¹ * ((m : ℂ) ^ (-(r : ℤ) - 1) *
            ∑ j ∈ Finset.range m, polylog (-((r + 1 : ℕ) : ℤ)) (ζ ^ j * z)) := by
        rw [hderiv]
      _ = (m : ℂ) ^ (-((r + 1 : ℕ) : ℤ) - 1) *
            ∑ j ∈ Finset.range m, polylog (-((r + 1 : ℕ) : ℤ)) (ζ ^ j * z) := by
        rw [← mul_assoc, hexp]

/-- Distribution in nonpositive integer weight `n ≤ 0` over the powers of any primitive `m`-th
root of unity, valid for all `z` with `z ^ m ≠ 1`. -/
theorem polylog_distribution_of_nonpos_of_isPrimitiveRoot {n : ℤ} (hn : n ≤ 0) {m : ℕ} {ζ z : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hz : z ^ m ≠ 1) :
    polylog n (z ^ m) = (m : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range m, polylog n (ζ ^ j * z) := by
  lift -n to ℕ using neg_nonneg.mpr hn with r hr
  obtain rfl : n = -(r : ℤ) := neg_eq_iff_eq_neg.mp hr.symm
  exact polylog_neg_nat_pow_of_isPrimitiveRoot r hζ hz

/-- Distribution in nonpositive integer weight `n ≤ 0` over the standard `m`-th roots of unity
`exp (2 * π * I * j / m)`, valid wherever `z ^ m ≠ 1`. No `0 < m` hypothesis is needed because
`z ^ 0 = 1` is already excluded by `z ^ m ≠ 1`. -/
theorem polylog_distribution_of_nonpos (n : ℤ) (hn : n ≤ 0) (m : ℕ) {z : ℂ} (hz : z ^ m ≠ 1) :
    polylog n (z ^ m) = (m : ℂ) ^ (n - 1) *
      ∑ j ∈ Finset.range m, polylog n (Complex.exp (2 * Real.pi * Complex.I * j / m) * z) := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hz (pow_zero z)
  rw [polylog_distribution_of_nonpos_of_isPrimitiveRoot hn (Complex.isPrimitiveRoot_exp m hm) hz]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hexp :
      Complex.exp (2 * Real.pi * Complex.I / m) ^ j =
        Complex.exp (2 * Real.pi * Complex.I * j / m) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hexp]

/-- Distribution in nonpositive integer weight `n ≤ 0` on the `m`-ray star-slit domain where every
`exp (2 * π * I * j / m) * z` avoids `[1, ∞)`. -/
theorem polylog_distribution_of_nonpos_of_slitPlane (n : ℤ) (hn : n ≤ 0) (m : ℕ) (hm : 0 < m)
    {z : ℂ} (hz : ∀ j ∈ Finset.range m,
      1 - Complex.exp (2 * Real.pi * Complex.I * j / m) * z ∈ Complex.slitPlane) :
    polylog n (z ^ m) = (m : ℂ) ^ (n - 1) *
      ∑ j ∈ Finset.range m, polylog n (Complex.exp (2 * Real.pi * Complex.I * j / m) * z) := by
  have hzm_slit : 1 - z ^ m ∈ Complex.slitPlane :=
    Complex.one_sub_pow_mem_slitPlane_of_forall_exp hm hz
  have hzm_ne : z ^ m ≠ 1 := fun h =>
    Complex.slitPlane_ne_zero hzm_slit (by rw [h, sub_self])
  exact polylog_distribution_of_nonpos n hn m hzm_ne

/-- Duplication (`m = 2`) for nonpositive-weight polylogarithms away from `z = ±1`. -/
theorem polylog_sq_of_nonpos {n : ℤ} (hn : n ≤ 0) {z : ℂ} (hz : z ^ 2 ≠ 1) :
    polylog n (z ^ 2) = (2 : ℂ) ^ (n - 1) * (polylog n z + polylog n (-z)) := by
  have hζ : IsPrimitiveRoot (-1 : ℂ) 2 :=
    IsPrimitiveRoot.neg_one_of_two_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  simpa [Finset.sum_range_succ] using polylog_distribution_of_nonpos_of_isPrimitiveRoot hn hζ hz

-- At `m = 1`, the distribution right-hand side reduces immediately to `polylog n z`.
example (n : ℤ) (z : ℂ) :
    (1 : ℂ) ^ (n - 1) *
        ∑ j ∈ Finset.range 1, polylog n (Complex.exp (2 * Real.pi * Complex.I * j / 1) * z) =
      polylog n z := by
  simp

-- In weight zero with `m = 2`, the duplication prefactor is `1 / 2`, not `2`.
example {z : ℂ} (hz : z ^ 2 ≠ 1) :
    polylog 0 (z ^ 2) = (1 / 2 : ℂ) * (polylog 0 z + polylog 0 (-z)) := by
  simpa [one_div] using polylog_sq_of_nonpos (n := 0) le_rfl hz

-- On the unit circle at `z = I`, `I ^ 2 = -1 ≠ 1` and weight `-1` duplication gives `-1 / 4`.
example : (2 : ℂ) ^ ((-1 : ℤ) - 1) * (polylog (-1) Complex.I + polylog (-1) (-Complex.I)) =
    -(1 / 4 : ℂ) := by
  have hI : Complex.I ^ 2 ≠ (1 : ℂ) := by norm_num [Complex.I_sq]
  rw [← polylog_sq_of_nonpos (by omega) hI, Complex.I_sq]
  exact polylog_neg_one_neg_one

-- At the excluded pole `z = 1`, totalised division does not satisfy weight-zero duplication.
example : polylog 0 ((1 : ℂ) ^ 2) ≠
    (2 : ℂ) ^ ((0 : ℤ) - 1) * (polylog 0 1 + polylog 0 (-1)) := by
  norm_num [polylog_zero_weight]

end TauCeti.Polylog
