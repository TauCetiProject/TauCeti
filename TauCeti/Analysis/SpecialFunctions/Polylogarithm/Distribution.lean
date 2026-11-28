/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.RootsOfUnity.SlitPlane
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import TauCeti.RingTheory.RootsOfUnity.PartialFractions

/-!
# Distribution relations of polylogarithms

For every integer weight `n` and every `m ≥ 1`, the principal polylogarithm satisfies the
multiplicative distribution relation
`polylog n (z ^ m) = m ^ (n - 1) * ∑ j ∈ Finset.range m, polylog n (ζ ^ j * z)`
for any primitive `m`-th root of unity `ζ`, on the domain
`Ω_m = {z : ℂ | 1 - z ^ m ∈ Complex.slitPlane}`. By
`IsPrimitiveRoot.one_sub_pow_mem_slitPlane_iff`, `Ω_m` is exactly the set of `z` for which `z ^ m`
and every rotate `ζ ^ j * z` avoid the branch cut `[1, ∞)`, so every term is a principal value at
a point of analyticity. The prefactor `m ^ (n - 1)` is an integer power, `1 / m` in weight zero.

In nonpositive weight `n ≤ 0`, `Li_n(z)` is a rational function with sole pole at `z = 1`, and the
relation holds on the larger set `{z : ℂ | z ^ m ≠ 1}`. In weight zero it is the root-of-unity
partial-fraction identity `IsPrimitiveRoot.sum_pow_mul_div_one_sub`; higher negative weights follow
by induction on `r` on the open set `{w : ℂ | w ^ m ≠ 1}`: applying the Euler operator
`z ↦ z * deriv · z` scales the left-hand side by `m` (`mul_deriv_polylog_neg_nat_comp_pow`) and
commutes with each rotation `w ↦ ζ ^ j * w` on the right-hand side
(`mul_deriv_polylog_neg_nat_comp_const_mul`).

Positive weights are obtained from weight zero by the inverse of the same mechanism. Both sides
of the weight-`(n + 1)` relation are holomorphic on `Ω_m`, their Euler derivatives are `m` times
the two sides of the weight-`n` relation (`mul_deriv_polylog_comp_const_mul_pow`), and both vanish
at `0`; since `Ω_m` is star-shaped about `0`, hence connected, the two sides agree.

## Main declarations

* `TauCeti.Polylog.polylog_distribution_of_nonpos_of_isPrimitiveRoot`: distribution in weight
  `n ≤ 0` over powers of any primitive `m`-th root of unity on `{z | z ^ m ≠ 1}`.
* `TauCeti.Polylog.polylog_distribution_of_nonpos`: distribution in weight `n ≤ 0` with the
  standard roots `exp (2 * π * I * j / m)` on `{z | z ^ m ≠ 1}`.
* `TauCeti.Polylog.polylog_sq_of_nonpos`: duplication (`m = 2`) in weight `n ≤ 0` on
  `{z | z ^ 2 ≠ 1}`.
* `TauCeti.Polylog.polylog_distribution_of_isPrimitiveRoot`: distribution in every integer weight
  over powers of any primitive `m`-th root of unity on `{z | 1 - z ^ m ∈ Complex.slitPlane}`.
* `TauCeti.Polylog.polylog_distribution`: distribution in every integer weight with the standard
  roots `exp (2 * π * I * j / m)`, wherever every `exp (2 * π * I * j / m) * z` avoids `[1, ∞)`.
* `TauCeti.Polylog.polylog_sq`: duplication in every integer weight on
  `{z | 1 - z ^ 2 ∈ Complex.slitPlane}`.

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
private theorem polylog_neg_nat_pow_of_isPrimitiveRoot (r : ℕ) {m : ℕ} {ζ z : ℂ}
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
      exact mul_deriv_polylog_neg_nat_comp_const_mul r (ζ ^ j) z
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

/-- The rotates by the standard `m`-th roots of unity `exp (2 * π * I * j / m)` are the rotates by
the powers of the primitive root `exp (2 * π * I / m)`. -/
private theorem sum_polylog_exp_mul (n : ℤ) (m : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range m, polylog n (Complex.exp (2 * Real.pi * Complex.I * j / m) * z) =
      ∑ j ∈ Finset.range m, polylog n (Complex.exp (2 * Real.pi * Complex.I / m) ^ j * z) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_natCast_mul]
  ring_nf

/-- Distribution in nonpositive integer weight `n ≤ 0` over the standard `m`-th roots of unity
`exp (2 * π * I * j / m)`, valid wherever `z ^ m ≠ 1`. No `0 < m` hypothesis is needed because
`z ^ 0 = 1` is already excluded by `z ^ m ≠ 1`. -/
theorem polylog_distribution_of_nonpos (n : ℤ) (hn : n ≤ 0) (m : ℕ) {z : ℂ} (hz : z ^ m ≠ 1) :
    polylog n (z ^ m) = (m : ℂ) ^ (n - 1) *
      ∑ j ∈ Finset.range m, polylog n (Complex.exp (2 * Real.pi * Complex.I * j / m) * z) := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hz (pow_zero z)
  rw [sum_polylog_exp_mul,
    polylog_distribution_of_nonpos_of_isPrimitiveRoot hn (Complex.isPrimitiveRoot_exp m hm) hz]

/-- Duplication (`m = 2`) for nonpositive-weight polylogarithms away from `z = ±1`. -/
theorem polylog_sq_of_nonpos {n : ℤ} (hn : n ≤ 0) {z : ℂ} (hz : z ^ 2 ≠ 1) :
    polylog n (z ^ 2) = (2 : ℂ) ^ (n - 1) * (polylog n z + polylog n (-z)) := by
  have hζ : IsPrimitiveRoot (-1 : ℂ) 2 :=
    IsPrimitiveRoot.neg_one_of_two_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  simpa [Finset.sum_range_succ] using polylog_distribution_of_nonpos_of_isPrimitiveRoot hn hζ hz

/-- One step of the induction on the weight: if the distribution relation holds in weight `n`
throughout `{w | 1 - w ^ m ∈ Complex.slitPlane}`, it holds there in weight `n + 1`. Both sides are
holomorphic on this connected domain, vanish at `0`, and have Euler derivatives equal to `m` times
the two sides of the weight-`n` relation. -/
private theorem polylog_distribution_add_one {n : ℤ} {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hm : 0 < m)
    (ih : ∀ w : ℂ, 1 - w ^ m ∈ Complex.slitPlane →
      polylog n (w ^ m) = (m : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range m, polylog n (ζ ^ j * w))
    {z : ℂ} (hz : 1 - z ^ m ∈ Complex.slitPlane) :
    polylog (n + 1) (z ^ m) =
      (m : ℂ) ^ (n + 1 - 1) * ∑ j ∈ Finset.range m, polylog (n + 1) (ζ ^ j * z) := by
  set U : Set ℂ := {w : ℂ | 1 - w ^ m ∈ Complex.slitPlane}
  have hUo : IsOpen U := Complex.isOpen_setOf_one_sub_pow_mem_slitPlane m
  have hrot {w : ℂ} (hw : w ∈ U) (j : ℕ) (hj : j ∈ Finset.range m) :
      1 - ζ ^ j * w ^ 1 ∈ Complex.slitPlane := by
    rw [pow_one]
    exact (hζ.one_sub_pow_mem_slitPlane_iff hm).mp hw j hj
  have hdiff {w : ℂ} (hw : w ∈ U) (j : ℕ) (hj : j ∈ Finset.range m) :
      DifferentiableAt ℂ (fun v ↦ polylog (n + 1) (ζ ^ j * v)) w :=
    (differentiableAt_polylog (n + 1) (by simpa using hrot hw j hj)).comp w
      (differentiableAt_id.const_mul (ζ ^ j))
  have hf : DifferentiableOn ℂ (fun w ↦ polylog (n + 1) (w ^ m)) U := fun w hw ↦
    ((differentiableAt_polylog (n + 1) hw).comp w (differentiableAt_pow m)).differentiableWithinAt
  have hg : DifferentiableOn ℂ
      (fun w ↦ (m : ℂ) ^ (n + 1 - 1) * ∑ j ∈ Finset.range m, polylog (n + 1) (ζ ^ j * w)) U :=
    fun w hw ↦
      ((DifferentiableAt.fun_sum fun j hj ↦ hdiff hw j hj).const_mul _).differentiableWithinAt
  -- The Euler derivatives of the two sides agree on `U`, by the weight-`n` relation.
  have heuler {w : ℂ} (hw : w ∈ U) :
      w * deriv (fun w ↦ polylog (n + 1) (w ^ m)) w = w * deriv
        (fun w ↦ (m : ℂ) ^ (n + 1 - 1) * ∑ j ∈ Finset.range m, polylog (n + 1) (ζ ^ j * w)) w := by
    have hlhs := mul_deriv_polylog_comp_const_mul_pow (n + 1) m 1 (z := w) (by rwa [one_mul])
    simp only [one_mul, add_sub_cancel_right] at hlhs
    have hrhs : w * deriv (fun w ↦ (m : ℂ) ^ (n + 1 - 1) *
        ∑ j ∈ Finset.range m, polylog (n + 1) (ζ ^ j * w)) w =
          (m : ℂ) ^ (n + 1 - 1) * ∑ j ∈ Finset.range m, polylog n (ζ ^ j * w) := by
      rw [deriv_const_mul _ (DifferentiableAt.fun_sum fun j hj ↦ hdiff hw j hj),
        deriv_fun_sum fun j hj ↦ hdiff hw j hj, mul_left_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      simpa using mul_deriv_polylog_comp_const_mul_pow (n + 1) 1 (ζ ^ j) (hrot hw j hj)
    have hpow : (m : ℂ) * (m : ℂ) ^ (n - 1) = (m : ℂ) ^ (n + 1 - 1) := by
      rw [← zpow_one_add₀ (Nat.cast_ne_zero.mpr hm.ne' : (m : ℂ) ≠ 0)]
      ring_nf
    rw [hlhs, ih w hw, hrhs, ← mul_assoc, hpow]
  -- Hence the derivatives agree on `U`: away from `0` by cancelling `w`, and at `0` by continuity.
  have hderiv : U.EqOn (deriv fun w ↦ polylog (n + 1) (w ^ m)) (deriv fun w ↦
      (m : ℂ) ^ (n + 1 - 1) * ∑ j ∈ Finset.range m, polylog (n + 1) (ζ ^ j * w)) := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · refine ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        (hf.analyticAt (hUo.mem_nhds hw)).deriv.continuousAt
        (hg.analyticAt (hUo.mem_nhds hw)).deriv.continuousAt).mp ?_).eq_of_nhds
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hUo.mem_nhds hw)] with v hv0 hvU
      exact mul_left_cancel₀ hv0 (heuler hvU)
    · exact mul_left_cancel₀ hw0 (heuler hw)
  have h0 : (0 : ℂ) ∈ U := by simp [U, zero_pow hm.ne', Complex.one_mem_slitPlane]
  exact hUo.eqOn_of_deriv_eq (Complex.isConnected_setOf_one_sub_pow_mem_slitPlane hm).isPreconnected
    hf hg hderiv h0 (by simp [zero_pow hm.ne']) hz

/-- **Distribution in every integer weight.** For every integer weight `n`, every primitive `m`-th
root of unity `ζ`, and every `z` with `1 - z ^ m ∈ Complex.slitPlane` (equivalently, `z ^ m` and
every rotate `ζ ^ j * z` lie off the branch cut `[1, ∞)`),
`Liₙ(z ^ m) = m ^ (n - 1) * ∑ j < m, Liₙ(ζ ^ j * z)`. The hypothesis forces `m ≠ 0`. -/
theorem polylog_distribution_of_isPrimitiveRoot (n : ℤ) {m : ℕ} {ζ z : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hz : 1 - z ^ m ∈ Complex.slitPlane) :
    polylog n (z ^ m) = (m : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range m, polylog n (ζ ^ j * z) := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ by
    simp [h, Complex.zero_notMem_slitPlane] at hz
  have hne {w : ℂ} (hw : 1 - w ^ m ∈ Complex.slitPlane) : w ^ m ≠ 1 := fun h ↦
    Complex.slitPlane_ne_zero hw (by rw [h, sub_self])
  rcases le_or_gt n 0 with hn | hn
  · exact polylog_distribution_of_nonpos_of_isPrimitiveRoot hn hζ (hne hz)
  -- Positive weights: induction from weight zero.
  lift n to ℕ using hn.le
  clear hn
  induction n generalizing z with
  | zero => exact polylog_distribution_of_nonpos_of_isPrimitiveRoot le_rfl hζ (hne hz)
  | succ k ih =>
    rw [Nat.cast_succ]
    exact polylog_distribution_add_one hζ hm (fun w hw ↦ ih hw) hz

/-- **Distribution in every integer weight**, over the standard `m`-th roots of unity: for
`0 < m` and every `z` such that each rotate `exp (2 * π * I * j / m) * z` (`j < m`) lies off the
branch cut `[1, ∞)`, `Liₙ(z ^ m) = m ^ (n - 1) * ∑ j < m, Liₙ(exp (2 * π * I * j / m) * z)`. -/
theorem polylog_distribution (n : ℤ) (m : ℕ) (hm : 0 < m) {z : ℂ}
    (hz : ∀ j ∈ Finset.range m,
      1 - Complex.exp (2 * Real.pi * Complex.I * j / m) * z ∈ Complex.slitPlane) :
    polylog n (z ^ m) = (m : ℂ) ^ (n - 1) *
      ∑ j ∈ Finset.range m, polylog n (Complex.exp (2 * Real.pi * Complex.I * j / m) * z) := by
  rw [sum_polylog_exp_mul, polylog_distribution_of_isPrimitiveRoot n
    (Complex.isPrimitiveRoot_exp m hm.ne') (Complex.one_sub_pow_mem_slitPlane_of_forall_exp hm hz)]

/-- **Duplication in every integer weight.** For every `z` with `1 - z ^ 2 ∈ Complex.slitPlane`
(that is, `z` off the two rays `(-∞, -1]` and `[1, ∞)`),
`Liₙ(z ^ 2) = 2 ^ (n - 1) * (Liₙ(z) + Liₙ(-z))`. -/
theorem polylog_sq (n : ℤ) {z : ℂ} (hz : 1 - z ^ 2 ∈ Complex.slitPlane) :
    polylog n (z ^ 2) = (2 : ℂ) ^ (n - 1) * (polylog n z + polylog n (-z)) := by
  have hζ : IsPrimitiveRoot (-1 : ℂ) 2 :=
    IsPrimitiveRoot.neg_one_of_two_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
  simpa [Finset.sum_range_succ] using polylog_distribution_of_isPrimitiveRoot n hζ hz

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

-- Weight two, `m = 2`, `z = 1 / 2`: `Li₂(1 / 4) = 2 * (Li₂(1 / 2) + Li₂(-1 / 2))`.
example : polylog 2 (1 / 4) = 2 * (polylog 2 (1 / 2) + polylog 2 (-(1 / 2))) := by
  have h := polylog_sq 2 (z := 1 / 2) (by norm_num [Complex.mem_slitPlane_iff])
  norm_num at h
  simpa using h

-- At `z = I` on the unit circle, `1 - I ^ 2 = 2` is off the cut, so
-- `Li₂(-1) = 2 * (Li₂(I) + Li₂(-I))`.
example : polylog 2 (-1) = 2 * (polylog 2 Complex.I + polylog 2 (-Complex.I)) := by
  have h := polylog_sq 2 (z := Complex.I) (by norm_num [Complex.I_sq, Complex.mem_slitPlane_iff])
  norm_num [Complex.I_sq] at h
  exact h

end TauCeti.Polylog
