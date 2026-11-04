/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Carlson's completely symmetric elliptic integral `R_G`

This file defines Carlson's completely symmetric elliptic integral of the second kind
(DLMF 19.16.3)

`R_G(x, y, z) = ¼ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2)
  (x / (t + x) + y / (t + y) + z / (t + z)) t dt`

for complex `x, y, z`, with the principal branch of each factor `(t + x) ^ (-1/2 : ℂ)`. In
Carlson's normal form of Legendre's integrals, the complete integral of the second kind is
`E(k) = 2 R_G(0, 1 - k², 1)`, and the perimeter of an ellipse is a multiple of an `R_G` value.

The integral converges absolutely whenever `x, y, z` lie in `Complex.slitPlane ∪ {0}`
(`Complex.integrableOn_carlsonRGIntegrand`), including when two or all three arguments vanish
(at `(0, 0, 0)` the integrand vanishes identically, giving `R_G(0, 0, 0) = 0`). Wherever the
integral fails to converge outside this domain, `carlsonRG` is a totalized value.

## Main results

* `Complex.carlsonRGIntegrand` — the integrand of `R_G`.
* `Complex.carlsonRG` — the integral `R_G`.
* `Complex.integrableOn_carlsonRGIntegrand` — absolute convergence of the defining
  integral on `(slitPlane ∪ {0})³`.
* `Complex.carlsonRG_comm_left`, `Complex.carlsonRG_comm_right` — `R_G` is
  symmetric in its three arguments.
* `Complex.carlsonRG_ofReal_mul` — homogeneity of degree `1/2` under positive real
  scaling.
* `Complex.carlsonRG_self` — the diagonal value `R_G(x, x, x) = x^(1/2)`.
* `Complex.carlsonRG_pos` — `R_G` is a positive real number at nonnegative real
  arguments, not all zero.

## References

* NIST *Digital Library of Mathematical Functions*, §19.16 and §19.20,
  <https://dlmf.nist.gov/19.16>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
* B. C. Carlson, Numerical computation of real or complex elliptic integrals, *Numer. Algorithms*
  10 (1995), 13–26.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) formalizes Carlson's book,
including `R_G`, on top of Carlson's general `R`-function, a Dirichlet average over a simplex.
This file instead works directly from the integral definition above and is not ported from it.
-/

public section

open MeasureTheory Set Filter Topology
open Complex (slitPlane mem_slitPlane_iff ofReal_mem_slitPlane)
open scoped ComplexOrder

namespace Complex

/-- The integrand of Carlson's `R_G` (DLMF 19.16.3) at `t`:
`(t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) (x / (t + x) + y / (t + y) + z / (t + z)) t`,
with principal complex powers of each factor. -/
noncomputable def carlsonRGIntegrand (x y z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
      (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t

/-- The explicit formula for `carlsonRGIntegrand`. -/
theorem carlsonRGIntegrand_def (x y z : ℂ) (t : ℝ) :
    carlsonRGIntegrand x y z t =
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
          (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t :=
  (rfl)

/-- **Carlson's completely symmetric elliptic integral of the second kind** (DLMF 19.16.3):
`R_G(x, y, z) = ¼ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2)
(x / (t + x) + y / (t + y) + z / (t + z)) t dt`, the integral of `carlsonRGIntegrand`.

The integral converges when `x, y, z ∈ slitPlane ∪ {0}` (`integrableOn_carlsonRGIntegrand`);
wherever the integral fails to converge, the value is a totalized junk value. -/
noncomputable def carlsonRG (x y z : ℂ) : ℂ :=
  (1 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), carlsonRGIntegrand x y z t

/-- The defining integral of `carlsonRG`. -/
theorem carlsonRG_def (x y z : ℂ) :
    carlsonRG x y z = (1 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), carlsonRGIntegrand x y z t :=
  (rfl)

/-! ### Convergence -/

/-- **Convergence of `R_G`.** The integrand of `carlsonRG x y z` is integrable on `(0, ∞)`
whenever `x, y, z ∈ slitPlane ∪ {0}`, including when two or all three arguments vanish. -/
theorem integrableOn_carlsonRGIntegrand {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane ∪ {0}) :
    IntegrableOn (carlsonRGIntegrand x y z) (Ioi 0) := by
  -- Each of the three symmetric summands vanishes identically when its numerator argument `u` is
  -- `0`, and equals `u (t + u)^(-3/2) (t + v)^(-1/2) (t + w)^(-1/2) t = O((1 + t)^(-3/2))` on
  -- `(0, ∞)` when `u ∈ slitPlane` (since `(t + v)^(-1/2) (t + w)^(-1/2) t = O(1)`).
  have hterm {u v w : ℂ} (hu : u ∈ slitPlane ∪ {0}) (hv : v ∈ slitPlane ∪ {0})
      (hw : w ∈ slitPlane ∪ {0}) :
      IntegrableOn (fun t : ℝ => ((t : ℂ) + u) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) *
          (u / ((t : ℂ) + u)) * t) (Ioi 0) := by
    rcases hu with hu | hu
    · have hrew (t : ℝ) : ((t : ℂ) + u) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * (u / ((t : ℂ) + u)) * t =
          u * (((t : ℂ) + u) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) *
            ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * t) := by
        have hpow : ((t : ℂ) + u) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + u)⁻¹ =
            ((t : ℂ) + u) ^ (-(3 / 2) : ℂ) := by
          rw [TauCeti.cpow_mul_inv (by norm_num)]
          norm_num
        rw [div_eq_mul_inv u ((t : ℂ) + u)]
        linear_combination
          (u * ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * t) * hpow
      simp_rw [hrew]
      refine Integrable.const_mul ?_ u
      have hcont := (((TauCeti.continuousOn_ofReal_add_cpow (Or.inl hu) (-(3 / 2))).mul
        (TauCeti.continuousOn_ofReal_add_cpow hv (-(1 / 2)))).mul
        (TauCeti.continuousOn_ofReal_add_cpow hw (-(1 / 2)))).mul
        Complex.continuous_ofReal.continuousOn
      obtain ⟨Cu, hCu0, hCu⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_one_add_rpow hu
        (r := -(3 / 2)) (by norm_num)
      have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
      obtain ⟨Cv, hCv⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hv hr
      obtain ⟨Cw, hCw⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hw hr
      have hCv0 : 0 ≤ Cv := by simpa using (norm_nonneg _).trans (hCv 1 one_pos)
      have hCw0 : 0 ≤ Cw := by simpa using (norm_nonneg _).trans (hCw 1 one_pos)
      push_cast at hCu hCv hCw
      refine ((TauCeti.integrableOn_rpow_mul_one_add_rpow one_pos one_half_pos).const_mul
        (Cu * Cv * Cw)).mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have ht_cancel : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t = 1 := by
        rw [← Real.rpow_add ht0]
        norm_num [Real.rpow_neg_one, inv_mul_cancel₀ ht0.ne']
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      calc ‖((t : ℂ) + u) ^ (-(3 / 2) : ℂ)‖ * ‖((t : ℂ) + v) ^ (-(1 / 2) : ℂ)‖ *
            ‖((t : ℂ) + w) ^ (-(1 / 2) : ℂ)‖ * t
          ≤ (Cu * (1 + t) ^ (-(3 / 2) : ℝ)) * (Cv * t ^ (-(1 / 2) : ℝ)) *
              (Cw * t ^ (-(1 / 2) : ℝ)) * t := by
            gcongr
            exacts [hCu t ht0.le, hCv t ht0, hCw t ht0]
        _ = Cu * Cv * Cw * (t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t) *
            (1 + t) ^ (-(3 / 2) : ℝ) := by ring
        _ = Cu * Cv * Cw * (t ^ ((1 : ℝ) - 1) * (1 + t) ^ (-((1 : ℝ) + 1 / 2))) := by
            rw [ht_cancel]
            norm_num
    · rw [Set.mem_singleton_iff.mp hu]
      simp
  refine (((hterm hx hy hz).add (hterm hy hz hx)).add (hterm hz hx hy)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, carlsonRGIntegrand]
  ring

/-! ### Symmetry -/

/-- `R_G` is symmetric in its first two arguments. -/
theorem carlsonRG_comm_left (x y z : ℂ) : carlsonRG x y z = carlsonRG y x z := by
  simp only [carlsonRG_def, carlsonRGIntegrand]
  congr 2
  funext t
  ring

/-- `R_G` is symmetric in its second and third arguments. Together with `carlsonRG_comm_left`,
`R_G` is symmetric in all three arguments. -/
theorem carlsonRG_comm_right (x y z : ℂ) : carlsonRG x y z = carlsonRG x z y := by
  simp only [carlsonRG_def, carlsonRGIntegrand]
  congr 2
  funext t
  ring

/-! ### Homogeneity -/

/-- **Homogeneity of `R_G`.** For real `l > 0`, `R_G(l x, l y, l z) = l^(1/2) R_G(x, y, z)`.
No hypothesis on `x, y, z` is needed: the substitution `t = l s` identifies the two integrals
whether or not they converge. -/
theorem carlsonRG_ofReal_mul {l : ℝ} (hl : 0 < l) (x y z : ℂ) :
    carlsonRG (l * x) (l * y) (l * z) = (l : ℂ) ^ (1 / 2 : ℂ) * carlsonRG x y z := by
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hscale (s : ℝ) (w : ℂ) : (((l * s : ℝ) : ℂ) + l * w) ^ (-(1 / 2) : ℂ) =
      (l : ℂ) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + w) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_mul, ← mul_add, TauCeti.ofReal_mul_cpow hl.le]
  have hscale_div (s : ℝ) (w : ℂ) :
      (l : ℂ) * w / (((l * s : ℝ) : ℂ) + l * w) = w / ((s : ℂ) + w) := by
    rw [Complex.ofReal_mul, ← mul_add, mul_div_mul_left _ _ hl0]
  -- `l² · (l^(-1/2))³ = l^(1/2)`: the Jacobian and the factor `t = l s` against the three
  -- rescaled powers.
  have hl3 : (l : ℂ) * (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 = (l : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_nat_mul, ← pow_two, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hl0]
    norm_num
  have h := integral_comp_mul_left_Ioi' (carlsonRGIntegrand (l * x) (l * y) (l * z)) 0 hl
  rw [mul_zero] at h
  have hfun : (fun s : ℝ => carlsonRGIntegrand (l * x) (l * y) (l * z) (l * s)) =
      fun s : ℝ => (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 * carlsonRGIntegrand x y z s := by
    funext s
    simp only [carlsonRGIntegrand]
    rw [hscale, hscale, hscale, hscale_div, hscale_div, hscale_div, Complex.ofReal_mul]
    ring
  rw [carlsonRG_def, carlsonRG_def, ← h, hfun, integral_const_mul, Complex.real_smul, ← hl3]
  ring

/-! ### Diagonal value -/

/-- **The diagonal value of `R_G`**: `R_G(x, x, x) = x^(1/2)` for `x` in the slit plane. -/
@[simp]
theorem carlsonRG_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRG x x x = x ^ (1 / 2 : ℂ) := by
  have hmem (t : ℝ) (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane hx ht
  have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
  -- `-6x (t + x)^(-1/2) + 2x² (t + x)^(-3/2)` is an antiderivative of `3x t (t + x)^(-5/2)`.
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -6 * x * ((t : ℂ) + x) ^ (-((1 / 2 : ℝ) : ℂ)) +
          2 * x ^ 2 * ((t : ℂ) + x) ^ (-((3 / 2 : ℝ) : ℂ)))
        (carlsonRGIntegrand x x x t) t := by
    intro t ht
    have hd (s : ℂ) := (((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := s)
      (hmem t ht)).comp_ofReal
    have h := ((hd (-((1 / 2 : ℝ) : ℂ))).const_mul (-6 * x)).add
      ((hd (-((3 / 2 : ℝ) : ℂ))).const_mul (2 * x ^ 2))
    simp only [id] at h
    convert h using 1
    unfold carlsonRGIntegrand
    have hne := Complex.slitPlane_ne_zero (hmem t ht)
    -- Write every power of `w = t + x` through `u = w^(-1/2)`, using `u² = w⁻¹`.
    set w : ℂ := (t : ℂ) + x with hw
    set u : ℂ := w ^ (-(1 / 2) : ℂ) with hu
    have hu2 : u ^ 2 = w⁻¹ := by
      rw [hu, ← Complex.cpow_nat_mul, ← Complex.cpow_neg_one]
      norm_num
    have hp3 : w ^ (-((1 / 2 : ℝ) : ℂ) - 1) = u ^ 3 := by
      rw [hu, ← Complex.cpow_nat_mul]
      norm_num
    have hp5 : w ^ (-((3 / 2 : ℝ) : ℂ) - 1) = u ^ 5 := by
      rw [hu, ← Complex.cpow_nat_mul]
      norm_num
    have ht' : (t : ℂ) = w - x := by rw [hw]; ring
    have hu2' : u ^ 2 * w = 1 := by rw [hu2, inv_mul_cancel₀ hne]
    rw [hp3, hp5, div_eq_mul_inv, ← hu2]
    push_cast
    linear_combination (3 * x * u ^ 5) * ht' + (3 * x * u ^ 3) * hu2'
  have hlim : Tendsto (fun t : ℝ => -6 * x * ((t : ℂ) + x) ^ (-((1 / 2 : ℝ) : ℂ)) +
      2 * x ^ 2 * ((t : ℂ) + x) ^ (-((3 / 2 : ℝ) : ℂ))) atTop (𝓝 0) := by
    simpa using
      ((Complex.tendsto_ofReal_add_cpow_neg x (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (-6 * x)).add
      ((Complex.tendsto_ofReal_add_cpow_neg x (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
        (2 * x ^ 2))
  rw [carlsonRG_def, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_carlsonRGIntegrand (Or.inl hx) (Or.inl hx) (Or.inl hx)) hlim]
  -- The value at `t = 0` is `-6 x · x^(-1/2) + 2 x² · x^(-3/2) = -4 x^(1/2)`.
  have h1 : x * x ^ (-((1 / 2 : ℝ) : ℂ)) = x ^ (1 / 2 : ℂ) := by
    conv_lhs => enter [1]; rw [← Complex.cpow_one x]
    rw [← Complex.cpow_add _ _ hx0]
    norm_num
  have h2 : x ^ 2 * x ^ (-((3 / 2 : ℝ) : ℂ)) = x ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hx0]
    norm_num
  simp only [Complex.ofReal_zero, zero_add]
  linear_combination (3 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

/-! ### Real arguments -/

/-- **`R_G` is positive at real arguments**: for real `x, y ≥ 0` and `z > 0`, `R_G(x, y, z)` is a
positive real number (in the order `ComplexOrder`, so its imaginary part is `0`). By symmetry,
up to two of the three arguments may vanish. -/
theorem carlsonRG_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
    0 < carlsonRG x y z := by
  set f : ℝ → ℝ := fun t => (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ) *
    (t + z) ^ (-(1 / 2) : ℝ) * (x / (t + x) + y / (t + y) + z / (t + z)) * t with hf
  have heq : EqOn (carlsonRGIntegrand x y z) (fun t => ((f t : ℝ) : ℂ)) (Ioi 0) :=
    fun t ht => by
      have ht : (0 : ℝ) < t := ht
      simp only [carlsonRGIntegrand, hf, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_add, Complex.ofReal_cpow (by positivity : 0 ≤ t + x),
        Complex.ofReal_cpow (by positivity : 0 ≤ t + y),
        Complex.ofReal_cpow (by positivity : 0 ≤ t + z)]
      -- After `push_cast` the two sides differ only in how the exponent `-(1 / 2)` is cast.
      push_cast
      ring
  have hint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_carlsonRGIntegrand (TauCeti.ofReal_mem_slitPlane_union_zero hx)
      (TauCeti.ofReal_mem_slitPlane_union_zero hy)
      (Or.inl (ofReal_mem_slitPlane.mpr hz))).congr_fun heq measurableSet_Ioi
    simpa using h.re
  have hpos (t : ℝ) (ht : t ∈ Ioi 0) : 0 < f t := by
    have : (0 : ℝ) < t := ht
    simp only [hf]
    positivity
  have hI : 0 < ∫ t in Ioi (0 : ℝ), f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => (hpos t ht).le)) hint]
    refine lt_of_lt_of_le ?_ (measure_mono fun t ht => ⟨(hpos t ht).ne', ht⟩ :
      volume (Ioi (0 : ℝ)) ≤ volume (Function.support f ∩ Ioi 0))
    simp
  rw [carlsonRG_def, setIntegral_congr_fun measurableSet_Ioi heq, integral_complex_ofReal]
  exact mul_pos (by norm_num) (Complex.zero_lt_real.mpr hI)

end Complex
