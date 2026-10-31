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

The integral converges absolutely when `x, y, z` lie in `Complex.slitPlane ∪ {0}` and at most
one of them is `0`. Since the integrand is symmetric in `x, y, z`, the convergence theorem
`Complex.integrableOn_carlsonRG_integrand` is stated with the possibly vanishing argument
in the first position. Outside this domain `carlsonRG` is a totalized value and carries no
meaning.

## Main results

* `Complex.carlsonRG` — the integral `R_G`.
* `Complex.integrableOn_carlsonRG_integrand` — absolute convergence of the defining
  integral.
* `Complex.carlsonRG_comm_left`, `Complex.carlsonRG_comm_right` — `R_G` is
  symmetric in its three arguments.
* `Complex.carlsonRG_ofReal_mul` — homogeneity of degree `1/2` under positive real
  scaling.
* `Complex.carlsonRG_self` — the diagonal value `R_G(x, x, x) = x^(1/2)`.
* `Complex.carlsonRG_pos` — `R_G` is a positive real number at nonnegative real
  arguments, at most one of them zero.

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

/-- **Carlson's completely symmetric elliptic integral of the second kind** (DLMF 19.16.3):
`R_G(x, y, z) = ¼ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2)
(x / (t + x) + y / (t + y) + z / (t + z)) t dt`, with principal complex powers of each factor.

The integral converges when `x, y, z ∈ slitPlane ∪ {0}` with at most one of them `0`
(`integrableOn_carlsonRG_integrand`); elsewhere the value is a totalized junk value. -/
noncomputable def carlsonRG (x y z : ℂ) : ℂ :=
  (1 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ),
    ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
        (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t

/-- The defining integral of `carlsonRG`. -/
theorem carlsonRG_def (x y z : ℂ) :
    carlsonRG x y z = (1 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
          (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t :=
  (rfl)

/-! ### Bounds on the factors of the integrand -/

/-- The norm of the principal power `w ^ (-1/2)` is the real power `‖w‖ ^ (-1/2)`. -/
private theorem norm_cpow_neg_half (w : ℂ) : ‖w ^ (-(1 / 2) : ℂ)‖ = ‖w‖ ^ (-(1 / 2) : ℝ) := by
  simpa using Complex.norm_cpow_real w (-(1 / 2))

/-- For `x ∈ slitPlane ∪ {0}`, the factor `(t + x)^(-1/2)` is `O(t^(-1/2))` for `t > 0`. -/
private theorem exists_norm_cpow_le_rpow {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖((t : ℂ) + x) ^ (-(1 / 2) : ℂ)‖ ≤ C * t ^ (-(1 / 2) : ℝ) := by
  rcases hx with hx | hx
  · obtain ⟨c, hc, h⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hx
    refine ⟨c ^ (-(1 / 2) : ℝ), by positivity, fun t ht => ?_⟩
    have h1 : c * t ≤ ‖(t : ℂ) + x‖ := by nlinarith [h t ht.le]
    rw [norm_cpow_neg_half, ← Real.mul_rpow hc.le ht.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    rw [mem_singleton_iff.mp hx, add_zero, norm_cpow_neg_half, Complex.norm_real,
      Real.norm_of_nonneg ht.le, one_mul]

/-- For `y ∈ slitPlane`, the factor `(t + y)^(-1/2)` is `O((1 + t)^(-1/2))` for `t ≥ 0`. -/
private theorem exists_norm_cpow_le_one_add_rpow {y : ℂ} (hy : y ∈ slitPlane) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖((t : ℂ) + y) ^ (-(1 / 2) : ℂ)‖ ≤ C * (1 + t) ^ (-(1 / 2) : ℝ) := by
  obtain ⟨c, hc, h⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hy
  refine ⟨c ^ (-(1 / 2) : ℝ), by positivity, fun t ht => ?_⟩
  rw [norm_cpow_neg_half, ← Real.mul_rpow hc.le (by linarith)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (h t ht) (by norm_num)

/-- For `x ∈ slitPlane ∪ {0}`, the term `x / (t + x) · t` of the integrand is bounded for
`t > 0`. -/
private theorem exists_norm_div_mul_le {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖x / ((t : ℂ) + x) * t‖ ≤ C := by
  rcases hx with hx | hx
  · obtain ⟨c, hc, h⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hx
    refine ⟨‖x‖ / c, by positivity, fun t ht => ?_⟩
    have hpos : 0 < ‖(t : ℂ) + x‖ := lt_of_lt_of_le (by positivity) (h t ht.le)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div,
      div_le_div_iff₀ hpos hc]
    have := h t ht.le
    nlinarith [norm_nonneg x]
  · exact ⟨0, le_rfl, fun t _ => by simp [mem_singleton_iff.mp hx]⟩

/-- For `x ∈ slitPlane ∪ {0}`, the factor `(t + x)^(-1/2)` is continuous for `t > 0`. -/
private theorem continuousOn_cpow {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) (Ioi 0) := fun _ ht =>
  ((Complex.continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
    (TauCeti.ofReal_add_mem_slitPlane_of_mem_union hx ht)).continuousWithinAt

/-- For `x ∈ slitPlane ∪ {0}`, the term `x / (t + x)` is continuous for `t > 0`. -/
private theorem continuousOn_div {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ContinuousOn (fun t : ℝ => x / ((t : ℂ) + x)) (Ioi 0) := fun _ ht =>
  (continuousAt_const.div (Complex.continuous_ofReal.add continuous_const).continuousAt
    (Complex.slitPlane_ne_zero
      (TauCeti.ofReal_add_mem_slitPlane_of_mem_union hx ht))).continuousWithinAt

/-! ### Convergence -/

/-- **Convergence of `R_G`.** The integrand of `carlsonRG x y z` is integrable on `(0, ∞)` when
`x ∈ slitPlane ∪ {0}` and `y, z ∈ slitPlane`. By symmetry of the integrand in `x, y, z` this
covers every argument triple in `slitPlane ∪ {0}` with at most one zero entry. -/
theorem integrableOn_carlsonRG_integrand {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
        (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t) (Ioi 0) := by
  -- The first factor is `O(t^(-1/2))`, the next two are `O((1 + t)^(-1/2))`, and the sum of
  -- the three terms `w / (t + w)` multiplied by `t` is bounded.
  obtain ⟨Cx, hCx0, hCx⟩ := exists_norm_cpow_le_rpow hx
  obtain ⟨Cy, hCy0, hCy⟩ := exists_norm_cpow_le_one_add_rpow hy
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_cpow_le_one_add_rpow hz
  obtain ⟨Dx, hDx0, hDx⟩ := exists_norm_div_mul_le hx
  obtain ⟨Dy, hDy0, hDy⟩ := exists_norm_div_mul_le (Or.inl hy)
  obtain ⟨Dz, hDz0, hDz⟩ := exists_norm_div_mul_le (Or.inl hz)
  have hcont := ((((continuousOn_cpow hx).mul (continuousOn_cpow (Or.inl hy))).mul
    (continuousOn_cpow (Or.inl hz))).mul (((continuousOn_div hx).add
      (continuousOn_div (Or.inl hy))).add (continuousOn_div (Or.inl hz)))).mul
    Complex.continuous_ofReal.continuousOn
  -- The majorant `t^(-1/2) (1 + t)⁻¹` is the beta-integral integrand with `a = b = 1/2`.
  refine ((TauCeti.integrableOn_rpow_mul_one_add_rpow one_half_pos one_half_pos).const_mul
    (Cx * Cy * Cz * (Dx + Dy + Dz))).mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  have hsum : ‖(x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t‖ ≤
      Dx + Dy + Dz := by
    rw [add_mul, add_mul]
    exact (norm_add₃_le).trans (add_le_add_three (hDx t ht) (hDy t ht) (hDz t ht))
  have hone : (1 + t) ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-(1 / 2) : ℝ) =
      (1 + t) ^ (-((1 / 2 : ℝ) + 1 / 2)) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hhalf : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [mul_assoc _ _ (t : ℂ), norm_mul, norm_mul, norm_mul]
  calc _ ≤ Cx * t ^ (-(1 / 2) : ℝ) * (Cy * (1 + t) ^ (-(1 / 2) : ℝ)) *
        (Cz * (1 + t) ^ (-(1 / 2) : ℝ)) * (Dx + Dy + Dz) := by
        gcongr
        exacts [hCx t ht, hCy t ht.le, hCz t ht.le]
    _ = _ := by rw [hhalf, ← hone]; ring

/-! ### Symmetry -/

/-- `R_G` is symmetric in its first two arguments. -/
theorem carlsonRG_comm_left (x y z : ℂ) : carlsonRG x y z = carlsonRG y x z := by
  simp only [carlsonRG_def]
  congr 2
  funext t
  ring

/-- `R_G` is symmetric in its second and third arguments. Together with `carlsonRG_comm_left`,
`R_G` is symmetric in all three arguments. -/
theorem carlsonRG_comm_right (x y z : ℂ) : carlsonRG x y z = carlsonRG x z y := by
  simp only [carlsonRG_def]
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
  have h := integral_comp_mul_left_Ioi' (fun t : ℝ => ((t : ℂ) + l * x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + l * y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + l * z) ^ (-(1 / 2) : ℂ) *
      (l * x / ((t : ℂ) + l * x) + l * y / ((t : ℂ) + l * y) + l * z / ((t : ℂ) + l * z)) * t)
    0 hl
  rw [mul_zero] at h
  have hfun : (fun s : ℝ => (((l * s : ℝ) : ℂ) + l * x) ^ (-(1 / 2) : ℂ) *
      (((l * s : ℝ) : ℂ) + l * y) ^ (-(1 / 2) : ℂ) * (((l * s : ℝ) : ℂ) + l * z) ^ (-(1 / 2) : ℂ) *
        (l * x / (((l * s : ℝ) : ℂ) + l * x) + l * y / (((l * s : ℝ) : ℂ) + l * y) +
          l * z / (((l * s : ℝ) : ℂ) + l * z)) * ((l * s : ℝ) : ℂ)) =
      fun s : ℝ => (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 * (((s : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((s : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + z) ^ (-(1 / 2) : ℂ) *
          (x / ((s : ℂ) + x) + y / ((s : ℂ) + y) + z / ((s : ℂ) + z)) * s) := by
    funext s
    rw [hscale, hscale, hscale, hscale_div, hscale_div, hscale_div, Complex.ofReal_mul]
    ring
  rw [carlsonRG_def, carlsonRG_def, ← h, hfun, integral_const_mul, Complex.real_smul, ← hl3]
  ring

/-! ### Diagonal value -/

/-- **The diagonal value of `R_G`**: `R_G(x, x, x) = x^(1/2)` for `x` in the slit plane. -/
@[simp]
theorem carlsonRG_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRG x x x = x ^ (1 / 2 : ℂ) := by
  have hmem (t : ℝ) (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane_of_nonneg hx ht
  have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
  -- `-6x (t + x)^(-1/2) + 2x² (t + x)^(-3/2)` is an antiderivative of `3x t (t + x)^(-5/2)`.
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -6 * x * ((t : ℂ) + x) ^ (-((1 / 2 : ℝ) : ℂ)) +
          2 * x ^ 2 * ((t : ℂ) + x) ^ (-((3 / 2 : ℝ) : ℂ)))
        (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
            (x / ((t : ℂ) + x) + x / ((t : ℂ) + x) + x / ((t : ℂ) + x)) * t) t := by
    intro t ht
    have hd (s : ℂ) := (((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := s)
      (hmem t ht)).comp_ofReal
    have h := ((hd (-((1 / 2 : ℝ) : ℂ))).const_mul (-6 * x)).add
      ((hd (-((3 / 2 : ℝ) : ℂ))).const_mul (2 * x ^ 2))
    simp only [id] at h
    convert h using 1
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
      ((TauCeti.tendsto_ofReal_add_cpow_neg hx (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (-6 * x)).add
      ((TauCeti.tendsto_ofReal_add_cpow_neg hx (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
        (2 * x ^ 2))
  rw [carlsonRG_def, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_carlsonRG_integrand (Or.inl hx) hx hx) hlim]
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

/-- At a positive real base, the principal power `(t + w) ^ (-1/2)` is the real one. -/
private theorem ofReal_add_cpow_neg_half {w t : ℝ} (hw : 0 ≤ w) (ht : 0 < t) :
    ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) = (((t + w) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by linarith)]
  push_cast
  rfl

/-- **`R_G` is positive at real arguments**: for real `x ≥ 0` and `y, z > 0`, `R_G(x, y, z)` is a
positive real number (in the order `ComplexOrder`, so its imaginary part is `0`). By symmetry,
any one of the three arguments may be the one that vanishes. -/
theorem carlsonRG_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    0 < carlsonRG x y z := by
  set f : ℝ → ℝ := fun t => (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ) *
    (t + z) ^ (-(1 / 2) : ℝ) * (x / (t + x) + y / (t + y) + z / (t + z)) * t with hf
  have heq : EqOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
        ((x : ℂ) / ((t : ℂ) + x) + (y : ℂ) / ((t : ℂ) + y) + (z : ℂ) / ((t : ℂ) + z)) * t)
      (fun t => ((f t : ℝ) : ℂ)) (Ioi 0) :=
    fun t ht => by
      simp only [hf, ofReal_add_cpow_neg_half hx ht, ofReal_add_cpow_neg_half hy.le ht,
        ofReal_add_cpow_neg_half hz.le ht, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_add]
  have hint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_carlsonRG_integrand (TauCeti.ofReal_mem_slitPlane_union_zero hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)).congr_fun heq measurableSet_Ioi
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
