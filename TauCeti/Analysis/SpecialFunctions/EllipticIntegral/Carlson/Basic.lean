/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Carlson's symmetric elliptic integral of the first kind

This file defines Carlson's symmetric elliptic integral of the first kind (DLMF 19.16.1)

`R_F(x, y, z) = ½ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) dt`

for complex `x, y, z`, with the principal branch of each factor `(t + x) ^ (-1/2 : ℂ)`, together
with its degenerate case `R_C(x, y) = R_F(x, y, y)` (DLMF 19.2.17). Carlson's integrals are
symmetric replacements for Legendre's incomplete elliptic integrals: every Legendre integral is a
combination of them, and they are the input to the duplication algorithm for computing elliptic
integrals.

The integral defining `R_F` converges absolutely when `x, y, z` lie in `Complex.slitPlane ∪ {0}`
and at most one of them is `0`. Since `R_F` is symmetric, the convergence theorem
`Complex.integrableOn_carlsonRF_integrand` is stated with the possibly vanishing argument
in the first position. The behavior of `carlsonRF` outside this domain is not characterized here;
where the integrand is not integrable, `carlsonRF` is the totalized value `0` of the Bochner
integral and carries no meaning.

## Main results

* `Complex.carlsonRF`, `Complex.carlsonRC` — the integrals `R_F` and `R_C`.
* `Complex.integrableOn_carlsonRF_integrand` — absolute convergence of the defining
  integral.
* `Complex.carlsonRF_comm_left`, `Complex.carlsonRF_comm_right` — `R_F` is
  symmetric in its three arguments.
* `Complex.carlsonRF_ofReal_mul` — homogeneity of degree `-1/2` under positive real
  scaling.
* `Complex.carlsonRF_self`, `Complex.carlsonRC_self` — the diagonal values
  `R_F(x, x, x) = R_C(x, x) = x^(-1/2)`.
* `Complex.carlsonRF_pos` — `R_F` is a positive real number at nonnegative real
  arguments, at most one of them zero.
* `Complex.carlsonRC_eq_integral` — the defining integral of `R_C` (DLMF 19.2.17).
* `Complex.carlsonRC_ofReal_eq_arccos`, `Complex.carlsonRC_ofReal_eq_arcosh` — the
  elementary evaluation of `R_C` at real arguments (DLMF 19.2.19, 19.2.20):
  `R_C(x, y) = arccos √(x/y) / √(y - x)` for `0 ≤ x < y`, and
  `R_C(x, y) = arcosh √(x/y) / √(x - y)` for `0 < y < x`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.16 and §19.2(iv),
  <https://dlmf.nist.gov/19.16>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
* B. C. Carlson, Numerical computation of real or complex elliptic integrals, *Numer. Algorithms*
  10 (1995), 13–26.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) formalizes Carlson's book,
including `R_F`, on top of Carlson's general `R`-function, a Dirichlet average over a simplex. This
file instead works directly from the integral definition above and is not ported from it.
-/

public section

open MeasureTheory Set Filter Topology
open Complex (slitPlane mem_slitPlane_iff ofReal_mem_slitPlane)
open scoped ComplexOrder

namespace Complex

/-- **Carlson's symmetric elliptic integral of the first kind** (DLMF 19.16.1):
`R_F(x, y, z) = ½ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) dt`, with principal complex
powers of each factor.

The integral converges when `x, y, z ∈ slitPlane ∪ {0}` with at most one of them `0`
(`integrableOn_carlsonRF_integrand`); its behavior outside this domain is not characterized here.
Where the integrand is not integrable, the value is the totalized junk value `0`. -/
noncomputable def carlsonRF (x y z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
    ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)

/-- **Carlson's degenerate integral** `R_C(x, y) = R_F(x, y, y)` (DLMF 19.2.17). Its integral form
`½ ∫₀^∞ (t + x)^(-1/2) (t + y)⁻¹ dt` is `carlsonRC_eq_integral`. -/
noncomputable def carlsonRC (x y : ℂ) : ℂ :=
  carlsonRF x y y

/-- The defining integral of `carlsonRF`. -/
theorem carlsonRF_def (x y z : ℂ) :
    carlsonRF x y z = (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) :=
  (rfl)

/-- `carlsonRC` is the degenerate case `R_C(x, y) = R_F(x, y, y)` of `carlsonRF`. -/
theorem carlsonRC_def (x y : ℂ) : carlsonRC x y = carlsonRF x y y :=
  (rfl)

/-! ### Convergence -/

/-- **Convergence of `R_F`.** The integrand of `carlsonRF x y z` is integrable on `(0, ∞)` when
`x ∈ slitPlane ∪ {0}` and `y, z ∈ slitPlane`. By symmetry of the integrand this covers every
argument triple in `slitPlane ∪ {0}` with at most one zero entry. -/
theorem integrableOn_carlsonRF_integrand {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) (Ioi 0) := by
  have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx hr
  obtain ⟨Cy, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le hy hr
  obtain ⟨Cz, hCz⟩ := TauCeti.exists_norm_ofReal_add_cpow_le hz hr
  obtain ⟨Cy', hCy'⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow (Or.inl hy) hr
  obtain ⟨Cz', hCz'⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow (Or.inl hz) hr
  push_cast at hCx hCy hCz hCy' hCz'
  have hcpow {w : ℂ} (hw : w ∈ slitPlane ∪ {0}) :
      ContinuousOn (fun t : ℝ => ((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) (Ioi 0) := fun _ ht =>
    ((Complex.continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
      (TauCeti.ofReal_add_mem_slitPlane_of_mem_union hw ht)).continuousWithinAt
  have hcont := ((hcpow hx).mul (hcpow (Or.inl hy))).mul (hcpow (Or.inl hz))
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · -- Near `0` the last two factors are bounded and the first is `O(t^(-1/2))`.
    have hg : IntegrableOn (fun t : ℝ => Cx * t ^ (-(1 / 2) : ℝ) * Cy * Cz) (Ioc 0 1) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := -(1 / 2)) (by norm_num)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
      exact ((h.const_mul Cx).mul_const Cy).mul_const Cz
    refine hg.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have h1 := hCx t ht.1
    have h2 := hCy t ht.1.le
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)) (hCz t ht.1.le)
      (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans h1) ((norm_nonneg _).trans h2))
  · -- Near `∞` each factor is `O(t^(-1/2))`, so the integrand is `O(t^(-3/2))`.
    have hg : IntegrableOn
        (fun t : ℝ => Cx * t ^ (-(1 / 2) : ℝ) * (Cy' * t ^ (-(1 / 2) : ℝ)) *
          (Cz' * t ^ (-(1 / 2) : ℝ))) (Ioi 1) := by
      refine IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (a := -(3 / 2)) (by norm_num)
        one_pos).const_mul (Cx * Cy' * Cz')) (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) < t := one_pos.trans ht
      have hpow : t ^ (-(3 / 2) : ℝ) =
          t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
        norm_num
      simp only [hpow]
      ring
    refine hg.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := one_pos.trans ht
    have h1 := hCx t ht0
    have h2 := hCy' t ht0
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)) (hCz' t ht0)
      (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans h1) ((norm_nonneg _).trans h2))

/-! ### Symmetry and homogeneity -/

/-- `R_F` is symmetric in its first two arguments. -/
theorem carlsonRF_comm_left (x y z : ℂ) : carlsonRF x y z = carlsonRF y x z := by
  simp only [carlsonRF_def]
  congr 2
  funext t
  ring

/-- `R_F` is symmetric in its last two arguments. -/
theorem carlsonRF_comm_right (x y z : ℂ) : carlsonRF x y z = carlsonRF x z y := by
  simp only [carlsonRF_def]
  congr 2
  funext t
  ring

/-- **Homogeneity of `R_F`.** For real `l > 0`,
`R_F(l x, l y, l z) = l^(-1/2) R_F(x, y, z)`. No hypothesis on `x, y, z` is needed: the substitution
`t = l s` identifies the two integrals whether or not they converge. -/
theorem carlsonRF_ofReal_mul {l : ℝ} (hl : 0 < l) (x y z : ℂ) :
    carlsonRF (l * x) (l * y) (l * z) = (l : ℂ) ^ (-(1 / 2) : ℂ) * carlsonRF x y z := by
  have hscale (s : ℝ) (w : ℂ) : (((l * s : ℝ) : ℂ) + l * w) ^ (-(1 / 2) : ℂ) =
      (l : ℂ) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + w) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_mul, ← mul_add, TauCeti.ofReal_mul_cpow hl.le]
  have hl3 : (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 = (l : ℂ) ^ (-(1 / 2) : ℂ) := by
    have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
    calc (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3
        = (l : ℂ) ^ (1 : ℂ) * (l : ℂ) ^ (-(1 / 2) : ℂ) * (l : ℂ) ^ (-(1 / 2) : ℂ) *
            (l : ℂ) ^ (-(1 / 2) : ℂ) := by rw [Complex.cpow_one]; ring
      _ = (l : ℂ) ^ (-(1 / 2) : ℂ) := by
        rw [← Complex.cpow_add _ _ hl0, ← Complex.cpow_add _ _ hl0, ← Complex.cpow_add _ _ hl0]
        norm_num
  have h := integral_comp_mul_left_Ioi' (fun t : ℝ => ((t : ℂ) + l * x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + l * y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + l * z) ^ (-(1 / 2) : ℂ)) 0 hl
  rw [mul_zero] at h
  have hfun : (fun s : ℝ => (((l * s : ℝ) : ℂ) + l * x) ^ (-(1 / 2) : ℂ) *
      (((l * s : ℝ) : ℂ) + l * y) ^ (-(1 / 2) : ℂ) * (((l * s : ℝ) : ℂ) + l * z) ^ (-(1 / 2) : ℂ)) =
      fun s : ℝ => ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 * (((s : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((s : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + z) ^ (-(1 / 2) : ℂ)) := by
    funext s
    rw [hscale, hscale, hscale]
    ring
  rw [carlsonRF_def, carlsonRF_def, ← h, hfun, integral_const_mul, Complex.real_smul]
  conv_rhs => rw [← hl3]
  ring

/-! ### Diagonal values -/

/-- **The integral form of `R_C`** (DLMF 19.2.17):
`R_C(x, y) = ½ ∫₀^∞ (t + x)^(-1/2) (t + y)⁻¹ dt`. -/
theorem carlsonRC_eq_integral (x y : ℂ) :
    carlsonRC x y = (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y)⁻¹ := by
  rw [carlsonRC_def, carlsonRF_def]
  congr 2
  funext t
  rw [mul_assoc, cpow_neg_half_mul_self]

/-- **The diagonal value of `R_F`**: `R_F(x, x, x) = x^(-1/2)` for `x` in the slit plane. -/
@[simp]
theorem carlsonRF_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRF x x x = x ^ (-(1 / 2) : ℂ) := by
  have hmem (t : ℝ) (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane hx ht
  -- `-2 (t + x)^(-1/2)` is an antiderivative of `(t + x)^(-3/2)` on `[0, ∞)`.
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ))
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) t := by
    intro t ht
    have h := ((((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := (-(1 / 2) : ℂ))
      (hmem t ht)).comp_ofReal).const_mul (-2 : ℂ)
    simp only [id] at h
    convert h using 1
    rw [← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero (hmem t ht)),
      ← Complex.cpow_add _ _ (Complex.slitPlane_ne_zero (hmem t ht)),
      show (-(1 / 2) : ℂ) + -(1 / 2) + -(1 / 2) = -(1 / 2) - 1 by norm_num]
    ring
  have hlim : Tendsto (fun t : ℝ => -2 * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) atTop (𝓝 0) := by
    obtain ⟨C, hC⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow (Or.inl hx)
      (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
    push_cast at hC
    have h0 : Tendsto (fun t : ℝ => C * t ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
    rw [show (0 : ℂ) = -2 * 0 by simp]
    refine Tendsto.const_mul _ (squeeze_zero_norm' ?_ h0)
    filter_upwards [eventually_gt_atTop 0] with t ht using hC t ht
  rw [carlsonRF_def, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_carlsonRF_integrand (Or.inl hx) hx hx) hlim]
  simp only [Complex.ofReal_zero, zero_add]
  ring

/-- **The diagonal value of `R_C`**: `R_C(x, x) = x^(-1/2)` for `x` in the slit plane. -/
@[simp]
theorem carlsonRC_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRC x x = x ^ (-(1 / 2) : ℂ) :=
  carlsonRF_self hx

/-! ### Real arguments -/

/-- **`R_F` is positive at real arguments**: for real `x ≥ 0` and `y, z > 0`, `R_F(x, y, z)` is a
positive real number (in the order `ComplexOrder`, so its imaginary part is `0`). By symmetry, any
one of the three arguments may be the one that vanishes. -/
theorem carlsonRF_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    0 < carlsonRF x y z := by
  have hreal {w t : ℝ} (hw : 0 ≤ w) (ht : 0 < t) :
      ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) = (((t + w) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by linarith)]
    push_cast
    rfl
  set f : ℝ → ℝ := fun t => (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ) *
    (t + z) ^ (-(1 / 2) : ℝ) with hf
  have heq : EqOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) (fun t => ((f t : ℝ) : ℂ)) (Ioi 0) := fun t ht => by
    simp only [hf, hreal hx ht, hreal hy.le ht, hreal hz.le ht, Complex.ofReal_mul]
  have hint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_carlsonRF_integrand (TauCeti.ofReal_mem_slitPlane_union_zero hx)
      (ofReal_mem_slitPlane.mpr hy)
      (ofReal_mem_slitPlane.mpr hz)).congr_fun heq measurableSet_Ioi
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
  rw [carlsonRF_def, setIntegral_congr_fun measurableSet_Ioi heq, integral_complex_ofReal,
    show (1 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ), f t : ℝ) : ℂ) =
      ((1 / 2 * ∫ t in Ioi (0 : ℝ), f t : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_lt_real.mpr (by positivity)

/-! ### Elementary evaluation of `R_C` -/

/-- At real arguments `x ≥ 0`, `y > 0`, `R_C(x, y)` is half the real integral
`∫₀^∞ (√(t + x))⁻¹ (t + y)⁻¹ dt`, so an antiderivative `G` of that integrand on `(0, ∞)` that is
continuous at `0` and vanishes at `∞` gives `R_C(x, y) = -G(0)/2`. -/
private theorem carlsonRC_ofReal_eq_of_hasDerivAt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    {G : ℝ → ℝ} (hG0 : ContinuousWithinAt G (Ici 0) 0)
    (hG : ∀ t : ℝ, 0 < t → HasDerivAt G ((√(t + x))⁻¹ * (t + y)⁻¹) t)
    (hGlim : Tendsto G atTop (𝓝 0)) :
    carlsonRC x y = ((-G 0 / 2 : ℝ) : ℂ) := by
  have heq : EqOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y)⁻¹)
      (fun t => (((√(t + x))⁻¹ * (t + y)⁻¹ : ℝ) : ℂ)) (Ioi 0) := fun t ht => by
    have ht : (0 : ℝ) < t := ht
    dsimp only
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith), Complex.ofReal_mul,
      Complex.ofReal_cpow (by linarith)]
    push_cast
    rfl
  have hint : IntegrableOn (fun t : ℝ => (√(t + x))⁻¹ * (t + y)⁻¹) (Ioi 0) := by
    have h := integrableOn_carlsonRF_integrand (TauCeti.ofReal_mem_slitPlane_union_zero hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hy)
    simp only [mul_assoc, cpow_neg_half_mul_self] at h
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using
      (h.congr_fun heq measurableSet_Ioi).re
  rw [carlsonRC_eq_integral, setIntegral_congr_fun measurableSet_Ioi heq,
    integral_complex_ofReal, integral_Ioi_of_hasDerivAt_of_tendsto hG0 hG hint hGlim]
  push_cast
  ring

/-- **Elementary `R_C`, circular case** (DLMF 19.2.19): for real `0 ≤ x < y`,
`R_C(x, y) = arccos (√(x / y)) / √(y - x)`. -/
theorem carlsonRC_ofReal_eq_arccos {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    carlsonRC x y = ((Real.arccos (√(x / y)) / √(y - x) : ℝ) : ℂ) := by
  have hy : 0 < y := hx.trans_lt hxy
  have hc : 0 < √(y - x) := Real.sqrt_pos.mpr (by linarith)
  rw [carlsonRC_ofReal_eq_of_hasDerivAt hx hy
    (G := fun t => -(2 / √(y - x)) * Real.arccos (√((t + x) / (t + y)))) ?_ ?_ ?_]
  · simp only [zero_add]
    congr 1
    field_simp
  · have : ContinuousAt (fun t : ℝ => (t + x) / (t + y)) 0 :=
      (continuousAt_id.add continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by simp only [zero_add]; exact hy.ne')
    exact (continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.comp this))).continuousWithinAt
  · intro t ht
    have hty : 0 < t + y := by linarith
    have htx : 0 < t + x := by linarith
    have hu : HasDerivAt (fun t : ℝ => (t + x) / (t + y))
        ((1 * (t + y) - (t + x) * 1) / (t + y) ^ 2) t :=
      ((hasDerivAt_id t).add_const x).div ((hasDerivAt_id t).add_const y) hty.ne'
    have hs := hu.sqrt (div_pos htx hty).ne'
    have hlt : √((t + x) / (t + y)) < 1 := by
      rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one hty]
      linarith
    have ha := ((Real.hasDerivAt_arccos (by linarith [Real.sqrt_nonneg ((t + x) / (t + y))])
      hlt.ne).comp t hs).const_mul (-(2 / √(y - x)))
    simp only [Function.comp_def] at ha
    convert ha using 1
    -- Split the square roots of quotients, then clear denominators.
    rw [Real.sq_sqrt (div_pos htx hty).le,
      show 1 - (t + x) / (t + y) = (y - x) / (t + y) by field_simp; ring,
      Real.sqrt_div (by linarith : (0 : ℝ) ≤ y - x), Real.sqrt_div htx.le,
      show 1 * (t + y) - (t + x) * 1 = y - x by ring]
    have hsx := Real.sqrt_pos.mpr htx
    have hsy := Real.sqrt_pos.mpr hty
    field_simp
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hty.le]
    ring
  · have h1 := (Real.continuous_sqrt.tendsto 1).comp (TauCeti.tendsto_add_div_add_atTop x y)
    rw [Real.sqrt_one] at h1
    simpa using ((Real.continuous_arccos.tendsto 1).comp h1).const_mul (-(2 / √(y - x)))

/-- **Elementary `R_C`, hyperbolic case** (DLMF 19.2.20): for real `0 < y < x`,
`R_C(x, y) = arcosh (√(x / y)) / √(x - y)`. -/
theorem carlsonRC_ofReal_eq_arcosh {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    carlsonRC x y = ((Real.arcosh (√(x / y)) / √(x - y) : ℝ) : ℂ) := by
  have hc : 0 < √(x - y) := Real.sqrt_pos.mpr (by linarith)
  have hone (t : ℝ) (ht : 0 ≤ t) : 1 < √((t + x) / (t + y)) := by
    rw [Real.lt_sqrt zero_le_one, one_pow, one_lt_div (by linarith)]
    linarith
  -- The antiderivative is differentiable on all of `[0, ∞)`.
  have hderiv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt
      (fun t => -(2 / √(x - y)) * Real.arcosh (√((t + x) / (t + y))))
      ((√(t + x))⁻¹ * (t + y)⁻¹) t := by
    have hty : 0 < t + y := by linarith
    have htx : 0 < t + x := by linarith
    have hu : HasDerivAt (fun t : ℝ => (t + x) / (t + y))
        ((1 * (t + y) - (t + x) * 1) / (t + y) ^ 2) t :=
      ((hasDerivAt_id t).add_const x).div ((hasDerivAt_id t).add_const y) hty.ne'
    have hs := hu.sqrt (div_pos htx hty).ne'
    have ha := ((Real.hasDerivAt_arcosh (hone t ht)).comp t hs).const_mul (-(2 / √(x - y)))
    simp only [Function.comp_def] at ha
    convert ha using 1
    -- Split the square roots of quotients, then clear denominators.
    rw [Real.sq_sqrt (div_pos htx hty).le,
      show (t + x) / (t + y) - 1 = (x - y) / (t + y) by field_simp; ring,
      Real.sqrt_div (by linarith : (0 : ℝ) ≤ x - y), Real.sqrt_div htx.le,
      show 1 * (t + y) - (t + x) * 1 = -(x - y) by ring]
    have hsx := Real.sqrt_pos.mpr htx
    have hsy := Real.sqrt_pos.mpr hty
    field_simp
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hty.le]
    ring
  rw [carlsonRC_ofReal_eq_of_hasDerivAt (hy.le.trans hyx.le) hy
    (hderiv 0 le_rfl).continuousAt.continuousWithinAt (fun t ht => hderiv t ht.le) ?_]
  · simp only [zero_add]
    congr 1
    field_simp
  · have h1 := (Real.continuous_sqrt.tendsto 1).comp (TauCeti.tendsto_add_div_add_atTop x y)
    rw [Real.sqrt_one] at h1
    have h1' : Tendsto (fun t => √((t + x) / (t + y))) atTop (𝓝[Ici 1] 1) :=
      tendsto_nhdsWithin_iff.mpr ⟨h1, by
        filter_upwards [eventually_ge_atTop 0] with t ht using (hone t ht).le⟩
    have h := ((Real.continuousOn_arcosh 1 self_mem_Ici).tendsto.comp h1').const_mul
      (-(2 / √(x - y)))
    simpa [Real.arcosh_zero] using h

end Complex
