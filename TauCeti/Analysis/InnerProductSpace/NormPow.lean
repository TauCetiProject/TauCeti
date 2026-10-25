/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.Gradient

/-!
# Real powers of the norm away from the origin

Mathlib computes the derivative of `x ↦ ‖x‖ ^ p` on the whole inner-product space when
`1 < p`.  Negative powers, which occur in the Newtonian kernel, are smooth only away from the
origin.  This file supplies the corresponding local derivative, Hessian, and Laplacian formulas
under the explicit hypothesis `x ≠ 0`, together with the Laplacian of the dipole-type product
`x ↦ ⟪a, x⟫ ‖x‖^p`.  The critical exponents give the functions `‖x‖^(2 - dim E)` and
`⟪a, x⟫ ‖x‖^(-dim E)`, harmonic away from the origin, from which the Poisson kernel of a ball is
assembled. The logarithm of the norm, the limit of `(‖x‖ ^ p - 1) / p` as `p → 0`, has
derivative `‖x‖⁻² ⟨x, ·⟩` and Laplacian `(dim E - 2) / ‖x‖²` away from the origin.

The Hessian is bounded by `‖x‖ ^ (p - 2)` in size and, for `p ≤ 3`, by `‖a - b‖ ‖b‖ ^ (p - 3)`
in its variation between points `a` and `b` with `2 ‖a - b‖ ≤ ‖b‖`.  For negative `p` these are
the size and smoothness estimates of a singular integral kernel.

The first derivative proof adapts Mathlib's `hasFDerivAt_norm_rpow`, retaining its norm-square
chain-rule argument while replacing the global exponent hypothesis with the local condition
`x ≠ 0`.

## Main declarations

* `hasFDerivAt_norm_rpow_of_ne`: the derivative of an arbitrary real power away from zero.
* `iteratedFDeriv_two_norm_rpow_apply`: the Hessian of an arbitrary real power away from zero.
* `norm_iteratedFDeriv_two_norm_rpow_le`: the Hessian is `O(‖x‖ ^ (p - 2))`.
* `norm_iteratedFDeriv_two_norm_rpow_sub_le`: for `p ≤ 3`, the Hessian changes by
  `O(‖a - b‖ ‖b‖ ^ (p - 3))` between points `a` and `b` with `2 ‖a - b‖ ≤ ‖b‖`.
* `laplacian_norm_rpow_of_ne`: the radial Laplacian formula
  `Δ ‖x‖^p = p (p + dim E - 2) ‖x‖^(p-2)` away from zero.
* `laplacian_inner_mul_norm_rpow_of_ne`: the dipole formula
  `Δ (⟪a, x⟫ ‖x‖^p) = p (p + dim E) ⟪a, x⟫ ‖x‖^(p-2)` away from zero.
* `harmonicAt_norm_rpow_two_sub_finrank`, `harmonicAt_inner_mul_norm_rpow_neg_finrank`: the
  harmonic radial and dipole powers.
* `hasFDerivAt_log_norm_of_ne`, `laplacian_log_norm_of_ne`: the derivative and the Laplacian of
  `x ↦ log ‖x‖` away from zero.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from the origin, the derivative of `x ↦ ‖x‖ ^ p` is
`p ‖x‖ ^ (p - 2) ⟨x, ·⟩`.  Unlike Mathlib's `hasFDerivAt_norm_rpow`, this local form
allows every real exponent. -/
theorem hasFDerivAt_norm_rpow_of_ne (p : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- The Fréchet derivative of an arbitrary real power of the norm away from the origin. -/
theorem fderiv_norm_rpow_of_ne (p : ℝ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖ ^ p) x = (p * ‖x‖ ^ (p - 2)) • innerSL ℝ x :=
  (hasFDerivAt_norm_rpow_of_ne p hx).fderiv

/-- Away from the origin, the derivative of `x ↦ log ‖x‖` is `‖x‖⁻² ⟨x, ·⟩`. -/
theorem hasFDerivAt_log_norm_of_ne {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ Real.log ‖y‖) ((‖x‖ ^ 2)⁻¹ • innerSL ℝ x) x := by
  have h := ((Real.hasDerivAt_log (pow_pos (norm_pos_iff.2 hx) 2).ne').div_const 2
    ).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  convert h using 1
  · funext y
    simp only [Function.comp_apply, Real.log_pow]
    ring
  · ext v
    simp only [smul_apply, coe_innerSL_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    ring

/-- Away from the origin, the derivative of `x ↦ log ‖x‖` has norm `‖x‖⁻¹`. -/
theorem norm_fderiv_log_norm_of_ne {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E ↦ Real.log ‖y‖) x‖ = ‖x‖⁻¹ := by
  rw [(hasFDerivAt_log_norm_of_ne hx).fderiv, norm_smul, innerSL_apply_norm, norm_inv, norm_pow,
    norm_norm]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp

/-- The Hessian of `x ↦ ‖x‖ ^ p` away from the origin, evaluated on two directions. -/
theorem iteratedFDeriv_two_norm_rpow_apply (p : ℝ) {x : E} (hx : x ≠ 0) (v w : E) :
    iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ p) x ![v, w] =
      p * (p - 2) * ‖x‖ ^ (p - 4) * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ +
        p * ‖x‖ ^ (p - 2) * ⟪v, w⟫_ℝ := by
  have hne : ∀ᶠ y in nhds x, y ≠ 0 := eventually_ne_nhds hx
  have hfd : fderiv ℝ (fun y : E ↦ ‖y‖ ^ p) =ᶠ[nhds x]
      fun y ↦ (p * ‖y‖ ^ (p - 2)) • innerSL ℝ y := by
    filter_upwards [hne] with y hy
    exact fderiv_norm_rpow_of_ne p hy
  have hc : DifferentiableAt ℝ (fun y : E ↦ p * ‖y‖ ^ (p - 2)) x :=
    (hasFDerivAt_norm_rpow_of_ne (p - 2) hx).const_mul p |>.differentiableAt
  have hi : DifferentiableAt ℝ (innerSL ℝ : E → E →L[ℝ] ℝ) x :=
    (innerSL ℝ).differentiableAt
  rw [iteratedFDeriv_two_apply, hfd.fderiv_eq, fderiv_fun_smul hc hi]
  rw [((hasFDerivAt_norm_rpow_of_ne (p - 2) hx).const_mul p).fderiv]
  rw [(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv]
  -- `innerSL ℝ` is bundled as a conjugate-linear map, so this evaluation is not syntactically
  -- an instance of `innerSL_apply_apply`; it is stated separately rather than proved by `rfl`.
  have hinner : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) v w = ⟪v, w⟫_ℝ := innerSL_apply_apply (𝕜 := ℝ) v w
  simp only [Fin.isValue, Matrix.cons_val_zero, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, coe_innerSL_apply, smul_eq_mul,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hinner]
  ring_nf

/-- The Hessian of `x ↦ ‖x‖ ^ p` away from the origin has operator norm at most
`|p| (|p - 2| + 1) ‖x‖ ^ (p - 2)`. -/
theorem norm_iteratedFDeriv_two_norm_rpow_le (p : ℝ) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ p) x‖ ≤ |p| * (|p - 2| + 1) * ‖x‖ ^ (p - 2) := by
  have hN : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h42 : ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN]
    ring_nf
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  have hm : m = ![m 0, m 1] := by ext i; fin_cases i <;> rfl
  rw [hm, iteratedFDeriv_two_norm_rpow_apply p hx, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm x (m 0)
  have h2 := abs_real_inner_le_norm x (m 1)
  have h3 := abs_real_inner_le_norm (m 0) (m 1)
  have hX := Real.rpow_pos_of_pos hN (p - 4)
  have hY := Real.rpow_pos_of_pos hN (p - 2)
  calc |p * (p - 2) * ‖x‖ ^ (p - 4) * ⟪x, m 0⟫_ℝ * ⟪x, m 1⟫_ℝ +
        p * ‖x‖ ^ (p - 2) * ⟪m 0, m 1⟫_ℝ|
      ≤ |p| * |p - 2| * ‖x‖ ^ (p - 4) * (‖x‖ * ‖m 0‖) * (‖x‖ * ‖m 1‖) +
          |p| * ‖x‖ ^ (p - 2) * (‖m 0‖ * ‖m 1‖) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hX]
          gcongr
        · rw [abs_mul, abs_mul, abs_of_pos hY]
          gcongr
    _ = |p| * (|p - 2| + 1) * ‖x‖ ^ (p - 2) * (‖m 0‖ * ‖m 1‖) := by
        rw [← h42]
        ring

/-- Along the line `s ↦ b + s • d`, the Hessian formula of `x ↦ ‖x‖ ^ p`
(`TauCeti.iteratedFDeriv_two_norm_rpow_apply`) evaluated on two fixed directions `v`, `w` is
differentiable at every `t` with `b + t • d ≠ 0`, with derivative at most
`|p (p - 2)| (|p - 4| + 3) ‖b + t • d‖ ^ (p - 3) ‖d‖ ‖v‖ ‖w‖` in absolute value. -/
private theorem exists_hasDerivAt_norm_rpow_hessian_line (p : ℝ) (b d v w : E) {t : ℝ}
    (hz : b + t • d ≠ 0) :
    ∃ g', HasDerivAt (fun s : ℝ ↦ p * (p - 2) * ‖b + s • d‖ ^ (p - 4) * ⟪b + s • d, v⟫_ℝ *
        ⟪b + s • d, w⟫_ℝ + p * ‖b + s • d‖ ^ (p - 2) * ⟪v, w⟫_ℝ) g' t ∧
      |g'| ≤ |p * (p - 2)| * (|p - 4| + 3) * ‖b + t • d‖ ^ (p - 3) * ‖d‖ * ‖v‖ * ‖w‖ := by
  set z := b + t • d with hzdef
  have hN : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpath : HasDerivAt (fun s : ℝ ↦ b + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add b
  have hnorm (q : ℝ) :
      HasDerivAt (fun s : ℝ ↦ ‖b + s • d‖ ^ q) (q * ‖z‖ ^ (q - 2) * ⟪z, d⟫_ℝ) t := by
    simpa [Function.comp_def, mul_assoc] using
      (hasFDerivAt_norm_rpow_of_ne q hz).comp_hasDerivAt t hpath
  have hinner (u : E) : HasDerivAt (fun s : ℝ ↦ ⟪b + s • d, u⟫_ℝ) ⟪d, u⟫_ℝ t := by
    simpa using hpath.inner ℝ (hasDerivAt_const t u)
  refine ⟨p * (p - 2) * (p - 4) * ‖z‖ ^ (p - 4 - 2) * ⟪z, d⟫_ℝ * ⟪z, v⟫_ℝ * ⟪z, w⟫_ℝ +
      p * (p - 2) * ‖z‖ ^ (p - 4) * ⟪d, v⟫_ℝ * ⟪z, w⟫_ℝ +
      p * (p - 2) * ‖z‖ ^ (p - 4) * ⟪z, v⟫_ℝ * ⟪d, w⟫_ℝ +
      p * (p - 2) * ‖z‖ ^ (p - 4) * ⟪z, d⟫_ℝ * ⟪v, w⟫_ℝ,
    (((((hnorm (p - 4)).const_mul (p * (p - 2))).mul (hinner v)).mul (hinner w)).add
      (((hnorm (p - 2)).const_mul p).mul_const ⟪v, w⟫_ℝ)).congr_deriv ?_, ?_⟩
  · -- `ring_nf` also normalizes the real exponents `p - 2 - 2` and `p - 4`.
    simp only [Pi.mul_apply, ← hzdef]
    ring_nf
  -- Each term is a power of `‖z‖` times inner products, each bounded by Cauchy–Schwarz.
  have h6 : ‖z‖ ^ (p - 4 - 2) * ‖z‖ ^ 3 = ‖z‖ ^ (p - 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN]
    ring_nf
  have h4 : ‖z‖ ^ (p - 4) * ‖z‖ = ‖z‖ ^ (p - 3) := by
    rw [← Real.rpow_add_one hN.ne']
    ring_nf
  have hzd := abs_real_inner_le_norm z d
  have hzv := abs_real_inner_le_norm z v
  have hzw := abs_real_inner_le_norm z w
  have hdv := abs_real_inner_le_norm d v
  have hdw := abs_real_inner_le_norm d w
  have hvw := abs_real_inner_le_norm v w
  have hX := Real.rpow_pos_of_pos hN (p - 4 - 2)
  have hY := Real.rpow_pos_of_pos hN (p - 4)
  set A := |p * (p - 2)|
  have hA : A = |p| * |p - 2| := abs_mul _ _
  calc
    _ ≤ A * |p - 4| * ‖z‖ ^ (p - 4 - 2) * (‖z‖ * ‖d‖) * (‖z‖ * ‖v‖) * (‖z‖ * ‖w‖) +
        A * ‖z‖ ^ (p - 4) * (‖d‖ * ‖v‖) * (‖z‖ * ‖w‖) +
        A * ‖z‖ ^ (p - 4) * (‖z‖ * ‖v‖) * (‖d‖ * ‖w‖) +
        A * ‖z‖ ^ (p - 4) * (‖z‖ * ‖d‖) * (‖v‖ * ‖w‖) := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
      · simp only [abs_mul, abs_of_pos hX, hA]
        gcongr
      all_goals
        simp only [abs_mul, abs_of_pos hY, hA]
        gcongr
    _ = A * (|p - 4| * (‖z‖ ^ (p - 4 - 2) * ‖z‖ ^ 3) + 3 * (‖z‖ ^ (p - 4) * ‖z‖)) *
        ‖d‖ * ‖v‖ * ‖w‖ := by ring
    _ = _ := by
      rw [h6, h4]
      ring

/-- **Smoothness of the Hessian of `x ↦ ‖x‖ ^ p`** for `p ≤ 3`: if `2 ‖a - b‖ ≤ ‖b‖`, then

`‖D²(‖·‖ ^ p)(a) - D²(‖·‖ ^ p)(b)‖ ≤ |p (p - 2)| (7 - p) 2 ^ (3 - p) ‖a - b‖ ‖b‖ ^ (p - 3)`.

For `p < 0` this is the smoothness estimate of a singular kernel homogeneous of degree `p - 2`.
The hypothesis `p ≤ 3` is what makes `‖z‖ ^ (p - 3)` largest where `‖z‖` is smallest on the
segment from `b` to `a`, where `‖z‖ ≥ ‖b‖ / 2`. -/
theorem norm_iteratedFDeriv_two_norm_rpow_sub_le {p : ℝ} (hp : p ≤ 3) {a b : E}
    (hab : 2 * ‖a - b‖ ≤ ‖b‖) :
    ‖iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ p) a - iteratedFDeriv ℝ 2 (fun y : E ↦ ‖y‖ ^ p) b‖ ≤
      |p * (p - 2)| * (7 - p) * 2 ^ (3 - p) * ‖a - b‖ * ‖b‖ ^ (p - 3) := by
  have hC : 0 ≤ |p * (p - 2)| * (7 - p) * 2 ^ (3 - p) * ‖a - b‖ * ‖b‖ ^ (p - 3) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith))
      (by positivity)) (norm_nonneg _)) (by positivity)
  rcases eq_or_ne b 0 with rfl | hb
  · obtain rfl : a = 0 := by
      rw [sub_zero, norm_zero] at hab
      exact norm_eq_zero.mp (by linarith [norm_nonneg a])
    simp
  set d := a - b with hd
  have hbN : 0 < ‖b‖ := norm_pos_iff.mpr hb
  -- Every point of the segment from `b` to `a` has norm at least `‖b‖ / 2`.
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖b‖ / 2 ≤ ‖b + t • d‖ := by
    have htd : ‖t • d‖ ≤ ‖d‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have := norm_sub_norm_le b (-(t • d))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hpow (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖b + t • d‖ ^ (p - 3) ≤ 2 ^ (3 - p) * ‖b‖ ^ (p - 3) := by
    calc ‖b + t • d‖ ^ (p - 3) ≤ (‖b‖ / 2) ^ (p - 3) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (hseg t ht) (by linarith)
      _ = 2 ^ (3 - p) * ‖b‖ ^ (p - 3) := by
          rw [Real.div_rpow hbN.le zero_le_two, div_eq_mul_inv, ← Real.rpow_neg zero_le_two]
          ring_nf
  have ha : a ≠ 0 := by
    have := hseg 1 ⟨zero_le_one, le_rfl⟩
    rw [one_smul, hd, add_sub_cancel] at this
    exact norm_pos_iff.mp (by linarith)
  refine ContinuousMultilinearMap.opNorm_le_bound hC fun m ↦ ?_
  set v := m 0
  set w := m 1
  have hm : m = ![v, w] := by ext i; fin_cases i <;> rfl
  rw [Fin.prod_univ_two, sub_apply, hm,
    iteratedFDeriv_two_norm_rpow_apply p ha, iteratedFDeriv_two_norm_rpow_apply p hb]
  -- Apply the mean value inequality to the Hessian formula along the segment from `b` to `a`.
  set g : ℝ → ℝ := fun s ↦ p * (p - 2) * ‖b + s • d‖ ^ (p - 4) * ⟪b + s • d, v⟫_ℝ *
    ⟪b + s • d, w⟫_ℝ + p * ‖b + s • d‖ ^ (p - 2) * ⟪v, w⟫_ℝ with hg
  have key (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    exists_hasDerivAt_norm_rpow_hessian_line p b d v w (t := t)
      (norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hseg t ht)))
  choose! g' hg' hg'b using key
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := g) (f' := g')
    (fun t ht ↦ (hg' t ht).hasDerivWithinAt) (C := |p * (p - 2)| * (7 - p) * 2 ^ (3 - p) *
      ‖d‖ * ‖b‖ ^ (p - 3) * (‖v‖ * ‖w‖)) fun t ht ↦ by
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    rw [Real.norm_eq_abs]
    refine (hg'b t ht').trans ?_
    rw [abs_of_nonpos (by linarith : p - 4 ≤ 0)]
    have := hpow t ht'
    calc |p * (p - 2)| * (-(p - 4) + 3) * ‖b + t • d‖ ^ (p - 3) * ‖d‖ * ‖v‖ * ‖w‖
        = |p * (p - 2)| * (7 - p) * ‖d‖ * ‖v‖ * ‖w‖ * ‖b + t • d‖ ^ (p - 3) := by ring
      _ ≤ |p * (p - 2)| * (7 - p) * ‖d‖ * ‖v‖ * ‖w‖ * (2 ^ (3 - p) * ‖b‖ ^ (p - 3)) := by
        gcongr
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith))
          (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  simpa only [hg, one_smul, zero_smul, add_zero, hd, add_sub_cancel, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hmvt

variable [FiniteDimensional ℝ E]

/-- The Laplacian of a real power of the norm away from the origin is
`p (p + dim E - 2) ‖x‖ ^ (p - 2)`. -/
theorem laplacian_norm_rpow_of_ne (p : ℝ) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ ‖y‖ ^ p) x =
      p * (p + Module.finrank ℝ E - 2) * ‖x‖ ^ (p - 2) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : E ↦ ‖y‖ ^ p) (stdOrthonormalBasis ℝ E)) x]
  simp_rw [iteratedFDeriv_two_norm_rpow_apply p hx]
  rw [Finset.sum_add_distrib]
  have hfirst :
      ∑ i, p * (p - 2) * ‖x‖ ^ (p - 4) * ⟪x, stdOrthonormalBasis ℝ E i⟫_ℝ *
          ⟪x, stdOrthonormalBasis ℝ E i⟫_ℝ =
        p * (p - 2) * ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst]
  simp_rw [real_inner_self_eq_norm_sq,
    (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one, one_pow]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hrpow : ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 2) := by
    calc
      ‖x‖ ^ (p - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (p - 4) * ‖x‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two]
      _ = ‖x‖ ^ ((p - 4) + 2) := (Real.rpow_add hnorm _ _).symm
      _ = ‖x‖ ^ (p - 2) := by ring_nf
  rw [mul_assoc (p * (p - 2)), hrpow]
  ring

/-- The Laplacian of the dipole-type product `x ↦ ⟪a, x⟫ ‖x‖ ^ p` away from the origin is
`p (p + dim E) ⟪a, x⟫ ‖x‖ ^ (p - 2)`. -/
theorem laplacian_inner_mul_norm_rpow_of_ne (a : E) (p : ℝ) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ ⟪a, y⟫_ℝ * ‖y‖ ^ p) x =
      p * (p + Module.finrank ℝ E) * ⟪a, x⟫_ℝ * ‖x‖ ^ (p - 2) := by
  have hℓd : ∀ y, HasFDerivAt (fun y : E ↦ ⟪a, y⟫_ℝ) (toDual ℝ E a) y :=
    fun y ↦ (toDual ℝ E a).hasFDerivAt
  have hℓ : ContDiffAt ℝ 2 (fun y : E ↦ ⟪a, y⟫_ℝ) x := (toDual ℝ E a).contDiff.contDiffAt
  have hg : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ p) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  -- The linear factor has constant derivative, hence vanishing Laplacian.
  have hΔℓ : Δ (fun y : E ↦ ⟪a, y⟫_ℝ) x = 0 := by
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)) x]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [iteratedFDeriv_two_apply, funext fun y ↦ (hℓd y).fderiv]
    simp
  rw [hℓ.laplacian_fun_mul hg, laplacian_norm_rpow_of_ne p hx, hΔℓ,
    (hasGradientAt_iff_hasFDerivAt.mpr (hℓd x)).gradient, inner_gradient_right, conj_trivial,
    fderiv_norm_rpow_of_ne p hx]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm x a]
  ring

/-- Away from the origin, `x ↦ ‖x‖ ^ (2 - dim E)` is harmonic. -/
theorem harmonicAt_norm_rpow_two_sub_finrank {x : E} (hx : x ≠ 0) :
    HarmonicAt (fun y : E ↦ ‖y‖ ^ (2 - Module.finrank ℝ E : ℝ)) x := by
  refine ⟨(contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [laplacian_norm_rpow_of_ne _ hy, Pi.zero_apply]
  ring

/-- Away from the origin, the dipole `x ↦ ⟪a, x⟫ ‖x‖ ^ (-dim E)` is harmonic. -/
theorem harmonicAt_inner_mul_norm_rpow_neg_finrank (a : E) {x : E} (hx : x ≠ 0) :
    HarmonicAt (fun y : E ↦ ⟪a, y⟫_ℝ * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ))) x := by
  refine ⟨(toDual ℝ E a).contDiff.contDiffAt.mul
    ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [laplacian_inner_mul_norm_rpow_of_ne a _ hy, Pi.zero_apply]
  ring

/-- The Laplacian of `x ↦ log ‖x‖` away from the origin is `(dim E - 2) / ‖x‖²`. -/
theorem laplacian_log_norm_of_ne {x : E} (hx : x ≠ 0) :
    Δ (fun y : E ↦ Real.log ‖y‖) x = (Module.finrank ℝ E - 2) / ‖x‖ ^ 2 := by
  have ht : ‖x‖ ^ 2 ≠ 0 := by positivity
  have hcomp : (fun y : E ↦ Real.log ‖y‖) = (fun t ↦ Real.log t / 2) ∘ fun y : E ↦ ‖y‖ ^ 2 := by
    funext y
    simp only [Function.comp_apply, Real.log_pow]
    ring
  have hlog : deriv (fun t : ℝ ↦ Real.log t / 2) = fun t ↦ t⁻¹ / 2 := by
    funext t
    rw [deriv_div_const, Real.deriv_log]
  rw [hcomp, ContDiffAt.laplacian_comp (q := fun y : E ↦ ‖y‖ ^ 2)
    ((Real.contDiffAt_log.2 ht).div_const _) (contDiff_norm_sq ℝ).contDiffAt, laplacian_norm_sq,
    hlog, deriv_div_const, deriv_inv, norm_gradient_eq_norm_fderiv, fderiv_norm_sq_apply,
    RCLike.norm_nsmul ℝ, innerSL_apply_norm, nsmul_eq_mul]
  dsimp only
  field_simp
  ring

end TauCeti

end
