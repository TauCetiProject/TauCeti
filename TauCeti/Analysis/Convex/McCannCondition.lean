/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Analysis.Convex.RecessionConstant
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.Convex.FunctionTopology
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Matrix.MinkowskiDeterminant

/-!
# Consequences of McCann's condition

A function `U : ℝ → ℝ` satisfies *McCann's condition* in dimension `n` when
`φ(s) = sⁿ U(s⁻ⁿ)` is convex and nonincreasing on `(0, ∞)`. This is the hypothesis of McCann's
displacement convexity of the internal energy `∫ U(dμ/dρ) dρ`. This file records the scalar facts
about `U` and `φ` that it is used through, independently of any transport, and McCann's pointwise
inequality at a positive operator, where the dimension `n` is that of the underlying space.

## Main results

* `TauCeti.pow_mul_apply_div_pow_eq`: for `r, a > 0`, `aⁿ U(r / aⁿ) = r φ(r^{-1/n} a)`.
* `TauCeti.pow_mul_apply_div_pow_le`: McCann's pointwise inequality, comparing `aⁿ U(r / aⁿ)` with
  the convex combination of its values at `1` and `a₁` when `(1 - t) + t a₁ ≤ a`.
* `ContinuousLinearMap.IsPositive.det_mul_apply_div_det_le`: McCann's pointwise inequality at a
  positive operator `A`, comparing `Jₜ U(r / Jₜ)` with the convex combination of its values at
  `t = 0` and `t = 1`, where `Jₜ = det ((1 - t) • 1 + t • A)`.
* `TauCeti.pow_mul_apply_inv_pow_le_recessionConstant`: if `φ` is nonincreasing on `(0, ∞)`, then
  the recession constant of `U` bounds `φ` above there.
* `TauCeti.measurable_apply_max_of_convexOn`: if `φ` is convex on `(0, ∞)`, then `U` is measurable
  on `[0, ∞)`.

## References

* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179.
-/

public section

open Set Filter Module

namespace TauCeti

variable {U : ℝ → ℝ} {n : ℕ}

/-- For `r > 0` and `a > 0`, the function `a ↦ aⁿ U(r / aⁿ)` is `r φ(c a)` with
`φ(s) = sⁿ U(s⁻ⁿ)` and `c = r^{-1/n}`. -/
theorem pow_mul_apply_div_pow_eq (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) :
    a ^ n * U (r / a ^ n) =
      r * ((r⁻¹ ^ (n⁻¹ : ℝ) * a) ^ n * U ((r⁻¹ ^ (n⁻¹ : ℝ) * a) ^ n)⁻¹) := by
  rw [mul_pow, Real.rpow_inv_natCast_pow (inv_nonneg.2 hr.le) hn,
    show (r⁻¹ * a ^ n)⁻¹ = r / a ^ n by field_simp]
  field_simp

/-- If `φ(s) = sⁿ U(s⁻ⁿ)` is nonincreasing on `(0, ∞)`, with `n ≠ 0`, then the recession constant
`U'(∞) = lim U(r) / r` bounds `φ` above on `(0, ∞)`, because `U(r) / r = φ(r^{-1/n})`. -/
theorem pow_mul_apply_inv_pow_le_recessionConstant (hn : n ≠ 0)
    (ha : AntitoneOn (fun s : ℝ => s ^ n * U (s ^ n)⁻¹) (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    ((s ^ n * U (s ^ n)⁻¹ : ℝ) : EReal) ≤ recessionConstant U := by
  rw [recessionConstant_def]
  refine le_limsup_of_frequently_le (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop (s ^ n)⁻¹, eventually_gt_atTop 0] with r hr hr0
  set c := r⁻¹ ^ (n⁻¹ : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos (inv_pos.2 hr0) _
  have hcn : c ^ n = r⁻¹ := Real.rpow_inv_natCast_pow (inv_nonneg.2 hr0.le) hn
  have hcs : c ≤ s := by
    refine (pow_le_pow_iff_left₀ hc0.le hs.le hn).1 ?_
    rw [hcn]
    exact inv_le_of_inv_le₀ (by positivity) hr
  have := ha (mem_Ioi.2 hc0) (mem_Ioi.2 hs) hcs
  rw [EReal.coe_le_coe_iff]
  refine this.trans_eq ?_
  simp only [hcn, inv_inv]
  ring

/-- **McCann's pointwise inequality.** Let `U 0 = 0` and let `φ(s) = sⁿ U(s⁻ⁿ)` be convex and
nonincreasing on `(0, ∞)`, with `n ≠ 0`. If `a > 0` and `a₁ ≥ 0` satisfy the concavity bound
`(1 - t) + t a₁ ≤ a` for some `t ∈ [0, 1]`, then for every `r ≥ 0`,
`aⁿ U(r / aⁿ) ≤ (1 - t) U(r) + t a₁ⁿ U(r / a₁ⁿ)` when `a₁ > 0`, and
`aⁿ U(r / aⁿ) ≤ (1 - t) U(r) + t r L` when `a₁ = 0`, where `L` bounds `φ` above. -/
theorem pow_mul_apply_div_pow_le (hn : n ≠ 0) (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ n * U (s ^ n)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ n * U (s ^ n)⁻¹) (Ioi 0)) {r t a a₁ L : ℝ} (hr : 0 ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hapos : 0 < a) (ha₁ : 0 ≤ a₁) (hle : 1 - t + t * a₁ ≤ a)
    (hL : a₁ = 0 → 0 < r → ∀ s ∈ Ioi (0 : ℝ), s ^ n * U (s ^ n)⁻¹ ≤ L) :
    a ^ n * U (r / a ^ n) ≤
      (1 - t) * U r + t * (if a₁ = 0 then r * L else a₁ ^ n * U (r / a₁ ^ n)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [hU0]
  set φ : ℝ → ℝ := fun s => s ^ n * U (s ^ n)⁻¹
  set c := r⁻¹ ^ (n⁻¹ : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos (inv_pos.2 hr) _
  have hU1 : U r = r * φ (c * 1) := by
    simpa using pow_mul_apply_div_pow_eq (U := U) hn hr one_pos
  rw [pow_mul_apply_div_pow_eq hn hr hapos, hU1, mul_one]
  split_ifs with ha₁0
  · -- The degenerate case: compare with `φ (c (1 - t))` and use the bound `L` at `0`.
    subst ha₁0
    have hφL := hL rfl hr
    rcases ht.2.eq_or_lt with rfl | ht₁
    · simpa using mul_le_mul_of_nonneg_left (hφL _ (mul_pos hc0 hapos)) hr.le
    have hb : 0 < 1 - t := sub_pos.2 ht₁
    have h₁ : φ (c * a) ≤ φ ((1 - t) * c) :=
      ha (mem_Ioi.2 (mul_pos hb hc0)) (mem_Ioi.2 (mul_pos hc0 hapos))
        (by nlinarith)
    have h₂ := hc.apply_mul_le_of_forall_le hφL hc0 hb (by linarith [ht.1])
    have := mul_le_mul_of_nonneg_left (h₁.trans h₂) hr.le
    linarith
  · have ha₁' : 0 < a₁ := lt_of_le_of_ne ha₁ (Ne.symm ha₁0)
    rw [pow_mul_apply_div_pow_eq hn hr ha₁']
    have hpos : 0 < 1 - t + t * a₁ := by
      rcases ht.2.eq_or_lt with rfl | ht₁
      · simpa using ha₁'
      · nlinarith [ht.1]
    have h₁ : φ (c * a) ≤ φ (c * (1 - t + t * a₁)) :=
      ha (mem_Ioi.2 (mul_pos hc0 hpos)) (mem_Ioi.2 (mul_pos hc0 hapos))
        (mul_le_mul_of_nonneg_left hle hc0.le)
    have h₂ : φ (c * (1 - t + t * a₁)) ≤ (1 - t) * φ c + t * φ (c * a₁) := by
      have := hc.2 (mem_Ioi.2 hc0) (mem_Ioi.2 (mul_pos hc0 ha₁')) (sub_nonneg.2 ht.2) ht.1
        (by ring)
      simp only [smul_eq_mul] at this
      convert this using 2
      ring
    have := mul_le_mul_of_nonneg_left (h₁.trans h₂) hr.le
    linarith

/-- **McCann's inequality at a positive operator.** Let `U 0 = 0` and let `φ(s) = sⁿ U(s⁻ⁿ)` be
convex and nonincreasing on `(0, ∞)`, where `n ≥ 1` is the dimension of `E`. For a positive operator
`A` on `E`, write `Jₛ = det ((1 - s) • 1 + s • A)`. For `0 < t < 1` and `r ≥ 0`,
`Jₜ U(r / Jₜ) ≤ (1 - t) U(r) + t J₁ U(r / J₁)` when `J₁ ≠ 0`, and
`Jₜ U(r / Jₜ) ≤ (1 - t) U(r) + t L r` when `J₁ = 0`, provided `L` then bounds `φ` above. The
concavity of `s ↦ Jₛ^{1/n}` is Minkowski's determinant inequality. -/
theorem _root_.ContinuousLinearMap.IsPositive.det_mul_apply_div_det_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    {A : E →L[ℝ] E} (hA : A.IsPositive) (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹) (Ioi 0))
    {r t L : ℝ} (hr : 0 ≤ r) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hL : A.det = 0 → 0 < r →
      ∀ s ∈ Ioi (0 : ℝ), s ^ finrank ℝ E * U (s ^ finrank ℝ E)⁻¹ ≤ L) :
    ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det *
        U (r / ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det) ≤
      (1 - t) * U r + t * (if A.det = 0 then L * r else A.det * U (r / A.det)) := by
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn)
  have hA' := (ContinuousLinearMap.isPositive_toLinearMap_iff _).2 hA
  have hJ : 0 < ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det :=
    hA.det_one_sub_smul_id_add_smul_pos ht₀.le ht₁
  have hJ₁ : 0 ≤ A.det := hA'.det_nonneg
  -- Minkowski's determinant inequality: `s ↦ det ((1 - s) • 1 + s • A) ^ (1 / n)` is concave.
  have hle : 1 - t + t * A.det ^ (n⁻¹ : ℝ) ≤
      ((1 - t) • ContinuousLinearMap.id ℝ E + t • A).det ^ (n⁻¹ : ℝ) := by
    have := LinearMap.concaveOn_det_rpow.2 ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2
      ContinuousLinearMap.isPositive_id) hA' (sub_nonneg.2 ht₁.le) ht₀.le (sub_add_cancel 1 t)
    simpa [ContinuousLinearMap.det, smul_eq_mul] using this
  have key := pow_mul_apply_div_pow_le hn hU0 hc ha (r := r) (L := L) hr ⟨ht₀.le, ht₁.le⟩
    (Real.rpow_pos_of_pos hJ _) (Real.rpow_nonneg hJ₁ _) hle
    fun ha₁ => hL ((Real.rpow_eq_zero hJ₁ hn').1 ha₁)
  rw [Real.rpow_inv_natCast_pow hJ.le hn, Real.rpow_inv_natCast_pow hJ₁ hn] at key
  simp only [Real.rpow_eq_zero hJ₁ hn'] at key
  refine key.trans_eq ?_
  split_ifs <;> ring

/-- If `φ(s) = sⁿ U(s⁻ⁿ)` is convex on `(0, ∞)`, with `n ≠ 0`, then `U` is measurable on
`[0, ∞)`: it is continuous on `(0, ∞)`, where `U(r) = r φ(r^{-1/n})` with `φ` convex. -/
theorem measurable_apply_max_of_convexOn (hn : n ≠ 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ n * U (s ^ n)⁻¹) :
    Measurable fun r : ℝ => U (max r 0) := by
  refine measurable_of_continuousOn_compl_singleton 0 fun r hr => ?_
  rcases lt_or_gt_of_ne hr with hr | hr
  · -- Left of `0` the function is constant.
    refine (continuousAt_const (y := U 0)).congr ?_ |>.continuousWithinAt
    filter_upwards [Iio_mem_nhds hr] with r' hr'
    rw [max_eq_right hr'.le]
  · -- Right of `0` it is `r ↦ r φ(r^{-1/n})`, with `φ` continuous as a convex function.
    have hφ : ContinuousOn (fun s : ℝ => s ^ n * U (s ^ n)⁻¹) (Ioi 0) := by
      simpa using hc.continuousOn_interior
    have hpos : 0 < r⁻¹ ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos (inv_pos.2 hr) _
    have hcont : ContinuousAt (fun r : ℝ => r * ((r⁻¹ ^ (n⁻¹ : ℝ)) ^ n *
        U ((r⁻¹ ^ (n⁻¹ : ℝ)) ^ n)⁻¹)) r := by
      exact continuousAt_id.mul ((hφ.continuousAt (Ioi_mem_nhds hpos)).comp
        (f := fun r : ℝ => r⁻¹ ^ (n⁻¹ : ℝ))
        ((continuousAt_inv₀ hr.ne').rpow_const (.inl (inv_ne_zero hr.ne'))))
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [Ioi_mem_nhds hr] with r' hr'
    have := pow_mul_apply_div_pow_eq (U := U) hn hr' one_pos
    simp only [one_pow, div_one, one_mul, mul_one] at this
    rw [max_eq_left (le_of_lt hr'), this]

end TauCeti
