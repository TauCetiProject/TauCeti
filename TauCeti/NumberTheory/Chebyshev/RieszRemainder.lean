/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Lipschitz
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.Chebyshev.PsiSubTheta

/-!
# Lipschitz and size bounds for the Riesz remainder

For coefficients `c : ℕ → ℂ` with `‖c(n)‖ ≤ Λ(n)` and a constant `D ∈ ℂ` put
`G(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1) + y D = TauCeti.rieszSum c y + y D`;
for `c(n) = χ(n) Λ(n)` and `D = (L′/L)(1, χ)` this is the *Riesz remainder* `G_χ` of a Dirichlet
character (see `TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder`). For the
trivial character the Riesz remainder is `G_1(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y +
(1 + γ) y`, with the real sum written as `∑ n ∈ Ioc 0 ⌊y⌋₊, …`, the index set of `Chebyshev.psi`.
The Lipschitz bounds for Riesz sums (`TauCeti.norm_rieszSum_sub_rieszSum_le`,
`TauCeti.norm_mul_rieszSum_div_sub_mul_rieszSum_div_le`), Chebyshev's bound `ψ(y) ≤ 3 y`
(`Chebyshev.psi_le_three_mul_self`) and Mertens' first theorem
`|∑_{n ≤ y} Λ(n) / n - log y| ≤ log 4 + 4` (`Chebyshev.abs_sum_vonMangoldt_div_sub_log_le`)
give, for `a ≥ 0`, `w, w' > 0` and `y, z ≥ 1`,
* `|w G(a / w) - w' G(a / w')| ≤ 3 (a / min w w') |w - w'|`, also for `G_1`;
* `|G(y) - G(z)| ≤ |y - z| (log (max y z) + log 4 + 4 + ‖D‖)` and
  `|G_1(y) - G_1(z)| ≤ (log 4 + 4 + γ) |y - z|`;
* `|G(y)| ≤ y (log y + log 4 + 4 + ‖D‖)` and `|G_1(y)| ≤ (log 4 + 6 + γ) y`.

All constants above are at most `2 + γ + (log 4 + 4)`, so this one absolute constant serves in the
bounds for `G_χ` and `G_1`.

## Main results

* `Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le`, `Chebyshev.norm_rieszSum_add_mul_sub_le`,
  `Chebyshev.norm_rieszSum_add_mul_le`: the three bounds for `G` with `‖c(n)‖ ≤ Λ(n)`.
* `Chebyshev.abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le`,
  `Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le`,
  `Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le`: the three bounds for `G_1`.

## References

* The Riesz remainder and these bounds, in the form with an absolute constant, are those of the
  formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open Finset ArithmeticFunction
open scoped Chebyshev
open Real (eulerMascheroniConstant)

namespace Chebyshev

open TauCeti

/-! ### The Riesz remainder of coefficients bounded by `Λ` -/

/-- `ψ` bounds the partial sums of coefficients dominated by `Λ`, over the index set
`Icc 1 ⌊y⌋₊` of `TauCeti.rieszSum`: `∑_{1 ≤ n ≤ y} ‖c(n)‖ ≤ ψ(y) ≤ 3 y` for `y ≥ 0`. -/
private theorem sum_Icc_norm_le_three_mul {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) {y : ℝ}
    (hy : 0 ≤ y) : ∑ n ∈ Icc 1 ⌊y⌋₊, ‖c n‖ ≤ 3 * y := by
  refine (sum_le_sum fun n _ ↦ hc n).trans ?_
  rw [show Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ from Icc_succ_left_eq_Ioc _ _, ← psi]
  exact psi_le_three_mul_self hy

/-- Ordered case of `Chebyshev.norm_mul_rieszSum_div_add_mul_sub_le`. -/
private theorem norm_mul_rieszSum_div_add_mul_sub_le_of_le {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ) {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hww' : w ≤ w') :
    ‖(w : ℂ) * (rieszSum c (a / w) + ((a / w : ℝ) : ℂ) * D) -
        (w' : ℂ) * (rieszSum c (a / w') + ((a / w' : ℝ) : ℂ) * D)‖ ≤
      3 * (a / w) * (w' - w) := by
  have hD (v : ℝ) (hv : 0 < v) : (v : ℂ) * (((a / v : ℝ) : ℂ) * D) = a * D := by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hv.ne']
  rw [mul_add, mul_add, hD w hw, hD w' (hw.trans_le hww'), add_sub_add_right_eq_sub]
  exact (norm_mul_rieszSum_div_sub_mul_rieszSum_div_le c hw hww').trans
    (mul_le_mul_of_nonneg_right (sum_Icc_norm_le_three_mul hc (by positivity))
      (sub_nonneg.2 hww'))

/-- **Lipschitz bound in the weight for the Riesz remainder.** Let
`‖c(n)‖ ≤ Λ(n)` for all `n`, let `D ∈ ℂ` and `G(y) = TauCeti.rieszSum c y + y D`. For
`a ≥ 0` and `w, w' > 0`, `‖w G(a / w) - w' G(a / w')‖ ≤ 3 (a / min w w') |w - w'|`. -/
theorem norm_mul_rieszSum_div_add_mul_sub_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ)
    {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * (rieszSum c (a / w) + ((a / w : ℝ) : ℂ) * D) -
        (w' : ℂ) * (rieszSum c (a / w') + ((a / w' : ℝ) : ℂ) * D)‖ ≤
      3 * (a / min w w') * |w - w'| := by
  rcases le_total w w' with h | h
  · rw [min_eq_left h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact norm_mul_rieszSum_div_add_mul_sub_le_of_le hc D ha hw h
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h), norm_sub_rev]
    exact norm_mul_rieszSum_div_add_mul_sub_le_of_le hc D ha hw' h

/-- **Lipschitz bound for the Riesz remainder.** Let `‖c(n)‖ ≤ Λ(n)` for all
`n`, let `D ∈ ℂ` and `G(y) = TauCeti.rieszSum c y + y D`. If `max y z ≥ 1`, then
`‖G(y) - G(z)‖ ≤ |y - z| (log (max y z) + log 4 + 4 + ‖D‖)`. -/
theorem norm_rieszSum_add_mul_sub_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ) {y z : ℝ}
    (h : 1 ≤ max y z) :
    ‖(rieszSum c y + y * D) - (rieszSum c z + z * D)‖ ≤
      |y - z| * (Real.log (max y z) + (Real.log 4 + 4) + ‖D‖) := by
  wlog hzy : z ≤ y generalizing y z
  · rw [norm_sub_rev, abs_sub_comm, max_comm]
    exact this (by rwa [max_comm]) (not_le.1 hzy).le
  rw [max_eq_left hzy] at h ⊢
  have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, ‖c n‖ / n ≤ Real.log y + (Real.log 4 + 4) := by
    refine (sum_le_sum fun n _ ↦ div_le_div_of_nonneg_right (hc n) n.cast_nonneg).trans ?_
    rw [show Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ from Icc_succ_left_eq_Ioc _ _]
    exact sum_vonMangoldt_div_le h
  rw [abs_of_nonneg (sub_nonneg.2 hzy), add_sub_add_comm, ← sub_mul, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_rieszSum_sub_rieszSum_le c hzy).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.2 hzy)
  · rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 hzy)]

/-- **Size bound for the Riesz remainder.** Let `‖c(n)‖ ≤ Λ(n)` for all `n` and
`D ∈ ℂ`. For `y ≥ 1`, `‖TauCeti.rieszSum c y + y D‖ ≤ y (log y + log 4 + 4 + ‖D‖)`. -/
theorem norm_rieszSum_add_mul_le {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ Λ n) (D : ℂ) {y : ℝ}
    (hy : 1 ≤ y) :
    ‖rieszSum c y + y * D‖ ≤ y * (Real.log y + (Real.log 4 + 4) + ‖D‖) := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  simpa [abs_of_nonneg hy0, max_eq_left hy0] using
    norm_rieszSum_add_mul_sub_le hc D (z := 0) (le_max_of_le_left hy)

/-! ### The Riesz remainder of the trivial character -/

/-- Ordered case of `Chebyshev.abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le`. -/
private theorem abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le_of_le {a w w' : ℝ} (ha : 0 ≤ a)
    (hw : 0 < w) (hww' : w ≤ w') :
    |w * (∑ n ∈ Ioc 0 ⌊a / w⌋₊, Λ n * (a / w / n - 1) - a / w * Real.log (a / w) +
          (1 + eulerMascheroniConstant) * (a / w)) -
        w' * (∑ n ∈ Ioc 0 ⌊a / w'⌋₊, Λ n * (a / w' / n - 1) - a / w' * Real.log (a / w') +
          (1 + eulerMascheroniConstant) * (a / w'))| ≤ 3 * (a / w) * (w' - w) := by
  have hw' := hw.trans_le hww'
  have hX := mul_sum_Ioc_floor_div_le_mul_sum (c := ⇑Λ) (fun n ↦ vonMangoldt_nonneg) (a := a) hw
    hww'
  have hY := (norm_mul_rieszSum_div_sub_mul_rieszSum_div_le (fun n ↦ (Λ n : ℂ)) (a := a) hw
    hww').trans (mul_le_mul_of_nonneg_right (sum_Icc_norm_le_three_mul
      (fun n ↦ (Complex.norm_real _).trans_le (Real.norm_of_nonneg vonMangoldt_nonneg).le)
      (by positivity)) (sub_nonneg.2 hww'))
  rw [← ofReal_sum_Ioc_floor_mul_div_sub_one, ← ofReal_sum_Ioc_floor_mul_div_sub_one,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hY
  have hL : a * Real.log (a / w) - a * Real.log (a / w') = a * (Real.log w' - Real.log w) := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp
    · rw [Real.log_div ha'.ne' hw.ne', Real.log_div ha'.ne' hw'.ne']
      ring
  have hlog : Real.log w' - Real.log w ≤ (w' - w) / w := by
    have h := Real.log_le_sub_one_of_pos (div_pos hw' hw)
    rwa [Real.log_div hw'.ne' hw.ne', ← div_self hw.ne', div_sub_div_same] at h
  have h1 : a * (Real.log w' - Real.log w) ≤ a / w * (w' - w) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlog ha
  have h2 : 0 ≤ a * (Real.log w' - Real.log w) :=
    mul_nonneg ha (sub_nonneg.2 (Real.log_le_log hw hww'))
  have e (v : ℝ) (hv : 0 < v) (S : ℝ) :
      v * (S - a / v * Real.log (a / v) + (1 + eulerMascheroniConstant) * (a / v)) =
        v * S - a * Real.log (a / v) + (1 + eulerMascheroniConstant) * a := by
    field_simp
  rw [e w hw, e w' hw', abs_le]
  constructor <;> linarith [abs_le.1 hY]

/-- **Lipschitz bound in the weight for the trivial Riesz remainder.** Let
`G₁(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y`. For `a ≥ 0` and `w, w' > 0`,
`|w G₁(a / w) - w' G₁(a / w')| ≤ 3 (a / min w w') |w - w'|`. -/
theorem abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le {a w w' : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (hw' : 0 < w') :
    |w * (∑ n ∈ Ioc 0 ⌊a / w⌋₊, Λ n * (a / w / n - 1) - a / w * Real.log (a / w) +
          (1 + eulerMascheroniConstant) * (a / w)) -
        w' * (∑ n ∈ Ioc 0 ⌊a / w'⌋₊, Λ n * (a / w' / n - 1) - a / w' * Real.log (a / w') +
          (1 + eulerMascheroniConstant) * (a / w'))| ≤ 3 * (a / min w w') * |w - w'| := by
  rcases le_total w w' with h | h
  · rw [min_eq_left h, abs_sub_comm w, abs_of_nonneg (sub_nonneg.2 h)]
    exact abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le_of_le ha hw h
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
    exact abs_mul_sum_Ioc_floor_div_sub_mul_log_add_sub_le_of_le ha hw' h

/-- Ordered case of `Chebyshev.abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le`. -/
private theorem abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le_of_le {y z : ℝ}
    (hz : 1 ≤ z) (hzy : z ≤ y) :
    |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + eulerMascheroniConstant) * y) -
        (∑ n ∈ Ioc 0 ⌊z⌋₊, Λ n * (z / n - 1) - z * Real.log z +
          (1 + eulerMascheroniConstant) * z)| ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * (y - z) := by
  have hf : ContinuousOn (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n * (t / n - 1) - t * Real.log t +
      (1 + eulerMascheroniConstant) * t) (Set.Icc z y) :=
    (((continuous_sum_Ioc_floor_mul_div_sub_one _).continuousOn).sub
      Real.continuous_mul_log.continuousOn).add (by fun_prop)
  have hd : ∀ x ∈ Set.Ico z y, HasDerivWithinAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n * (t / n - 1) -
      t * Real.log t + (1 + eulerMascheroniConstant) * t) (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 / n) -
        (Real.log x + 1) + (1 + eulerMascheroniConstant) * 1) (Set.Ici x) x := fun x hx ↦
    ((hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one _ x).sub
      (Real.hasDerivAt_mul_log (by linarith [hx.1])).hasDerivWithinAt).add
      ((hasDerivAt_id' x).const_mul _).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico z y, ‖∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 / n) - (Real.log x + 1) +
      (1 + eulerMascheroniConstant) * 1‖ ≤ Real.log 4 + 4 + eulerMascheroniConstant := by
    intro x hx
    have h := abs_le.1 (abs_sum_vonMangoldt_div_sub_log_le (hz.trans hx.1))
    simp only [mul_one_div] at h ⊢
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant]
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment hf hd hb y ⟨hzy, le_rfl⟩
  rwa [Real.norm_eq_abs] at key

/-- **Lipschitz bound for the trivial Riesz remainder.** Let
`G₁(y) = ∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y`. For `y, z ≥ 1`,
`|G₁(y) - G₁(z)| ≤ (log 4 + 4 + γ) |y - z|`. -/
theorem abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le {y z : ℝ} (hy : 1 ≤ y)
    (hz : 1 ≤ z) :
    |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + eulerMascheroniConstant) * y) -
        (∑ n ∈ Ioc 0 ⌊z⌋₊, Λ n * (z / n - 1) - z * Real.log z +
          (1 + eulerMascheroniConstant) * z)| ≤
      (Real.log 4 + 4 + eulerMascheroniConstant) * |y - z| := by
  rcases le_total z y with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le_of_le hz h
  · rw [abs_sub_comm y z, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
    exact abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_sub_le_of_le hy h

/-- **Size bound for the trivial Riesz remainder.** For `y ≥ 1`,
`|∑_{1 ≤ n ≤ y} Λ(n) (y / n - 1) - y log y + (1 + γ) y| ≤ (log 4 + 6 + γ) y`. -/
theorem abs_sum_Ioc_floor_mul_div_sub_one_sub_mul_log_add_le {y : ℝ} (hy : 1 ≤ y) :
    |∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) - y * Real.log y + (1 + eulerMascheroniConstant) * y| ≤
      (Real.log 4 + 6 + eulerMascheroniConstant) * y := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hS : ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (y / n - 1) = y * ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n / n - ψ y := by
    rw [psi, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ ↦ by ring
  have hE := abs_le.1 (abs_sum_vonMangoldt_div_sub_log_le hy)
  have h1 := mul_le_mul_of_nonneg_left hE.2 hy0
  have h2 := mul_le_mul_of_nonneg_left hE.1 hy0
  have hγ : 0 ≤ eulerMascheroniConstant * y :=
    mul_nonneg (by linarith [Real.one_half_lt_eulerMascheroniConstant]) hy0
  rw [hS, abs_le]
  constructor <;> linarith [psi_le_three_mul_self hy0, psi_nonneg y]

end Chebyshev
