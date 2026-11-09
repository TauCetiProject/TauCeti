/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Coarse bounds near the zeros of a large-parameter Seiberg–Witten solution

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold,
a solution at parameter `r` has normalized spinor `χ = α u₀ + β`, where `α` is a section of the
twisting line and `β` the component orthogonal to the canonical spinor `u₀`. Write
`w₊ = max (1 - |α|²) 0` for the vacuum defect and `h = (2 r)^(-1/2)` for the length scale, so
that `1 / r = 2 h²`. Taubes's coarse estimates include, with a constant `C` independent of `r`
and of the solution,

* the `L¹` defect bound `r ∫ |1 - |χ|²| ≤ C`, where `|χ|² = |α|² + |β|²`;
* the pointwise bound `|β|² ≤ (C / r) w₊ + C / r²`;
* the pointwise gradient bound `|∇_a α|² + r |∇β|² ≤ C r w₊ + C`;
* the pointwise bound `|α|² + |β|² ≤ 1 + C / r`;
* the `L²` bound `‖∂bar_a α‖₂ ≤ C r^(-1/2) (‖∂_a α‖₂ + 1)`;
* the projected Dirac equation, which gives `|∂bar_a α| ≤ C (|∇β| + |α| + |β|)`.

This file derives from them the coarse bounds on the region `{|α|² ≤ 1 / 2}` that contains the
support of the cutoff current `Θ = i F_a + d(χ(|α|²) τ)`
(`TauCeti.SeibergWitten.tsupport_cutoffCurrent_subset`):

* `Vol {|α|² ≤ 1 / 2} ≤ 4 C / r = 8 C h²`
  (`TauCeti.SeibergWitten.measureReal_setOf_norm_sq_le_le`);
* `‖β‖₂² ≤ 2 C (C + Vol X) / r²`, so `‖β‖₂ = O(h²)`
  (`TauCeti.SeibergWitten.integral_norm_sq_le_div_sq`);
* `‖∇_a α‖₂² ≤ 2 C (C + Vol X)`
  (`TauCeti.SeibergWitten.integral_norm_sq_le_of_add_mul_norm_sq_le`);
* `‖∂bar_a α‖₂² ≤ C² (√(2 C (C + Vol X)) + 1)² / r`, so `‖∂bar_a α‖₂ = O(h)`
  (`TauCeti.SeibergWitten.integral_norm_sq_le_div`);
* the pointwise bound `|∂bar_a α| ≤ C (√(2 C) + √(2 (1 + C)))`
  (`TauCeti.SeibergWitten.norm_le_mul_sqrt_add_sqrt`).

The constants depend only on `C` and the volume of `X`, which is what makes these bounds uniform
over a compact family of geometric data and forcing terms. The three integral bounds share one
estimate, `TauCeti.SeibergWitten.integral_le_of_le_mul_max_one_sub`: a nonnegative function
bounded pointwise by `C r w₊ + C` has integral at most `2 C (C + Vol X)`. It holds because the
`β` bound lets the vacuum defect be absorbed into the `L¹` defect, `w₊ ≤ 2 |1 - |χ|²| + 2 C / r²`
once `2 C ≤ r`.

The fields are functions on an arbitrary measure space with values in arbitrary normed groups,
and the hypotheses are the displayed estimates, so the results apply in a coordinate chart and
on the whole manifold alike.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open MeasureTheory Filter

namespace TauCeti.SeibergWitten

variable {X A B F₁ F₂ F₃ F₄ : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
  [NormedAddCommGroup F₃] [NormedAddCommGroup F₄] {α : X → A} {β : X → B} {C r : ℝ}

/-- Pointwise absorption of the vacuum defect: if `b ≤ (C / r) max (1 - s) 0 + C / r²` and
`2 C ≤ r`, then `max (1 - s) 0 ≤ 2 |1 - s - b| + 2 C / r²`. -/
private theorem max_one_sub_le_of_le {s b : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hCr : 2 * C ≤ r)
    (hb : b ≤ C / r * max (1 - s) 0 + C / r ^ 2) :
    max (1 - s) 0 ≤ 2 * |1 - s - b| + 2 * C / r ^ 2 := by
  have hCr₂ : 0 ≤ 2 * C / r ^ 2 := by positivity
  rcases le_total (1 - s) 0 with h | h
  · rw [max_eq_right h]
    linarith [abs_nonneg (1 - s - b)]
  · rw [max_eq_left h] at hb ⊢
    have hhalf : C / r ≤ 1 / 2 := by
      rw [div_le_iff₀ hr]
      linarith
    have := mul_le_mul_of_nonneg_right hhalf h
    have := le_abs_self (1 - s - b)
    have : 2 * C / r ^ 2 = 2 * (C / r ^ 2) := by ring
    linarith

/-- **The integrated coarse bound.** Let `(α, β)` satisfy the `L¹` defect bound
`r ∫ |1 - |α|² - |β|²| ≤ C` and, almost everywhere, `|β|² ≤ (C / r) w₊ + C / r²` with
`w₊ = max (1 - |α|²) 0`, on a finite measure space, where `2 C ≤ r`. Then every function `g`
with `0 ≤ g ≤ C r w₊ + C` almost everywhere has integral at most `2 C (C + Vol X)`. -/
theorem integral_le_of_le_mul_max_one_sub [IsFiniteMeasure μ] {g : X → ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hCr : 2 * C ≤ r) (hδ : Integrable (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hβ : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2)
    (hg₀ : 0 ≤ᵐ[μ] g) (hg : ∀ᵐ x ∂μ, g x ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C) :
    ∫ x, g x ∂μ ≤ 2 * C * (C + μ.real Set.univ) := by
  have hint : Integrable
      (fun x ↦ 2 * C * r * |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| + (2 * C ^ 2 / r + C)) μ :=
    (hδ.abs.const_mul _).add (integrable_const _)
  have hCC : 2 * C ^ 2 / r ≤ C := by
    rw [div_le_iff₀ hr]
    nlinarith
  calc ∫ x, g x ∂μ
      ≤ ∫ x, (2 * C * r * |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| + (2 * C ^ 2 / r + C)) ∂μ := by
        refine integral_mono_of_nonneg hg₀ hint ?_
        filter_upwards [hβ, hg] with x hβx hgx
        -- Absorb the vacuum defect into the `L¹` defect: `w₊ ≤ 2 |1 - |χ|²| + 2 C / r²`.
        have hw := max_one_sub_le_of_le hr hC hCr hβx
        calc g x ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C := hgx
          _ ≤ C * r * (2 * |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| + 2 * C / r ^ 2) + C := by gcongr
          _ = 2 * C * r * |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| + (2 * C ^ 2 / r + C) := by
            field_simp
            ring
    _ = 2 * C * (r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ) +
          (2 * C ^ 2 / r + C) * μ.real Set.univ := by
        rw [integral_add (hδ.abs.const_mul _) (integrable_const _), integral_const_mul,
          integral_const, smul_eq_mul]
        ring
    _ ≤ 2 * C * C + 2 * C * μ.real Set.univ := by
        gcongr
        linarith
    _ = 2 * C * (C + μ.real Set.univ) := by ring

/-- **The volume of the low-modulus region.** If `r ∫ |1 - |α|² - |β|²| ≤ C` and, almost
everywhere, `|β|² ≤ (C / r) w₊ + C / r²` with `w₊ = max (1 - |α|²) 0`, where `r ≥ 1` and
`8 C ≤ r`, then the region `{|α|² ≤ 1 / 2}` has measure at most `4 C / r`, that is `8 C h²` for
`h = (2 r)^(-1/2)`. The measure need not be finite. -/
theorem measureReal_setOf_norm_sq_le_le (hr : 1 ≤ r) (hC : 0 ≤ C) (hCr : 8 * C ≤ r)
    (hδ : Integrable (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hβ : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) :
    μ.real {x | ‖α x‖ ^ 2 ≤ 1 / 2} ≤ 4 * C / r := by
  have hr₀ : 0 < r := by linarith
  have hCr₁ : C / r ≤ 1 / 8 := by
    rw [div_le_iff₀ hr₀]
    linarith
  have hCr₂ : C / r ^ 2 ≤ C / r := div_le_div_of_nonneg_left hC hr₀ (by nlinarith)
  -- Where `|α|² ≤ 1 / 2`, the `β` bound gives `|β|² ≤ 1 / 4`, so `|1 - |α|² - |β|²| ≥ 1 / 4`.
  have hsub : {x | ‖α x‖ ^ 2 ≤ 1 / 2} ≤ᵐ[μ]
      {x | 1 / 4 ≤ ‖1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2‖} := by
    filter_upwards [hβ] with x hx hs
    have hw : max (1 - ‖α x‖ ^ 2) 0 ≤ 1 := max_le (by linarith [sq_nonneg ‖α x‖]) zero_le_one
    have : C / r * max (1 - ‖α x‖ ^ 2) 0 ≤ C / r := by
      simpa using mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ C / r)
    simp only [Real.norm_eq_abs] at hs ⊢
    exact le_abs.2 (Or.inl (by linarith))
  have hfin := (hδ.measure_norm_ge_lt_top (by norm_num : (0 : ℝ) < 1 / 4)).ne
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (.of_forall fun x ↦ norm_nonneg _) hδ.norm
    (1 / 4)
  simp only [Real.norm_eq_abs] at hmarkov hfin hsub
  have hint : ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C / r := by
    rw [le_div_iff₀ hr₀]
    linarith
  calc μ.real {x | ‖α x‖ ^ 2 ≤ 1 / 2}
      ≤ μ.real {x | 1 / 4 ≤ |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2|} :=
        ENNReal.toReal_mono hfin (measure_mono_ae hsub)
    _ ≤ 4 * C / r := by
        rw [mul_div_assoc]
        linarith

/-- **The `L²` bound on `β`.** Under the `L¹` defect bound `r ∫ |1 - |α|² - |β|²| ≤ C` and the
pointwise bound `|β|² ≤ (C / r) w₊ + C / r²`, with `w₊ = max (1 - |α|²) 0` and `2 C ≤ r`, on a
finite measure space, `∫ |β|² ≤ 2 C (C + Vol X) / r²`. Thus `‖β‖₂ = O(h²)` for
`h = (2 r)^(-1/2)`. -/
theorem integral_norm_sq_le_div_sq [IsFiniteMeasure μ] (hr : 0 < r) (hC : 0 ≤ C)
    (hCr : 2 * C ≤ r) (hδ : Integrable (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hβ : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) :
    ∫ x, ‖β x‖ ^ 2 ∂μ ≤ 2 * C * (C + μ.real Set.univ) / r ^ 2 := by
  have h := integral_le_of_le_mul_max_one_sub (g := fun x ↦ r ^ 2 * ‖β x‖ ^ 2) hr hC hCr hδ hL1
    hβ (.of_forall fun x ↦ by positivity) <| by
      filter_upwards [hβ] with x hx
      calc r ^ 2 * ‖β x‖ ^ 2 ≤ r ^ 2 * (C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) := by gcongr
        _ = C * r * max (1 - ‖α x‖ ^ 2) 0 + C := by field_simp
  rw [integral_const_mul] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **The `L²` bound on the covariant derivative of `α`.** Under the `L¹` defect bound
`r ∫ |1 - |α|² - |β|²| ≤ C`, the pointwise bound `|β|² ≤ (C / r) w₊ + C / r²` and the pointwise
gradient bound `|∇_a α|² + r |∇β|² ≤ C r w₊ + C`, with `w₊ = max (1 - |α|²) 0` and `2 C ≤ r`, on a
finite measure space, `∫ |∇_a α|² ≤ 2 C (C + Vol X)`. Here `∇_a α` and `∇β` are any functions
`Dα` and `Dβ` satisfying the gradient bound. -/
theorem integral_norm_sq_le_of_add_mul_norm_sq_le [IsFiniteMeasure μ] {Dα : X → F₁}
    {Dβ : X → F₂} (hr : 0 < r) (hC : 0 ≤ C) (hCr : 2 * C ≤ r)
    (hδ : Integrable (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hβ : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ᵐ x ∂μ, ‖Dα x‖ ^ 2 + r * ‖Dβ x‖ ^ 2 ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C) :
    ∫ x, ‖Dα x‖ ^ 2 ∂μ ≤ 2 * C * (C + μ.real Set.univ) :=
  integral_le_of_le_mul_max_one_sub hr hC hCr hδ hL1 hβ (.of_forall fun x ↦ by positivity) <| by
    filter_upwards [hgrad] with x hx
    have : 0 ≤ r * ‖Dβ x‖ ^ 2 := by positivity
    linarith

/-- **The `L²` bound on `∂bar_a α`.** Assume the hypotheses of
`TauCeti.SeibergWitten.integral_norm_sq_le_of_add_mul_norm_sq_le`, that `∂_a α` is pointwise
dominated by `∇_a α`, and Taubes's estimate `‖∂bar_a α‖₂ ≤ C r^(-1/2) (‖∂_a α‖₂ + 1)`, written
with `L²` norms `√(∫ |f|²)`. Then `∫ |∂bar_a α|² ≤ C² (√(2 C (C + Vol X)) + 1)² / r`, so
`‖∂bar_a α‖₂ = O(h)` for `h = (2 r)^(-1/2)`. Here `∇_a α`, `∇β`, `∂_a α` and `∂bar_a α` are any
functions `Dα`, `Dβ`, `Dα'` and `Dbar` satisfying these hypotheses. -/
theorem integral_norm_sq_le_div [IsFiniteMeasure μ] {Dα : X → F₁} {Dβ : X → F₂}
    {Dα' : X → F₃} {Dbar : X → F₄} (hr : 0 < r) (hC : 0 ≤ C) (hCr : 2 * C ≤ r)
    (hδ : Integrable (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hβ : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2)
    (hgrad : ∀ᵐ x ∂μ, ‖Dα x‖ ^ 2 + r * ‖Dβ x‖ ^ 2 ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C)
    (hDα' : ∀ᵐ x ∂μ, ‖Dα' x‖ ≤ ‖Dα x‖)
    (hDbar : √(∫ x, ‖Dbar x‖ ^ 2 ∂μ) ≤ C / √r * (√(∫ x, ‖Dα' x‖ ^ 2 ∂μ) + 1)) :
    ∫ x, ‖Dbar x‖ ^ 2 ∂μ ≤ C ^ 2 * (√(2 * C * (C + μ.real Set.univ)) + 1) ^ 2 / r := by
  have hα' : ∫ x, ‖Dα' x‖ ^ 2 ∂μ ≤ 2 * C * (C + μ.real Set.univ) :=
    integral_norm_sq_le_of_add_mul_norm_sq_le (Dβ := Dβ) hr hC hCr hδ hL1 hβ <| by
      filter_upwards [hgrad, hDα'] with x hx hx'
      have := pow_le_pow_left₀ (norm_nonneg _) hx' 2
      linarith
  have hbound : √(∫ x, ‖Dbar x‖ ^ 2 ∂μ) ≤ C / √r * (√(2 * C * (C + μ.real Set.univ)) + 1) :=
    hDbar.trans (by gcongr)
  calc ∫ x, ‖Dbar x‖ ^ 2 ∂μ = √(∫ x, ‖Dbar x‖ ^ 2 ∂μ) ^ 2 :=
        (Real.sq_sqrt (integral_nonneg fun x ↦ by positivity)).symm
    _ ≤ (C / √r * (√(2 * C * (C + μ.real Set.univ)) + 1)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
    _ = C ^ 2 * (√(2 * C * (C + μ.real Set.univ)) + 1) ^ 2 / r := by
        rw [mul_pow, div_pow, Real.sq_sqrt hr.le]
        ring

/-- **The pointwise bound on `∂bar_a α`.** Let `r ≥ 1` and `C ≥ 0`. At a point where the spinor
components satisfy `|α|² + |β|² ≤ 1 + C / r`, the gradient bound
`|∇_a α|² + r |∇β|² ≤ C r w₊ + C` with `w₊ = max (1 - |α|²) 0`, and the projected Dirac bound
`|∂bar_a α| ≤ C (|∇β| + |α| + |β|)`, the bound `|∂bar_a α| ≤ C (√(2 C) + √(2 (1 + C)))` holds.
Here `a`, `b`, `Da`, `Db` and `d` stand for the values of `α`, `β`, `∇_a α`, `∇β` and
`∂bar_a α` at that point. -/
theorem norm_le_mul_sqrt_add_sqrt {a : A} {b : B} {Da : F₁} {Db : F₂} {d : F₃} (hr : 1 ≤ r)
    (hC : 0 ≤ C) (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 1 + C / r)
    (hgrad : ‖Da‖ ^ 2 + r * ‖Db‖ ^ 2 ≤ C * r * max (1 - ‖a‖ ^ 2) 0 + C)
    (hd : ‖d‖ ≤ C * (‖Db‖ + ‖a‖ + ‖b‖)) :
    ‖d‖ ≤ C * (√(2 * C) + √(2 * (1 + C))) := by
  have hr₀ : 0 < r := by linarith
  -- The gradient bound with `w₊ ≤ 1` and `r ≥ 1` gives `|∇β|² ≤ 2 C`.
  have hDb : ‖Db‖ ≤ √(2 * C) := by
    refine Real.le_sqrt_of_sq_le ?_
    have hw : max (1 - ‖a‖ ^ 2) 0 ≤ 1 := max_le (by linarith [sq_nonneg ‖a‖]) zero_le_one
    have : C * r * max (1 - ‖a‖ ^ 2) 0 ≤ C * r := by
      simpa using mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ C * r)
    nlinarith [sq_nonneg ‖Da‖, sq_nonneg ‖Db‖]
  -- `(|α| + |β|)² ≤ 2 (|α|² + |β|²) ≤ 2 (1 + C)`.
  have hab' : ‖a‖ + ‖b‖ ≤ √(2 * (1 + C)) := by
    refine Real.le_sqrt_of_sq_le ?_
    have : C / r ≤ C := div_le_self hC hr
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc ‖d‖ ≤ C * (‖Db‖ + ‖a‖ + ‖b‖) := hd
    _ ≤ C * (√(2 * C) + √(2 * (1 + C))) := by
        rw [add_assoc]
        gcongr

end TauCeti.SeibergWitten
