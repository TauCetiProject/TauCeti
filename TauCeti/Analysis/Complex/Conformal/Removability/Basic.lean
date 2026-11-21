/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Painlevé removability across a line

A line is a removable set for *continuous* holomorphic functions: if `F` is continuous on an open
set `Ω ⊆ ℂ` and holomorphic on `Ω` off a line, then `F` is holomorphic on all of `Ω`. This is the
straight-line base case of removability across analytic arcs; circles and charted analytic arcs are
treated in `Removability/Circle.lean` and `Removability/Arc.lean`. It is the analytic content that
makes the Schwarz reflection principle work, and it is what lets two functions holomorphic on the
two open sides of a line be glued along it as soon as the glued function is continuous.

The proof is the classical Morera argument. By
`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`, holomorphy on an open set is
equivalent to continuity together with the vanishing of every rectangle-boundary integral
(`Complex.IsConservativeOn`). Continuity is a hypothesis; for the rectangle integrals we work with
the real axis and split each rectangle there into its part above and its part below. Each half is
bounded by the axis, so its *open interior* misses the axis entirely, where `F` is holomorphic;
Mathlib's continuous-on-closed Cauchy–Goursat lemma
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` then makes each half's
boundary integral vanish, and the shared axis edge cancels when the two halves are recombined. An
arbitrary line is reduced to the real axis by the affine chart `w ↦ p + (q - p) * w`, which is a
biholomorphism of `ℂ` carrying `ℝ` onto the line through `p` and `q`.

The results hold for functions `F : ℂ → E` valued in any complex Banach space `E`.

## Main results

* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero`: removability of the
  real axis, the base case carrying the Morera argument.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_im_pos_of_differentiableOn_im_neg`:
  the gluing form — holomorphic above the axis, holomorphic below it, continuous across it, hence
  holomorphic.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap`:
  removability of any subset of the line through two points `p` and `q`, including the singleton
  case `p = q`.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_im_eq` and
  `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_re_eq`: the horizontal and
  vertical special cases `{z | z.im = c}` and `{z | z.re = c}`.

The Cauchy foundations consumed here are Mathlib's: the rectangle Cauchy–Goursat theorem
(`Analysis/Complex/CauchyIntegral.lean`) and the disc Morera theorem
(`Analysis/Complex/HasPrimitives.lean`).

## References

* Ahlfors, *Complex Analysis*, Chapter 4.6.
* Rudin, *Real and Complex Analysis*, Chapter 11.
-/

public section

namespace TauCeti

open Complex Set intervalIntegral MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω : Set ℂ} {F : ℂ → E}

/-- A rectangle whose open imaginary range avoids `0` has a vanishing boundary integral for any
function continuous on a domain `Ω` containing the (closed) rectangle and holomorphic on the part
of `Ω` off the real axis. This is the per-rectangle input to Morera's theorem; it is applied both
to axis-avoiding rectangles directly and to the two axis-bounded halves of a straddling
rectangle. -/
private lemma boundaryIntegral_eq_zero_off_axis
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω) (haxis : (0 : ℝ) ∉ uIoo z.im w.im) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w
    (hcont.mono hsub) (hdiff.mono fun p hp => ?_)
  rw [Complex.mem_reProdIm, Ioo_min_max, Ioo_min_max] at hp
  exact ⟨hsub (Complex.mem_reProdIm.mpr ⟨uIoo_subset_uIcc_self hp.1, uIoo_subset_uIcc_self hp.2⟩),
    fun h0 => haxis (h0 ▸ hp.2)⟩

/-- The integral of `F` along a vertical edge of the rectangle — the edge with fixed real part `a`
— splits at the real axis: the interval integral over `[[z.im, w.im]]` equals the sum of the
integrals over `z.im → 0` and `0 → w.im`, whenever `F` is continuous on a domain `Ω` containing the
rectangle and `0` lies in the imaginary range `[[z.im, w.im]]`. This is the edge-splitting step
used to recombine the two halves of a straddling rectangle. -/
private lemma vertical_edge_split_at_zero
    (hcont : ContinuousOn F Ω) {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (h0mem : (0 : ℝ) ∈ [[z.im, w.im]]) {a : ℝ} (ha : a ∈ [[z.re, w.re]]) :
    (∫ y : ℝ in z.im..w.im, F (↑a + ↑y * I)) =
      (∫ y : ℝ in z.im..(0 : ℝ), F (↑a + ↑y * I)) +
        ∫ y : ℝ in (0 : ℝ)..w.im, F (↑a + ↑y * I) := by
  -- `F` is continuous along the edge, hence interval-integrable on the parts below and above `0`.
  have contV : ContinuousOn (fun t : ℝ => F (↑a + ↑t * I)) [[z.im, w.im]] :=
    hcont.comp (by fun_prop) fun t ht => hsub (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨by simpa using ha, by simpa using ht⟩)
  refine (integral_add_adjacent_intervals ?_ ?_).symm
  · exact (contV.mono (uIcc_subset_uIcc left_mem_uIcc h0mem)).intervalIntegrable
  · exact (contV.mono (uIcc_subset_uIcc h0mem right_mem_uIcc)).intervalIntegrable

/-- A rectangle that *straddles* the real axis — `0` lies strictly inside its imaginary range — has
a vanishing boundary integral: split it at the axis into a lower and an upper half, each an
axis-bounded rectangle handled by `boundaryIntegral_eq_zero_off_axis`, and recombine, the shared
axis edge cancelling. -/
private lemma boundaryIntegral_eq_zero_of_straddling
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω) (hstr : (0 : ℝ) ∈ uIoo z.im w.im) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  have h0mem : (0 : ℝ) ∈ [[z.im, w.im]] := uIoo_subset_uIcc_self hstr
  -- The lower half `[z, ↑w.re]` and the upper half `[↑z.re, w]`, each bounded by the axis.
  have R1 := boundaryIntegral_eq_zero_off_axis hcont hdiff (z := z) (w := w.re)
    (fun p hp => hsub <| by
      simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.ofReal_re,
        Complex.ofReal_im] at hp ⊢
      exact ⟨hp.1, uIcc_subset_uIcc left_mem_uIcc h0mem hp.2⟩) (by simp)
  have R2 := boundaryIntegral_eq_zero_off_axis hcont hdiff (z := z.re) (w := w)
    (fun p hp => hsub <| by
      simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.ofReal_re,
        Complex.ofReal_im] at hp ⊢
      exact ⟨hp.1, uIcc_subset_uIcc h0mem right_mem_uIcc hp.2⟩) (by simp)
  simp only [Complex.ofReal_re, Complex.ofReal_im] at R1 R2
  -- Split each vertical edge at the axis into its part below and its part above.
  rw [vertical_edge_split_at_zero hcont hsub h0mem right_mem_uIcc,
    vertical_edge_split_at_zero hcont hsub h0mem left_mem_uIcc, smul_add, smul_add]
  linear_combination (norm := module) R1 + R2

variable [CompleteSpace E]

/-- **Painlevé removability of the real axis.** A function continuous on an open set `Ω ⊆ ℂ` and
holomorphic on the part of `Ω` off the real axis is holomorphic on all of `Ω`.

This is the base case of removability across a line: an arbitrary line is reduced to it by an
affine change of variable in
`TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0})) :
    DifferentiableOn ℂ F Ω := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ).mp ⟨?_, hcont⟩
  intro z w hsub
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hstr : (0 : ℝ) ∈ uIoo z.im w.im
  · exact boundaryIntegral_eq_zero_of_straddling hcont hdiff hsub hstr
  · exact boundaryIntegral_eq_zero_off_axis hcont hdiff hsub hstr

/-- **Gluing across the real axis.** A function on an open set `Ω ⊆ ℂ` that is holomorphic on the
open upper part and on the open lower part of `Ω`, and merely *continuous* on `Ω`, is holomorphic
on all of `Ω`. This is the form in which removability is used to glue two separately defined
holomorphic branches along the axis, as in the Schwarz reflection principle. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_im_pos_of_differentiableOn_im_neg
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hpos : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | 0 < z.im}))
    (hneg : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im < 0})) :
    DifferentiableOn ℂ F Ω := by
  refine differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hΩ hcont ?_
  have hoffAxis : Ω ∩ {z : ℂ | z.im ≠ 0} = Ω ∩ {z | 0 < z.im} ∪ Ω ∩ {z | z.im < 0} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_union, ne_iff_lt_or_gt]
    tauto
  rw [hoffAxis]
  exact hpos.union_of_isOpen hneg (hΩ.inter (isOpen_lt continuous_const continuous_im))
    (hΩ.inter (isOpen_lt continuous_im continuous_const))

private theorem
    differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap_of_ne
    {p q : ℂ} {S : Set ℂ}
    (hpq : p ≠ q) (hS : S ⊆ Set.range (AffineMap.lineMap (k := ℝ) p q))
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω \ S)) :
    DifferentiableOn ℂ F Ω := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hφdiff : Differentiable ℂ (fun w : ℂ => p + (q - p) * w) := by fun_prop
  have hψdiff : Differentiable ℂ (fun z : ℂ => (z - p) / (q - p)) := by fun_prop
  -- `w ↦ p + (q - p) * w` is a biholomorphism of `ℂ`, with inverse `z ↦ (z - p) / (q - p)`.
  have hφinv : ∀ z : ℂ, p + (q - p) * ((z - p) / (q - p)) = z := fun z => by
    rw [mul_div_cancel₀ _ hd]; ring
  have hΩ'open : IsOpen ((fun w : ℂ => p + (q - p) * w) ⁻¹' Ω) := hΩ.preimage hφdiff.continuous
  -- Pulled back along the chart, the removable set is swallowed by the real axis.
  have key : DifferentiableOn ℂ (F ∘ fun w : ℂ => p + (q - p) * w)
      ((fun w : ℂ => p + (q - p) * w) ⁻¹' Ω) := by
    refine differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hΩ'open
      (hcont.comp hφdiff.continuous.continuousOn fun w hw => hw) ?_
    refine hdiff.comp hφdiff.differentiableOn fun w hw => ⟨hw.1, fun hmem => hw.2 ?_⟩
    obtain ⟨t, ht⟩ := hS hmem
    rw [AffineMap.lineMap_apply_module', Complex.real_smul] at ht
    -- `t * (q - p) + p = p + (q - p) * w` forces `w = t`, hence `w.im = 0`.
    have hwt : (q - p) * w = (q - p) * (t : ℂ) := by linear_combination -ht
    simp [mul_left_cancel₀ hd hwt]
  -- Transport back along the inverse chart.
  refine (key.comp hψdiff.differentiableOn fun z hz => ?_).congr fun z _ => ?_
  · simpa only [Set.mem_preimage, hφinv z] using hz
  · simp only [Function.comp_apply, hφinv z]

/-- **Painlevé removability across a line.** Let `S` be any subset of the line through points
`p` and `q`, such as the whole line or a segment. A function continuous on an open set `Ω ⊆ ℂ`
and holomorphic on `Ω \ S` is holomorphic on all of `Ω`.

For distinct `p` and `q`, the line is straightened to the real axis by the affine chart
`w ↦ p + (q - p) * w`; when `p = q`, `S` is a singleton and is contained in any nondegenerate
line through `p`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap
    {p q : ℂ} {S : Set ℂ}
    (hS : S ⊆ Set.range (AffineMap.lineMap (k := ℝ) p q))
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω \ S)) :
    DifferentiableOn ℂ F Ω := by
  by_cases hpq : p = q
  · subst q
    refine differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap_of_ne
      (p := p) (q := p + 1) (by simp) (fun z hz => ?_) hΩ hcont hdiff
    obtain ⟨t, rfl⟩ := hS hz
    exact ⟨0, by simp⟩
  · exact differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap_of_ne
      hpq hS hΩ hcont hdiff

/-- **Painlevé removability across a horizontal line.** A function continuous on an open set
`Ω ⊆ ℂ` and holomorphic off the horizontal line `{z | z.im = c}` is holomorphic on all of `Ω`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_im_eq {c : ℝ}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ {z : ℂ | z.im = c})) :
    DifferentiableOn ℂ F Ω := by
  refine differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap
    (p := c * I) (q := 1 + c * I) (fun z hz => ?_) hΩ hcont hdiff
  rw [mem_ofPred_eq] at hz
  exact ⟨z.re, Complex.ext (by simp [AffineMap.lineMap_apply_module'])
    (by simp [AffineMap.lineMap_apply_module', hz])⟩

/-- **Painlevé removability across a vertical line.** A function continuous on an open set
`Ω ⊆ ℂ` and holomorphic off the vertical line `{z | z.re = c}` is holomorphic on all of `Ω`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_re_eq {c : ℝ}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ {z : ℂ | z.re = c})) :
    DifferentiableOn ℂ F Ω := by
  refine differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap
    (p := (c : ℂ)) (q := (c : ℂ) + I) (fun z hz => ?_) hΩ hcont hdiff
  rw [mem_ofPred_eq] at hz
  exact ⟨z.im, Complex.ext (by simp [AffineMap.lineMap_apply_module', hz])
    (by simp [AffineMap.lineMap_apply_module'])⟩

end TauCeti
