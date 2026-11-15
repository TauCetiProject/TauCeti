/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Fourier.TwistedWirtinger
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The Cauchy–Riemann operator on a flat line bundle over a torus

Let `ω₁, ω₂ ∈ ℂ` be linearly independent over `ℝ`, so that they span a lattice `Λ` and `ℂ / Λ` is a
torus with its flat complex structure. A unitary character `χ : Λ → U(1)`,
`χ(ω₁) = exp (2πiθ₁)`, `χ(ω₂) = exp (2πiθ₂)`, defines a flat Hermitian line bundle over `ℂ / Λ`,
with holonomy `χ`. Its sections are the functions `u : ℂ → ℂ` with

`u (z + ω₁) = exp (2πiθ₁) u z`,  `u (z + ω₂) = exp (2πiθ₂) u z`,

and its holomorphic structure is the Cauchy–Riemann operator `∂bar u`
(`TauCeti.conjWirtingerDeriv u z 1`). The line bundle is trivial as a flat bundle exactly when
`θ₁` and `θ₂` are integers. This file proves the a priori estimate behind the invertibility of
`∂bar` on every nontrivial flat line: for every `C²` section `u`,

`π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²) ∫_P |u|² ≤ ∫_P |∂bar u|²`

(`TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq`), where
`‖θ‖ℤ = |θ - round θ|` is the distance to the nearest integer and the integrals are over the
fundamental parallelogram `P = {s ω₁ + t ω₂ | s, t ∈ [0, 1]}`, written in the lattice coordinates
`(s, t)`. The constant is positive exactly when the holonomy is nontrivial. The same estimate holds
for the formal adjoint, the operator `∂`
(`TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq`). For the square lattice
`ω₁ = 1`, `ω₂ = i` the constant is `π² (‖θ₁‖ℤ² + ‖θ₂‖ℤ²) / 2`.

If the holonomy has infinite image, that is if `θ₁` or `θ₂` is irrational, then every power of
the line and every pullback to a finite cover of the torus is again a nontrivial flat line
(`TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`). A section of the `j`-th
power pulled back to the cover with lattice basis `a ω₁ + b ω₂, c ω₁ + d ω₂`, `a d - b c ≠ 0`,
is twisted by `j (a θ₁ + b θ₂)` and `j (c θ₁ + d θ₂)`. The new basis is again linearly
independent (`TauCeti.im_conj_intCast_mul_add_mul_intCast_mul_add`), and the constant of the
estimate stays positive (`TauCeti.pi_sq_div_two_mul_sq_abs_sub_round_div_add_pos`). So the
estimates for `∂bar` and for `∂` hold with a positive constant on every power and finite cover:
`TauCeti.exists_pos_mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq_of_irrational`
and `TauCeti.exists_pos_mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq_of_irrational`
are their versions with an existential constant. This is the leading-order model in Taubes's
construction of Seiberg–Witten solutions near a square-zero pseudoholomorphic torus with a flat
normal bundle of irrational holonomy, where the leading inverse acts on the powers `N ^ j` of the
normal line.

## Proof

Write `v (s, t) = u (s ω₁ + t ω₂)`, `A = ∂_s v` and `B = ∂_t v`. Eliminating `∂u` from
`A = ω₁ ∂u + conj ω₁ ∂bar u` and `B = ω₂ ∂u + conj ω₂ ∂bar u` gives
`2 i D ∂bar u = ω₂ A - ω₁ B` with `D = Im (conj ω₁ ω₂) ≠ 0`, hence

`4 D² |∂bar u|² = |ω₂|² |A|² + |ω₁|² |B|² - 2 Re (conj ω₁ ω₂) Re (A conj B) + 2 D Im (A conj B)`.

The last term integrates to zero over the fundamental domain: `2 i Im (A conj B)` is
`∂_s (v conj B) - ∂_t (v conj A)` by symmetry of second derivatives, and `v conj B` and `v conj A`
are periodic because the twists have modulus one. The remaining terms are bounded below pointwise
by `D² / 2 · (|A|² / |ω₁|² + |B|² / |ω₂|²)`, and on each coordinate line the twisted Wirtinger
inequality (`TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_eq_exp_mul`) bounds
`∫ |A|²` and `∫ |B|²` below by `(2π ‖θ₁‖ℤ)² ∫ |v|²` and `(2π ‖θ₂‖ℤ)² ∫ |v|²`. Fubini's theorem
assembles the lines.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
-/

public section

open Complex ComplexConjugate MeasureTheory Set
open scoped Real Interval

namespace TauCeti

variable {u : ℂ → ℂ} {ω₁ ω₂ χ₁ χ₂ : ℂ} {θ₁ θ₂ : ℝ}

section Lines

/-- The lattice coordinate line `s ↦ s ω₁ + t ω₂` has velocity `ω₁`. -/
private theorem hasDerivAt_latticeCoord_fst (s t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) * ω₁ + t * ω₂) ω₁ s := by
  simpa using ((hasDerivAt_id s).ofReal_comp.mul_const ω₁).add_const ((t : ℂ) * ω₂)

/-- The lattice coordinate line `t ↦ s ω₁ + t ω₂` has velocity `ω₂`. -/
private theorem hasDerivAt_latticeCoord_snd (s t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (s : ℂ) * ω₁ + t * ω₂) ω₂ t := by
  simpa using ((hasDerivAt_id t).ofReal_comp.mul_const ω₂).const_add ((s : ℂ) * ω₁)

private theorem continuous_latticeCoord :
    Continuous fun p : ℝ × ℝ ↦ (p.1 : ℂ) * ω₁ + p.2 * ω₂ :=
  ((continuous_ofReal.comp continuous_fst).mul continuous_const).add
    ((continuous_ofReal.comp continuous_snd).mul continuous_const)

/-- **Twisted Wirtinger inequality along the second lattice direction.** If `u` is `C¹` and
`u (z + ω₂) = exp (2πiθ₂) u z`, the derivative of `u` along `ω₂` controls `u` in `L²` over the
fundamental domain, in lattice coordinates. -/
private theorem mul_setIntegral_norm_sq_le_snd (hu : ContDiff ℝ 1 u)
    (h₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z) :
    (2 * π * |θ₂ - round θ₂|) ^ 2 *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₂‖ ^ 2 := by
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hR : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hFi : Integrable (fun p : ℝ × ℝ ↦ ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ((hu.continuous.comp continuous_latticeCoord).norm.pow 2).continuousOn
      |>.integrableOn_compact hR
  have hGi : Integrable (fun p : ℝ × ℝ ↦ ‖fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₂‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (((hdc.comp continuous_latticeCoord).clm_apply continuous_const).norm.pow 2).continuousOn
      |>.integrableOn_compact hR
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hFi, integral_prod _ hGi,
    ← integral_const_mul]
  refine integral_mono (hFi.integral_prod_left.const_mul _) hGi.integral_prod_left fun s ↦ ?_
  dsimp only
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  -- On the line `t ↦ s ω₁ + t ω₂`, apply the one-dimensional twisted Wirtinger inequality.
  have hline : ContDiff ℝ 1 fun t : ℝ ↦ (s : ℂ) * ω₁ + t * ω₂ :=
    contDiff_const.add (ofRealCLM.contDiff.mul contDiff_const)
  have hf : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ u (s * ω₁ + t * ω₂)) 0 1 :=
    (hu.comp hline).contDiffOn.absolutelyContinuousOnInterval
  have hff' : ∀ᵐ t, t ∈ Ι (0 : ℝ) 1 → HasDerivAt (fun t : ℝ ↦ u (s * ω₁ + t * ω₂))
      (fderiv ℝ u (s * ω₁ + t * ω₂) ω₂) t :=
    Filter.Eventually.of_forall fun t _ ↦
      (hud _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_latticeCoord_snd s t)
  have hf' : MemLp (fun t : ℝ ↦ fderiv ℝ u (s * ω₁ + t * ω₂) ω₂) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((hdc.comp (hline.continuous)).clm_apply continuous_const).continuousOn
      |>.memLp_restrict_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self 2
  have hfab : u (s * ω₁ + ((1 : ℝ) : ℂ) * ω₂) =
      exp (2 * π * θ₂ * I) * u (s * ω₁ + ((0 : ℝ) : ℂ) * ω₂) := by
    simpa using h₂ (s * ω₁)
  simpa using mul_integral_norm_sq_le_integral_norm_sq_of_eq_exp_mul zero_lt_one hf hff' hf' hfab

/-- Exchanging the two lattice vectors and the two lattice coordinates leaves integrals over the
fundamental domain unchanged. -/
private theorem setIntegral_comp_latticeCoord_swap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℂ → E) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, F (p.1 * ω₂ + p.2 * ω₁) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, F (p.1 * ω₁ + p.2 * ω₂) := by
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap, add_comm]

/-- **Twisted Wirtinger inequality along the first lattice direction**, by exchanging the two
lattice vectors and the two coordinates. -/
private theorem mul_setIntegral_norm_sq_le_fst (hu : ContDiff ℝ 1 u)
    (h₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z) :
    (2 * π * |θ₁ - round θ₁|) ^ 2 *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₁‖ ^ 2 := by
  have h := mul_setIntegral_norm_sq_le_snd (ω₁ := ω₂) hu h₁
  rwa [setIntegral_comp_latticeCoord_swap (fun z ↦ ‖u z‖ ^ 2),
    setIntegral_comp_latticeCoord_swap (fun z ↦ ‖fderiv ℝ u z ω₁‖ ^ 2)] at h

end Lines

section IntegrationByParts

/-- **A periodic potential.** Let `u` be `C²` with `u (z + ω₁) = χ₁ u z` for a unit complex
number `χ₁`, and `v (s, t) = u (s ω₁ + t ω₂)`. For every direction `w`, the function
`v conj (Du w)` is periodic in `s`, so its `s`-derivative `∂_s v conj (Du w) + v conj (D²u ω₁ w)`
integrates to zero over the fundamental domain. -/
private theorem setIntegral_potential_eq_zero (hu : ContDiff ℝ 2 u) (hχ₁ : ‖χ₁‖ = 1)
    (h₁ : ∀ z, u (z + ω₁) = χ₁ * u z) (w : ℂ) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      (fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₁ * conj (fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) w) +
        u (p.1 * ω₁ + p.2 * ω₂) * conj (fderiv ℝ (fderiv ℝ u) (p.1 * ω₁ + p.2 * ω₂) ω₁ w)) =
      0 := by
  set L : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * ω₁ + p.2 * ω₂ with hL
  have hLc : Continuous L := continuous_latticeCoord
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
  have hdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hddc : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) le_rfl).continuous_fderiv one_ne_zero
  -- The derivatives of `v` and of `conj (Du w)` along the first coordinate.
  have hv (s t : ℝ) : HasDerivAt (fun s ↦ u (L (s, t))) (fderiv ℝ u (L (s, t)) ω₁) s :=
    (hud _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_latticeCoord_fst s t)
  have hd (s t : ℝ) : HasDerivAt (fun s ↦ conj (fderiv ℝ u (L (s, t)) w))
      (conj (fderiv ℝ (fderiv ℝ u) (L (s, t)) ω₁ w)) s := by
    have h := ((hdu _).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_latticeCoord_fst (ω₁ := ω₁) (ω₂ := ω₂) s t)).clm_apply (hasDerivAt_const s w)
    simpa using h.star
  -- Differentiating `u (z + ω₁) = χ₁ u z` twists the derivative by the same `χ₁`.
  have hdu₁ (z : ℂ) : fderiv ℝ u (z + ω₁) = χ₁ • fderiv ℝ u z := by
    have := congrArg (fun g ↦ fderiv ℝ g z) (funext h₁ : (fun z ↦ u (z + ω₁)) = fun z ↦ χ₁ * u z)
    simpa only [fderiv_comp_add_right, fderiv_const_mul (hud z)] using this
  have hconj : χ₁ * conj χ₁ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ₁]
    simp
  have hL₁ (t : ℝ) : L (1, t) = L (0, t) + ω₁ := by simp only [hL]; push_cast; ring
  refine setIntegral_rect_eq_zero_of_hasDerivAt_fst ?_
    (Φ := fun p ↦ u (L p) * conj (fderiv ℝ u (L p) w))
    (fun s t ↦ (hv s t).mul (hd s t)) fun t ↦ ?_
  · have h₁c := (hdc.comp hLc).clm_apply (continuous_const (y := ω₁))
    have h₂c := (hdc.comp hLc).clm_apply (continuous_const (y := w))
    have h₃c := ((hddc.comp hLc).clm_apply (continuous_const (y := ω₁))).clm_apply
      (continuous_const (y := w))
    exact (h₁c.mul (continuous_conj.comp h₂c)).add
      ((hu.continuous.comp hLc).mul (continuous_conj.comp h₃c))
  · simp only [hL₁, h₁, hdu₁, _root_.smul_apply, smul_eq_mul, map_mul]
    linear_combination (u (L (0, t)) * conj (fderiv ℝ u (L (0, t)) w)) * hconj

/-- **The imaginary part of the cross term integrates to zero.** For a `C²` function `u` twisted by
unit complex numbers along `ω₁` and `ω₂`, with `A = ∂_s v`, `B = ∂_t v` and
`v (s, t) = u (s ω₁ + t ω₂)`, the integral of `Im (A conj B)` over the fundamental domain
vanishes: `2 i Im (A conj B) = ∂_s (v conj B) - ∂_t (v conj A)`, and both potentials are periodic.
-/
private theorem setIntegral_im_mul_conj_eq_zero (hu : ContDiff ℝ 2 u) (hχ₁ : ‖χ₁‖ = 1)
    (hχ₂ : ‖χ₂‖ = 1) (h₁ : ∀ z, u (z + ω₁) = χ₁ * u z) (h₂ : ∀ z, u (z + ω₂) = χ₂ * u z) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₁ *
      conj (fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₂)).im = 0 := by
  have hint₁ := setIntegral_potential_eq_zero (ω₂ := ω₂) hu hχ₁ h₁ ω₂
  have hint₂ := setIntegral_potential_eq_zero (ω₂ := ω₁) hu hχ₂ h₂ ω₁
  rw [setIntegral_comp_latticeCoord_swap (fun z ↦ fderiv ℝ u z ω₂ * conj (fderiv ℝ u z ω₁) +
    u z * conj (fderiv ℝ (fderiv ℝ u) z ω₂ ω₁))] at hint₂
  have hc : Continuous fun p : ℝ × ℝ ↦ (p.1 : ℂ) * ω₁ + p.2 * ω₂ := continuous_latticeCoord
  have hdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have huc : Continuous u := hu.continuous
  set F₁ : ℂ → ℂ := fun z ↦ fderiv ℝ u z ω₁ * conj (fderiv ℝ u z ω₂) +
    u z * conj (fderiv ℝ (fderiv ℝ u) z ω₁ ω₂)
  set F₂ : ℂ → ℂ := fun z ↦ fderiv ℝ u z ω₂ * conj (fderiv ℝ u z ω₁) +
    u z * conj (fderiv ℝ (fderiv ℝ u) z ω₂ ω₁)
  have hR : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hF₁ : Continuous F₁ := by fun_prop
  have hF₂ : Continuous F₂ := by fun_prop
  have h := integral_sub ((hF₁.comp hc).continuousOn.integrableOn_compact (μ := volume) hR)
    ((hF₂.comp hc).continuousOn.integrableOn_compact hR)
  simp only [Function.comp_apply] at h
  rw [hint₁, hint₂, sub_zero] at h
  -- The second-derivative terms cancel by symmetry, leaving `A conj B - B conj A`.
  have hdiff (z : ℂ) : F₁ z - F₂ z =
      ((2 * (fderiv ℝ u z ω₁ * conj (fderiv ℝ u z ω₂)).im : ℝ) : ℂ) * I := by
    simp only [F₁, F₂, hu.contDiffAt.isSymmSndFDerivAt (by simp) ω₁ ω₂, ← sub_conj, map_mul,
      conj_conj]
    ring
  simp only [hdiff, integral_mul_const, integral_complex_ofReal] at h
  simpa [I_ne_zero, integral_const_mul] using h.symm

end IntegrationByParts

section Estimate

/-- `2 i Im (conj ω₁ ω₂) = ω₂ conj ω₁ - ω₁ conj ω₂`. -/
private theorem two_mul_I_mul_im_conj_mul :
    (2 * I * (conj ω₁ * ω₂).im : ℂ) = ω₂ * conj ω₁ - ω₁ * conj ω₂ := by
  have h := sub_conj (conj ω₁ * ω₂)
  simp only [map_mul, conj_conj, ofReal_mul, ofReal_ofNat] at h
  linear_combination -h

/-- The pointwise expansion of `|ω₂ A - ω₁ B|²`, written for `W` with `2 i D W = ω₂ A - ω₁ B`,
`D = Im (conj ω₁ ω₂)`. -/
private theorem four_mul_sq_mul_norm_sq_eq_of_mul_eq {W A B : ℂ}
    (hW : W * (2 * I * (conj ω₁ * ω₂).im) = ω₂ * A - ω₁ * B) :
    4 * (conj ω₁ * ω₂).im ^ 2 * ‖W‖ ^ 2 = ‖ω₂‖ ^ 2 * ‖A‖ ^ 2 + ‖ω₁‖ ^ 2 * ‖B‖ ^ 2 -
      2 * (conj ω₁ * ω₂).re * (A * conj B).re + 2 * (conj ω₁ * ω₂).im * (A * conj B).im := by
  have h := congrArg (fun z ↦ ‖z‖ ^ 2) hW
  simp only [Complex.sq_norm, normSq_apply, mul_re, mul_im, sub_re, sub_im, conj_re, conj_im,
    I_re, I_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat] at h ⊢
  linear_combination h

/-- The pointwise expansion of `|conj ω₂ A - conj ω₁ B|²`, written for `W` with
`-2 i D W = conj ω₂ A - conj ω₁ B`, `D = Im (conj ω₁ ω₂)`. -/
private theorem four_mul_sq_mul_norm_sq_eq_of_mul_neg_eq {W A B : ℂ}
    (hW : W * -(2 * I * (conj ω₁ * ω₂).im) = conj ω₂ * A - conj ω₁ * B) :
    4 * (conj ω₁ * ω₂).im ^ 2 * ‖W‖ ^ 2 = ‖ω₂‖ ^ 2 * ‖A‖ ^ 2 + ‖ω₁‖ ^ 2 * ‖B‖ ^ 2 -
      2 * (conj ω₁ * ω₂).re * (A * conj B).re + -1 * (2 * (conj ω₁ * ω₂).im * (A * conj B).im) := by
  -- Conjugating reduces this to the expansion for `conj W`, `conj A`, `conj B`.
  have hW' : conj W * (2 * I * (conj ω₁ * ω₂).im) = ω₂ * conj A - ω₁ * conj B := by
    have h := congrArg conj hW
    simp only [map_mul, map_sub, map_neg, map_ofNat, conj_conj, conj_I, conj_ofReal] at h
    linear_combination h
  have h := four_mul_sq_mul_norm_sq_eq_of_mul_eq hW'
  rw [norm_conj, norm_conj, norm_conj, ← map_mul, conj_re, conj_im] at h
  linear_combination h

/-- The pointwise lower bound for the real part of the expansion: with `D = Im (conj ω₁ ω₂) ≠ 0`,
`|ω₂|² |A|² + |ω₁|² |B|² - 2 Re (conj ω₁ ω₂) Re (A conj B)` is at least
`D² / 2 · (|A|² / |ω₁|² + |B|² / |ω₂|²)`. -/
private theorem le_norm_sq_mul_add_norm_sq_mul_sub (hω : (conj ω₁ * ω₂).im ≠ 0) (A B : ℂ) :
    (conj ω₁ * ω₂).im ^ 2 / 2 * (‖A‖ ^ 2 / ‖ω₁‖ ^ 2 + ‖B‖ ^ 2 / ‖ω₂‖ ^ 2) ≤
      ‖ω₂‖ ^ 2 * ‖A‖ ^ 2 + ‖ω₁‖ ^ 2 * ‖B‖ ^ 2 - 2 * (conj ω₁ * ω₂).re * (A * conj B).re := by
  set D := (conj ω₁ * ω₂).im
  set r := (conj ω₁ * ω₂).re
  have hω₁ : ω₁ ≠ 0 := by rintro rfl; simp [D] at hω
  have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp [D] at hω
  set p := ‖ω₁‖
  set q := ‖ω₂‖
  have hp : 0 < p := norm_pos_iff.2 hω₁
  have hq : 0 < q := norm_pos_iff.2 hω₂
  set a := ‖A‖
  set b := ‖B‖
  -- `r² + D² = p² q²`, `|r| ≤ p q` and `r Re (A conj B) ≤ |r| a b`.
  have hrD : r ^ 2 + D ^ 2 = p ^ 2 * q ^ 2 := by
    have h := Complex.sq_norm (conj ω₁ * ω₂)
    rw [normSq_apply, norm_mul, norm_conj, mul_pow] at h
    rw [h]
    ring
  have hrP : r * (A * conj B).re ≤ |r| * (a * b) := by
    calc r * (A * conj B).re ≤ |r * (A * conj B).re| := le_abs_self _
      _ = |r| * |(A * conj B).re| := abs_mul _ _
      _ ≤ |r| * (a * b) := by
        gcongr
        simpa [a, b] using abs_re_le_norm (A * conj B)
  have hlhs : D ^ 2 / 2 * (a ^ 2 / p ^ 2 + b ^ 2 / q ^ 2) =
      D ^ 2 * (q ^ 2 * a ^ 2 + p ^ 2 * b ^ 2) / (2 * (p ^ 2 * q ^ 2)) := by
    field_simp
  rw [hlhs, div_le_iff₀ (by positivity)]
  -- After clearing denominators, the difference is
  -- `(p q - |r|)² (q² a² + p² b²) + 2 p q |r| (q a - p b)² + 4 p² q² (|r| a b - r Re (A conj B))`.
  have h₁ := mul_nonneg (sq_nonneg (p * q - |r|))
    (add_nonneg (sq_nonneg (q * a)) (sq_nonneg (p * b)))
  have h₂ := mul_nonneg (mul_nonneg (mul_nonneg hp.le hq.le) (abs_nonneg r))
    (sq_nonneg (q * a - p * b))
  have h₃ := mul_le_mul_of_nonneg_left hrP (by positivity : (0 : ℝ) ≤ 4 * p ^ 2 * q ^ 2)
  have h₄ : D ^ 2 = p ^ 2 * q ^ 2 - |r| ^ 2 := by rw [sq_abs]; linarith
  rw [h₄]
  nlinarith [h₁, h₂, h₃]

/-- The integral of the real part of the expansion over the fundamental domain is bounded below by
the twisted Wirtinger inequalities on the coordinate lines. -/
private theorem mul_setIntegral_le_setIntegral_sub (hu : ContDiff ℝ 1 u)
    (hω : (conj ω₁ * ω₂).im ≠ 0)
    (h₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (h₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z) :
    (conj ω₁ * ω₂).im ^ 2 / 2 * (4 * π ^ 2) *
        (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        (‖ω₂‖ ^ 2 * ‖fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₁‖ ^ 2 +
          ‖ω₁‖ ^ 2 * ‖fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₂‖ ^ 2 -
          2 * (conj ω₁ * ω₂).re * (fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₁ *
            conj (fderiv ℝ u (p.1 * ω₁ + p.2 * ω₂) ω₂)).re) := by
  set L : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * ω₁ + p.2 * ω₂
  set D := (conj ω₁ * ω₂).im
  have hLc : Continuous L := continuous_latticeCoord
  have hR : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hW₁ := mul_setIntegral_norm_sq_le_fst (ω₂ := ω₂) hu h₁
  have hW₂ := mul_setIntegral_norm_sq_le_snd (ω₁ := ω₁) hu h₂
  -- Integrate the pointwise lower bound.
  have hGc : Continuous fun p ↦ ‖ω₂‖ ^ 2 * ‖fderiv ℝ u (L p) ω₁‖ ^ 2 +
      ‖ω₁‖ ^ 2 * ‖fderiv ℝ u (L p) ω₂‖ ^ 2 -
      2 * (conj ω₁ * ω₂).re * (fderiv ℝ u (L p) ω₁ * conj (fderiv ℝ u (L p) ω₂)).re := by
    fun_prop
  have hHc : Continuous fun p ↦ D ^ 2 / 2 *
      (‖fderiv ℝ u (L p) ω₁‖ ^ 2 / ‖ω₁‖ ^ 2 + ‖fderiv ℝ u (L p) ω₂‖ ^ 2 / ‖ω₂‖ ^ 2) := by
    fun_prop
  have hmono : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, D ^ 2 / 2 *
      (‖fderiv ℝ u (L p) ω₁‖ ^ 2 / ‖ω₁‖ ^ 2 + ‖fderiv ℝ u (L p) ω₂‖ ^ 2 / ‖ω₂‖ ^ 2) ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (‖ω₂‖ ^ 2 * ‖fderiv ℝ u (L p) ω₁‖ ^ 2 +
        ‖ω₁‖ ^ 2 * ‖fderiv ℝ u (L p) ω₂‖ ^ 2 -
        2 * (conj ω₁ * ω₂).re * (fderiv ℝ u (L p) ω₁ * conj (fderiv ℝ u (L p) ω₂)).re) :=
    setIntegral_mono_on (hHc.continuousOn.integrableOn_compact hR)
      (hGc.continuousOn.integrableOn_compact hR) hR.isClosed.measurableSet
      fun p _ ↦ le_norm_sq_mul_add_norm_sq_mul_sub hω _ _
  calc D ^ 2 / 2 * (4 * π ^ 2) *
        (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (L p)‖ ^ 2 =
      D ^ 2 / 2 * ((2 * π * |θ₁ - round θ₁|) ^ 2 *
          (∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (L p)‖ ^ 2) / ‖ω₁‖ ^ 2 +
        (2 * π * |θ₂ - round θ₂|) ^ 2 *
          (∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (L p)‖ ^ 2) / ‖ω₂‖ ^ 2) := by ring
    _ ≤ D ^ 2 / 2 *
        ((∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ u (L p) ω₁‖ ^ 2) / ‖ω₁‖ ^ 2 +
          (∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ u (L p) ω₂‖ ^ 2) / ‖ω₂‖ ^ 2) := by
      gcongr _ * (?_ / _ + ?_ / _)
    _ = _ := by
      have hA' : IntegrableOn (fun p ↦ ‖fderiv ℝ u (L p) ω₁‖ ^ 2 / ‖ω₁‖ ^ 2)
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
        (Continuous.continuousOn (by fun_prop)).integrableOn_compact hR
      have hB' : IntegrableOn (fun p ↦ ‖fderiv ℝ u (L p) ω₂‖ ^ 2 / ‖ω₂‖ ^ 2)
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
        (Continuous.continuousOn (by fun_prop)).integrableOn_compact hR
      rw [integral_const_mul, integral_add hA' hB', integral_div, integral_div]
    _ ≤ _ := hmono

/-- The common lower bound for `∂bar` and `∂`: if `4 D² ∫ |W|²` equals the integral of the real part
of the expansion, it dominates `∫ |u|²`. -/
private theorem mul_setIntegral_le_of_four_mul (hD : (conj ω₁ * ω₂).im ≠ 0) {W : ℝ × ℝ → ℂ}
    {G : ℝ × ℝ → ℝ} {V : ℝ}
    (hlow : (conj ω₁ * ω₂).im ^ 2 / 2 * (4 * π ^ 2) *
        (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) * V ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, G p)
    (hW : 4 * (conj ω₁ * ω₂).im ^ 2 * ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖W p‖ ^ 2 =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, G p) :
    π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) * V ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖W p‖ ^ 2 := by
  have h4 : 0 < 4 * (conj ω₁ * ω₂).im ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ h4
  rw [hW]
  refine le_of_eq_of_le ?_ hlow
  ring

/-- **The estimate from a pointwise identity.** If `4 D² |W|²` equals the real part of the expansion
plus `ε` times its imaginary part `2 D Im (A conj B)`, then `∫ |W|²` dominates `∫ |u|²`, since the
imaginary part integrates to zero. -/
private theorem mul_setIntegral_norm_sq_le_of_four_mul_sq_mul_norm_sq_eq (hu : ContDiff ℝ 2 u)
    (hω : (conj ω₁ * ω₂).im ≠ 0)
    (h₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (h₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z) {W : ℂ → ℂ} (ε : ℝ)
    (hpt : ∀ z, 4 * (conj ω₁ * ω₂).im ^ 2 * ‖W z‖ ^ 2 =
      ‖ω₂‖ ^ 2 * ‖fderiv ℝ u z ω₁‖ ^ 2 + ‖ω₁‖ ^ 2 * ‖fderiv ℝ u z ω₂‖ ^ 2 -
        2 * (conj ω₁ * ω₂).re * (fderiv ℝ u z ω₁ * conj (fderiv ℝ u z ω₂)).re +
        ε * (2 * (conj ω₁ * ω₂).im * (fderiv ℝ u z ω₁ * conj (fderiv ℝ u z ω₂)).im)) :
    π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖W (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 := by
  set L : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * ω₁ + p.2 * ω₂
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hR : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hLc : Continuous L := continuous_latticeCoord
  have hGc : Continuous fun p ↦ ‖ω₂‖ ^ 2 * ‖fderiv ℝ u (L p) ω₁‖ ^ 2 +
      ‖ω₁‖ ^ 2 * ‖fderiv ℝ u (L p) ω₂‖ ^ 2 -
      2 * (conj ω₁ * ω₂).re * (fderiv ℝ u (L p) ω₁ * conj (fderiv ℝ u (L p) ω₂)).re := by
    fun_prop
  have hIc : Continuous fun p ↦ ε * (2 * (conj ω₁ * ω₂).im *
      (fderiv ℝ u (L p) ω₁ * conj (fderiv ℝ u (L p) ω₂)).im) := by
    fun_prop
  have him := setIntegral_im_mul_conj_eq_zero hu (by simpa using norm_exp_ofReal_mul_I (2 * π * θ₁))
    (by simpa using norm_exp_ofReal_mul_I (2 * π * θ₂)) h₁ h₂
  refine mul_setIntegral_le_of_four_mul (W := fun p ↦ W (L p))
    (V := ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (L p)‖ ^ 2)
    (G := fun p ↦ ‖ω₂‖ ^ 2 * ‖fderiv ℝ u (L p) ω₁‖ ^ 2 + ‖ω₁‖ ^ 2 * ‖fderiv ℝ u (L p) ω₂‖ ^ 2 -
      2 * (conj ω₁ * ω₂).re * (fderiv ℝ u (L p) ω₁ * conj (fderiv ℝ u (L p) ω₂)).re)
    hω (mul_setIntegral_le_setIntegral_sub hu1 hω h₁ h₂) ?_
  rw [← integral_const_mul]
  simp only [hpt]
  rw [integral_add (hGc.continuousOn.integrableOn_compact hR)
    (hIc.continuousOn.integrableOn_compact hR), integral_const_mul, integral_const_mul, him,
    mul_zero, mul_zero, add_zero]

/-- **The Cauchy–Riemann operator on a flat line over a torus is coercive.** Let `ω₁, ω₂` be
linearly independent over `ℝ`, and let `u` be a `C²` section of the flat line with holonomy
`exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`. Then, over the fundamental parallelogram in lattice
coordinates,
`π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²) ∫ |u|² ≤ ∫ |∂bar u|²`, with `‖θ‖ℤ = |θ - round θ|`.
The constant is positive exactly when the holonomy is nontrivial. -/
theorem mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq (hu : ContDiff ℝ 2 u)
    (hω : (conj ω₁ * ω₂).im ≠ 0)
    (h₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (h₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z) :
    π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1‖ ^ 2 := by
  refine mul_setIntegral_norm_sq_le_of_four_mul_sq_mul_norm_sq_eq hu hω h₁ h₂
    (W := fun z ↦ conjWirtingerDeriv u z 1) 1 fun z ↦ ?_
  -- Pointwise, `2 i D ∂bar u = ω₂ A - ω₁ B`.
  rw [one_mul]
  refine four_mul_sq_mul_norm_sq_eq_of_mul_eq ?_
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, two_mul_I_mul_im_conj_mul]
  simp only [smul_eq_mul]
  ring

/-- **The adjoint estimate.** Under the hypotheses of
`TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq`, the operator `∂`,
the formal adjoint of `∂bar` up to sign, satisfies the same estimate. -/
theorem mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq (hu : ContDiff ℝ 2 u)
    (hω : (conj ω₁ * ω₂).im ≠ 0)
    (h₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (h₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z) :
    π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2) *
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ‖u (p.1 * ω₁ + p.2 * ω₂)‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖wirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1‖ ^ 2 := by
  refine mul_setIntegral_norm_sq_le_of_four_mul_sq_mul_norm_sq_eq hu hω h₁ h₂
    (W := fun z ↦ wirtingerDeriv u z 1) (-1) fun z ↦ ?_
  -- Pointwise, `-2 i D ∂u = conj ω₂ A - conj ω₁ B`.
  refine four_mul_sq_mul_norm_sq_eq_of_mul_neg_eq ?_
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, two_mul_I_mul_im_conj_mul]
  simp only [smul_eq_mul]
  ring

end Estimate

section Irrational

/-- **The orientation of a sublattice basis.** For integers `a, b, c, d`,
`Im (conj (a ω₁ + b ω₂) (c ω₁ + d ω₂)) = (a d - b c) Im (conj ω₁ ω₂)`. -/
theorem im_conj_intCast_mul_add_mul_intCast_mul_add (a b c d : ℤ) :
    (conj (a * ω₁ + b * ω₂) * (c * ω₁ + d * ω₂)).im =
      ((a * d - b * c : ℤ) : ℝ) * (conj ω₁ * ω₂).im := by
  simp only [map_add, map_mul, map_intCast, mul_im, add_im, add_re, mul_re, conj_re, conj_im,
    intCast_re, intCast_im]
  push_cast
  ring

/-- **A sublattice basis is linearly independent.** If `ω₁, ω₂` are linearly independent over `ℝ`
and `a d - b c ≠ 0`, then so are `a ω₁ + b ω₂` and `c ω₁ + d ω₂`. -/
theorem im_conj_intCast_mul_add_mul_intCast_mul_add_ne_zero (hω : (conj ω₁ * ω₂).im ≠ 0)
    {a b c d : ℤ} (hdet : a * d - b * c ≠ 0) :
    (conj (a * ω₁ + b * ω₂) * (c * ω₁ + d * ω₂)).im ≠ 0 := by
  rw [im_conj_intCast_mul_add_mul_intCast_mul_add]
  exact mul_ne_zero (by exact_mod_cast hdet) hω

/-- **The constant of the coercivity estimates is positive** when one of the two twists is not an
integer and both lattice vectors are nonzero. -/
theorem pi_sq_div_two_mul_sq_abs_sub_round_div_add_pos {x y : ℝ}
    (hxy : x ∉ range ((↑) : ℤ → ℝ) ∨ y ∉ range ((↑) : ℤ → ℝ)) (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    0 < π ^ 2 / 2 * (|x - round x| ^ 2 / ‖ω₁‖ ^ 2 + |y - round y| ^ 2 / ‖ω₂‖ ^ 2) := by
  -- The distance to the nearest integer is positive off the integers.
  have hpos {x : ℝ} (hx : x ∉ range ((↑) : ℤ → ℝ)) : 0 < |x - round x| :=
    abs_pos.2 (sub_ne_zero.2 fun h ↦ hx ⟨round x, h.symm⟩)
  refine mul_pos (by positivity) ?_
  rcases hxy with h | h
  · have := hpos h
    exact add_pos_of_pos_of_nonneg (by positivity) (by positivity)
  · have := hpos h
    exact add_pos_of_nonneg_of_pos (by positivity) (by positivity)

/-- For a power and a finite-cover pullback of a flat line with infinite holonomy, the new lattice
basis is linearly independent and the constant of the coercivity estimates is positive. -/
private theorem im_conj_mul_ne_zero_and_pos_of_irrational (hθ : Irrational θ₁ ∨ Irrational θ₂)
    (hω : (conj ω₁ * ω₂).im ≠ 0) {j a b c d : ℤ} (hj : j ≠ 0) (hdet : a * d - b * c ≠ 0) :
    (conj (a * ω₁ + b * ω₂) * (c * ω₁ + d * ω₂)).im ≠ 0 ∧
    0 < π ^ 2 / 2 *
      (|(j * (a * θ₁ + b * θ₂) : ℝ) - round (j * (a * θ₁ + b * θ₂) : ℝ)| ^ 2 /
          ‖(a * ω₁ + b * ω₂ : ℂ)‖ ^ 2 +
        |(j * (c * θ₁ + d * θ₂) : ℝ) - round (j * (c * θ₁ + d * θ₂) : ℝ)| ^ 2 /
          ‖(c * ω₁ + d * ω₂ : ℂ)‖ ^ 2) := by
  have hne := im_conj_intCast_mul_add_mul_intCast_mul_add_ne_zero hω hdet
  refine ⟨hne, pi_sq_div_two_mul_sq_abs_sub_round_div_add_pos
    (notMem_range_intCast_or_notMem_range_intCast_of_irrational hθ hj hdet) ?_ ?_⟩ <;>
  · rintro h0
    simp [h0] at hne

/-- **Coercivity of `∂bar` on the powers and finite covers of a flat line with infinite
holonomy.** Let `ω₁, ω₂` be linearly independent and let `θ₁` or `θ₂` be irrational. For every
nonzero integer `j` and every sublattice basis `a ω₁ + b ω₂, c ω₁ + d ω₂` with `a d - b c ≠ 0`,
there is `C > 0` such that every `C²` section `u` of the `j`-th power of the line, pulled back to
the torus of the sublattice, satisfies `C ∫ |u|² ≤ ∫ |∂bar u|²` over its fundamental domain. -/
theorem exists_pos_mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq_of_irrational
    (hu : ContDiff ℝ 2 u) (hθ : Irrational θ₁ ∨ Irrational θ₂) (hω : (conj ω₁ * ω₂).im ≠ 0)
    {j a b c d : ℤ} (hj : j ≠ 0) (hdet : a * d - b * c ≠ 0)
    (h₁ : ∀ z, u (z + (a * ω₁ + b * ω₂)) =
      exp (2 * π * ((j * (a * θ₁ + b * θ₂) : ℝ) : ℂ) * I) * u z)
    (h₂ : ∀ z, u (z + (c * ω₁ + d * ω₂)) =
      exp (2 * π * ((j * (c * θ₁ + d * θ₂) : ℝ) : ℂ) * I) * u z) :
    ∃ C > 0, C * ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖u (p.1 * (a * ω₁ + b * ω₂) + p.2 * (c * ω₁ + d * ω₂))‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖conjWirtingerDeriv u (p.1 * (a * ω₁ + b * ω₂) + p.2 * (c * ω₁ + d * ω₂)) 1‖ ^ 2 :=
  have h := im_conj_mul_ne_zero_and_pos_of_irrational hθ hω hj hdet
  ⟨_, h.2, mul_setIntegral_norm_sq_le_setIntegral_norm_conjWirtingerDeriv_sq hu h.1 h₁ h₂⟩

/-- **Coercivity of `∂` on the powers and finite covers of a flat line with infinite holonomy.**
Under the same hypotheses as the estimate for `∂bar`, the formal adjoint `∂` satisfies
`C ∫ |u|² ≤ ∫ |∂u|²` for some `C > 0`. -/
theorem exists_pos_mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq_of_irrational
    (hu : ContDiff ℝ 2 u) (hθ : Irrational θ₁ ∨ Irrational θ₂) (hω : (conj ω₁ * ω₂).im ≠ 0)
    {j a b c d : ℤ} (hj : j ≠ 0) (hdet : a * d - b * c ≠ 0)
    (h₁ : ∀ z, u (z + (a * ω₁ + b * ω₂)) =
      exp (2 * π * ((j * (a * θ₁ + b * θ₂) : ℝ) : ℂ) * I) * u z)
    (h₂ : ∀ z, u (z + (c * ω₁ + d * ω₂)) =
      exp (2 * π * ((j * (c * θ₁ + d * θ₂) : ℝ) : ℂ) * I) * u z) :
    ∃ C > 0, C * ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖u (p.1 * (a * ω₁ + b * ω₂) + p.2 * (c * ω₁ + d * ω₂))‖ ^ 2 ≤
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ‖wirtingerDeriv u (p.1 * (a * ω₁ + b * ω₂) + p.2 * (c * ω₁ + d * ω₂)) 1‖ ^ 2 :=
  have h := im_conj_mul_ne_zero_and_pos_of_irrational hθ hω hj hdet
  ⟨_, h.2, mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq hu h.1 h₁ h₂⟩

end Irrational

end TauCeti
