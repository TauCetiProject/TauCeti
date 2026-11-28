/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonvanishing theta functions are quadratic exponentials of trivial Riemann form

Let `D = (B, χ)` be an Appell–Humbert datum for a full lattice `L` in a finite-dimensional
complex normed space `V`, and let `f ∈ D.thetaSpace` be a theta function.

## Main results

* `TauCeti.AppellHumbertData.isCompact_range_norm_twistedTranslate`: the values
  `‖D.twistedTranslate u f 0‖` form a compact subset of `ℝ` as `u` varies over `V`.
* `TauCeti.AppellHumbertData.apply_smul_of_riemannForm_nonpos`: along any direction `u` with
  `D.riemannForm (I • u) u ≤ 0`, `f (t • u) = exp (t * t * D.form u u / 2) * f 0` for all `t : ℂ`.
* `TauCeti.AppellHumbertData.eq_exp_of_ne_zero`: if `f` never vanishes on `V`, then
  `D.riemannForm = 0`, `D.semichar l = 1` for all `l : L`, and
  `f z = exp (D.form z z / 2) * f 0` for all `z : V`.

## Provenance

Adapted from `New.IsAppellHumbert.isCompact_range_norm_thetaShift`,
`New.IsAppellHumbert.apply_smul_of_nonpos`, and `New.IsAppellHumbert.eq_exp_of_ne_zero` in
`src/Lib/Shimura/ComplexTheta/AppellHumbertData.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), using `TauCeti.AppellHumbertData` (whose Riemann
form `E = Im H` is the negative of `grh-lean`'s `E_B`).
-/

public section

open Complex

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L]
  {D : AppellHumbertData L} {f : V → ℂ}

/-- For a theta function `f ∈ D.thetaSpace` on a full lattice `L`, the set of values
`‖D.twistedTranslate u f 0‖` (`u : V`) is compact. -/
theorem isCompact_range_norm_twistedTranslate (hf : f ∈ D.thetaSpace) :
    IsCompact (Set.range fun u : V ↦ ‖D.twistedTranslate u f 0‖) := by
  have : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let b0 := Module.finBasis ℤ L
  let b := b0.ofZLatticeBasis ℝ L
  let K : Set V := Set.image (fun c : _ → ℝ ↦ ∑ i, c i • b i) (Set.pi Set.univ fun _ ↦ Set.Icc 0 1)
  have hK : IsCompact K := (isCompact_univ_pi fun _ ↦ isCompact_Icc).image (by fun_prop)
  have hcont : Continuous fun u : V ↦ ‖D.twistedTranslate u f 0‖ := by
    have hfc : Continuous f := (differentiable_of_mem_thetaSpace hf).continuous
    simp only [twistedTranslate_apply, map_zero, zero_add]
    have hform : Continuous fun u : V ↦ D.form u u :=
      isBoundedBilinearMap_apply.continuous.comp (D.form.continuous.prodMk continuous_id)
    fun_prop
  have hrange : (Set.range fun u : V ↦ ‖D.twistedTranslate u f 0‖) =
      (fun u : V ↦ ‖D.twistedTranslate u f 0‖) '' K := by
    refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
    rintro _ ⟨u, rfl⟩
    let l : L := ∑ i, ⌊b.repr u i⌋ • b0 i
    refine ⟨u - l, ⟨fun i ↦ b.repr u i - ⌊b.repr u i⌋, fun i _ ↦
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩, ?_⟩
    · have hl : (l : V) = ∑ i, (⌊b.repr u i⌋ : ℝ) • b i := by
        change L.subtype (∑ i, ⌊b.repr u i⌋ • b0 i) = _
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, Int.cast_smul_eq_zsmul]; simp [b]
      rw [hl]
      simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr u]
    · dsimp only
      have hu : u = (u - l) + l := (sub_add_cancel u (l : V)).symm
      conv_rhs => rw [hu]
      rw [D.twistedTranslate_add_eq_smul_of_mem_thetaSpace hf (u - l) l, Pi.smul_apply,
        norm_smul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_exp]
      simp
  rw [hrange]
  exact hK.image hcont

/-- If `f ∈ D.thetaSpace` and `D.riemannForm (I • u) u ≤ 0`, then
`f (t • u) = exp (t * t * D.form u u / 2) * f 0` for every `t : ℂ`. -/
theorem apply_smul_of_riemannForm_nonpos (hf : f ∈ D.thetaSpace) (u : V)
    (h_nonpos : D.riemannForm (I • u) u ≤ 0) (t : ℂ) :
    f (t • u) = exp (t * t * D.form u u / 2) * f 0 := by
  let g (s : ℂ) : ℂ := exp (-(s * s * D.form u u / 2)) * f (s • u)
  have hf_diff : Differentiable ℂ f := differentiable_of_mem_thetaSpace hf
  have hre_le (s : ℂ) : (D.form (s • u) (s • u)).re ≤ (s * s * D.form u u).re := by
    have him : (D.form u u).re ≤ (D.form (I • u) u).im := by
      rw [D.riemannForm_apply] at h_nonpos
      have h2 : (D.form u (I • u) - D.form (I • u) u).im ≤ 0 :=
        ((div_nonpos_iff.mp h_nonpos).resolve_left fun h ↦ by linarith [Real.pi_pos, h.right]).left
      have h3 : D.form u (I • u) = I * D.form u u := by rw [map_smul, smul_eq_mul]
      rw [h3, Complex.sub_im, Complex.I_mul_im] at h2; linarith
    have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
    have hform_s : D.form (s • u) (s • u) =
        ((s.re : ℂ) * D.form u u + (s.im : ℂ) * D.form (I • u) u) * s := by
      rw [map_smul, smul_eq_mul, mul_comm]; congr 1; conv_lhs => rw [hs]
      simp only [add_smul, mul_smul, Complex.coe_smul, map_add, map_smul, _root_.add_apply,
        _root_.smul_apply, Complex.real_smul]
    have hexp : (s * s * D.form u u).re - (D.form (s • u) (s • u)).re =
          s.im ^ 2 * ((D.form (I • u) u).im - (D.form u u).re) := by
      rw [hform_s]
      have hsym := D.re_form_comm u (I • u)
      simp only [map_smul, smul_eq_mul, Complex.I_mul_re] at hsym
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, ← hsym]; ring
    linarith [mul_nonneg (sq_nonneg s.im) (sub_nonneg.mpr him)]
  obtain ⟨C, hC⟩ := (isCompact_range_norm_twistedTranslate hf).bddAbove
  have hg_le (s : ℂ) : ‖g s‖ ≤ C :=
    calc ‖g s‖ = Real.exp (-((s * s * D.form u u).re / 2)) * ‖f (s • u)‖ := by
          simp [g, Complex.norm_exp]
      _ ≤ Real.exp (-((D.form (s • u) (s • u)).re / 2)) * ‖f (s • u)‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hre_le s])) (norm_nonneg _)
      _ = ‖D.twistedTranslate (s • u) f 0‖ := by simp [twistedTranslate_apply, Complex.norm_exp]
      _ ≤ C := hC ⟨s • u, rfl⟩
  have hg_diff : Differentiable ℂ g :=
    (Differentiable.cexp (by fun_prop)).mul (hf_diff.comp (differentiable_id.smul_const u))
  have hg_const : g t = g 0 := hg_diff.apply_eq_apply_of_bounded
    (isBounded_iff_forall_norm_le.mpr ⟨C, Set.forall_mem_range.mpr hg_le⟩) t 0
  simpa [g, exp_neg, field] using hg_const

/-- If a theta function `f ∈ D.thetaSpace` has no zero on `V`, then `D.riemannForm = 0`,
`D.semichar l = 1` for all `l : L`, and `f z = exp (D.form z z / 2) * f 0` for all `z : V`. -/
theorem eq_exp_of_ne_zero (hf : f ∈ D.thetaSpace) (hf_ne : ∀ z : V, f z ≠ 0) :
    D.riemannForm = 0 ∧ (∀ l : L, D.semichar l = 1) ∧
      ∀ z : V, f z = exp (D.form z z / 2) * f 0 := by
  have on_line (z : V) (t : ℂ) : f (t • z) = exp (t * t * D.form z z / 2) * f 0 := by
    rcases le_total (D.riemannForm (I • z) z) 0 with hle | hge
    · exact apply_smul_of_riemannForm_nonpos hf z hle t
    · have hinv : f⁻¹ ∈ (-D).thetaSpace := by
        refine (mem_thetaSpace_iff _).mpr ⟨(differentiable_of_mem_thetaSpace hf).inv hf_ne,
          fun l w ↦ ?_⟩
        simp only [Pi.inv_apply, apply_add_of_mem_thetaSpace hf l w, factor_def, form_neg,
          semichar_neg, _root_.neg_apply, Circle.coe_inv_eq_conj, ← Complex.inv_eq_conj
          (Circle.norm_coe _), neg_div, ← neg_add, exp_neg, mul_inv]
      have h := apply_smul_of_riemannForm_nonpos hinv z (by simpa using hge) t
      simp only [Pi.inv_apply, form_neg, _root_.neg_apply, mul_neg, neg_div, exp_neg] at h
      simpa [inv_inv, mul_comm] using congrArg Inv.inv h
  have hre_eq (z : V) : (D.form z z).re = (D.form (I • z) z).im := by
    have heq : exp (D.form (I • z) (I • z) / 2) * f 0 = exp (I * I * D.form z z / 2) * f 0 := by
      have h1 := on_line (I • z) 1
      have h2 := on_line z I
      rw [one_smul, one_mul, one_mul] at h1
      exact h1.symm.trans h2
    have hnorm := congrArg (‖·‖) (mul_right_cancel₀ (hf_ne 0) heq)
    simp only [Complex.norm_exp] at hnorm
    have h3 := Real.exp_injective hnorm
    simp only [map_smul, smul_eq_mul, Complex.I_mul_I, neg_one_mul, Complex.neg_re,
      Complex.div_ofNat_re, Complex.I_mul_re] at h3
    linarith
  refine ⟨LinearMap.ext₂ fun u v ↦ ?_, fun l ↦ ?_, fun z ↦ by simpa using on_line z 1⟩
  · have hpolar := hre_eq (u + I • v)
    simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, map_add, map_neg,
      _root_.add_apply, _root_.neg_apply, Complex.add_re, Complex.add_im, Complex.neg_im,
      hre_eq u] at hpolar
    have hsym := D.re_form_comm u (I • v)
    have hsym' := D.re_form_comm v (I • u)
    have hrv := hre_eq v
    simp only [map_smul, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im] at hsym hsym' hpolar
    have him : (D.form v u).im = (D.form u v).im := by linarith
    simp [riemannForm_apply, him]
  · have hat : f l = exp (D.form l l / 2) * f 0 := by simpa using on_line l 1
    have hlaw := apply_add_of_mem_thetaSpace hf l 0
    simp only [zero_add, factor_def, map_zero, hat] at hlaw
    have hcoe : (D.semichar l : ℂ) = 1 :=
      mul_right_cancel₀ (mul_ne_zero (exp_ne_zero (D.form l l / 2)) (hf_ne 0))
        (by rw [one_mul]; linear_combination hlaw.symm)
    exact Subtype.ext hcoe

end TauCeti.AppellHumbertData
