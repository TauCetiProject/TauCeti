/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Positive Appell–Humbert data and the parts of the form

Let `D = (B, χ)` be an Appell–Humbert datum for a subgroup `L` of a complex normed space `V`, with
Riemann form `E` (`TauCeti.AppellHumbertData`).

**Positivity.** The Riemann form is *positive* (`TauCeti.AppellHumbertData.IsPositive`) if
`E (i u, u) > 0` for `u ≠ 0`; equivalently, the Hermitian form `H (u, v) = E (i u, v) + i E (u, v)`
of `E` is positive definite. A positive Riemann form is nondegenerate
(`TauCeti.AppellHumbertData.IsPositive.nondegenerate`), and on a finite-dimensional space
`E (i u, u)` is bounded below by a positive multiple of `‖u‖²`
(`TauCeti.AppellHumbertData.IsPositive.exists_pos_mul_sq_le`, from the coercivity of positive
continuous bilinear forms, `IsCompact.exists_pos_forall_mul_norm_sq_le`).

**The parts of `B`.** The form `B` is real linear in its first and complex linear in its second
variable. Its part that is complex linear in both variables,
`B₁ (u, v) = (B (u, v) - i B (i u, v)) / 2` (`TauCeti.AppellHumbertData.symmetricPart`), is
symmetric because the real part of `B` is; so `B - B₁`
(`TauCeti.AppellHumbertData.hermitianPart`) has the same Riemann form as `B`, and its real part on
the diagonal is `Re (B - B₁) (u, u) = π E (i u, u)`. For a positive datum this grows like `‖u‖²`.

## Main declarations

* `TauCeti.AppellHumbertData.IsPositive`: positivity of the Riemann form.
* `TauCeti.AppellHumbertData.symmetricPart`, `TauCeti.AppellHumbertData.hermitianPart`: the complex
  bilinear part of `B` and the rest.

## Provenance

`TauCeti.AppellHumbertData.symmetricPart_comm` is adapted from `New.IsAppellHumbert.linearPart_symm`
(file `src/Lib/Shimura/ComplexTheta/DimensionFormula.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Chapter 3 (classical factors) and Section 4.1.
-/

public section

open Complex
open scoped Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  (D : AppellHumbertData L)

/-! ### Positivity -/

/-- The Riemann form `E` of an Appell–Humbert datum is **positive** if `E (i u, u) > 0` for every
`u ≠ 0`, that is if the Hermitian form `E (i u, v) + i E (u, v)` is positive definite. -/
def IsPositive : Prop :=
  ∀ u : V, u ≠ 0 → 0 < D.riemannForm (I • u) u

/-- The defining property of a positive Riemann form. -/
theorem isPositive_iff : D.IsPositive ↔ ∀ u : V, u ≠ 0 → 0 < D.riemannForm (I • u) u := Iff.rfl

variable {D}

/-- For a positive Riemann form, `E (i u, u) > 0` for `u ≠ 0`. -/
theorem IsPositive.pos (hD : D.IsPositive) {u : V} (hu : u ≠ 0) : 0 < D.riemannForm (I • u) u :=
  D.isPositive_iff.mp hD u hu

/-- A positive Riemann form is bounded below by a positive multiple of `‖u‖²` on the diagonal
`(i u, u)`. -/
theorem IsPositive.exists_pos_mul_sq_le [FiniteDimensional ℂ V] (hD : D.IsPositive) :
    ∃ c > 0, ∀ u : V, c * ‖u‖ ^ 2 ≤ D.riemannForm (I • u) u := by
  -- `(u, v) ↦ E (i u, v)` is a continuous real bilinear form on the finite-dimensional space `V`,
  -- positive on the diagonal away from `0`, hence coercive.
  let b : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ D.riemannForm ∘ₗ
      ((I • LinearMap.id : V →ₗ[ℂ] V).restrictScalars ℝ))
  have hb (u v : V) : b u v = D.riemannForm (I • u) v := by simp [b]
  obtain ⟨c, hc, hle⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ b) continuousOn_const fun _ _ v hv ↦ by simpa only [hb] using hD.pos hv
  exact ⟨c, hc, fun u ↦ by simpa only [hb] using hle () rfl u⟩

/-- A positive Riemann form is nondegenerate. -/
theorem IsPositive.nondegenerate (hD : D.IsPositive) : D.riemannForm.Nondegenerate := by
  refine ⟨fun u hu ↦ ?_, fun u hu ↦ ?_⟩ <;> by_contra h <;> have := hD.pos h
  · rw [D.riemannForm_swap, hu] at this
    simp at this
  · rw [hu] at this
    exact this.false

/-! ### The parts of the form -/

variable (D)

/-- `Re B (i u, v) = -Im B (v, u)`: the real part of `B` is symmetric and `B` is complex linear in
its second variable. -/
theorem re_form_I_smul (u v : V) : (D.form (I • u) v).re = -(D.form v u).im := by
  rw [D.re_form_comm, (D.form v).map_smul, smul_eq_mul, mul_re, I_re, I_im]
  ring

/-- The **complex bilinear part** `B₁ (u, v) = (B (u, v) - i B (i u, v)) / 2` of the form `B` of an
Appell–Humbert datum. It is symmetric (`TauCeti.AppellHumbertData.symmetricPart_comm`). -/
noncomputable def symmetricPart : V →L[ℂ] V →L[ℂ] ℂ where
  toFun u := (2 : ℂ)⁻¹ • (D.form u - I • D.form (I • u))
  map_add' u v := by
    simp only [smul_add, map_add]
    module
  map_smul' c u := by
    -- Write `c = a + b i`: the form is real linear in its first variable.
    have hc : c • u = c.re • u + c.im • (I • u) := by
      conv_lhs => rw [← Complex.re_add_im c]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    have hIc : I • c • u = c.re • (I • u) - c.im • u := by
      rw [hc, smul_add, smul_comm I c.re u, smul_comm I c.im (I • u), smul_smul I I u, I_mul_I,
        neg_one_smul, smul_neg, sub_eq_add_neg]
    have h1 (v : V) : D.form (c • u) v = c.re * D.form u v + c.im * D.form (I • u) v := by
      rw [hc, map_add, D.form.map_smul c.re u, D.form.map_smul c.im (I • u)]
      simp [Complex.real_smul]
    have h2 (v : V) : D.form (I • c • u) v = c.re * D.form (I • u) v - c.im * D.form u v := by
      rw [hIc, map_sub, D.form.map_smul c.re (I • u), D.form.map_smul c.im u]
      simp [Complex.real_smul]
    ext v
    simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul,
      RingHom.id_apply, h1, h2]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (2⁻¹ * c.im * D.form (I • u) v) * I_sq
  cont := by fun_prop

/-- The defining formula of the complex bilinear part of `B`. -/
theorem symmetricPart_apply (u v : V) :
    D.symmetricPart u v = (D.form u v - I * D.form (I • u) v) / 2 := by
  simp [symmetricPart, div_eq_inv_mul]

/-- The complex bilinear part of `B` is symmetric, as the real part of `B` is. -/
theorem symmetricPart_comm (u v : V) : D.symmetricPart u v = D.symmetricPart v u := by
  have hre (u v : V) : (D.form (I • u) v).im = (D.form (I • v) u).im := by
    have h := D.re_form_comm (I • u) (I • v)
    simp only [(D.form _).map_smul, smul_eq_mul, mul_re, I_re, I_im, zero_mul, one_mul,
      zero_sub] at h
    linarith
  rw [symmetricPart_apply, symmetricPart_apply]
  congr 1
  apply Complex.ext
  · simp only [sub_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, sub_neg_eq_add,
      D.re_form_comm u v, hre u v]
  · simp only [sub_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, re_form_I_smul]
    ring

/-- The **Hermitian part** `B - B₁` of the form `B` of an Appell–Humbert datum: it is conjugate
linear in its first variable, and `B - B₁ = π H (·₂, ·₁)` for a Hermitian form `H`. It has the
same Riemann form as `B` (`TauCeti.AppellHumbertData.hermitianPart_sub_hermitianPart`). -/
noncomputable def hermitianPart : V →L[ℝ] V →L[ℂ] ℂ :=
  D.form - D.symmetricPart.restrictScalars ℝ

/-- The defining formula of the Hermitian part of `B`. -/
theorem hermitianPart_apply (u v : V) :
    D.hermitianPart u v = D.form u v - D.symmetricPart u v := (rfl)

/-- The Hermitian part of `B` has the same Riemann form as `B`:
`(B - B₁) (v, u) - (B - B₁) (u, v) = 2πi E (u, v)`. -/
theorem hermitianPart_sub_hermitianPart (u v : V) :
    D.hermitianPart v u - D.hermitianPart u v = 2 * π * I * D.riemannForm u v := by
  rw [hermitianPart_apply, hermitianPart_apply, D.symmetricPart_comm v u, ← D.form_sub_form]
  ring

/-- On the diagonal, the real part of the Hermitian part of `B` is `π E (i u, u)`. -/
theorem re_hermitianPart_self (u : V) : (D.hermitianPart u u).re = π * D.riemannForm (I • u) u := by
  rw [hermitianPart_apply, symmetricPart_apply, riemannForm_apply, (D.form u).map_smul,
    smul_eq_mul]
  simp only [sub_re, div_ofNat_re, mul_re, I_re, I_im, sub_im, mul_im]
  field_simp
  ring

/-- The imaginary parts of `B` and of its complex bilinear part agree on the diagonal. -/
theorem im_symmetricPart_self (u : V) : (D.symmetricPart u u).im = (D.form u u).im := by
  rw [symmetricPart_apply, div_ofNat_im, sub_im, mul_im, I_re, I_im, re_form_I_smul]
  ring

end TauCeti.AppellHumbertData
