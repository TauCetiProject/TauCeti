/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Symplectic.ComplexModule
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The standard compatible triple on the complex line

The analytic Heegaard Floer roadmap uses the complex line both as the local model for
holomorphic-curve domains and as the one-dimensional target model for elementary checks. The
existing file `TauCeti.Geometry.Symplectic.StandardCompatible` builds the standard compatible
triple on a doubled real inner-product space `V × V`; this file transports the case `V = ℝ`
across Mathlib's real-linear equivalence `Complex.equivRealProdCLM.symm`.

The resulting almost complex structure on `ℂ` is multiplication by `Complex.I`, and the
transported symplectic form is the standard area form
`ω(z, w) = z.re * w.im - z.im * w.re`. Compatibility is inherited from the transported standard
model, giving a concrete non-vacuous model for the pointwise `J`-holomorphic and energy API.

## Main declarations

* `TauCeti.complexLineEquivRealProd`: the real-linear equivalence `ℂ ≃ₗ[ℝ] ℝ × ℝ`.
* `TauCeti.realProdEquivComplexLine`: its inverse, from `ℝ × ℝ` to `ℂ`.
* `TauCeti.stdComplexStructure`: the standard almost complex structure on `ℂ`,
  `z ↦ Complex.I * z`.
* `TauCeti.stdComplexSymplecticForm`: the standard symplectic area form on `ℂ`.
* `TauCeti.realProdEquivComplexLine_isComplexLinearMap` and
  `TauCeti.realProdEquivComplexLine_isSymplectomorphism`: the coordinate equivalence preserves
  the standard complex and symplectic structures.
* `TauCeti.stdComplexSymplecticForm_compatible`: compatibility of the standard area form with
  the standard complex structure.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the standard complex line is `ℝ²` with `J(x, y) = (-y, x)` and
`ω((x₁, y₁), (x₂, y₂)) = x₁ y₂ - y₁ x₂`.
-/

public section

namespace TauCeti

open Complex

/-- The real-linear equivalence from the complex line to its real-coordinate product. -/
noncomputable abbrev complexLineEquivRealProd : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  Complex.equivRealProdCLM.toLinearEquiv

/-- The real-linear equivalence from real-coordinate pairs to the complex line. -/
noncomputable abbrev realProdEquivComplexLine : (ℝ × ℝ) ≃ₗ[ℝ] ℂ :=
  complexLineEquivRealProd.symm

/-- The standard almost complex structure on `ℂ`, transported from
`AlmostComplexStructure.product ℝ` along `realProdEquivComplexLine`. -/
noncomputable def stdComplexStructure : AlmostComplexStructure ℂ :=
  (AlmostComplexStructure.product ℝ).transport realProdEquivComplexLine

/-- The standard symplectic area form on `ℂ`, transported from the standard form on `ℝ × ℝ`. -/
noncomputable def stdComplexSymplecticForm : SymplecticForm ℂ :=
  (stdSymplecticForm (V := ℝ)).transport realProdEquivComplexLine

@[simp]
lemma complexLineEquivRealProd_apply (z : ℂ) :
    complexLineEquivRealProd z = (z.re, z.im) :=
  rfl

@[simp]
lemma realProdEquivComplexLine_apply (p : ℝ × ℝ) :
    realProdEquivComplexLine p = p.1 + p.2 * Complex.I :=
  Complex.equivRealProdCLM_symm_apply p

/-- The standard complex structure on `ℂ` is multiplication by `Complex.I`. -/
@[simp]
lemma stdComplexStructure_apply (z : ℂ) :
    stdComplexStructure z = Complex.I * z := by
  apply Complex.ext <;>
    simp [stdComplexStructure, realProdEquivComplexLine, complexLineEquivRealProd,
      Complex.mul_re, Complex.mul_im]

lemma stdComplexStructure_one : stdComplexStructure 1 = Complex.I := by
  simp

lemma stdComplexStructure_I : stdComplexStructure Complex.I = -1 := by
  simp

/-- The standard complex structure on `ℂ` is the one induced by its native complex module
structure. -/
lemma stdComplexStructure_eq_ofComplexModule :
    stdComplexStructure = AlmostComplexStructure.ofComplexModule ℂ := by
  ext z
  simp [AlmostComplexStructure.ofComplexModule_apply]

/-- The real-coordinate equivalence from `ℝ × ℝ` to `ℂ` is complex-linear for the standard
complex structures. -/
lemma realProdEquivComplexLine_isComplexLinearMap :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) stdComplexStructure
      realProdEquivComplexLine.toLinearMap :=
  AlmostComplexStructure.isComplexLinearMap_transport (AlmostComplexStructure.product ℝ)
    realProdEquivComplexLine

/-- The real-coordinate equivalence from `ℂ` to `ℝ × ℝ` is complex-linear for the standard
complex structures. -/
lemma complexLineEquivRealProd_isComplexLinearMap :
    IsComplexLinearMap stdComplexStructure (AlmostComplexStructure.product ℝ)
      complexLineEquivRealProd.toLinearMap :=
  AlmostComplexStructure.isComplexLinearMap_symm_transport (AlmostComplexStructure.product ℝ)
    realProdEquivComplexLine

/-- The standard symplectic form on `ℂ` is the usual coordinate area form. -/
@[simp]
lemma stdComplexSymplecticForm_apply (z w : ℂ) :
    stdComplexSymplecticForm z w = z.re * w.im - z.im * w.re := by
  simp [stdComplexSymplecticForm, realProdEquivComplexLine,
    complexLineEquivRealProd]
  ring

/-- The standard area of `(z, I z)` is the squared norm in real coordinates. -/
lemma stdComplexSymplecticForm_apply_stdComplexStructure_self (z : ℂ) :
    stdComplexSymplecticForm z (stdComplexStructure z) = z.re * z.re + z.im * z.im := by
  simp [Complex.mul_re, Complex.mul_im]

/-- The real-coordinate equivalence from `ℝ × ℝ` to `ℂ` is a symplectomorphism for the
standard symplectic forms. -/
lemma realProdEquivComplexLine_isSymplectomorphism :
    SymplecticForm.IsSymplectomorphism (stdSymplecticForm (V := ℝ)) stdComplexSymplecticForm
      realProdEquivComplexLine := by
  exact (SymplecticForm.isSymplectomorphism_iff_transport_eq
    (ω₁ := stdSymplecticForm (V := ℝ)) (ω₂ := stdComplexSymplecticForm)
    (e := realProdEquivComplexLine)).mpr rfl

/-- The real-coordinate equivalence from `ℂ` to `ℝ × ℝ` is a symplectomorphism for the
standard symplectic forms. -/
lemma complexLineEquivRealProd_isSymplectomorphism :
    SymplecticForm.IsSymplectomorphism stdComplexSymplecticForm (stdSymplecticForm (V := ℝ))
      complexLineEquivRealProd :=
  realProdEquivComplexLine_isSymplectomorphism.symm

/-- The standard symplectic form on `ℂ` is invariant under multiplication by `I`. -/
lemma stdComplexSymplecticForm_invariant :
    stdComplexSymplecticForm.Invariant stdComplexStructure :=
  (stdSymplecticForm_invariant_product (V := ℝ)).transport realProdEquivComplexLine

/-- The standard symplectic form on `ℂ` tames multiplication by `I`. -/
lemma stdComplexSymplecticForm_tames :
    stdComplexSymplecticForm.Tames stdComplexStructure :=
  (stdSymplecticForm_tames_product (V := ℝ)).transport realProdEquivComplexLine

/-- The standard symplectic area form on `ℂ` is compatible with the standard complex structure. -/
lemma stdComplexSymplecticForm_compatible :
    stdComplexSymplecticForm.Compatible stdComplexStructure :=
  (stdSymplecticForm_compatible_product (V := ℝ)).transport realProdEquivComplexLine

/-- The associated compatible metric on `ℂ` is the standard real dot product. -/
lemma stdComplexSymplecticForm_associatedBilinForm (z w : ℂ) :
    stdComplexSymplecticForm.associatedBilinForm stdComplexStructure z w =
      z.re * w.re + z.im * w.im := by
  rw [SymplecticForm.associatedBilinForm_apply, stdComplexStructure_apply,
    stdComplexSymplecticForm_apply]
  simp [Complex.mul_re, Complex.mul_im]

end TauCeti
