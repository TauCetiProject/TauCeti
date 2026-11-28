/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.Gauge
public import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Branch independence and algebraic logarithmic twists on a family of tori

Two complex logarithms `a` and `b` of the same nonzero number (`Complex.exp a = Complex.exp b`)
differ by `2πi k` for an integer `k`, so translating the fibre coordinate of a family of tori
`(Y × E)/Λ` by `(a / 2πi) • P y l` and by `(b / 2πi) • P y l` yields the same quotient class
(`TauCeti.torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq`).

Over a base `Y` with a function `φ : Y → ℂ` and a period section `μ : Λ`, this gives the globally
well-defined fibrewise logarithmic twist equivalence
`TauCeti.torusFamilyLogTwistMap`: `[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` on `(Y × E) / Λ`,
together with its restriction `TauCeti.torusFamilyLogTwistEquiv` to the punctured locus
`{φ ∘ p ≠ 0}`.

## Main declarations

* `TauCeti.torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq`: two logarithms of the same number
  give the same quotient point when used as translation coefficients of a period.
* `TauCeti.torusFamilyLogTwistMap`: the fibrewise equivalence
  `[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` on `(Y × E) / Λ`.
* `TauCeti.torusFamilyLogTwistMap_mk_of_exp_eq`: branch-independence of `torusFamilyLogTwistMap`
  whenever `exp L = φ y`.
* `TauCeti.torusFamilyLogTwistEquiv`: restriction of `torusFamilyLogTwistMap` to the punctured
  family `{φ ∘ p ≠ 0}`.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- Two logarithms of the same number give the same point in `(Y × E)/Λ` when used as translation
coefficients of a period `P y l`, since they differ by `2πi k`. -/
theorem torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq {Y Λ E : Type*} [AddCommGroup Λ]
    [AddCommGroup E] [Module ℂ E] (P : Y → Λ →ₗ[ℤ] E) (l : Λ) {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) (y : Y) (e : E) :
    letI := periodAddAction P
    (Quotient.mk _ (y, e + (a / (2 * π * I)) • P y l) :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      Quotient.mk _ (y, e + (b / (2 * π * I)) • P y l) := by
  let _ := periodAddAction P
  obtain ⟨k, hk⟩ := Complex.exists_div_two_pi_I_smul_eq_add_zsmul h (P y l)
  rw [hk, ← map_zsmul, ← add_assoc, ← periodAddAction_vadd P (k • l) (y, _)]
  exact AddAction.orbitRel.Quotient.quotient_vadd_eq (g := k • l)
    (a := (y, e + (b / (2 * π * I)) • P y l))

section LogTwist

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] [Module ℂ E]
  (φ : Y → ℂ) (P : Y → Λ →ₗ[ℤ] E)

/-- The fibrewise logarithmic twist `[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` on the torus
family `(Y × E) / Λ`. On the locus `{φ ≠ 0}` it is independent of the branch of the logarithm
(`torusFamilyLogTwistMap_mk_of_exp_eq`). -/
noncomputable def torusFamilyLogTwistMap (μ : Λ) :
    (letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) ≃
      (letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :=
  torusFamilyGauge P fun y ↦ (log (φ y) / (2 * π * I)) • P y μ

/-- On representatives, the logarithmic twist adds `(log (φ y) / 2πi) • P y μ` to the fibre
coordinate. -/
@[simp] theorem torusFamilyLogTwistMap_mk (μ : Λ) (y : Y) (e : E) :
    letI := periodAddAction P
    torusFamilyLogTwistMap φ P μ (Quotient.mk _ (y, e)) =
      Quotient.mk _ (y, e + (log (φ y) / (2 * π * I)) • P y μ) :=
  torusFamilyGauge_mk P _ y e

/-- The logarithmic twist preserves the family projection to `Y`. -/
@[simp] theorem torusFamilyProjection_torusFamilyLogTwistMap (μ : Λ)
    (y : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyProjection P (torusFamilyLogTwistMap φ P μ y) = torusFamilyProjection P y :=
  torusFamilyProjection_gauge P _ y

/-- **Branch independence of the logarithmic twist.** Any logarithm `L` of `φ y` computes the
logarithmic twist on the fibre over `y`, because integer multiples of `2πi` shift the fibre by
periods in `P y (Λ)`. -/
theorem torusFamilyLogTwistMap_mk_of_exp_eq (μ : Λ) {y : Y} {L : ℂ} (hL : exp L = φ y) (e : E) :
    letI := periodAddAction P
    torusFamilyLogTwistMap φ P μ (Quotient.mk _ (y, e)) =
      Quotient.mk _ (y, e + (L / (2 * π * I)) • P y μ) := by
  have hφ : φ y ≠ 0 := hL ▸ Complex.exp_ne_zero L
  have hexp : exp (log (φ y)) = exp L := (Complex.exp_log hφ).trans hL.symm
  rw [torusFamilyLogTwistMap_mk]
  exact torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq P μ hexp y e

/-- The logarithmic twist for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistMap_zero :
    torusFamilyLogTwistMap φ P 0 = Equiv.refl _ := by
  have h : (fun y ↦ (log (φ y) / (2 * π * I)) • P y 0) = 0 := by
    ext y
    simp
  rw [torusFamilyLogTwistMap, h, torusFamilyGauge_zero]

/-- Composing logarithmic twists adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistMap_trans (μ₁ μ₂ : Λ) :
    (torusFamilyLogTwistMap φ P μ₁).trans (torusFamilyLogTwistMap φ P μ₂) =
      torusFamilyLogTwistMap φ P (μ₁ + μ₂) := by
  rw [torusFamilyLogTwistMap, torusFamilyLogTwistMap, torusFamilyGauge_trans,
    torusFamilyLogTwistMap]
  congr 1
  ext y
  simp [smul_add]

/-- The inverse of a logarithmic twist negates its period parameter. -/
@[simp] theorem torusFamilyLogTwistMap_symm (μ : Λ) :
    (torusFamilyLogTwistMap φ P μ).symm = torusFamilyLogTwistMap φ P (-μ) := by
  rw [torusFamilyLogTwistMap, torusFamilyGauge_symm, torusFamilyLogTwistMap]
  congr 1
  ext y
  simp

/-- The logarithmic twist restricted to the punctured torus family `{φ ∘ p ≠ 0}`. -/
noncomputable def torusFamilyLogTwistEquiv (μ : Λ) :
    (letI := periodAddAction P;
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) ≃
    (letI := periodAddAction P;
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) :=
  (torusFamilyLogTwistMap φ P μ).subtypeEquiv fun y ↦ by simp

/-- Coercion of `torusFamilyLogTwistEquiv` to the ambient torus family is
`torusFamilyLogTwistMap`. -/
@[simp] theorem coe_torusFamilyLogTwistEquiv (μ : Λ)
    (y : letI := periodAddAction P
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) :
    (torusFamilyLogTwistEquiv φ P μ y :
        letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyLogTwistMap φ P μ y.val := (rfl)

/-- The punctured logarithmic twist for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistEquiv_zero :
    torusFamilyLogTwistEquiv φ P 0 = Equiv.refl _ := by
  simp only [torusFamilyLogTwistEquiv, torusFamilyLogTwistMap_zero, Equiv.subtypeEquiv_refl]

/-- Composing punctured logarithmic twists adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistEquiv_trans (μ₁ μ₂ : Λ) :
    (torusFamilyLogTwistEquiv φ P μ₁).trans (torusFamilyLogTwistEquiv φ P μ₂) =
      torusFamilyLogTwistEquiv φ P (μ₁ + μ₂) := by
  simp only [torusFamilyLogTwistEquiv, Equiv.subtypeEquiv_trans, torusFamilyLogTwistMap_trans]

/-- The inverse of a punctured logarithmic twist negates its period parameter. -/
@[simp] theorem torusFamilyLogTwistEquiv_symm (μ : Λ) :
    (torusFamilyLogTwistEquiv φ P μ).symm = torusFamilyLogTwistEquiv φ P (-μ) := by
  ext y
  simp only [torusFamilyLogTwistEquiv, Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    torusFamilyLogTwistMap_symm]

end LogTwist

end TauCeti
