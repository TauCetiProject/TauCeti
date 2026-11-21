/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# Complex contractions and coefficients of real one-forms

`ContinuousAlternatingMap.apply_const_complex` evaluates a real one-form on a complex vector
using its coefficients on the real basis `(1, I)`. It identifies differential-form line
integrands with their coordinate expressions.

`ContinuousAlternatingMap.holCurry` is the output-scaled contraction `ι_v - I • ι_{I • v}`,
bundled as a continuous complex-bilinear map in the vector and the form.
`ContinuousAlternatingMap.alternatizeUncurryFin_holCurry_comp` gives its anticommutation
with alternation of a conjugate-linear family.
-/

public section

namespace ContinuousAlternatingMap

/-- A real one-form on the complex plane evaluates on a vector using its coefficients on
the real basis `(1, I)`. -/
theorem apply_const_complex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℂ [⋀^Fin 1]→L[ℝ] F) (v : ℂ) :
    α (fun _ ↦ v) = v.re • α (fun _ ↦ 1) + v.im • α (fun _ ↦ Complex.I) := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp [Complex.real_smul]
  simpa only [map_add, map_smul, ofSubsingleton_symm_apply_apply] using
    congrArg ((ofSubsingleton ℝ ℂ F (0 : Fin 1)).symm α) hv

section Holomorphic

open Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

/-- The output-scaled contraction `φ ↦ ι_v φ - I • ι_{I • v} φ`, as a complex-linear map in the
vector with values in real-linear maps of the form: twice the complex-linear part of currying. -/
private noncomputable def holCurryAux :
    E →L[ℂ] (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
  (2 : ℝ) • ContinuousLinearMap.complexLinearPart (E := E)
    (F := (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
    (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap.flip

private theorem holCurryAux_apply (v : E) (φ : E [⋀^Fin (k + 1)]→L[ℝ] F) :
    holCurryAux v φ = φ.curryLeft v - I • φ.curryLeft (I • v) := by
  simp [holCurryAux, smul_smul]

/-- The output-scaled contraction `φ ↦ ι_v φ - I • ι_{I • v} φ`, as a continuous
complex-bilinear map in the vector and the form. -/
noncomputable def holCurry :
    E →L[ℂ] (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℂ] E [⋀^Fin k]→L[ℝ] F where
  toFun v := (holCurryAux v).complexOfMapISmul fun φ ↦ by
    ext w
    simp [holCurryAux_apply, smul_sub, smul_smul]
  map_add' v w := by
    ext φ : 1
    simp only [ContinuousLinearMap.coe_complexOfMapISmul, map_add, _root_.add_apply]
  map_smul' c v := by
    ext φ : 1
    simp only [ContinuousLinearMap.coe_complexOfMapISmul, map_smul, _root_.smul_apply,
      RingHom.id_apply]
  cont := by
    let ι := ContinuousLinearMap.restrictScalarsIsometry ℂ
      (E [⋀^Fin (k + 1)]→L[ℝ] F) (E [⋀^Fin k]→L[ℝ] F) ℝ ℝ
    apply ι.isometry.isUniformInducing.isInducing.continuous_iff.2
    simpa only [ι, Function.comp_def, ContinuousLinearMap.coe_restrictScalarsIsometry,
      ContinuousLinearMap.restrictScalars_complexOfMapISmul] using
      (holCurryAux (E := E) (F := F) (k := k)).continuous

/-- Evaluation of the holomorphic contraction, with `I` acting on the output. -/
theorem holCurry_apply (v : E) (φ : E [⋀^Fin (k + 1)]→L[ℝ] F) :
    holCurry v φ = φ.curryLeft v - I • φ.curryLeft (I • v) := by
  rw [← holCurryAux_apply]
  exact congrFun (ContinuousLinearMap.coe_complexOfMapISmul (holCurryAux v) _) φ

/-- Holomorphic contraction anticommutes with alternation of a conjugate-linear family. -/
theorem alternatizeUncurryFin_holCurry_comp
    (L : E →L[ℝ] E [⋀^Fin (k + 1)]→L[ℝ] F)
    (hL : ∀ v, L (I • v) = -I • L v) (v : E) :
    alternatizeUncurryFin ((holCurry v).restrictScalars ℝ ∘L L) =
      -holCurry v (alternatizeUncurryFin L) := by
  have hsplit : (holCurry v).restrictScalars ℝ ∘L L =
      (curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
        (n := k)).toContinuousLinearMap.flip v ∘L L -
      I • (curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
        (n := k)).toContinuousLinearMap.flip (I • v) ∘L L := by
    ext u : 1
    simp [holCurry_apply]
  have hcartan (y : E) := eq_sub_of_add_eq
    (alternatizeUncurryFin_curryLeft_comp_add_curryLeft L y)
  rw [hsplit, alternatizeUncurryFin_sub, alternatizeUncurryFin_smul,
    hcartan, hcartan, hL, holCurry_apply]
  simp only [smul_sub, smul_smul, mul_neg, I_mul_I, _root_.neg_neg, one_smul]
  abel

end Holomorphic

end ContinuousAlternatingMap
