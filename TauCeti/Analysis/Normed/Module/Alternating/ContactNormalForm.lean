/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Alternating.Curry
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.LinearAlgebra.BilinearForm.Contact.NormalForm

/-!
# The linear normal form of a contact covector on a normed space

Let `a` be a continuous covector and `ω` a continuous alternating two-form on a
finite-dimensional real normed space `V`, with `a` contact for `ω`: `a ≠ 0` and `ω` is
nondegenerate on `ker a` (`ContinuousAlternatingMap.isContact_toDual_flatL_iff`). Then there is
a continuous linear equivalence `e : V ≃ ℝⁿ × ℝⁿ × ℝ` in which `a` is the standard covector `dz`
and `ω` is the standard form `Σᵢ dqᵢ ∧ dpᵢ`
(`ContinuousAlternatingMap.exists_continuousLinearEquiv_stdContact`). The factors
`ℝⁿ` are Euclidean spaces, the model of the standard contact form
`TauCeti.innerProductContactForm`.

This is the linear normal form `Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`, restated
for forms given as continuous alternating maps, as they are in the exterior calculus on normed
spaces.

## Main declarations

* `ContinuousAlternatingMap.isContact_toDual_flatL_iff`: a covector is contact for a two-form
  exactly when it is nonzero and the two-form is nondegenerate on its kernel.
* `ContinuousAlternatingMap.exists_continuousLinearEquiv_stdContact`: a contact covector and its
  two-form are standard in suitable continuous linear coordinates.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

section IsContact

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A covector `a` is contact for an alternating two-form `ω` exactly when `a ≠ 0` and `ω` is
nondegenerate on `ker a`. -/
theorem isContact_toDual_flatL_iff {a : E [⋀^Fin 1]→L[𝕜] 𝕜} {ω : E [⋀^Fin 2]→L[𝕜] 𝕜} :
    Module.Dual.IsContact (toDual a : E →ₗ[𝕜] 𝕜) (flatL 𝕜 E 𝕜 ω).toLinearMap₁₂ ↔
      a ≠ 0 ∧ ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0 := by
  have hB (v w : E) : (flatL 𝕜 E 𝕜 ω).toLinearMap₁₂ v w = ω ![v, w] := flatL_apply_apply ω v w
  rw [Module.Dual.isContact_iff_of_isRefl (isAlt_toLinearMap₁₂_flatL ω).isRefl]
  simp only [ContinuousLinearMap.coe_coe, toDual_apply, hB]
  refine and_congr_left' (not_congr ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩)
  ext m
  have hm : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [hm, ← toDual_apply]
  exact LinearMap.congr_fun h (m 0)

end IsContact

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A covector `a` which is contact for an alternating form `ω` is the standard covector `dz`, and
`ω` the standard form `Σᵢ dqᵢ ∧ dpᵢ`, in suitable linear coordinates `V ≃ ℝⁿ × ℝⁿ × ℝ`. -/
theorem exists_continuousLinearEquiv_stdContact {a : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ}
    (hcon : Module.Dual.IsContact (toDual a : V →ₗ[ℝ] ℝ) (flatL ℝ V ℝ ω).toLinearMap₁₂) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ),
      (∀ v, a ![v] = (e v).2.2) ∧
        ∀ v w, ω ![v, w] = ∑ i, ((e v).1 i * (e w).2.1 i - (e v).2.1 i * (e w).1 i) := by
  let B : LinearMap.BilinForm ℝ V := (flatL ℝ V ℝ ω).toLinearMap₁₂
  have hB (v w : V) : B v w = ω ![v, w] := flatL_apply_apply ω v w
  have hBalt : B.IsAlt := isAlt_toLinearMap₁₂_flatL ω
  obtain ⟨n, e₁, ha₁, hB₁⟩ := hcon.exists_linearEquiv_eq_stdContact hBalt
  let L := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
    e₁.toContinuousLinearEquiv.trans (L.prodCongr (L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  refine ⟨n, e, fun v ↦ ?_, fun v w ↦ ?_⟩
  · have h := LinearMap.congr_fun ha₁ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, stdContactCovector_apply,
      ContinuousLinearMap.coe_coe] at h
    rw [← toDual_apply, ← h]
    simp [e]
  · rw [← hB, ← LinearMap.congr_fun₂ hB₁ v w]
    simp [e, L, stdContactBilinForm_apply, dotProduct, Finset.sum_sub_distrib]

end ContinuousAlternatingMap
