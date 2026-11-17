/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.LinearAlgebra.BilinearForm.Contact.NormalForm

/-!
# The linear normal form of a contact covector on a normed space

Let `a` be a continuous covector and `ω` a continuous alternating two-form on a
finite-dimensional real normed space `V`, with `a` contact for `ω`: `a ≠ 0` and `ω` is
nondegenerate on `ker a`. Then there is a continuous linear equivalence
`e : V ≃ ℝⁿ × ℝⁿ × ℝ` in which `a` is the standard covector `dz` and `ω` is the standard form
`Σᵢ dqᵢ ∧ dpᵢ` (`ContinuousAlternatingMap.exists_continuousLinearEquiv_stdContact`). The factors
`ℝⁿ` are Euclidean spaces, the model of the standard contact form
`TauCeti.innerProductContactForm`.

This is the linear normal form `Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`, restated
for forms given as continuous alternating maps, as they are in the exterior calculus on normed
spaces.

## Main declarations

* `ContinuousAlternatingMap.exists_continuousLinearEquiv_stdContact`: a contact covector and its
  two-form are standard in suitable continuous linear coordinates.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A covector `a` which is contact for an alternating form `ω` is the standard covector `dz`, and
`ω` the standard form `Σᵢ dqᵢ ∧ dpᵢ`, in suitable linear coordinates `V ≃ ℝⁿ × ℝⁿ × ℝ`. -/
theorem exists_continuousLinearEquiv_stdContact {a : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ),
      (∀ v, a ![v] = (e v).2.2) ∧
        ∀ v w, ω ![v, w] = ∑ i, ((e v).1 i * (e w).2.1 i - (e v).2.1 i * (e w).1 i) := by
  let B : LinearMap.BilinForm ℝ V := (flatL ℝ V ℝ ω).toLinearMap₁₂
  have hB (v w : V) : B v w = ω ![v, w] := flatL_apply_apply ω v w
  have hBalt : B.IsAlt := isAlt_toLinearMap₁₂_flatL ω
  have hcon : Module.Dual.IsContact (toDual a : V →ₗ[ℝ] ℝ) B := by
    refine (Module.Dual.isContact_iff_of_isRefl hBalt.isRefl).2
      ⟨fun h0 ↦ hne ?_, fun v hv hvw ↦ hnd v (by simpa using hv) fun w hw ↦ by
        simpa [hB] using hvw w (by simpa using hw)⟩
    ext m
    have hm : m = ![m 0] := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [hm, ← toDual_apply]
    exact LinearMap.congr_fun h0 (m 0)
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
