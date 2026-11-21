/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LatticeQuotient.DevelopingMap
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# A torus bundle with exact period forms but no global action coordinates

Let `B = (1, 2) × (0, 3π)` be the open rectangle of polar coordinates `(r, φ)`
(`TauCeti.polarRectangle`), and let `a : B → ℝ²` be the polar map

`a(r, φ) = (r cos φ, r sin φ)`

(`TauCeti.polarDevelopingMap`). Its differential at `(r, φ)` has determinant `r > 0`, so the
one-forms `α_i = 2π d a_i` (`TauCeti.CotangentBundle.developingForm`) are a global frame of `T*B`
(`TauCeti.isLocalFrameOn_developingForm_polarDevelopingMap`). They span the period lattice
`Λ ⊆ T*B`, and the torus bundle `T*B/Λ` (`TauCeti.CotangentBundle.LatticeQuotient`) is a regular
Lagrangian torus fibration whose period forms are exact, with developing map `a`.

Since the angle `φ` ranges over an interval longer than `2π`, the map `a` wraps the rectangle more
than once around the annulus `1 < ‖·‖ < 2`, and is not injective:
`a(3/2, π/2) = a(3/2, 5π/2)` (`TauCeti.not_injective_polarDevelopingMap`). Consequently:

* the action–angle chart of `T*B/Λ` with actions `a` is not injective
  (`TauCeti.not_injective_actionAngleChart_polarDevelopingMap`);
* more generally, no `C¹` functions `J : B → ℝ²` whose differentials, scaled by `2π`, lie in `Λ`
  at every point are injective (`TauCeti.not_injective_of_mem_span_polarDevelopingMap`). Such
  functions are integral affine functions `N a + b` of the developing map
  (`TauCeti.CotangentBundle.LatticeQuotient.exists_eq_mulVec_add_of_mem_span`), and none of these
  is injective.

So the fibration `T*B/Λ` admits no global action coordinates onto an open subset of `ℝ²`,
although its period forms are exact and its base is a convex rectangle. Injectivity of the
developing map is a separate condition for global action–angle coordinates.

## References

* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706.
-/

public section

noncomputable section

open Set Function Real TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

/-- The period `2π` of the angle coordinates of the action–angle chart is positive. -/
local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The open rectangle `(1, 2) × (0, 3π)` of polar coordinates `(r, φ)`. -/
def polarRectangle : Opens (ℝ × ℝ) :=
  ⟨Ioo 1 2 ×ˢ Ioo 0 (3 * π), isOpen_Ioo.prod isOpen_Ioo⟩

/-- A point lies in the polar rectangle when `1 < r < 2` and `0 < φ < 3π`. -/
@[simp]
theorem mem_polarRectangle {z : ℝ × ℝ} :
    z ∈ polarRectangle ↔ z.1 ∈ Ioo 1 2 ∧ z.2 ∈ Ioo 0 (3 * π) :=
  Iff.rfl

/-- The polar rectangle is convex, hence preconnected. -/
instance : PreconnectedSpace polarRectangle :=
  Subtype.preconnectedSpace ((convex_Ioo 1 2).prod (convex_Ioo 0 (3 * π))).isPreconnected

/-- The polar map `(r, φ) ↦ (r cos φ, r sin φ)` on `ℝ²`, with values in `Fin 2 → ℝ`. -/
private def polarMap (z : ℝ × ℝ) : Fin 2 → ℝ :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (polarCoord.symm z)

private theorem contDiff_polarMap : ContDiff ℝ ∞ polarMap := by
  have h : ⇑polarCoord.symm = fun z : ℝ × ℝ ↦ (z.1 * cos z.2, z.1 * sin z.2) :=
    funext polarCoord_symm_apply
  refine (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.contDiff.comp ?_
  rw [h]
  fun_prop

private theorem hasFDerivAt_polarMap (z : ℝ × ℝ) :
    HasFDerivAt polarMap ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearMap.comp
      (fderivPolarCoordSymm z)) z :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.hasFDerivAt.comp z (hasFDerivAt_polarCoord_symm z)

/-- The **polar developing map** `(r, φ) ↦ (r cos φ, r sin φ)` on the rectangle
`(1, 2) × (0, 3π)`. -/
def polarDevelopingMap : C^∞⟮𝓘(ℝ, ℝ × ℝ), polarRectangle; 𝓘(ℝ, Fin 2 → ℝ), Fin 2 → ℝ⟯ :=
  ⟨polarMap ∘ Subtype.val, contDiff_polarMap.contMDiff.comp contMDiff_subtype_val⟩

/-- The underlying function of the polar developing map is the polar map on the underlying
point. -/
private theorem coe_polarDevelopingMap : ⇑polarDevelopingMap = polarMap ∘ Subtype.val :=
  rfl

/-- The polar developing map sends `(r, φ)` to `(r cos φ, r sin φ)`. -/
@[simp]
theorem polarDevelopingMap_apply (z : polarRectangle) :
    polarDevelopingMap z = ![z.1.1 * cos z.1.2, z.1.1 * sin z.1.2] := by
  rw [coe_polarDevelopingMap, comp_apply, polarMap, polarCoord_symm_apply,
    ContinuousLinearEquiv.finTwoArrow_symm_apply]

/-- The differentials of the polar developing map are bijective: the polar map has Jacobian
determinant `r ≠ 0`. -/
theorem bijective_mfderiv_polarDevelopingMap (z : polarRectangle) :
    Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 2 → ℝ) polarDevelopingMap z) := by
  have hz : (z : ℝ × ℝ).1 ≠ 0 := (zero_lt_one.trans z.2.1.1).ne'
  -- The differential is that of the polar map on `ℝ²`.
  have hd : ⇑(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 2 → ℝ) polarDevelopingMap z) =
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm ∘ fderivPolarCoordSymm z := funext fun v ↦ by
    have h := Manifold.mfderiv_comp_subtype_val_apply (I := 𝓘(ℝ, Fin 2 → ℝ)) (f := polarMap)
      (x := z) v
    rw [mfderiv_eq_fderiv, (hasFDerivAt_polarMap z).fderiv] at h
    rw [coe_polarDevelopingMap, h]
    -- `rfl`: `NormedSpace.fromTangentSpace` is the identity equivalence of the model space.
    rfl
  have hP : Bijective (fderivPolarCoordSymm z) := by
    have hunit : IsUnit (fderivPolarCoordSymm z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
      rw [LinearMap.isUnit_iff_isUnit_det, ← ContinuousLinearMap.det,
        det_fderivPolarCoordSymm]
      exact hz.isUnit
    exact (Module.End.isUnit_iff _).1 hunit
  rw [hd]
  exact (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.bijective.comp hP

/-- **The polar developing map is not injective**: `a(3/2, π/2) = a(3/2, 5π/2)`. -/
theorem not_injective_polarDevelopingMap : ¬ Injective polarDevelopingMap := by
  have hπ := pi_pos
  let z₁ : polarRectangle := ⟨(3 / 2, π / 2), by
    rw [mem_polarRectangle]; exact ⟨⟨by norm_num, by norm_num⟩, ⟨by positivity, by linarith⟩⟩⟩
  let z₂ : polarRectangle := ⟨(3 / 2, π / 2 + 2 * π), by
    rw [mem_polarRectangle]; exact ⟨⟨by norm_num, by norm_num⟩, ⟨by positivity, by linarith⟩⟩⟩
  intro h
  have h12 : z₁ = z₂ := h (by
    rw [polarDevelopingMap_apply, polarDevelopingMap_apply]
    simp [z₁, z₂, cos_add_two_pi, sin_add_two_pi])
  have := congrArg (fun z : polarRectangle ↦ (z : ℝ × ℝ).2) h12
  simp only [z₁, z₂] at this
  linarith

/-- The period forms `2π d a_i` of the polar developing map are a global frame of the cotangent
bundle of the rectangle. -/
theorem isLocalFrameOn_developingForm_polarDevelopingMap :
    IsLocalFrameOn 𝓘(ℝ, ℝ × ℝ) ((ℝ × ℝ) →L[ℝ] ℝ) ∞
      (fun i x ↦ SmoothForm.degreeOneEquiv
        (CotangentBundle.developingForm (2 * π) polarDevelopingMap i) x) univ :=
  CotangentBundle.isLocalFrameOn_developingForm two_pi_pos.ne'
    bijective_mfderiv_polarDevelopingMap

/-- **No injective action coordinates over the polar rectangle.** No `C¹` map `J` on
`(1, 2) × (0, 3π)` whose differentials, scaled by `2π`, lie at every point in the lattice spanned
by the period forms `2π d a_i` of the polar developing map is injective. -/
theorem not_injective_of_mem_span_polarDevelopingMap {J : polarRectangle → Fin 2 → ℝ}
    (hJ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 2 → ℝ) 1 J)
    (hJα : ∀ x i, (2 * π) • (ContinuousLinearMap.proj i).comp
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Fin 2 → ℝ) J x) ∈ Submodule.span ℤ
        (range fun j ↦ SmoothForm.degreeOneEquiv
          (CotangentBundle.developingForm (2 * π) polarDevelopingMap j) x)) :
    ¬ Injective J :=
  CotangentBundle.LatticeQuotient.not_injective_of_mem_span
    isLocalFrameOn_developingForm_polarDevelopingMap two_pi_pos.ne'
    (polarDevelopingMap.contMDiff.of_le (by simp))
    (CotangentBundle.degreeOneEquiv_developingForm_apply _ _) hJ hJα
    not_injective_polarDevelopingMap

/-- **The action–angle chart over the polar rectangle is not injective.** -/
theorem not_injective_actionAngleChart_polarDevelopingMap :
    ¬ Injective (CotangentBundle.LatticeQuotient.actionAngleChart
      isLocalFrameOn_developingForm_polarDevelopingMap (2 * π) polarDevelopingMap) := by
  rw [CotangentBundle.LatticeQuotient.actionAngleChart_injective_iff]
  exact not_injective_polarDevelopingMap

end TauCeti
