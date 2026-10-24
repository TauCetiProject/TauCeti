/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

/-!
# Graphs of one-forms in a cotangent bundle

A smooth one-form `α` on a manifold `M` is a smooth section `s_α : x ↦ α_x` of the cotangent
bundle `T*M = TauCeti.CotangentBundle I M`; its image is the graph of `α`. Since the Liouville form
`λ` is tautological, `s_α^*λ = α` (`TauCeti.CotangentBundle.mpullback_liouvilleForm`), and so the
canonical symplectic form `ω = -dλ` pulls back to `s_α^*ω = -dα`
(`TauCeti.CotangentBundle.mpullback_symplecticForm`).

The section `s_α` has injective differential, because the projection `π : T*M → M` is a left
inverse of it (`Bundle.mfderiv_injective_of_proj_comp_eq_id`). Combining these facts with the
tangent-image predicates of `TauCeti.Geometry.Symplectic.Lagrangian.Manifold`:

* `s_α` is an isotropic map exactly when `α` is closed
  (`TauCeti.CotangentBundle.isIsotropicMap_section_iff`);
* when `M` is finite-dimensional, `T*M` has twice the dimension of `M`, so `s_α` is a Lagrangian
  map exactly when `α` is closed (`TauCeti.CotangentBundle.isLagrangianMap_section_iff`).

In particular the zero section of `T*M` is a Lagrangian map
(`TauCeti.CotangentBundle.isLagrangianMap_zeroSection`), and so is the graph of the differential
`df` of a smooth function (`TauCeti.CotangentBundle.isLagrangianMap_section_mextDerivₗ`). Since
`s_α^*λ = α`, the pulled-back Liouville form on the graph is exact exactly when `α` is.

## Main declarations

* `TauCeti.CotangentBundle.mpullback_symplecticForm`: `s_α^*ω = -dα`.
* `TauCeti.CotangentBundle.isIsotropicMap_section_iff`: the graph of `α` is isotropic iff
  `dα = 0`.
* `TauCeti.CotangentBundle.isLagrangianMap_section_iff`: the graph of `α` is Lagrangian iff
  `dα = 0`.
* `TauCeti.CotangentBundle.isLagrangianMap_zeroSection`: the zero section is Lagrangian.
* `TauCeti.CotangentBundle.isLagrangianMap_section_mextDerivₗ`: the graph of `df` is Lagrangian.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **The graph of a one-form pulls the symplectic form back to minus its derivative.** The
section of the cotangent bundle defined by a smooth one-form `α` pulls the canonical symplectic
form `ω = -dλ` back to `-dα`. -/
theorem mpullback_symplecticForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x))
      (SmoothForm.degreeOneEquiv α).contMDiff (symplecticForm I M) = -mextDerivₗ I 1 α := by
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_liouvilleForm]

/-- **The graph of a one-form is isotropic exactly when the form is closed.** The section of the
cotangent bundle defined by a smooth one-form `α` is an isotropic map for the canonical symplectic
form if and only if `dα = 0`. -/
theorem isIsotropicMap_section_iff (α : SmoothForm I M ℝ 1) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsIsotropicMap I
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) ↔
      α.IsClosed := by
  rw [SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff_mpullback_eq_zero
      (SmoothForm.degreeOneEquiv α).contMDiff, mpullback_symplecticForm, neg_eq_zero,
    SmoothForm.isClosed_def, ← mextDerivₗ_apply I 1 α, ZeroMemClass.coe_eq_zero]

variable [FiniteDimensional ℝ E]

/-- **The graph of a one-form is Lagrangian exactly when the form is closed.** On a
finite-dimensional manifold, the section of the cotangent bundle defined by a smooth one-form `α`
is a Lagrangian map for the canonical symplectic form if and only if `dα = 0`. -/
theorem isLagrangianMap_section_iff (α : SmoothForm I M ℝ 1) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsLagrangianMap I
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) ↔
      α.IsClosed := by
  rw [← isIsotropicMap_section_iff]
  refine ⟨fun h ↦ h.isIsotropicMap, fun h ↦ h.isLagrangianMap_of_finrank (fun x ↦ ?_) ?_⟩
  · -- The projection is a left inverse of the section.
    exact Bundle.mfderiv_injective_of_proj_comp_eq_id
      (((SmoothForm.degreeOneEquiv α).contMDiff x).mdifferentiableAt (by simp)) rfl
  · rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, two_mul]

/-- **The zero section is Lagrangian.** On a finite-dimensional manifold, the zero section of the
cotangent bundle is a Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_zeroSection :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsLagrangianMap I
      (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) := by
  have h := (isLagrangianMap_section_iff (0 : SmoothForm I M ℝ 1)).mpr <| by
    rw [SmoothForm.isClosed_def, ← mextDerivₗ_apply I 1, map_zero, ZeroMemClass.coe_zero]
  -- The section of the zero one-form is the zero section.
  convert h using 2 with x
  simp [zeroSection]

/-- **The graph of an exact one-form is Lagrangian.** On a finite-dimensional manifold, the section
of the cotangent bundle defined by the differential `df` of a smooth function `f` is a Lagrangian
map for the canonical symplectic form. -/
theorem isLagrangianMap_section_mextDerivₗ (f : SmoothForm I M ℝ 0) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsLagrangianMap I
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) :=
  (isLagrangianMap_section_iff _).mpr <| by
    rw [SmoothForm.isClosed_def, mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv]

end CotangentBundle

end TauCeti
