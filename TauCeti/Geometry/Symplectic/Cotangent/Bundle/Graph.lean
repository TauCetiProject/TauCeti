/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact

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
`df` of a smooth function (`TauCeti.CotangentBundle.isLagrangianMap_section_mextDerivₗ`).

Since `s_α^*λ = α`, the graph of `α` is an exact Lagrangian map for the primitive `λ` of `ω`, with
primitive `h`, exactly when `α = dh` (`TauCeti.CotangentBundle.isExactLagrangianMap_section_iff`).
So the graph is exact Lagrangian for some primitive exactly when `α` is an exact form
(`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_iff`); the zero section is exact
Lagrangian with primitive `0` (`TauCeti.CotangentBundle.isExactLagrangianMap_zeroSection`).

## Main declarations

* `TauCeti.CotangentBundle.mpullback_symplecticForm`: `s_α^*ω = -dα`.
* `TauCeti.CotangentBundle.isIsotropicMap_section_iff`: the graph of `α` is isotropic iff
  `dα = 0`.
* `TauCeti.CotangentBundle.isLagrangianMap_section_iff`: the graph of `α` is Lagrangian iff
  `dα = 0`.
* `TauCeti.CotangentBundle.isLagrangianMap_zeroSection`: the zero section is Lagrangian.
* `TauCeti.CotangentBundle.isLagrangianMap_section_mextDerivₗ`: the graph of `df` is Lagrangian.
* `TauCeti.CotangentBundle.isExactLagrangianMap_section_iff`: the graph of `α` is exact Lagrangian
  with primitive `h` iff `α = dh`.
* `TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_iff`: the graph of `α` is exact
  Lagrangian iff `α` is exact.
* `TauCeti.CotangentBundle.isExactLagrangianMap_zeroSection`: the zero section is exact
  Lagrangian.

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
    SmoothForm.isClosed_iff_mextDerivₗ_eq_zero]

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
  have h := (isLagrangianMap_section_iff (0 : SmoothForm I M ℝ 1)).mpr
    SmoothForm.isClosed_zero
  -- The section of the zero one-form is the zero section.
  convert h using 2 with x
  simp [zeroSection]

/-- **The graph of an exact one-form is Lagrangian.** On a finite-dimensional manifold, the section
of the cotangent bundle defined by the differential `df` of a smooth function `f` is a Lagrangian
map for the canonical symplectic form. -/
theorem isLagrangianMap_section_mextDerivₗ (f : SmoothForm I M ℝ 0) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsLagrangianMap I
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv (mextDerivₗ I 0 f) x)) :=
  (isLagrangianMap_section_iff _).mpr (SmoothForm.isClosed_mextDerivₗ f)

/-! ### Exact Lagrangian graphs -/

/-- **The graph of a one-form is exact Lagrangian exactly when the form is exact.** On a
finite-dimensional manifold, the section of the cotangent bundle defined by a smooth one-form `α`
is an exact Lagrangian map for the primitive `λ` of `ω = -dλ`, with primitive `h`, if and only if
`h` is smooth and `α = dh`. -/
theorem isExactLagrangianMap_section_iff (α : SmoothForm I M ℝ 1) {h : M → ℝ} :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsExactLagrangianMap I
        (liouvilleForm I M)
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) h ↔
      ContMDiff I 𝓘(ℝ) ∞ h ∧ α.1 = mextDeriv (RoughForm.ofFunction I h) := by
  -- The Liouville form is tautological: `s_α^*λ = α`.
  have hpull := congrArg Subtype.val (mpullback_liouvilleForm α)
  rw [SmoothForm.coe_mpullback] at hpull
  refine ⟨fun hL ↦ ⟨hL.contMDiff_primitive, hpull.symm.trans hL.mpullback_eq⟩,
    fun ⟨hh, hα⟩ ↦ ⟨(isLagrangianMap_section_iff α).mpr ?_, hh, hpull.trans hα⟩⟩
  rw [SmoothForm.isClosed_def, hα]
  exact mextDeriv_mextDeriv_ofFunction (hh.of_le (by simp))

/-- **The graph of a one-form is exact Lagrangian for some primitive exactly when the form is
exact.** On a finite-dimensional manifold, the pulled-back Liouville form on the graph of a smooth
one-form `α` has a smooth primitive making the graph an exact Lagrangian map if and only if `α` is
an exact form. -/
theorem exists_isExactLagrangianMap_section_iff (α : SmoothForm I M ℝ 1) :
    (∃ h : M → ℝ,
      (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsExactLagrangianMap I
        (liouvilleForm I M)
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x)) h) ↔
      α ∈ exactForms I M 1 := by
  simp only [isExactLagrangianMap_section_iff, exactForms_succ, LinearMap.mem_range]
  refine ⟨fun ⟨h, hh, hα⟩ ↦ ⟨⟨RoughForm.ofFunction I h,
    (isSmoothForm_ofFunction_iff.mpr hh).mem_smoothBundleForms⟩, Subtype.ext ?_⟩,
    fun ⟨g, hg⟩ ↦ ⟨fun x ↦ g.1 x 0, ?_, ?_⟩⟩
  · rw [mextDerivₗ_apply, hα]
  · rw [← isSmoothForm_ofFunction_iff, ← RoughForm.eq_ofFunction, isSmoothForm_def]
    exact g.contMDiff
  · rw [← hg, mextDerivₗ_apply, ← RoughForm.eq_ofFunction]

/-- **The zero section is exact Lagrangian.** On a finite-dimensional manifold, the zero section of
the cotangent bundle is an exact Lagrangian map for the primitive `λ` of `ω = -dλ`, with primitive
`0`, since `λ` vanishes along it. -/
theorem isExactLagrangianMap_zeroSection :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsExactLagrangianMap I
      (liouvilleForm I M) (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) 0 := by
  have h := (isExactLagrangianMap_section_iff (0 : SmoothForm I M ℝ 1) (h := 0)).mpr
    ⟨contMDiff_const, ?_⟩
  · -- The section of the zero one-form is the zero section.
    convert h using 2 with x
    simp [zeroSection]
  · funext x
    ext v
    simp [mextDeriv_ofFunction]

end CotangentBundle

end TauCeti
