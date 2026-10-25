/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# De Rham cohomology in degree zero

A `0`-form is a function, and its exterior derivative is the differential of that function.
A differentiable function has zero differential exactly when it is locally constant, so the
closed smooth `0`-forms are the locally constant real functions. Since there are no exact forms
in degree zero, this identifies `H⁰_dR(M)` with `LocallyConstant M ℝ`; on a connected manifold
it is one-dimensional.

On a preconnected noncompact manifold a locally constant function is constant, and a nonzero
constant does not have compact support, so compactly supported cohomology `H⁰_c(M)` vanishes.

Everything holds on `C²` manifolds with boundary or corners, without finite dimensionality,
separation or completeness hypotheses on the model.

## Main declarations

* `TauCeti.mem_closedForms_zero_iff`: a smooth `0`-form is closed exactly when its
  function is locally constant.
* `TauCeti.closedFormsZeroEquiv`: closed smooth `0`-forms are locally constant functions.
* `TauCeti.deRhamCohomologyZeroEquiv`: `H⁰_dR(M) ≃ₗ[ℝ] LocallyConstant M ℝ`.
* `TauCeti.finrank_deRhamCohomology_zero`: `H⁰_dR(M)` has dimension one when `M` is connected.
* `TauCeti.subsingleton_compactlySupportedDeRhamCohomology_zero`: `H⁰_c(M) = 0` when `M` is
  preconnected and noncompact.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, cohomology in
  degree zero, and section *Cohomology with Compact Support*.
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- A smooth real `0`-form is closed exactly when its function is locally constant. -/
theorem mem_closedForms_zero_iff (φ : SmoothForm I M ℝ 0) :
    φ ∈ closedForms I M 0 ↔ IsLocallyConstant fun x ↦ φ.1 x 0 := by
  have hφ : IsSmoothForm I ∞ (RoughForm.ofFunction I fun x ↦ φ.1 x 0) := by
    rw [← RoughForm.eq_ofFunction, isSmoothForm_def]
    exact φ.contMDiff
  have h := mextDeriv_ofFunction_eq_zero_iff
    ((isSmoothForm_ofFunction_iff.mp hφ).mdifferentiable (by simp))
  rwa [← RoughForm.eq_ofFunction, ← mem_closedForms] at h

variable (M) in
/-- Closed smooth real `0`-forms are exactly the locally constant real functions. -/
def closedFormsZeroEquiv : closedForms I M 0 ≃ₗ[ℝ] LocallyConstant M ℝ where
  toFun φ := ⟨fun x ↦ φ.1.1 x 0, (mem_closedForms_zero_iff I φ.1).mp φ.2⟩
  invFun f := ⟨⟨RoughForm.ofFunction I f,
      (isSmoothForm_ofFunction_iff.mpr fun x ↦ contMDiffAt_const.congr_of_eventuallyEq
        ((IsLocallyConstant.iff_eventually_eq f).mp f.isLocallyConstant x)).mem_smoothForms⟩,
    (mem_closedForms_zero_iff I _).mpr <| by
      simp only [RoughForm.ofFunction_apply]
      exact f.isLocallyConstant⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| Subtype.ext (RoughForm.eq_ofFunction φ.1.1).symm
  right_inv f := LocallyConstant.ext fun x ↦ RoughForm.ofFunction_apply (I := I) (f := ⇑f) x 0

/-- The locally constant function of a closed `0`-form is its value on the empty tuple. -/
@[simp]
theorem closedFormsZeroEquiv_apply (φ : closedForms I M 0) (x : M) :
    closedFormsZeroEquiv I M φ x = φ.1.1 x 0 := by
  rw [closedFormsZeroEquiv]
  rfl

/-- The closed `0`-form of a locally constant function is its `0`-form. -/
@[simp]
theorem coe_closedFormsZeroEquiv_symm_apply (f : LocallyConstant M ℝ) :
    ((closedFormsZeroEquiv I M).symm f).1.1 = RoughForm.ofFunction I f := by
  rw [closedFormsZeroEquiv]
  rfl

/-- In degree zero the cycle-class map is injective, since there are no exact `0`-forms. -/
theorem deRhamCohomology.mk_zero_injective :
    Function.Injective (deRhamCohomology.mk I (M := M) 0) := by
  refine (injective_iff_map_eq_zero _).mpr fun φ hφ ↦ ?_
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_zero, Submodule.mem_bot] at hφ
  exact Subtype.ext hφ

variable (M) in
/-- **Degree-zero de Rham cohomology.** `H⁰_dR(M)` is the space of locally constant real
functions on `M`, for any `C²` manifold with boundary or corners. -/
def deRhamCohomologyZeroEquiv : deRhamCohomology I M 0 ≃ₗ[ℝ] LocallyConstant M ℝ :=
  (LinearEquiv.ofBijective (deRhamCohomology.mk I 0)
    ⟨deRhamCohomology.mk_zero_injective I, deRhamCohomology.mk_surjective I 0⟩).symm ≪≫ₗ
    closedFormsZeroEquiv I M

/-- The class of a closed `0`-form corresponds to its locally constant function. -/
@[simp]
theorem deRhamCohomologyZeroEquiv_mk (φ : closedForms I M 0) (x : M) :
    deRhamCohomologyZeroEquiv I M (deRhamCohomology.mk I 0 φ) x = φ.1.1 x 0 := by
  rw [deRhamCohomologyZeroEquiv, LinearEquiv.trans_apply, ← closedFormsZeroEquiv_apply]
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  exact (LinearEquiv.ofBijective_apply _ _).symm

/-- A locally constant function corresponds to the class of its `0`-form. -/
@[simp]
theorem deRhamCohomologyZeroEquiv_symm_apply (f : LocallyConstant M ℝ) :
    (deRhamCohomologyZeroEquiv I M).symm f =
      deRhamCohomology.mk I 0 ((closedFormsZeroEquiv I M).symm f) := by
  rw [deRhamCohomologyZeroEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
  exact LinearEquiv.ofBijective_apply _ _

variable (M) in
/-- On a connected manifold, degree-zero de Rham cohomology is one-dimensional. -/
theorem finrank_deRhamCohomology_zero [ConnectedSpace M] :
    Module.finrank ℝ (deRhamCohomology I M 0) = 1 := by
  have hconst : Function.Bijective (LocallyConstant.constₗ (X := M) ℝ (Y := ℝ)) := by
    refine ⟨fun a b hab ↦ ?_, fun f ↦ ?_⟩
    · obtain ⟨x⟩ := ‹ConnectedSpace M›.toNonempty
      simpa using DFunLike.congr_fun hab x
    · obtain ⟨a, ha⟩ := f.exists_eq_const
      exact ⟨a, ha.symm⟩
  rw [(deRhamCohomologyZeroEquiv I M ≪≫ₗ (LinearEquiv.ofBijective _ hconst).symm).finrank_eq,
    Module.finrank_self]

/-- On a preconnected noncompact manifold, the only compactly supported closed `0`-form is zero:
its function is locally constant, hence constant, and a nonzero constant function on a noncompact
space does not have compact support. -/
theorem eq_zero_of_mem_compactlySupportedClosedForms_zero [PreconnectedSpace M]
    [NoncompactSpace M] {φ : SmoothForm I M ℝ 0}
    (hφ : φ ∈ compactlySupportedClosedForms I M 0) : φ = 0 := by
  rw [mem_compactlySupportedClosedForms, mem_compactlySupportedForms] at hφ
  obtain ⟨c, hc⟩ := ((mem_closedForms_zero_iff I φ).mp hφ.2).exists_eq_const
  have hφc (x : M) : φ.1 x 0 = c := congrFun hc x
  obtain rfl | h0 := eq_or_ne c 0
  · refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    rw [Subsingleton.elim v 0, hφc]
    simp
  · refine absurd (hφ.1.of_isClosed_subset isClosed_univ fun x _ ↦ ?_) (noncompact_univ M)
    refine subset_tsupport _ fun h ↦ h0 ?_
    rw [← hφc x, h]
    -- The support of a form is taken with the zero of the model fibre `E [⋀^Fin 0]→L[ℝ] ℝ`,
    -- which is not syntactically the zero of the tangent fibre that `coe_zero` rewrites.
    rfl

variable (M) in
/-- **Compactly supported cohomology in degree zero.** On a preconnected noncompact manifold,
`H⁰_c(M)` vanishes. -/
theorem subsingleton_compactlySupportedDeRhamCohomology_zero [PreconnectedSpace M]
    [NoncompactSpace M] : Subsingleton (compactlySupportedDeRhamCohomology I M 0) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I 0 c
  rw [show φ = 0 from Subtype.ext (eq_zero_of_mem_compactlySupportedClosedForms_zero I φ.2),
    map_zero]

end TauCeti
