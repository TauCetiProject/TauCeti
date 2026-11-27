/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.StarOrdered
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.CStarAlgebra.Module.Complemented.Basic

import Mathlib.Topology.Perfect
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Analysis.CStarAlgebra.Module.Action

/-!
# Non-complemented closed right ideals in `C(X, ℂ)` and `C([0, 1], ℂ)`

Unlike in Hilbert spaces, a closed C⋆-submodule `J` of a complete Hilbert C⋆-module need not be
orthogonally complemented, nor even satisfy `J⊥⊥ = J`. This file verifies the standard
counterexample: for any compact Hausdorff space `X` and non-isolated point `x₀ : X` (in particular
`X = [0, 1]` and `x₀ = 0`), the closed right ideal
`TauCeti.CStarSubmodule.vanishingAt X x₀ = {f ∈ C(X, ℂ) | f x₀ = 0}` in the right self-module
`C(X, ℂ)` has orthogonal complement `⊥`, satisfies `J < J⊥⊥ = ⊤`, is not orthogonally
complemented, and its subtype inclusion admits no C⋆-module adjoint.

## Main declarations

* `TauCeti.CStarSubmodule.vanishingAt`: the closed right ideal `{f ∈ C(X, ℂ) | f x₀ = 0}` as a
  `CStarSubmodule C(X, ℂ)ᵐᵒᵖ C(X, ℂ)`.
* `TauCeti.CStarSubmodule.orthogonal_vanishingAt`,
  `TauCeti.CStarSubmodule.lt_orthogonal_orthogonal_vanishingAt`,
  `TauCeti.CStarSubmodule.not_isOrthogonallyComplemented_vanishingAt`,
  `TauCeti.CStarSubmodule.not_exists_adjoint_subtype_vanishingAt`: failure of double-orthogonal
  reflexivity, orthogonal complementability, and adjointability of the inclusion.
* `TauCeti.CStarSubmodule.lt_orthogonal_orthogonal_vanishingAt_unitInterval`,
  `TauCeti.CStarSubmodule.not_isOrthogonallyComplemented_vanishingAt_unitInterval`,
  `TauCeti.CStarSubmodule.not_exists_adjoint_subtype_vanishingAt_unitInterval`: specialization to
  `X = [0, 1]` at `0`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1 and
  Chapter 3.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite

namespace TauCeti.CStarSubmodule

section ContinuousMapCounterexample

open ComplexOrder

private lemma vanishingAt_mul_mem {X : Type*} [TopologicalSpace X] (x₀ : X)
    {f : C(X, ℂ)} (hf : f ∈ (ContinuousMap.idealOfSet ℂ ({x₀}ᶜ : Set X)).restrictScalars ℂ)
    (g : C(X, ℂ)) :
    f * g ∈ (ContinuousMap.idealOfSet ℂ ({x₀}ᶜ : Set X)).restrictScalars ℂ :=
  (Submodule.restrictScalars_mem ℂ _ _).mpr
    ((ContinuousMap.idealOfSet ℂ ({x₀}ᶜ : Set X)).mul_mem_right g
      ((Submodule.restrictScalars_mem ℂ _ _).mp hf))

/-- The right ideal `{f ∈ C(X, ℂ) | f x₀ = 0}` of continuous complex-valued functions vanishing at
`x₀`, viewed as a C⋆-submodule of the right self-module `C(X, ℂ)`. -/
noncomputable def vanishingAt (X : Type*) [TopologicalSpace X] (x₀ : X) :
    CStarSubmodule C(X, ℂ)ᵐᵒᵖ C(X, ℂ) :=
  ofRightIdeal ((ContinuousMap.idealOfSet ℂ ({x₀}ᶜ : Set X)).restrictScalars ℂ)
    (vanishingAt_mul_mem x₀)

@[simp]
theorem mem_vanishingAt {X : Type*} [TopologicalSpace X] {x₀ : X} {f : C(X, ℂ)} :
    f ∈ vanishingAt X x₀ ↔ f x₀ = 0 := by
  rw [vanishingAt, mem_ofRightIdeal _ (vanishingAt_mul_mem x₀), Submodule.restrictScalars_mem,
    ContinuousMap.mem_idealOfSet_compl_singleton]

theorem isClosed_vanishingAt {X : Type*} [TopologicalSpace X] (x₀ : X) :
    IsClosed (vanishingAt X x₀ : Set C(X, ℂ)) := by
  rw [vanishingAt, ← coe_toSubmodule, toSubmodule_ofRightIdeal _ (vanishingAt_mul_mem x₀),
    Submodule.coe_restrictScalars]
  exact ContinuousMap.idealOfSet_closed ℂ ({x₀}ᶜ : Set X)

theorem vanishingAt_ne_top (X : Type*) [TopologicalSpace X] (x₀ : X) :
    vanishingAt X x₀ ≠ ⊤ := by
  intro h
  have h1 : (1 : C(X, ℂ)) ∈ vanishingAt X x₀ := h ▸ mem_top 1
  rw [mem_vanishingAt, ContinuousMap.one_apply] at h1
  exact one_ne_zero h1

/-- If `X` is compact Hausdorff and `{x₀}ᶜ` is dense (i.e. `x₀` is not isolated), then the closed
right ideal `vanishingAt X x₀` has orthogonal complement `⊥` in `C(X, ℂ)`. -/
theorem orthogonal_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    (vanishingAt X x₀).orthogonal = ⊥ := by
  let _ := CStarModule.distribSMul C(X, ℂ)ᵐᵒᵖ C(X, ℂ)
  rw [eq_bot_iff]
  intro g hg
  have hzero : Set.EqOn g (0 : C(X, ℂ)) ({x₀}ᶜ : Set X) := by
    intro y hy
    have hne : x₀ ≠ y := Ne.symm (Set.mem_compl_singleton_iff.mp hy)
    obtain ⟨φ, hφ0, hφ1, _⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x₀)) (isClosed_singleton (x := y))
      (Set.disjoint_singleton.mpr hne)
    let f : C(X, ℂ) := ⟨fun x ↦ (φ x : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩
    have hf : f ∈ vanishingAt X x₀ := by
      rw [mem_vanishingAt]
      simp [f, hφ0 rfl]
    have hprod := (mem_orthogonal_unop_iff.mp hg) f hf
    rw [CStarModule.unop_inner_mulOpposite] at hprod
    have hfy : f y = 1 := by simp [f, hφ1 rfl]
    have hmul : (star f * g) y = g y := by
      rw [ContinuousMap.mul_apply, ContinuousMap.star_apply, hfy, star_one, one_mul]
    have hval := congrArg (fun h : C(X, ℂ) ↦ h y) hprod
    rw [hmul, ContinuousMap.zero_apply] at hval
    exact hval
  exact ContinuousMap.ext fun x ↦ hzero.closure g.continuous continuous_const (hx₀ x)

theorem orthogonal_orthogonal_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    (vanishingAt X x₀).orthogonal.orthogonal = ⊤ := by
  rw [orthogonal_vanishingAt hx₀, orthogonal_bot]

/-- For any compact Hausdorff space `X` and non-isolated point `x₀`, the closed right ideal
`vanishingAt X x₀` is strictly smaller than its double orthogonal complement `⊤`. -/
theorem lt_orthogonal_orthogonal_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    vanishingAt X x₀ < (vanishingAt X x₀).orthogonal.orthogonal := by
  rw [orthogonal_orthogonal_vanishingAt hx₀]
  exact lt_top_iff_ne_top.mpr (vanishingAt_ne_top X x₀)

/-- For any compact Hausdorff space `X` and non-isolated point `x₀`, the closed right ideal
`vanishingAt X x₀` is not orthogonally complemented in `C(X, ℂ)`. -/
theorem not_isOrthogonallyComplemented_vanishingAt {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    ¬ (vanishingAt X x₀).IsOrthogonallyComplemented := by
  intro h
  exact (lt_orthogonal_orthogonal_vanishingAt hx₀).ne h.orthogonal_orthogonal.symm

/-- For any compact Hausdorff space `X` and non-isolated point `x₀`, the inclusion of the closed
right ideal `vanishingAt X x₀` into `C(X, ℂ)` has no C⋆-module adjoint. -/
theorem not_exists_adjoint_subtype_vanishingAt {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {x₀ : X} (hx₀ : Dense ({x₀}ᶜ : Set X)) :
    ¬ ∃ P : C(X, ℂ) → vanishingAt X x₀,
      LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := C(X, ℂ)ᵐᵒᵖ) (E := vanishingAt X x₀)).flip
        (CStarModule.innerₛₗ (A := C(X, ℂ)ᵐᵒᵖ) (E := C(X, ℂ))).flip
        (vanishingAt X x₀).subtype P := by
  rw [← isOrthogonallyComplemented_iff_exists_adjoint_subtype]
  exact not_isOrthogonallyComplemented_vanishingAt hx₀

/-- The closed right ideal `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` is strictly contained in `J⊥⊥ = ⊤`. -/
theorem lt_orthogonal_orthogonal_vanishingAt_unitInterval :
    vanishingAt unitInterval 0 < (vanishingAt unitInterval 0).orthogonal.orthogonal :=
  lt_orthogonal_orthogonal_vanishingAt (dense_compl_singleton (0 : unitInterval))

/-- The closed right ideal `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` is closed yet not orthogonally
complemented in `C([0, 1], ℂ)`. -/
theorem not_isOrthogonallyComplemented_vanishingAt_unitInterval :
    ¬ (vanishingAt unitInterval 0).IsOrthogonallyComplemented :=
  not_isOrthogonallyComplemented_vanishingAt (dense_compl_singleton (0 : unitInterval))

/-- The subtype inclusion of `J = {f ∈ C([0, 1], ℂ) | f 0 = 0}` into `C([0, 1], ℂ)` admits no
C⋆-module adjoint. -/
theorem not_exists_adjoint_subtype_vanishingAt_unitInterval :
    ¬ ∃ P : C(unitInterval, ℂ) → vanishingAt unitInterval 0,
      LinearMap.IsAdjointPair
        (CStarModule.innerₛₗ (A := C(unitInterval, ℂ)ᵐᵒᵖ) (E := vanishingAt unitInterval 0)).flip
        (CStarModule.innerₛₗ (A := C(unitInterval, ℂ)ᵐᵒᵖ) (E := C(unitInterval, ℂ))).flip
        (vanishingAt unitInterval 0).subtype P :=
  not_exists_adjoint_subtype_vanishingAt (dense_compl_singleton (0 : unitInterval))

end ContinuousMapCounterexample

end TauCeti.CStarSubmodule
