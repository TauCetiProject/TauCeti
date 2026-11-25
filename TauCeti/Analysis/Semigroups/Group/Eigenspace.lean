/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.PhaseShift.Basic
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Common fixed subspaces and eigenspaces of a strongly continuous group

For any strongly continuous group `U` on a real normed space `X`, the common fixed space
`{x | ∀ t : ℝ, U t x = x}` (`fixedSpace`) is a closed real submodule invariant under time
reversal.

For a complex-linear strongly continuous group `U` on a complex normed space `X`, the common fixed
subspace `{x | ∀ t : ℝ, U t x = x}` (`fixedSubmodule`) and the common eigenspace
`{x | ∀ t : ℝ, U t x = exp (ω * t * I) • x}` (`eigenspace`) at any angular frequency `ω : ℝ` are
closed complex submodules; `eigenspace` at `ω` is the fixed subspace of the phase shift
`U.phaseShift hU ω`.

On complete real and complex Hilbert spaces, these subspaces admit orthogonal projections.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.fixedSpace`: the closed real submodule of vectors
  fixed by `U t` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.fixedSubmodule`: the closed complex submodule of
  vectors fixed by `U t` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace`: the closed complex submodule of vectors
  satisfying `U t x = exp (ω * t * I) • x` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace_eq_fixedSubmodule_phaseShift`: `eigenspace`
  at `ω` equals the common fixed subspace of `U.phaseShift hU ω`.
* `TauCeti.Semigroups.StronglyContinuousGroup.reflect_fixedSpace`,
  `TauCeti.Semigroups.StronglyContinuousGroup.reflect_eigenspace`, and
  `TauCeti.Semigroups.StronglyContinuousGroup.phaseShift_eigenspace`: behavior of fixed spaces and
  eigenspaces under time reversal and phase shifts.
* `TauCeti.Semigroups.StronglyContinuousGroup.isClosed_fixedSpace`,
  `TauCeti.Semigroups.StronglyContinuousGroup.isClosed_fixedSubmodule`, and
  `TauCeti.Semigroups.StronglyContinuousGroup.isClosed_eigenspace`: closedness of the fixed
  subspaces and eigenspaces.
* `TauCeti.Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_fixedSpace`,
  `TauCeti.Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_fixedSubmodule`, and
  `TauCeti.Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_eigenspace`: orthogonal
  projection instances on complete Hilbert spaces.
-/

public section

noncomputable section

namespace TauCeti.Semigroups.StronglyContinuousGroup

section RealFixedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The real submodule of vectors fixed by every operator `U t` of a C₀-group. -/
def fixedSpace (U : StronglyContinuousGroup X) : Submodule ℝ X :=
  ⨅ t : ℝ, LinearMap.fixedSubmodule (U t).toLinearMap

/-- Membership in `fixedSpace` means being fixed by `U t` at every real time `t`. -/
@[simp]
theorem mem_fixedSpace_iff (U : StronglyContinuousGroup X) (x : X) :
    x ∈ U.fixedSpace ↔ ∀ t : ℝ, U t x = x := by
  simp [fixedSpace, LinearMap.mem_fixedSubmodule_iff]

/-- The common fixed space of a C₀-group is closed. -/
theorem isClosed_fixedSpace (U : StronglyContinuousGroup X) :
    IsClosed (U.fixedSpace : Set X) := by
  have hcar : (U.fixedSpace : Set X) = ⋂ t : ℝ, {x : X | U t x = x} := by
    ext x
    simp
  rw [hcar]
  exact isClosed_iInter fun t ↦ isClosed_eq (U t).continuous continuous_id

/-- Time reversal preserves the common fixed space. -/
@[simp]
theorem reflect_fixedSpace (U : StronglyContinuousGroup X) :
    U.reflect.fixedSpace = U.fixedSpace := by
  ext x
  simp only [mem_fixedSpace_iff, reflect_apply]
  exact ⟨fun h t ↦ by simpa only [neg_neg] using h (-t), fun h t ↦ h (-t)⟩

end RealFixedSpace

section FixedAndEigenspace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The complex submodule of vectors fixed by every operator `U t` of a complex-linear C₀-group. -/
def fixedSubmodule (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    Submodule ℂ X :=
  ⨅ t : ℝ, LinearMap.fixedSubmodule
    { toFun := U t
      map_add' := (U t).map_add
      map_smul' := U.map_smul_of_isComplexLinear hU t }

/-- Membership in `fixedSubmodule` means being fixed by `U t` at every real time `t`. -/
@[simp]
theorem mem_fixedSubmodule_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (x : X) :
    x ∈ U.fixedSubmodule hU ↔ ∀ t : ℝ, U t x = x := by
  simp [fixedSubmodule, LinearMap.mem_fixedSubmodule_iff]

/-- Restricting scalars to `ℝ` identifies the complex fixed submodule with `U.fixedSpace`. -/
@[simp]
theorem fixedSubmodule_restrictScalars (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    (U.fixedSubmodule hU).restrictScalars ℝ = U.fixedSpace := by
  ext x
  simp

/-- The common fixed subspace of a complex-linear C₀-group is closed. -/
theorem isClosed_fixedSubmodule (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    IsClosed (U.fixedSubmodule hU : Set X) := by
  have hcar : (U.fixedSubmodule hU : Set X) = ⋂ t : ℝ, {x : X | U t x = x} := by
    ext x
    simp
  rw [hcar]
  exact isClosed_iInter fun t ↦ isClosed_eq (U t).continuous continuous_id

/-- The common eigenspace at angular frequency `ω : ℝ` of a complex-linear C₀-group: the complex
submodule of vectors satisfying `U t x = exp (ω * t * I) • x` for every `t : ℝ`. -/
def eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    Submodule ℂ X :=
  (U.phaseShift hU ω).fixedSubmodule (U.isComplexLinear_phaseShift hU ω)

/-- The common eigenspace at frequency `ω` is the common fixed subspace of the phase-shifted group
`U.phaseShift hU ω`. -/
theorem eigenspace_eq_fixedSubmodule_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    U.eigenspace hU ω =
      (U.phaseShift hU ω).fixedSubmodule (U.isComplexLinear_phaseShift hU ω) := by
  rw [eigenspace]

/-- Restricting scalars to `ℝ` identifies the common eigenspace at frequency `ω` with the common
fixed space of the phase-shifted group `U.phaseShift hU ω`. -/
theorem eigenspace_restrictScalars (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.eigenspace hU ω).restrictScalars ℝ = (U.phaseShift hU ω).fixedSpace := by
  rw [eigenspace_eq_fixedSubmodule_phaseShift, fixedSubmodule_restrictScalars]

/-- Membership in `eigenspace` at frequency `ω` means `U t x = exp (ω * t * I) • x` for every
`t : ℝ`. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) (x : X) :
    x ∈ U.eigenspace hU ω ↔ ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x := by
  rw [eigenspace_eq_fixedSubmodule_phaseShift, mem_fixedSubmodule_iff]
  refine forall_congr' fun t ↦ ?_
  rw [phaseShift_apply_apply, neg_mul, Complex.exp_neg, inv_smul_eq_iff₀ (Complex.exp_ne_zero _)]

/-- The common eigenspace at frequency `0` is the common fixed subspace. -/
@[simp]
theorem eigenspace_zero (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    U.eigenspace hU 0 = U.fixedSubmodule hU := by
  ext x
  simp

/-- Time reversal negates the eigenfrequency of every common eigenspace. -/
@[simp]
theorem reflect_eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    U.reflect.eigenspace (U.reflect_isComplexLinear hU) ω = U.eigenspace hU (-ω) := by
  ext x
  simp only [mem_eigenspace_iff, reflect_apply]
  refine ⟨fun h t ↦ ?_, fun h t ↦ ?_⟩
  · simpa only [neg_neg, Complex.ofReal_neg, neg_mul, mul_neg] using h (-t)
  · simpa only [Complex.ofReal_neg, neg_mul, mul_neg, neg_neg] using h (-t)

/-- Phase shifting by `b` shifts the eigenfrequencies by `b`. -/
@[simp]
theorem phaseShift_eigenspace (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b ω : ℝ) :
    (U.phaseShift hU b).eigenspace (U.isComplexLinear_phaseShift hU b) ω =
      U.eigenspace hU (b + ω) := by
  apply Submodule.restrictScalars_injective ℝ
  rw [eigenspace_restrictScalars, eigenspace_restrictScalars, phaseShift_phaseShift]

/-- The common eigenspace at any angular frequency `ω` is closed. -/
theorem isClosed_eigenspace (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    IsClosed (U.eigenspace hU ω : Set X) :=
  isClosed_fixedSubmodule _ _

end FixedAndEigenspace

section Projection

/-- The common fixed space of a C₀-group on a complete real Hilbert space admits an orthogonal
projection. -/
instance hasOrthogonalProjection_fixedSpace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : StronglyContinuousGroup H) :
    U.fixedSpace.HasOrthogonalProjection :=
  have := U.isClosed_fixedSpace.completeSpace_coe
  inferInstance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The common fixed subspace of a complex-linear C₀-group on a complete complex Hilbert space
admits an orthogonal projection. -/
instance hasOrthogonalProjection_fixedSubmodule [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) : (U.fixedSubmodule hU).HasOrthogonalProjection :=
  have := (U.isClosed_fixedSubmodule hU).completeSpace_coe
  inferInstance

/-- The common eigenspace at frequency `ω` of a complex-linear C₀-group on a complete complex
Hilbert space admits an orthogonal projection. -/
instance hasOrthogonalProjection_eigenspace [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.eigenspace hU ω).HasOrthogonalProjection :=
  hasOrthogonalProjection_fixedSubmodule (U.phaseShift hU ω) (U.isComplexLinear_phaseShift hU ω)

end Projection

end TauCeti.Semigroups.StronglyContinuousGroup

end
