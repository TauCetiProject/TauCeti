/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Analysis.Semigroups.Group.PhaseShift
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Common fixed subspace and eigenspaces of a complex-linear C₀-group

For a complex-linear strongly continuous group `U` on a complex normed space `X`, the common fixed
subspace `{x | ∀ t : ℝ, U t x = x}` (`fixedSubmodule`) and the common eigenspace
`{x | ∀ t : ℝ, U t x = exp (ω * t * I) • x}` (`eigenspace`) at any angular frequency `ω : ℝ` are
closed complex submodules; `eigenspace` at `ω` is the fixed subspace of the phase shift
`U.phaseShift hU ω`.

On a complete complex Hilbert space, both submodules admit orthogonal projections.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousGroup.fixedSubmodule`: the closed complex submodule of
  vectors fixed by `U t` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace`: the closed complex submodule of vectors
  satisfying `U t x = exp (ω * t * I) • x` for every `t : ℝ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.eigenspace_eq_fixedSubmodule_phaseShift`: `eigenspace`
  at `ω` equals the common fixed subspace of `U.phaseShift hU ω`.
* `TauCeti.Semigroups.StronglyContinuousGroup.isClosed_fixedSubmodule` and
  `TauCeti.Semigroups.StronglyContinuousGroup.isClosed_eigenspace`: both submodules are closed.
* `TauCeti.Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_fixedSubmodule` and
  `TauCeti.Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_eigenspace`: orthogonal
  projection instances on a complete complex Hilbert space.
-/

public section

noncomputable section

namespace TauCeti.Semigroups.StronglyContinuousGroup

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

/-- The underlying set of `fixedSubmodule` is `{x | ∀ t : ℝ, U t x = x}`. -/
theorem coe_fixedSubmodule (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    (U.fixedSubmodule hU : Set X) = {x : X | ∀ t : ℝ, U t x = x} := by
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

/-- Membership in `eigenspace` at frequency `ω` means `U t x = exp (ω * t * I) • x` for every
`t : ℝ`. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) (x : X) :
    x ∈ U.eigenspace hU ω ↔ ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x := by
  rw [eigenspace_eq_fixedSubmodule_phaseShift, mem_fixedSubmodule_iff]
  simp only [phaseShift_apply_apply]
  refine forall_congr' fun t ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc U t x = Complex.exp ((ω * t : ℂ) * Complex.I) •
            (Complex.exp (-(ω * t : ℂ) * Complex.I) • U t x) := by
          rw [smul_smul, ← Complex.exp_add]
          have hexp : (ω * t : ℂ) * Complex.I + -(ω * t : ℂ) * Complex.I = 0 := by ring
          rw [hexp, Complex.exp_zero, one_smul]
      _ = Complex.exp (ω * t * Complex.I) • x := by rw [h]
  · rw [h, smul_smul, ← Complex.exp_add]
    have hexp : -(ω * t : ℂ) * Complex.I + ω * t * Complex.I = 0 := by ring
    rw [hexp, Complex.exp_zero, one_smul]

/-- The underlying set of `eigenspace` at `ω` is `{x | ∀ t : ℝ, U t x = exp (ω * t * I) • x}`. -/
theorem coe_eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    (U.eigenspace hU ω : Set X) =
      {x : X | ∀ t : ℝ, U t x = Complex.exp (ω * t * Complex.I) • x} := by
  ext x
  simp

/-- The common eigenspace at frequency `0` is the common fixed subspace. -/
@[simp]
theorem eigenspace_zero (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) :
    U.eigenspace hU 0 = U.fixedSubmodule hU := by
  ext x
  simp

/-- The common eigenspace at any angular frequency `ω` is closed. -/
theorem isClosed_eigenspace (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    IsClosed (U.eigenspace hU ω : Set X) :=
  isClosed_fixedSubmodule _ _

end FixedAndEigenspace

section Projection

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
