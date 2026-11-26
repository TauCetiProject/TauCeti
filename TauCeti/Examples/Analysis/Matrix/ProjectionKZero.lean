/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ProjectionKZero
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.UnitalComparison
public import Mathlib.Analysis.Complex.Basic

/-!
# Checks for the projection monoid and `K₀` of `ℂ`

The projection monoid `V(A)` compares matrix projections of different sizes through rectangular
matrices. For `A = ℂ` the `1 × 2` matrix `v = (1 0)` has `vᴴ v = diag(1, 0)` in `M₂(ℂ)` and
`v vᴴ = 1` in `M₁(ℂ)`, so `[diag(1, 0)] = [1]` in `V(ℂ)`, although the two matrices have
different sizes. The rank identifies `V(ℂ)` with `ℕ` and `K₀(ℂ)` with `ℤ`, with `[1ₙ] ↦ n`.
Over the zero algebra every matrix projection is zero, so `V(0)` and `K₀(0)` are trivial.

For the unital algebra `ℂ`, the forced unitization is `ℂ⁺ ≅ ℂ × ℂ`. Writing `K₀ᵖ(ℂ)` for the
projection `K₀`-group of `ℂ` itself, `K₀(ℂ⁺) ≅ K₀ᵖ(ℂ) × K₀(ℂ) ≅ ℤ²`, with the class of the unit of
`ℂ⁺` sent to `(1, 1)`; the augmentation induces the second projection, and its kernel `ℤ × 0`, the
`K₀`-group of `ℂ` defined through the unitization, is `K₀ᵖ(ℂ) ≅ ℤ`.
-/

public section

open Matrix Algebra

namespace TauCeti.ProjectionKZeroExample

/-- The projection `diag(1, 0)` in `M₂(ℂ)`. -/
def diagOneZero : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `diag(1, 0)` is a projection. -/
theorem isStarProjection_diagOneZero : IsStarProjection diagOneZero := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, diagOneZero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [IsSelfAdjoint, diagOneZero, star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The row `v = (1 0)` implements the equivalence of `diag(1, 0)` in `M₂(ℂ)` with `1` in
`M₁(ℂ)`: `vᴴ v = diag(1, 0)` and `v vᴴ = 1`. -/
theorem isMurrayVonNeumannEquivalent_diagOneZero_one :
    IsMurrayVonNeumannEquivalent diagOneZero (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨isStarProjection_diagOneZero, .one _, !![1, 0], ?_, ?_⟩
  · rw [diagOneZero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`[diag(1, 0)] = [1]` in `V(ℂ)`.** The classes agree although the representatives have
different sizes. -/
theorem mk_diagOneZero :
    ProjectionMonoid.mk diagOneZero isStarProjection_diagOneZero =
      ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _) :=
  ProjectionMonoid.mk_eq_mk isMurrayVonNeumannEquivalent_diagOneZero_one

/-- Under the rank isomorphism `V(ℂ) ≃+ ℕ`, the class of `diag(1, 0)` maps to `1`. -/
theorem rankAddEquiv_mk_diagOneZero :
    ProjectionMonoid.rankAddEquiv ℂ
      (ProjectionMonoid.mk diagOneZero isStarProjection_diagOneZero) = 1 := by
  rw [mk_diagOneZero, ProjectionMonoid.rankAddEquiv_mk, rank_one, Fintype.card_fin]

/-- Under the rank isomorphism `K₀(ℂ) ≃+ ℤ`, the class `[1ₙ]` maps to `n`. -/
example (n : ℕ) :
    ProjectionKZero.rankAddEquiv ℂ (GrothendieckAddGroup.of
      (ProjectionMonoid.mk (1 : Matrix (Fin n) (Fin n) ℂ) (.one _))) = n :=
  ProjectionKZero.rankAddEquiv_of_mk_one ℂ n

/-- In `K₀(ℂ)` the class `[1ₙ]` is `n` times the class of the identity of size one. -/
theorem of_mk_one_eq_nsmul (n : ℕ) :
    (GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin n) (Fin n) ℂ) (.one _)) :
        ProjectionKZero ℂ) =
      n • GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _)) :=
  by rw [ProjectionMonoid.mk_one, Fintype.card_fin, map_nsmul]

/-- Over the zero algebra `Fin 0 → ℂ` the projection monoid is trivial. -/
example : Subsingleton (ProjectionMonoid (Fin 0 → ℂ)) := inferInstance

/-- Over the zero algebra `Fin 0 → ℂ` the projection `K₀`-group is trivial. -/
example : Subsingleton (ProjectionKZero (Fin 0 → ℂ)) := inferInstance

/-- `K₀(ℂ⁺) ≅ ℤ²`, through the splitting `ℂ⁺ ≅ ℂ × ℂ` and the rank. -/
noncomputable def kZeroUnitizationEquiv : ProjectionKZero (Unitization ℂ ℂ) ≃+ ℤ × ℤ :=
  (UnitizationKZero.unitalProdEquiv ℂ ℂ).trans
    ((ProjectionKZero.rankAddEquiv ℂ).prodCongr (ProjectionKZero.rankAddEquiv ℂ))

/-- `K₀(ℂ⁺) ≅ ℤ²` is the rank on each component of `K₀(ℂ⁺) ≅ K₀ᵖ(ℂ) × K₀(ℂ)`. -/
theorem kZeroUnitizationEquiv_apply (x : ProjectionKZero (Unitization ℂ ℂ)) :
    kZeroUnitizationEquiv x =
      (ProjectionKZero.rankAddEquiv ℂ (UnitizationKZero.unitalProdEquiv ℂ ℂ x).1,
        ProjectionKZero.rankAddEquiv ℂ (UnitizationKZero.unitalProdEquiv ℂ ℂ x).2) :=
  (rfl)

/-- Under `K₀(ℂ⁺) ≅ ℤ²` the class of the unit of `ℂ⁺` is `(1, 1)`. -/
example : kZeroUnitizationEquiv (GrothendieckAddGroup.of
    (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) (Unitization ℂ ℂ)) (.one _))) = (1, 1) := by
  rw [kZeroUnitizationEquiv_apply, UnitizationKZero.unitalProdEquiv_apply,
    ProjectionKZero.map_of_mk, ProjectionKZero.prodEquiv_of_mk,
    ProjectionKZero.rankAddEquiv_of_mk, ProjectionKZero.rankAddEquiv_of_mk]
  simp [Matrix.map_one]

/-- Under `K₀(ℂ⁺) ≅ ℤ²` the homomorphism induced by the augmentation `ε : ℂ⁺ → ℂ` is the second
projection. -/
example (x : ProjectionKZero (Unitization ℂ ℂ)) :
    ProjectionKZero.rankAddEquiv ℂ (UnitizationKZero.augmentation ℂ ℂ x) =
      (kZeroUnitizationEquiv x).2 := by
  rw [kZeroUnitizationEquiv_apply, UnitizationKZero.unitalProdEquiv_apply_snd]

/-- The kernel of `K₀(ε)`, the `K₀`-group of `ℂ` through its unitization, is `ℤ`. -/
noncomputable example : UnitizationKZero ℂ ℂ ≃+ ℤ :=
  (UnitizationKZero.unitalEquiv ℂ ℂ).trans (ProjectionKZero.rankAddEquiv ℂ)

end TauCeti.ProjectionKZeroExample
