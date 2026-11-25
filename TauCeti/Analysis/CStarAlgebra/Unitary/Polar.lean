/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent

/-!
# The polar retraction of invertible elements onto unitaries

For an invertible element `x` of a unital C⋆-algebra `A`, main's `Units.polarUnitary x` is the
unitary factor `u` of the polar decomposition `x = u |x|`, `|x| = √(x⋆x)`
(`TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`). This file shows
that `u` is joined to `x` by a path of invertible elements (`TauCeti.joined_polarUnitary`):
`t ↦ u ((1 - t)|x| + t)` stays invertible, since `(1 - t)|x| + t` is strictly positive for
`t ∈ [0, 1]`.

Applied to the C⋆-algebras `CStarMatrix (Fin n) (Fin n) A`, this is the polar deformation of
OperatorKTheory K2.1: every invertible matrix over `A` is joined in `GLₙ(A)` to a unitary matrix,
so every class of the stable component group `π₀ GL_∞(A)` is the class of a unitary matrix
(`TauCeti.StableComponentGroup.exists_mk_eq_of_mem_unitary`). The roadmap's Check that the polar
deformation sends the invertible `2 ∈ ℂ` to the unitary `1` is `TauCeti.polarUnitary_two_complex`.

## Main definitions

* `TauCeti.GeneralLinearGroup.toCStarMatrixUnits`: invertible matrices over `A` as invertible
  elements of the C⋆-algebra `CStarMatrix (Fin n) (Fin n) A`.

## Main results

* `TauCeti.joined_polarUnitary`: `x` and its polar unitary lie in one path component of `Aˣ`.
* `TauCeti.GeneralLinearGroup.exists_mem_unitary_joined`: every invertible matrix is joined in
  `GLₙ(A)` to a unitary matrix.
* `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`,
  `TauCeti.StableComponentGroup.exists_mk_eq_of_mem_unitary`: unitary matrices represent every
  class of the stable component group.
-/

public section

noncomputable section

namespace TauCeti

section Polar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The straight-line interpolation `(1 - t) a + t` between a strictly positive `a` and `1` is
strictly positive for `t ∈ [0, 1]`. -/
theorem isStrictlyPositive_lineMap_one {a : A} (ha : IsStrictlyPositive a) (t : unitInterval) :
    IsStrictlyPositive ((1 - (t : ℝ)) • a + (t : ℝ) • (1 : A)) := by
  obtain ⟨t, ht₀, ht₁⟩ := t
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simpa using ha
  · exact isStrictlyPositive_add <| .inr ⟨smul_nonneg (by simpa using ht₁) ha.nonneg,
      IsStrictlyPositive.smul ht₀ isStrictlyPositive_one⟩

/-- An invertible element of a unital C⋆-algebra is joined to its polar unitary by a path of
invertible elements: `t ↦ u ((1 - t)|x| + t)`. -/
theorem joined_polarUnitary (x : Aˣ) : Joined x (Unitary.toUnits x.polarUnitary) := by
  have ha := x.isStrictlyPositive_sqrt_star_mul
  let γ : unitInterval → A := fun t ↦
    (x.polarUnitary : A) * ((1 - (t : ℝ)) • CFC.sqrt (star (x : A) * x) + (t : ℝ) • 1)
  have hγ : ∀ t, IsUnit (γ t) := fun t ↦
    (Unitary.toUnits x.polarUnitary).isUnit.mul (isStrictlyPositive_lineMap_one ha t).isUnit
  refine ⟨⟨⟨fun t ↦ (hγ t).unit, ?_⟩, ?_, ?_⟩⟩
  · rw [Units.isOpenEmbedding_val.continuous_iff]
    change Continuous γ
    fun_prop
  · ext
    simp [γ]
  · ext
    simp [γ]

open scoped ComplexOrder in
/-- The polar deformation sends the invertible `2 ∈ ℂ` to the unitary `1`. -/
theorem polarUnitary_two_complex : (Units.mk0 (2 : ℂ) two_ne_zero).polarUnitary = 1 :=
  Units.polarUnitary_eq_one (by norm_num)

/-- Every invertible element of a unital C⋆-algebra is joined through invertible elements to a
unitary, namely its polar unitary. Stated without `Units.polarUnitary` so that it applies to
`CStarMatrix` without synthesizing a real functional calculus there. -/
theorem exists_unitary_joined (x : Aˣ) : ∃ v : unitary A, Joined x (Unitary.toUnits v) :=
  ⟨_, joined_polarUnitary x⟩

end Polar

/-! ## Invertible matrices -/

section Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {n : ℕ}

/-- In a topological group, an element joined to `y` differs from it by an element of the
identity component. -/
theorem inv_mul_mem_connectedComponentOfOne_of_joined {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {x y : G} (h : Joined x y) :
    x⁻¹ * y ∈ Subgroup.connectedComponentOfOne G := by
  have : Joined (1 : G) (x⁻¹ * y) := by
    simpa using h.map (continuous_const.mul continuous_id : Continuous fun z : G ↦ x⁻¹ * z)
  exact pathComponent_subset_component _ this

/-- The identification of invertible matrices over `A` with invertible elements of the
C⋆-algebra `CStarMatrix (Fin n) (Fin n) A`. -/
@[expose] def GeneralLinearGroup.toCStarMatrixUnits :
    GL (Fin n) A ≃* (CStarMatrix (Fin n) (Fin n) A)ˣ :=
  Units.mapEquiv CStarMatrix.ofMatrixRingEquiv.toMulEquiv

omit [PartialOrder A] [StarOrderedRing A] in
theorem GeneralLinearGroup.continuous_toCStarMatrixUnits_symm :
    Continuous (toCStarMatrixUnits (A := A) (n := n)).symm :=
  Continuous.units_map _ continuous_id

/-- Every invertible matrix over a unital C⋆-algebra is joined in `GLₙ(A)` to a unitary matrix,
its polar unitary computed in `CStarMatrix (Fin n) (Fin n) A`. -/
theorem GeneralLinearGroup.exists_mem_unitary_joined (u : GL (Fin n) A) :
    ∃ v : GL (Fin n) A,
      (v : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ Joined u v := by
  obtain ⟨w, hw⟩ := exists_unitary_joined (toCStarMatrixUnits u)
  exact ⟨toCStarMatrixUnits.symm (Unitary.toUnits w), w.prop,
    by simpa using hw.map continuous_toCStarMatrixUnits_symm⟩

/-- Every invertible matrix over a unital C⋆-algebra has the class in the stable component group
of a unitary matrix of the same size. -/
theorem StableComponentGroup.exists_mem_unitary_mk_eq (u : GL (Fin n) A) :
    ∃ v : GL (Fin n) A,
      (v : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧
        mk A n v = mk A n u := by
  obtain ⟨v, hv, h⟩ := GeneralLinearGroup.exists_mem_unitary_joined u
  exact ⟨v, hv, (mk_eq_mk_iff.mpr ⟨n, le_rfl, by
    simpa using inv_mul_mem_connectedComponentOfOne_of_joined h⟩).symm⟩

/-- Every class of the stable component group of a unital C⋆-algebra is the class of a unitary
matrix. -/
theorem StableComponentGroup.exists_mk_eq_of_mem_unitary (x : StableComponentGroup A) :
    ∃ n, ∃ u : GL (Fin n) A,
      (u : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ mk A n u = x := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  exact ⟨n, exists_mem_unitary_mk_eq u⟩

end Matrix

end TauCeti
