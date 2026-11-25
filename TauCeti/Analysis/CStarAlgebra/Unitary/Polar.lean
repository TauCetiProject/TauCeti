/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent

/-!
# The polar retraction of invertible elements onto unitaries

For an invertible element `x` of a unital C⋆-algebra `A`, `Units.polarUnitary x` is the unitary
factor `u` of the polar decomposition `x = u |x|`, `|x| = √(x⋆x)`
(`TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`). This file shows
that `u` is joined to `x` by a path of invertible elements (`Units.joined_polarUnitary`):
`t ↦ u ((1 - t)|x| + t)` stays invertible, since `(1 - t)|x| + t` is strictly positive for
`t ∈ [0, 1]`. This straight-line path has the same endpoints as the polar deformation
`t ↦ x (x⋆x)^(-t/2)`.

Applied to the C⋆-algebras `CStarMatrix n n A`, every invertible matrix over `A` is joined in
`GLₙ(A)` to a unitary matrix, so every class of the stable component group `π₀ GL_∞(A)` is the
class of a unitary matrix (`TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`). For example,
the polar unitary of the invertible `2 ∈ ℂ` is `1` (`TauCeti.polarUnitary_two_complex`).

## Main results

* `Units.joined_polarUnitary`: `x` and its polar unitary lie in one path component of `Aˣ`.
* `Matrix.GeneralLinearGroup.exists_mem_unitary_joined`: every invertible matrix is joined in
  `GLₙ(A)` to a unitary matrix.
* `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq_mk`,
  `TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`: unitary matrices represent every
  class of the stable component group.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), §2.1.
-/

public section

noncomputable section

section Polar

variable {A : Type*} [CStarAlgebra A]

/-- The straight-line interpolation `(1 - t) a + t` between a strictly positive `a` and `1` is
strictly positive for `t ∈ [0, 1]`. -/
theorem IsStrictlyPositive.one_sub_smul_add_smul_one [PartialOrder A] [StarOrderedRing A] {a : A}
    (ha : IsStrictlyPositive a) (t : unitInterval) :
    IsStrictlyPositive ((1 - (t : ℝ)) • a + (t : ℝ) • (1 : A)) := by
  obtain ⟨t, ht₀, ht₁⟩ := t
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simpa using ha
  · exact isStrictlyPositive_add <| .inr ⟨smul_nonneg (by simpa using ht₁) ha.nonneg,
      IsStrictlyPositive.smul ht₀ isStrictlyPositive_one⟩

/-- An invertible element of a unital C⋆-algebra is joined to its polar unitary by a path of
invertible elements: `t ↦ u ((1 - t)|x| + t)`. -/
theorem Units.joined_polarUnitary [PartialOrder A] [StarOrderedRing A] (x : Aˣ) :
    Joined x (Unitary.toUnits x.polarUnitary) := by
  have ha := x.isStrictlyPositive_sqrt_star_mul
  let γ : unitInterval → A := fun t ↦
    (x.polarUnitary : A) * ((1 - (t : ℝ)) • CFC.sqrt (star (x : A) * x) + (t : ℝ) • 1)
  have hγ : ∀ t, IsUnit (γ t) := fun t ↦
    (Unitary.toUnits x.polarUnitary).isUnit.mul (ha.one_sub_smul_add_smul_one t).isUnit
  refine ⟨⟨⟨fun t ↦ (hγ t).unit, ?_⟩, ?_, ?_⟩⟩
  · rw [Units.isOpenEmbedding_val.continuous_iff]
    simp only [Function.comp_def, IsUnit.unit_spec, γ]
    fun_prop
  · ext
    simp [γ]
  · ext
    simp [γ]

/-- Every invertible element of a unital C⋆-algebra is joined through invertible elements to a
unitary, namely its polar unitary. Stated without `Units.polarUnitary` and an order on `A`, so
that it applies to `CStarMatrix` without synthesizing a real functional calculus there. -/
theorem Units.exists_unitary_joined (x : Aˣ) : ∃ v : unitary A, Joined x (Unitary.toUnits v) :=
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  ⟨_, x.joined_polarUnitary⟩

end Polar

namespace TauCeti

open scoped ComplexOrder in
/-- The polar unitary of the invertible `2 ∈ ℂ` is `1`. -/
theorem polarUnitary_two_complex : (Units.mk0 (2 : ℂ) two_ne_zero).polarUnitary = 1 :=
  Units.polarUnitary_eq_one (by norm_num)

end TauCeti

/-! ## Invertible matrices -/

section Matrix

variable {A : Type*} [CStarAlgebra A]

/-- Every invertible matrix over a unital C⋆-algebra is joined in `GLₙ(A)` to a unitary matrix,
its polar unitary computed in `CStarMatrix n n A`. -/
theorem Matrix.GeneralLinearGroup.exists_mem_unitary_joined {n : Type*} [Fintype n]
    [DecidableEq n] (u : GL n A) :
    ∃ v : GL n A, (v : Matrix n n A) ∈ unitary (Matrix n n A) ∧ Joined u v := by
  -- Mathlib's C⋆-algebra structure on `CStarMatrix n n A` is stated for an ordered `A`.
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw⟩ := (toCStarMatrixUnits u).exists_unitary_joined
  refine ⟨toCStarMatrixUnits.symm (Unitary.toUnits w), ?_,
    by simpa using hw.map (map_continuous (toCStarMatrixUnits (n := n) (A := A)).symm)⟩
  rw [coe_toCStarMatrixUnits_symm, CStarMatrix.ofMatrix_symm_mem_unitary_iff]
  exact w.prop

namespace TauCeti.StableComponentGroup

/-- Every invertible matrix over a unital C⋆-algebra has the class in the stable component group
of a unitary matrix of the same size. -/
theorem exists_mem_unitary_mk_eq_mk {n : ℕ} (u : GL (Fin n) A) :
    ∃ v : GL (Fin n) A,
      (v : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧
        mk A n v = mk A n u := by
  obtain ⟨v, hv, h⟩ := Matrix.GeneralLinearGroup.exists_mem_unitary_joined u
  exact ⟨v, hv, (mk_eq_mk_iff.mpr ⟨n, le_rfl, by
    simpa using h.inv_mul_mem_connectedComponentOfOne⟩).symm⟩

/-- Every class of the stable component group of a unital C⋆-algebra is the class of a unitary
matrix. -/
theorem exists_mem_unitary_mk_eq (x : StableComponentGroup A) :
    ∃ n, ∃ u : GL (Fin n) A,
      (u : Matrix (Fin n) (Fin n) A) ∈ unitary (Matrix (Fin n) (Fin n) A) ∧ mk A n u = x := by
  obtain ⟨n, u, rfl⟩ := exists_mk x
  exact ⟨n, exists_mem_unitary_mk_eq_mk u⟩

end TauCeti.StableComponentGroup

end Matrix
