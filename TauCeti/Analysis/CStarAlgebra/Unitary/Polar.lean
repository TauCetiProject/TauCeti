/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Invertible elements are joined to their polar unitaries

For an invertible element `x` of a unital C⋆-algebra `A`, `Units.polarUnitary x` is the unitary
factor `u` of the polar decomposition `x = u |x|`, `|x| = √(x⋆x)`
(`TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`). This file shows
that `u` is joined to `x` by a path of invertible elements (`Units.joined_polarUnitary`):
`t ↦ u ((1 - t)|x| + t)` stays invertible, since `(1 - t)|x| + t` is strictly positive for
`t ∈ [0, 1]`. This straight-line path has the same endpoints as the polar deformation
`t ↦ x (x⋆x)^(-t/2)`.

The consequences for invertible matrices and the stable component group are in
`TauCeti/Analysis/Matrix/GeneralLinearGroup/Polar.lean`.

## Main results

* `IsStrictlyPositive.one_sub_smul_add_smul`: `(1 - t) a + t b` is strictly positive for
  strictly positive `a`, `b` and `t ∈ [0, 1]`.
* `Units.joined_polarUnitary`: `x` and its polar unitary lie in one path component of `Aˣ`.
* `Units.exists_unitary_joined`: every invertible element is joined in `Aˣ` to a unitary.
* `IsConj.exists_mem_unitary_mul_mul_star_eq`: similar self-adjoint elements are unitarily
  equivalent.

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

/-- The straight-line interpolation `(1 - t) a + t b` between strictly positive `a` and `b` is
strictly positive for `t ∈ [0, 1]`. -/
theorem IsStrictlyPositive.one_sub_smul_add_smul [PartialOrder A] [StarOrderedRing A] {a b : A}
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) (t : unitInterval) :
    IsStrictlyPositive ((1 - (t : ℝ)) • a + (t : ℝ) • b) := by
  obtain ⟨t, ht₀, ht₁⟩ := t
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simpa using ha
  · exact isStrictlyPositive_add <| .inr ⟨smul_nonneg (by simpa using ht₁) ha.nonneg,
      hb.smul ht₀⟩

/-- An invertible element of a unital C⋆-algebra is joined to its polar unitary by a path of
invertible elements: `t ↦ u ((1 - t)|x| + t)`. -/
theorem Units.joined_polarUnitary [PartialOrder A] [StarOrderedRing A] (x : Aˣ) :
    Joined x (Unitary.toUnits x.polarUnitary) := by
  have ha := x.isStrictlyPositive_sqrt_star_mul
  let γ : unitInterval → A := fun t ↦
    (x.polarUnitary : A) * ((1 - (t : ℝ)) • CFC.sqrt (star (x : A) * x) + (t : ℝ) • 1)
  have hγ : ∀ t, IsUnit (γ t) := fun t ↦
    (Unitary.toUnits x.polarUnitary).isUnit.mul
      (ha.one_sub_smul_add_smul isStrictlyPositive_one t).isUnit
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

/-- **Similar self-adjoint elements are unitarily equivalent.** If an invertible element of a unital
C⋆-algebra conjugates a self-adjoint `x` to a self-adjoint `y`, then so does a unitary, namely its
polar unitary. Stated without `Units.polarUnitary` and an order on `A`, so that it applies to
`CStarMatrix`. -/
theorem IsConj.exists_mem_unitary_mul_mul_star_eq {x y : A} (h : IsConj x y)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : ∃ u ∈ unitary A, u * x * star u = y := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨a, ha⟩ := h
  refine ⟨a.polarUnitary, a.polarUnitary.property, ?_⟩
  rw [a.polarUnitary_mul_eq_mul_polarUnitary hx hy ha, mul_assoc,
    Unitary.mul_star_self_of_mem a.polarUnitary.property, mul_one]

end Polar
