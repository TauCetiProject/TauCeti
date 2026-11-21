/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Jacobian.Locus
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Normalizing the parameter of a nodal equation

Multiplying the parameter of `xy = a` by a unit does not change its coordinate algebra:
rescale the first coordinate by that unit, leaving the second coordinate fixed. This
coordinate change preserves the Jacobian ideal, hence also the singular subscheme and the
centre used to blow up a node.

Over a discrete valuation ring with uniformizer `π`, every nonzero parameter can therefore
be replaced by `πⁿ`. If the parameter lies in the maximal ideal, the normal form is either
`xy = 0` or `xy = πⁿ` with `n > 0`. These coordinate changes take place over the original
base ring; they require neither a root of a unit nor an extension of the residue field.

## References

* Stacks Project, Section 53.20, Tag 0C58: families of nodal curves.
* Stacks Project, Example 55.14.1, Tag 0CDC: nodal equations over a DVR.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

variable {R : Type*} [CommRing R]

/-- Rescale the first coordinate to remove a unit factor from the smoothing parameter. -/
def rescaleEquiv (a b : R) (u : Rˣ) (h : a = (u : R) * b) :
    NodeAlgebra R a ≃ₐ[R] NodeAlgebra R b := by
  let f : NodeAlgebra R a →ₐ[R] NodeAlgebra R b :=
    lift a (algebraMap R _ (u : R) * coord b 0) (coord b 1) (by
      rw [mul_assoc, coord_zero_mul_coord_one, ← map_mul, ← h])
  let g : NodeAlgebra R b →ₐ[R] NodeAlgebra R a :=
    lift b (algebraMap R _ (↑u⁻¹ : R) * coord a 0) (coord a 1) (by
      rw [mul_assoc, coord_zero_mul_coord_one, ← map_mul, h]
      simp)
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply hom_ext
    · simp only [AlgHom.comp_apply, g, f, lift_coord_zero, map_mul, AlgHom.commutes,
        AlgHom.id_apply]
      simp [← mul_assoc, ← map_mul]
    · simp [f, g]
  · apply hom_ext
    · simp only [AlgHom.comp_apply, f, g, lift_coord_zero, map_mul, AlgHom.commutes,
        AlgHom.id_apply]
      simp [← mul_assoc, ← map_mul]
    · simp [f, g]

/-- The first coordinate absorbs the unit factor. -/
@[simp]
theorem rescaleEquiv_coord_zero (a b : R) (u : Rˣ) (h : a = (u : R) * b) :
    rescaleEquiv a b u h (coord a 0) = algebraMap R _ (u : R) * coord b 0 := by
  simp [rescaleEquiv]

/-- The second coordinate is unchanged by rescaling. -/
@[simp]
theorem rescaleEquiv_coord_one (a b : R) (u : Rˣ) (h : a = (u : R) * b) :
    rescaleEquiv a b u h (coord a 1) = coord b 1 := by
  simp [rescaleEquiv]

/-- The inverse coordinate change absorbs the inverse unit. -/
@[simp]
theorem rescaleEquiv_symm_coord_zero (a b : R) (u : Rˣ) (h : a = (u : R) * b) :
    (rescaleEquiv a b u h).symm (coord b 0) =
      algebraMap R _ (↑u⁻¹ : R) * coord a 0 := by
  apply (rescaleEquiv a b u h).injective
  simp only [AlgEquiv.apply_symm_apply, map_mul, AlgEquiv.commutes,
    rescaleEquiv_coord_zero]
  simp [← mul_assoc, ← map_mul]

/-- The inverse coordinate change also fixes the second coordinate. -/
@[simp]
theorem rescaleEquiv_symm_coord_one (a b : R) (u : Rˣ) (h : a = (u : R) * b) :
    (rescaleEquiv a b u h).symm (coord b 1) = coord a 1 := by
  apply (rescaleEquiv a b u h).injective
  simp

/-- Removing a unit factor preserves the scheme-theoretic nodal centre. -/
@[simp]
theorem map_jacobianIdeal_rescaleEquiv (a b : R) (u : Rˣ) (h : a = (u : R) * b) :
    Ideal.map (rescaleEquiv a b u h) (jacobianIdeal a) = jacobianIdeal b := by
  simp only [jacobianIdeal_def, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
    rescaleEquiv_coord_zero, rescaleEquiv_coord_one]
  simp only [Ideal.span_insert,
    Ideal.span_singleton_mul_left_unit (u.isUnit.map (algebraMap R (NodeAlgebra R b)))]

section DiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R] {a π : R}

/-- A nodal equation with nonzero parameter over a DVR is isomorphic over the base to
`xy = πⁿ`. The coordinate change preserves its Jacobian ideal. -/
theorem exists_equiv_pow_of_ne_zero (hπ : Irreducible π) (ha : a ≠ 0) :
    ∃ (n : ℕ) (e : NodeAlgebra R a ≃ₐ[R] NodeAlgebra R (π ^ n)),
      (a ∈ IsLocalRing.maximalIdeal R ↔ 0 < n) ∧
        Ideal.map e (jacobianIdeal a) = jacobianIdeal (π ^ n) := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, rescaleEquiv a (π ^ n) u hu, ?_, map_jacobianIdeal_rescaleEquiv ..⟩
  simp [hu, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_pow_iff_of_not_isUnit hπ.not_isUnit, Nat.pos_iff_ne_zero]

/-- At a node of the special fibre, the smoothing parameter is zero or a positive power
of a uniformizer, after an isomorphism over the DVR preserving the nodal centre. -/
theorem exists_equiv_zero_or_pow (hπ : Irreducible π)
    (ha : a ∈ IsLocalRing.maximalIdeal R) :
    ∃ (b : R) (e : NodeAlgebra R a ≃ₐ[R] NodeAlgebra R b),
      (b = 0 ∨ ∃ n : ℕ, 0 < n ∧ b = π ^ n) ∧
        Ideal.map e (jacobianIdeal a) = jacobianIdeal b := by
  by_cases ha0 : a = 0
  · subst a
    exact ⟨0, AlgEquiv.refl, Or.inl rfl, by simp [Ideal.map]⟩
  obtain ⟨n, e, hn, he⟩ := exists_equiv_pow_of_ne_zero hπ ha0
  exact ⟨π ^ n, e, Or.inr ⟨n, hn.mp ha, rfl⟩, he⟩

end DiscreteValuationRing

end TauCeti.NodeAlgebra
