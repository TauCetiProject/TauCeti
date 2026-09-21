/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

/-!
# Orbits of nondegenerate special orthogonal groups

A special orthogonal transformation carries any vector of a fixed nonzero norm to any other,
provided the nondegenerate quadratic space has dimension at least two. The proof uses a pair of
reflections: one moves the vector, and the second corrects the determinant while fixing its image.

This is the linear-algebra input for the transitive action of a compact real Spin group on a
positive quadratic level set. The reflection and orthogonal-complement arguments reuse the
preceding Cartan--Dieudonne and orthogonal-group developments, following Lawson--Michelsohn,
*Spin Geometry*, Chapter I, Section 2.
-/

public section

open Module Submodule

namespace TauCeti.QuadraticMap

noncomputable section

universe u v

variable {K : Type u} {V : Type v} [Field K] [NeZero (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private noncomputable def reflectionPairSpecialOrthogonal
    (Q : QuadraticForm K V) (u v : V) [Invertible (Q u)] [Invertible (Q v)] :
    specialOrthogonalGroup Q :=
  ⟨(reflectionOrthogonal Q u : V ≃ₗ[K] V) * reflectionOrthogonal Q v, by
    rw [mem_specialOrthogonalGroup_iff]
    constructor
    · exact (orthogonalGroup Q).mul_mem (reflectionOrthogonal Q u).2
        (reflectionOrthogonal Q v).2
    · simp⟩

omit [NeZero (2 : K)] in
private theorem reflectionPairSpecialOrthogonal_apply
    (Q : QuadraticForm K V) (u v x : V) [Invertible (Q u)] [Invertible (Q v)] :
    (reflectionPairSpecialOrthogonal Q u v : V ≃ₗ[K] V) x =
      reflection Q u (reflection Q v x) := by
  simp only [reflectionPairSpecialOrthogonal, Subgroup.coe_mk, LinearEquiv.mul_apply,
    coe_reflectionOrthogonal]

/-- A nondegenerate special orthogonal group acts transitively on every nonzero quadratic level
set when the quadratic space has dimension at least two. -/
theorem exists_specialOrthogonal_map_eq_of_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hrank : 2 ≤ finrank K V) {x y : V} (hxy : Q x = Q y)
    (hy : Q y ≠ 0) : ∃ g : specialOrthogonalGroup Q, (g : V ≃ₗ[K] V) x = y := by
  rcases isUnit_sub_or_add_of_map_eq Q x y hxy hy with hsub | hadd
  · let _ : Invertible (Q (x - y)) := hsub.invertible
    obtain ⟨z, hzy, hzQ⟩ :=
      TauCeti.QuadraticMap.exists_orthogonal_anisotropic Q hQ hrank (y := y) hy
    let _ : Invertible (Q z) := (isUnit_iff_ne_zero.mpr hzQ).invertible
    refine ⟨reflectionPairSpecialOrthogonal Q z (x - y), ?_⟩
    rw [reflectionPairSpecialOrthogonal_apply]
    rw [reflection_sub_apply_eq_of_map_eq Q x y hxy]
    exact reflection_apply_of_isOrtho Q z hzy
  · let _ : Invertible (Q (x - -y)) := by
      simpa only [sub_neg_eq_add] using hadd.invertible
    have hyUnit : IsUnit (Q y) := isUnit_iff_ne_zero.mpr hy
    let _ : Invertible (Q y) := hyUnit.invertible
    refine ⟨reflectionPairSpecialOrthogonal Q y (x - -y), ?_⟩
    rw [reflectionPairSpecialOrthogonal_apply]
    rw [reflection_sub_apply_eq_of_map_eq Q x (-y)]
    · simp
    · simpa [QuadraticMap.map_neg] using hxy

end

end TauCeti.QuadraticMap
