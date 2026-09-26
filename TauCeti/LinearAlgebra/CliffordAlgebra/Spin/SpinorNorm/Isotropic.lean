/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Spinor norms of isotropic quadratic spaces

For a nondegenerate isotropic quadratic form in characteristic different from two, every scalar
is represented. A pair of reflections in vectors of norms `a` and `1` therefore has determinant
one and spinor norm the square class of `a`. This proves that the spinor norm on the special
orthogonal group is surjective, over any field. In particular it supplies the isotropic binary
case of the local spinor-norm calculation.

## References

O. T. O'Meara, *Introduction to Quadratic Forms*, §55.
-/

public section

namespace CliffordAlgebra

open TauCeti QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- The spinor norm on the special orthogonal group of a nondegenerate isotropic quadratic
space is surjective. -/
theorem spinorNorm_surjective_of_not_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hiso : ¬ Q.Anisotropic) :
    Function.Surjective (spinorNorm Q hQ) := by
  intro b
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, squareClassHom a = b := by
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective b.toAdd
    refine ⟨a.toMul, ?_⟩
    rw [squareClassHom_apply, squareClass_def]
    simpa using congrArg Multiplicative.ofAdd ha
  obtain ⟨x, hx⟩ := (represents_iff _ _).mp
    (Q.represents_of_nondegenerate_of_not_anisotropic hQ hiso (a : K))
  obtain ⟨y, hy⟩ := (represents_iff _ _).mp
    (Q.represents_of_nondegenerate_of_not_anisotropic hQ hiso 1)
  have hx0 : Q x ≠ 0 := by rw [hx]; exact a.ne_zero
  have hy0 : Q y ≠ 0 := by rw [hy]; exact one_ne_zero
  let _ : Invertible (Q x) := invertibleOfNonzero hx0
  let _ : Invertible (Q y) := invertibleOfNonzero hy0
  let g : QuadraticMap.specialOrthogonalGroup Q := ⟨reflection Q x * reflection Q y, by
    apply mem_specialOrthogonalGroup_iff.mpr
    exact ⟨(orthogonalGroup Q).mul_mem
      (reflection_mem_orthogonalGroup Q x)
      (reflection_mem_orthogonalGroup Q y), by simp⟩⟩
  refine ⟨g, ?_⟩
  rw [spinorNorm_apply]
  have hg : specialOrthogonalToOrthogonal Q g =
      reflectionOrthogonal Q x * reflectionOrthogonal Q y := by
    apply Subtype.ext
    simp only [coe_specialOrthogonalToOrthogonal, Subgroup.coe_mul,
      coe_reflectionOrthogonal, g]
  rw [hg, map_mul, orthogonalSpinorNorm_reflectionOrthogonal,
    orthogonalSpinorNorm_reflectionOrthogonal]
  have hxa : unitOfInvertible (Q x) = a := Units.ext hx
  have hy1 : unitOfInvertible (Q y) = (1 : Kˣ) := Units.ext hy
  rw [hxa, hy1]
  calc
    squareClassHom a * squareClassHom (1 : Kˣ) = squareClassHom a := by
      rw [← map_mul, mul_one]
    _ = b := ha

/-- The spinor norm on the full orthogonal group of a nondegenerate isotropic quadratic space
is surjective. -/
theorem orthogonalSpinorNorm_surjective_of_not_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hiso : ¬ Q.Anisotropic) :
    Function.Surjective (orthogonalSpinorNorm Q hQ) := by
  intro b
  obtain ⟨g, hg⟩ := spinorNorm_surjective_of_not_anisotropic Q hQ hiso b
  exact ⟨specialOrthogonalToOrthogonal Q g, by simpa using hg⟩

end CliffordAlgebra
