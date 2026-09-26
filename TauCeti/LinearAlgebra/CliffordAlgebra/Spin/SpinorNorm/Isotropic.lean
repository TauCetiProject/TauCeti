/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
import Mathlib.Tactic.NormNum.IsSquare
import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

/-!
# Spinor norms of isotropic quadratic spaces

For a nondegenerate isotropic quadratic form in characteristic different from two, every scalar
is represented. A pair of reflections in vectors of norms `a` and `1` therefore has determinant
one and spinor norm the square class of `a`. This proves that the spinor norm on the special
orthogonal group is surjective, over any field. In particular it supplies the isotropic binary
case of the local spinor-norm calculation.

Since the image of `Spin` in the special orthogonal group is the kernel of the spinor norm, an
isotropic space has `Spin → SO` surjective on `K`-points exactly when every unit of `K` is a
square. Over `ℚ` this fails already for the hyperbolic plane: although the kernel of the Spin
action is `{±1}`, the map on rational points is not onto.

## Main results

* `CliffordAlgebra.spinorNorm_surjective_of_not_anisotropic` and
  `CliffordAlgebra.orthogonalSpinorNorm_surjective_of_not_anisotropic`: the spinor norm of an
  isotropic space is surjective on `SO(Q)` and on `O(Q)`.
* `CliffordAlgebra.spinToSpecialOrthogonal_surjective_iff_of_not_anisotropic`: for an isotropic
  space, the Spin action on `SO(Q)` is surjective exactly when every unit is a square.
* `CliffordAlgebra.not_surjective_spinToSpecialOrthogonal_hyperbolicPlane_rat`: the Spin action
  of the rational hyperbolic plane is not surjective.

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
  obtain ⟨a, ha⟩ := squareClassHom_surjective b
  obtain ⟨x, hx⟩ := (represents_iff _ _).mp
    (Q.represents_of_nondegenerate_of_not_anisotropic hQ hiso (a : K))
  obtain ⟨y, hy⟩ := (represents_iff _ _).mp
    (Q.represents_of_nondegenerate_of_not_anisotropic hQ hiso 1)
  have hx0 : Q x ≠ 0 := by rw [hx]; exact a.ne_zero
  have hy0 : Q y ≠ 0 := by rw [hy]; exact one_ne_zero
  let _ : Invertible (Q x) := invertibleOfNonzero hx0
  let _ : Invertible (Q y) := invertibleOfNonzero hy0
  let g : QuadraticMap.specialOrthogonalGroup Q :=
    reflectionPairSpecialOrthogonal Q x y
  refine ⟨g, ?_⟩
  rw [spinorNorm_apply]
  have hg : specialOrthogonalToOrthogonal Q g =
      reflectionOrthogonal Q x * reflectionOrthogonal Q y := by
    simpa only [g] using reflectionPairSpecialOrthogonal_toOrthogonal Q x y
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

/-- For a nondegenerate isotropic quadratic space, the Spin action on the special orthogonal
group is surjective exactly when every unit of `K` is a square. A nonsquare unit `a` is the
spinor norm of some proper isometry, and that isometry has no Spin preimage. -/
theorem spinToSpecialOrthogonal_surjective_iff_of_not_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hiso : ¬ Q.Anisotropic) :
    Function.Surjective (spinToSpecialOrthogonal Q) ↔ ∀ a : Kˣ, IsSquare a := by
  constructor
  · intro hsurj a
    obtain ⟨g, hg⟩ := spinorNorm_surjective_of_not_anisotropic Q hQ hiso (squareClassHom a)
    obtain ⟨s, rfl⟩ := hsurj g
    rw [spinorNorm_spinToSpecialOrthogonal, eq_comm] at hg
    simpa using hg
  · intro hsq
    exact spinToSpecialOrthogonal_surjective_of_isSquare_apply Q hQ fun v _ ↦ by
      simpa using (hsq (unitOfInvertible (Q v))).map (Units.coeHom K)

/-- The Spin action on the special orthogonal group of the rational hyperbolic plane is not
surjective on rational points. -/
theorem not_surjective_spinToSpecialOrthogonal_hyperbolicPlane_rat :
    ¬ Function.Surjective (spinToSpecialOrthogonal (hyperbolicPlane ℚ)) := by
  have hiso : ¬ (hyperbolicPlane ℚ).Anisotropic := fun h ↦ by
    have h0 := h ![1, 1] (by simp)
    simpa using congr_fun h0 0
  rw [spinToSpecialOrthogonal_surjective_iff_of_not_anisotropic _ nondegenerate_hyperbolicPlane
    hiso]
  intro h
  have h2 : ¬ IsSquare (2 : ℚ) := by norm_num
  exact h2 (by simpa using (h (Units.mk0 2 two_ne_zero)).map (Units.coeHom ℚ))

end CliffordAlgebra
