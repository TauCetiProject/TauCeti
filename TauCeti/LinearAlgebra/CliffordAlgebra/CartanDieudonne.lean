/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.LinearAlgebra.CliffordAlgebra.ReflectionLift
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

/-!
# Cartan--Dieudonné for Lipschitz and Pin actions

Over a field of characteristic other than two, Cartan--Dieudonné and the action of a generating
vector show that the Lipschitz action is onto the orthogonal group.

## Main results

* `CliffordAlgebra.lipschitzToOrthogonal_surjective`: the Lipschitz action is onto for a
  finite-dimensional nondegenerate quadratic space.
* `CliffordAlgebra.pinToOrthogonal_surjective`: over a separably closed field of
  characteristic other than two, the Pin action is surjective on a finite-dimensional
  nondegenerate quadratic space.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

universe u v

namespace CliffordAlgebra

open TauCeti

variable {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) [Invertible (2 : K)]

/-- The Lipschitz action is onto the orthogonal group of a finite-dimensional nondegenerate
quadratic space over a field of characteristic other than two. -/
theorem lipschitzToOrthogonal_surjective [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (lipschitzToOrthogonal Q) := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  exact MonoidHom.range_eq_top.mp <|
    QuadraticMap.subgroup_eq_top_of_reflection_mem
      Q hQ (lipschitzToOrthogonal Q).range
      fun v _ ↦ by
        rw [MonoidHom.mem_range]
        exact ⟨⟨unitι Q v, unitι_mem_lipschitzGroup v⟩,
          lipschitzToOrthogonal_unitι Q v⟩

/-- Over a field of characteristic other than two, the twisted-conjugation homomorphism from the
Pin group is surjective when every reflection normalization scalar is a square. -/
theorem pinToOrthogonal_surjective_of_isSquare
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hsquare : ∀ (v : V) [Invertible (Q v)], IsSquare (-⅟(Q v))) :
    Function.Surjective (pinToOrthogonal Q) :=
  MonoidHom.range_eq_top.mp <|
    QuadraticMap.subgroup_eq_top_of_reflection_mem
      Q hQ (pinToOrthogonal Q).range
      fun v _ ↦ reflection_mem_range_pinToOrthogonal_of_isSquare Q v (hsquare v)

section IsSepClosed

variable [IsSepClosed K]

/-- The twisted-conjugation homomorphism from the Pin group is surjective for a
finite-dimensional nondegenerate quadratic space over a separably closed field of characteristic
other than two. -/
theorem pinToOrthogonal_surjective
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (pinToOrthogonal Q) :=
  pinToOrthogonal_surjective_of_isSquare Q hQ fun v _ ↦
    IsSepClosed.isSquare (-⅟(Q v))

end IsSepClosed
end CliffordAlgebra
