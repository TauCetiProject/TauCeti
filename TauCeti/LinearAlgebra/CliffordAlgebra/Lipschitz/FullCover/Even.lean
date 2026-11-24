/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.Basic

/-!
# The even part of the normalized full Clifford cover

The normalized full Clifford cover `CliffordAlgebra.cliffordFullCover Q` consists of the Lipschitz
elements whose reverse norm `reverse x * x` is `1` or `-1`. The even elements of the full cover
form a subgroup. Over a field in which every element is a square up to sign, as over `ℝ`, it covers
all of `SO(Q)` for a finite-dimensional nondegenerate quadratic space.

## Main definitions

* `CliffordAlgebra.cliffordFullCoverEven`: the subgroup of even elements of the full cover.

## Main results

* `CliffordAlgebra.range_spinToCliffordFullCover_le_cliffordFullCoverEven`: the Spin group lies
  in the even part of the full cover.
* `CliffordAlgebra.exists_cliffordFullCoverToOrthogonal_eq_and_mem_even_iff` and
  `CliffordAlgebra.map_cliffordFullCoverEven`: when every element is a square up to sign, an
  orthogonal transformation is the action of an even element of the full cover exactly when it
  lies in `SO(Q)`, so the even part of the full cover covers `SO(Q)`.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6, where `Pin(p, q)` is the norm `±1` cover.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe u v

section Ring

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)] (Q : QuadraticForm R M)

/-- The subgroup of even elements of the normalized full cover. -/
def cliffordFullCoverEven : Subgroup (cliffordFullCover Q) where
  carrier := {x | (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q}
  one_mem' := (even Q).one_mem
  mul_mem' hx hy := (even Q).mul_mem hx hy
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, ← Subalgebra.mem_toSubmodule, even_toSubmodule,
      ← involute_eq_self_iff, InvMemClass.coe_inv] at hx ⊢
    -- The grade involution is multiplicative, so it fixes the inverse of a unit it fixes.
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    nth_rw 1 [← hx]
    rw [← map_mul, Units.mul_inv, map_one]

/-- Membership in the even part of the full cover is evenness of the underlying Clifford
element. -/
@[simp]
theorem mem_cliffordFullCoverEven_iff (x : cliffordFullCover Q) :
    x ∈ cliffordFullCoverEven Q ↔
      (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q :=
  Iff.rfl

/-- The Spin group lies in the even part of the full cover. -/
theorem range_spinToCliffordFullCover_le_cliffordFullCoverEven :
    (spinToCliffordFullCover Q).range ≤ cliffordFullCoverEven Q :=
  fun x hx ↦
    (mem_cliffordFullCoverEven_iff Q x).2 ((mem_range_spinToCliffordFullCover_iff Q x).1 hx).1

end Ring

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] {Q : QuadraticForm K V}

/-- **The even part of the full cover covers `SO(Q)`.** Over a field in which every element is a
square up to sign, an orthogonal transformation of a finite-dimensional nondegenerate quadratic
space is the action of an even element of the full cover exactly when it has determinant one. -/
theorem exists_cliffordFullCoverToOrthogonal_eq_and_mem_even_iff (hQ : Q.Nondegenerate)
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) (g : QuadraticMap.orthogonalGroup Q) :
    (∃ x : cliffordFullCover Q, cliffordFullCoverToOrthogonal Q x = g ∧
        (((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q) ↔
      g ∈ QuadraticMap.specialOrthogonalWithin Q := by
  rw [QuadraticMap.mem_specialOrthogonalWithin_iff, ← QuadraticMap.orthogonalDet_apply]
  constructor
  · rintro ⟨x, rfl, hx⟩
    rw [cliffordFullCoverToOrthogonal_apply]
    exact det_lipschitzToOrthogonal_eq_one_of_mem_even Q _ hx
  · intro hg
    obtain ⟨x, rfl⟩ := cliffordFullCoverToOrthogonal_surjective hQ hK g
    rw [cliffordFullCoverToOrthogonal_apply] at hg
    exact ⟨x, rfl, mem_even_of_det_lipschitzToOrthogonal_eq_one Q _ hg⟩

/-- **The even part of the full cover covers `SO(Q)`.** Over a field in which every element is a
square up to sign, the image of the even part of the full cover of a finite-dimensional
nondegenerate quadratic space is `SO(Q)`. -/
theorem map_cliffordFullCoverEven (hQ : Q.Nondegenerate)
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    (cliffordFullCoverEven Q).map (cliffordFullCoverToOrthogonal Q) =
      QuadraticMap.specialOrthogonalWithin Q := by
  ext g
  rw [← exists_cliffordFullCoverToOrthogonal_eq_and_mem_even_iff hQ hK, Subgroup.mem_map]
  simp only [mem_cliffordFullCoverEven_iff, and_comm]

end Field

end CliffordAlgebra
