/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.Shift
public import TauCeti.RepresentationTheory.Quiver.GradedPair.Basic

/-!
# Shifts of graded coordinate spaces and of raising and lowering pairs

For an integer `c`, the shift `S(c)` of a graded coordinate space `S` has the same carrier and
the grades `S(c)ₐ = Sₐ₋c`: every coordinate of degree `k` is moved to degree `k + c`. A raising or
lowering pair on `S` is a pair on `S(c)` with the same operator. Under this convention a pair of
interval type `[b, e]` shifted by `c` has type `[b + c, e + c]`.

## Main definitions

* `TauCeti.GradedCoordSpace.shift`: the shifted coordinate presentation.
* `TauCeti.GradedPair.shift`: the same operator on the shifted grading.
* `TauCeti.GradedPairEquiv.shiftEquiv`: graded equivalences of pairs correspond to graded
  equivalences of their shifts.

## Main results

* `TauCeti.GradedCoordSpace.grade_shift`: the grades of `S(c)` are `TauCeti.Graded.shift S.grade
  (-c)`, that is `S(c)ₐ = Sₐ₋c`.
* `TauCeti.GradedCoordSpace.shift_zero`, `TauCeti.GradedCoordSpace.shift_shift`: the additive
  shift laws.
* `TauCeti.GradedPair.isomorphic_shift_iff`: shifting by `c` preserves and reflects graded
  isomorphism of pairs.

## References

* H. Atobe, S. Kondo, S. Yasuda, *Local newforms for the general linear groups over a
  non-archimedean local field*, Forum of Mathematics, Pi 10 (2022), e24, §3.1.
-/

public section

open Module

namespace TauCeti

namespace GradedCoordSpace

variable (S : GradedCoordSpace)

/-- The shift `S(c)` of a coordinate graded space, with `S(c)ₐ = Sₐ₋c`: the coordinate of degree
`k` is moved to degree `k + c`, and the carrier is unchanged. -/
abbrev shift (c : ℤ) : GradedCoordSpace :=
  ⟨S.n, fun i ↦ S.degree i + c⟩

variable {S} in
/-- A vector lies in the degree-`a` piece of `S(c)` exactly when it lies in the degree-`(a - c)`
piece of `S`. -/
@[simp]
theorem mem_grade_shift {c a : ℤ} {v : S.Carrier} :
    v ∈ (S.shift c).grade a ↔ v ∈ S.grade (a - c) := by
  simp only [mem_grade_iff]
  exact forall_congr' fun i ↦ by rw [Ne, Ne, ← eq_sub_iff_add_eq]

/-- The grades of `S(c)` are the grades of `S` shifted by `-c`. -/
theorem grade_shift (c : ℤ) : (S.shift c).grade = Graded.shift S.grade (-c) := by
  ext a v
  rw [Graded.shift_apply, mem_grade_shift, sub_eq_add_neg]

/-- The degree-`a` piece of `S(c)` has the dimension of the degree-`(a - c)` piece of `S`. -/
@[simp]
theorem finrank_grade_shift (c a : ℤ) :
    finrank ℂ ((S.shift c).grade a) = finrank ℂ (S.grade (a - c)) := by
  simp only [finrank_grade, eq_sub_iff_add_eq]

@[simp]
theorem shift_zero : S.shift 0 = S := by
  cases S
  simp [shift]

@[simp]
theorem shift_shift (c c' : ℤ) : (S.shift c).shift c' = S.shift (c + c') := by
  simp [shift, add_assoc]

end GradedCoordSpace

namespace GradedPair

variable {S T : GradedCoordSpace} {d : StepDirection}

/-- The shift of a pair by `c`: the same operator on the shifted grading `S(c)`. -/
def shift (P : GradedPair S d) (c : ℤ) : GradedPair (S.shift c) d where
  operator := P.operator
  isHomogeneous := by
    rw [GradedCoordSpace.grade_shift]
    exact LinearMap.isHomogeneous_shift_iff.2 P.isHomogeneous

@[simp]
theorem operator_shift (P : GradedPair S d) (c : ℤ) : (P.shift c).operator = P.operator :=
  (rfl)

@[simp]
theorem zero_shift (c : ℤ) : (0 : GradedPair S d).shift c = 0 :=
  (rfl)

end GradedPair

namespace GradedPairEquiv

variable {S T : GradedCoordSpace} {d : StepDirection} {P : GradedPair S d} {Q : GradedPair T d}

/-- Graded equivalences between two pairs are the graded equivalences between their shifts by
`c`, with the same underlying linear equivalence. -/
def shiftEquiv (c : ℤ) : GradedPairEquiv P Q ≃ GradedPairEquiv (P.shift c) (Q.shift c) where
  toFun e :=
    { toLinearEquiv := e.toLinearEquiv
      mem_grade_iff' a v := by
        simp only [GradedCoordSpace.mem_grade_shift, coe_toLinearEquiv, mem_grade_iff]
      map_operator' := e.map_operator' }
  invFun e :=
    { toLinearEquiv := e.toLinearEquiv
      mem_grade_iff' a v := by
        have h := e.mem_grade_iff' (a + c) v
        simp only [GradedCoordSpace.mem_grade_shift, add_sub_cancel_right] at h
        exact h
      map_operator' := e.map_operator' }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem shiftEquiv_apply_apply (c : ℤ) (e : GradedPairEquiv P Q) (v : S.Carrier) :
    shiftEquiv c e v = e v :=
  (rfl)

@[simp]
theorem shiftEquiv_symm_apply_apply (c : ℤ) (e : GradedPairEquiv (P.shift c) (Q.shift c))
    (v : S.Carrier) : (shiftEquiv c).symm e v = e v :=
  (rfl)

end GradedPairEquiv

namespace GradedPair

variable {S T : GradedCoordSpace} {d : StepDirection}

/-- Shifting two pairs by the same amount preserves and reflects graded isomorphism. -/
@[simp]
theorem isomorphic_shift_iff {P : GradedPair S d} {Q : GradedPair T d} (c : ℤ) :
    (P.shift c).Isomorphic (Q.shift c) ↔ P.Isomorphic Q := by
  rw [isomorphic_iff, isomorphic_iff]
  exact (GradedPairEquiv.shiftEquiv c).nonempty_congr.symm

end GradedPair

end TauCeti
