/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The degree-two grading on the dual numbers

This file gives the dual numbers their standard nonnegative grading: scalars have degree zero and
the infinitesimal generator has degree two. Thus only degrees zero and two are nonzero. The
grading is internal to `DualNumber R`, so the graded algebra supplied here compares directly with
the usual ungraded dual-number algebra.

## Main definitions

* `TauCeti.dualNumberGrade`: the degree pieces of the dual numbers.
* `TauCeti.dualNumberGradedAlgebra`: the corresponding graded-algebra structure.

## Main results

* `TauCeti.isInternal_dualNumberGrade`: the dual numbers are the internal direct sum of their
  scalar and infinitesimal pieces.
* `TauCeti.dualNumberGrade_zero_eq_ker_snd` and
  `TauCeti.dualNumberGrade_two_eq_ker_fst`: the two nonzero pieces in coordinates.
* `TauCeti.dualNumberGrade_eq_bot`: every degree other than zero and two vanishes.

## Implementation notes

In this grading the dual numbers `R[ε]` model the ring `R[x]/(x²)` with `deg x = 2`, which is the
zigzag algebra of a single vertex with no edges.
-/

public section

namespace TauCeti

universe u

variable (R : Type u) [CommSemiring R]

/-- The standard nonnegative grading on the dual numbers: degree zero consists of scalars,
degree two consists of scalar multiples of `DualNumber.eps`, and every other degree is zero. -/
noncomputable def dualNumberGrade (n : ℕ) : Submodule R (DualNumber R) :=
  if n = 0 then LinearMap.ker (TrivSqZeroExt.sndHom R R)
  else if n = 2 then LinearMap.ker (TrivSqZeroExt.fstHom R R R).toLinearMap
  else ⊥

/-- The degree-zero piece consists exactly of dual numbers with zero infinitesimal coordinate. -/
theorem dualNumberGrade_zero_eq_ker_snd :
    dualNumberGrade R 0 = LinearMap.ker (TrivSqZeroExt.sndHom R R) := by
  simp [dualNumberGrade]

/-- The degree-two piece consists exactly of dual numbers with zero scalar coordinate. -/
theorem dualNumberGrade_two_eq_ker_fst :
    dualNumberGrade R 2 = LinearMap.ker (TrivSqZeroExt.fstHom R R R).toLinearMap := by
  simp [dualNumberGrade]

/-- All pieces other than degrees zero and two vanish. -/
theorem dualNumberGrade_eq_bot {n : ℕ} (h0 : n ≠ 0) (h2 : n ≠ 2) :
    dualNumberGrade R n = ⊥ := by
  simp [dualNumberGrade, h0, h2]

/-- Membership in degree zero is detected by the infinitesimal coordinate. -/
@[simp]
theorem mem_dualNumberGrade_zero {x : DualNumber R} :
    x ∈ dualNumberGrade R 0 ↔ x.snd = 0 := by
  simp [dualNumberGrade_zero_eq_ker_snd]

/-- Membership in degree two is detected by the scalar coordinate. -/
@[simp]
theorem mem_dualNumberGrade_two {x : DualNumber R} :
    x ∈ dualNumberGrade R 2 ↔ x.fst = 0 := by
  simp [dualNumberGrade_two_eq_ker_fst]

/-- The scalar inclusion lands in degree zero. -/
theorem inl_mem_dualNumberGrade_zero (r : R) :
    TrivSqZeroExt.inl r ∈ dualNumberGrade R 0 := by
  simp

/-- The algebra map lands in degree zero. -/
theorem algebraMap_mem_dualNumberGrade_zero (r : R) :
    algebraMap R (DualNumber R) r ∈ dualNumberGrade R 0 := by
  simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- The infinitesimal inclusion lands in degree two. -/
theorem inr_mem_dualNumberGrade_two (r : R) :
    TrivSqZeroExt.inr r ∈ dualNumberGrade R 2 := by
  simp

/-- The dual-number generator has degree two. -/
theorem eps_mem_dualNumberGrade_two :
    DualNumber.eps ∈ dualNumberGrade R 2 := by
  simpa only [DualNumber.eps] using inr_mem_dualNumberGrade_two R 1

/-- Multiplication adds degrees in the standard grading of the dual numbers. -/
theorem mul_mem_dualNumberGrade {m n : ℕ} {x y : DualNumber R}
    (hx : x ∈ dualNumberGrade R m) (hy : y ∈ dualNumberGrade R n) :
    x * y ∈ dualNumberGrade R (m + n) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp only [mem_dualNumberGrade_zero] at hx hy ⊢
      simp [hx, hy]
    · rcases eq_or_ne n 2 with rfl | hn2
      · simp only [mem_dualNumberGrade_zero] at hx
        simp only [mem_dualNumberGrade_two] at hy ⊢
        simp [hy]
      · have : y = 0 := by
          rw [dualNumberGrade_eq_bot R hn0 hn2] at hy
          exact hy
        subst y
        simp
  · rcases eq_or_ne m 2 with rfl | hm2
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp only [mem_dualNumberGrade_two] at hx
        simp only [mem_dualNumberGrade_zero] at hy
        simp [hx]
      · rcases eq_or_ne n 2 with rfl | hn2
        · have hxfst : x.fst = 0 := (mem_dualNumberGrade_two (R := R)).mp hx
          have hyfst : y.fst = 0 := (mem_dualNumberGrade_two (R := R)).mp hy
          have hxy : x * y = 0 := by
            apply TrivSqZeroExt.ext
            · simp [hxfst, hyfst]
            · simp [hxfst, hyfst]
          rw [hxy]
          exact (dualNumberGrade R (2 + 2)).zero_mem
        · have : y = 0 := by
            simpa [dualNumberGrade_eq_bot R hn0 hn2] using hy
          subst y
          simp
    · have : x = 0 := by
        simpa [dualNumberGrade_eq_bot R hm0 hm2] using hx
      subst x
      simp

/-- The standard grading makes the dual numbers a graded monoid. This is a theorem rather than a
global instance so callers choose when to install the grading. -/
theorem dualNumberGradedMonoid : SetLike.GradedMonoid (dualNumberGrade R) where
  one_mem := by simp
  mul_mem _ _ _ _ := mul_mem_dualNumberGrade R

namespace DualNumberGrading

/-- The degree-zero part of a dual number, valued in the degree-zero submodule. -/
private noncomputable def degreeZeroPart : DualNumber R →ₗ[R] dualNumberGrade R 0 :=
  ((TrivSqZeroExt.inlAlgHom R R R).toLinearMap.comp
    (TrivSqZeroExt.fstHom R R R).toLinearMap).codRestrict
      (dualNumberGrade R 0) fun _ => by simp

/-- The degree-two part of a dual number, valued in the degree-two submodule. -/
private noncomputable def degreeTwoPart : DualNumber R →ₗ[R] dualNumberGrade R 2 :=
  ((TrivSqZeroExt.inrHom R R).comp (TrivSqZeroExt.sndHom R R)).codRestrict
    (dualNumberGrade R 2) fun _ => by simp

@[simp]
private theorem coe_degreeZeroPart_apply (x : DualNumber R) :
    (degreeZeroPart R x : DualNumber R) = TrivSqZeroExt.inl x.fst := by
  rfl

@[simp]
private theorem coe_degreeTwoPart_apply (x : DualNumber R) :
    (degreeTwoPart R x : DualNumber R) = TrivSqZeroExt.inr x.snd := by
  rfl

/-- The two-coordinate decomposition, regarded as an element of the direct sum of all grades. -/
private noncomputable def decompose :
    DualNumber R →ₗ[R] DirectSum ℕ (fun n => dualNumberGrade R n) :=
  (DirectSum.lof R ℕ (fun n => dualNumberGrade R n) 0).comp (degreeZeroPart R) +
    (DirectSum.lof R ℕ (fun n => dualNumberGrade R n) 2).comp (degreeTwoPart R)

/-- Reassembling the two coordinate parts recovers the original dual number. -/
private theorem coeAddMonoidHom_decompose (x : DualNumber R) :
    DirectSum.coeAddMonoidHom (dualNumberGrade R) (decompose R x) = x := by
  simpa [decompose, DirectSum.lof_eq_of] using TrivSqZeroExt.inl_fst_add_inr_snd_eq x

/-- Decomposing the sum of a family of graded components recovers that family. -/
private theorem decompose_coeAddMonoidHom (x : DirectSum ℕ (fun n => dualNumberGrade R n)) :
    decompose R (DirectSum.coeAddMonoidHom (dualNumberGrade R) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n x =>
      rcases eq_or_ne n 0 with rfl | hn0
      · have hx := (mem_dualNumberGrade_zero R).1 x.property
        have hzero : degreeZeroPart R x = x := Subtype.ext (TrivSqZeroExt.ext rfl (by simp [hx]))
        have htwo : degreeTwoPart R x = 0 := Subtype.ext (by simp [hx])
        simp [decompose, hzero, htwo, DirectSum.lof_eq_of]
      rcases eq_or_ne n 2 with rfl | hn2
      · have hx := (mem_dualNumberGrade_two R).1 x.property
        have hzero : degreeZeroPart R x = 0 := Subtype.ext (by simp [hx])
        have htwo : degreeTwoPart R x = x := Subtype.ext (TrivSqZeroExt.ext (by simp [hx]) rfl)
        simp [decompose, hzero, htwo, DirectSum.lof_eq_of]
      · obtain rfl : x = 0 := Subtype.ext (by simpa [dualNumberGrade_eq_bot R hn0 hn2] using x.2)
        simp

/-- The coordinate decomposition of the dual numbers into their degree pieces. -/
@[instance_reducible]
private noncomputable def decomposition : DirectSum.Decomposition (dualNumberGrade R) where
  decompose' := decompose R
  left_inv := coeAddMonoidHom_decompose R
  right_inv := decompose_coeAddMonoidHom R

end DualNumberGrading

/-- The dual numbers are the internal direct sum of the scalar piece in degree zero and the
infinitesimal piece in degree two. -/
theorem isInternal_dualNumberGrade : DirectSum.IsInternal (dualNumberGrade R) :=
  letI := DualNumberGrading.decomposition R
  DirectSum.Decomposition.isInternal _

/-- The standard degree-two grading makes `DualNumber R` a graded algebra. This is a definition
rather than a global instance so callers choose when to install it locally. -/
@[instance_reducible]
noncomputable def dualNumberGradedAlgebra : GradedAlgebra (dualNumberGrade R) := by
  letI := dualNumberGradedMonoid R
  exact DirectSum.IsInternal.gradedAlgebra (isInternal_dualNumberGrade R)

end TauCeti
