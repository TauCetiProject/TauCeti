/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.Sampling
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Polynomial

/-! # Sign determination on the whole real line

`sampleProduct Q` multiplies the nonzero members of a finite polynomial family.
Its `Polynomial.signSamples` realize all and only the sign conditions realized anywhere
in an ordered real closed field. Roots supply the point samples, Rolle supplies samples
in bounded complementary intervals, and two outer points cover the unbounded intervals.
Zero inputs, repeated factors, constant families, and empty tuples are included.

`fullInverse_mulVec_signSum_pos_iff` characterizes whole-line realizability by positivity
of the recovered BKR sample counts. These counts count sample points, not all points of
the real line; no assertion of finite cardinality for an interval is made.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, second edition](https://doi.org/10.1007/3-540-33099-2),
Chapter 10, for univariate sign determination by roots and complementary intervals.
-/

public section

namespace TauCeti.SignDetermination

open Polynomial Finset SignType
open scoped Matrix

section Product

variable {R J : Type*} [CommSemiring R] [Fintype J]

open scoped Classical in
/-- The product of the nonzero input polynomials. It is `1` if all inputs are zero. -/
noncomputable def sampleProduct (Q : J → R[X]) : R[X] :=
  ∏ j ∈ Finset.univ.filter (fun j => Q j ≠ 0), Q j

open scoped Classical in
/-- The sampling polynomial omits precisely the zero inputs. -/
theorem sampleProduct_def (Q : J → R[X]) :
    sampleProduct Q = ∏ j ∈ Finset.univ.filter (fun j => Q j ≠ 0), Q j := (rfl)

/-- Every nonzero input divides the sampling polynomial. -/
theorem dvd_sampleProduct (Q : J → R[X]) {j : J} (hj : Q j ≠ 0) : Q j ∣ sampleProduct Q := by
  classical
  rw [sampleProduct_def]
  exact dvd_prod_of_mem Q (by simp [hj])

/-- Omitting zero inputs makes the sampling polynomial nonzero. -/
theorem sampleProduct_ne_zero [IsDomain R] (Q : J → R[X]) : sampleProduct Q ≠ 0 := by
  classical
  rw [sampleProduct_def]
  exact prod_ne_zero_iff.mpr fun j hj => (mem_filter.mp hj).2

/-- A family of zero polynomials has sampling polynomial `1`. -/
@[simp]
theorem sampleProduct_zero : sampleProduct (fun _ : J => (0 : R[X])) = 1 := by
  classical
  simp [sampleProduct_def]

/-- An empty tuple has sampling polynomial `1`. -/
@[simp]
theorem sampleProduct_of_isEmpty [IsEmpty J] (Q : J → R[X]) : sampleProduct Q = 1 := by
  classical
  simp [sampleProduct_def]

end Product

variable {R J : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R] [Fintype J]

/-- Every whole-line sign condition occurs at a root, critical point, or outer sample
of the product of the nonzero inputs. The same sample works for every input. -/
theorem exists_mem_signSamples_sign_eq (Q : J → R[X]) (x : R) :
    ∃ y ∈ (sampleProduct Q).signSamples, ∀ j, sign ((Q j).eval y) = sign ((Q j).eval x) := by
  obtain ⟨y, hy, hxy | hfree⟩ :=
    (sampleProduct Q).exists_mem_signSamples (sampleProduct_ne_zero Q) x
  · exact ⟨y, hy, fun j => by rw [hxy]⟩
  refine ⟨y, hy, fun j => ?_⟩
  by_cases hj : Q j = 0
  · simp [hj]
  have hne : ∀ z ∈ Set.uIcc x y, (Q j).eval z ≠ 0 := by
    intro z hz hz0
    exact hfree z hz (eval_eq_zero_of_dvd_of_eval_eq_zero (dvd_sampleProduct Q hj) hz0)
  rcases le_total x y with hxy | hyx
  · exact ((Q j).sign_eval_const hxy
      (fun z hz => hne z (Set.Icc_subset_uIcc hz))).symm
  · exact (Q j).sign_eval_const hyx (fun z hz => hne z (Set.Icc_subset_uIcc' hz))

/-- A sign condition has positive sample count exactly when it is realized on the whole line.
Use this characterization before expanding sample membership with `Finset.signCount_pos`. -/
theorem signCount_signSamples_pos_iff (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount (sampleProduct Q).signSamples Q σ ↔
      ∃ x : R, ∀ j, sign ((Q j).eval x) = σ j := by
  rw [signCount_pos]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hsign⟩ := exists_mem_signSamples_sign_eq Q x
    exact ⟨y, hy, fun j => (hsign j).trans (hx j)⟩

/-- Inverting the BKR moments of the sample set determines whole-line realizability.
The recovered entries are rational casts of natural sample counts. -/
theorem fullInverse_mulVec_signSum_pos_iff [DecidableEq J]
    (Q : J → R[X]) (σ : J → SignType) :
    0 < (fullInverse J *ᵥ (fun e =>
      (signSum (sampleProduct Q).signSamples (∏ j, Q j ^ (e j).val) : ℚ))) σ ↔
      ∃ x : R, ∀ j, sign ((Q j).eval x) = σ j := by
  rw [fullInverse_mulVec_signSum]
  simp only [Nat.cast_pos, signCount_signSamples_pos_iff]

end TauCeti.SignDetermination
