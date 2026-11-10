/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation

/-!
# Length and descents in the marked Weyl presentation

The isomorphism stored in `TauCeti.weylCoxeterSystem` identifies the Weyl group with the
abstract Coxeter group of its base. Its inverse is the original `TauCeti.weylCoxeterHom`,
not an isomorphism with an unspecified permutation of the simple generators.

This file identifies abstract presentation length with the number of positive roots sent
negative. Reduced words
and right descents are preserved and reflected; in particular a right descent is detected
by the sign of the image of the corresponding positive simple root. The length function
also agrees with that of any other Coxeter system with the same marked simple reflections,
even if its Coxeter matrix is presented differently.

No spanning assumption on the root or coroot families is required.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1, no. 5.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, §§1.7--1.9.
-/

public section

namespace RootPairing

open TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- Length in the abstract presented group is the number of positive roots made negative
by its image under the specified presentation homomorphism. -/
@[simp]
theorem presentation_length_eq_inversions (w : (coxeterMatrixOfBase P b).Group) :
    (coxeterMatrixOfBase P b).toCoxeterSystem.length w =
      (inversions P b (weylCoxeterHom P b w)).ncard := by
  have h := CoxeterSystem.length_map (coxeterMatrixOfBase P b).toCoxeterSystem
    (weylCoxeterSystem P b).mulEquiv.symm w
  simpa only [toCoxeterSystem_map_weylCoxeterSystem_mulEquiv_symm, length_weylCoxeterSystem_eq,
    weylCoxeterSystem_mulEquiv_symm_apply] using h.symm

/-- The marked presentation preserves and reflects reduced words. -/
theorem isReduced_presentation_iff (l : List b.support) :
    (coxeterMatrixOfBase P b).toCoxeterSystem.IsReduced l ↔
      (weylCoxeterSystem P b).IsReduced l := by
  simp only [CoxeterSystem.IsReduced, presentation_length_eq_inversions,
    weylCoxeterHom_wordProd, weylCoxeterSystem_wordProd, length_weylCoxeterSystem_eq]

/-- Right descents in the Weyl Coxeter system are exactly the simple roots whose images
are negative. The root on the right is positive before applying `w`. -/
theorem isRightDescent_weylCoxeterSystem_iff (w : P.weylGroup) (i : b.support) :
    (weylCoxeterSystem P b).IsRightDescent w i ↔
      ¬ b.IsPos (P.weylGroupToPerm w (i : ι)) := by
  rw [CoxeterSystem.IsRightDescent, weylCoxeterSystem_simple,
    length_weylCoxeterSystem_eq, length_weylCoxeterSystem_eq,
    ncard_inversions_mul_ofIdx_lt_iff P b w (b.isPos_of_mem_support i.2),
    mem_inversions, and_iff_right (b.isPos_of_mem_support i.2)]

/-- The specified presentation homomorphism preserves and reflects right descents. -/
theorem isRightDescent_presentation_iff
    (w : (coxeterMatrixOfBase P b).Group) (i : b.support) :
    (coxeterMatrixOfBase P b).toCoxeterSystem.IsRightDescent w i ↔
      (weylCoxeterSystem P b).IsRightDescent (weylCoxeterHom P b w) i := by
  simp only [CoxeterSystem.IsRightDescent, presentation_length_eq_inversions,
    map_mul, CoxeterMatrix.toCoxeterSystem_simple, weylCoxeterHom_apply_simple,
    weylCoxeterSystem_simple, length_weylCoxeterSystem_eq]

/-- Abstract right descents are detected by the sign of the image of the marked simple
root, rather than by a choice of an unmarked Coxeter structure. -/
theorem isRightDescent_presentation_iff_not_isPos
    (w : (coxeterMatrixOfBase P b).Group) (i : b.support) :
    (coxeterMatrixOfBase P b).toCoxeterSystem.IsRightDescent w i ↔
      ¬ b.IsPos (P.weylGroupToPerm (weylCoxeterHom P b w) (i : ι)) := by
  rw [isRightDescent_presentation_iff, isRightDescent_weylCoxeterSystem_iff]

/-- Any Coxeter system on the Weyl group with the same indexed simple reflections has
length equal to the intrinsic inversion count. The matrix need not be definitionally
`coxeterMatrixOfBase P b`. -/
theorem length_eq_ncard_inversions_of_simple_eq {C : CoxeterMatrix b.support}
    (cs : CoxeterSystem C P.weylGroup)
    (hcs : ∀ i, cs.simple i = weylGroup.ofIdx P (i : ι)) (w : P.weylGroup) :
    cs.length w = (inversions P b w).ncard := by
  exact (cs.length_eq_of_simple_eq (weylCoxeterSystem P b)
    (by simpa only [weylCoxeterSystem_simple] using hcs) w).trans
    (length_weylCoxeterSystem_eq P b w)

end RootPairing
