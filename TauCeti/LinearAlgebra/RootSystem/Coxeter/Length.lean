/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Presentation
public import TauCeti.GroupTheory.Coxeter.Length

/-!
# Length and descents in the marked Weyl presentation

The isomorphism stored in `TauCeti.weylCoxeterSystem` identifies the Weyl group with the
abstract Coxeter group of its base. Its inverse is the original `TauCeti.weylCoxeterHom`,
not an isomorphism with an unspecified permutation of the simple generators.

This file gives the generator and word equations in the reverse direction and identifies
abstract presentation length with the number of positive roots sent negative. Reduced words
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

/-- The inverse of the isomorphism stored in the Weyl Coxeter system is the original
homomorphism from the presentation, with the same marking of generators. -/
@[simp]
theorem weylCoxeterSystem_mulEquiv_symm_apply
    (w : (coxeterMatrixOfBase P b).Group) :
    (weylCoxeterSystem P b).mulEquiv.symm w = weylCoxeterHom P b w := by
  have h : (weylCoxeterSystem P b).mulEquiv.symm.toMonoidHom = weylCoxeterHom P b := by
    apply (coxeterMatrixOfBase P b).toCoxeterSystem.ext_simple
    intro i
    exact (weylCoxeterSystem_simple P b i).trans (weylCoxeterHom_apply_simple P b i).symm
  exact DFunLike.congr_fun h w

/-- The inverse marking sends an actual simple root reflection to its own abstract generator. -/
@[simp]
theorem weylCoxeterSystem_mulEquiv_ofIdx (i : b.support) :
    (weylCoxeterSystem P b).mulEquiv (weylGroup.ofIdx P (i : ι)) =
      (coxeterMatrixOfBase P b).simple i := by
  apply (weylCoxeterSystem P b).mulEquiv.symm.injective
  simp

/-- Passing from a word in actual simple root reflections to the presentation retains
its ordered list of letters. -/
@[simp]
theorem weylCoxeterSystem_mulEquiv_wordProd (l : List b.support) :
    (weylCoxeterSystem P b).mulEquiv (wordProd P b l) =
      (coxeterMatrixOfBase P b).toCoxeterSystem.wordProd l := by
  apply (weylCoxeterSystem P b).mulEquiv.symm.injective
  simp

/-- Length in the abstract presented group is the number of positive roots made negative
by its image under the specified presentation homomorphism. -/
@[simp]
theorem presentation_length_eq_inversions (w : (coxeterMatrixOfBase P b).Group) :
    (coxeterMatrixOfBase P b).toCoxeterSystem.length w =
      (inversions P b (weylCoxeterHom P b w)).ncard := by
  have hcs : (coxeterMatrixOfBase P b).toCoxeterSystem.map
      (weylCoxeterSystem P b).mulEquiv.symm = weylCoxeterSystem P b := by
    apply CoxeterSystem.simple_determines_coxeterSystem
    rfl
  have h := length_map (coxeterMatrixOfBase P b).toCoxeterSystem
    (weylCoxeterSystem P b).mulEquiv.symm w
  simpa only [hcs, length_weylCoxeterSystem_eq,
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
theorem length_eq_inversions_of_simple_eq {C : CoxeterMatrix b.support}
    (cs : CoxeterSystem C P.weylGroup)
    (hcs : ∀ i, cs.simple i = weylGroup.ofIdx P (i : ι)) (w : P.weylGroup) :
    cs.length w = (inversions P b w).ncard := by
  have hword (l : List b.support) : cs.wordProd l = wordProd P b l := by
    induction l with
    | nil => simp
    | cons i l ih => simp only [CoxeterSystem.wordProd_cons, wordProd_cons, hcs, ih]
  apply le_antisymm
  · obtain ⟨l, hl, hlen⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b w
    calc
      cs.length w = cs.length (cs.wordProd l) := congrArg cs.length ((hword l).trans hl).symm
      _ ≤ l.length := cs.length_wordProd_le l
      _ = _ := hlen
  · obtain ⟨l, hl, rfl⟩ := cs.exists_isReduced w
    have hlen := hl.eq
    rw [hword] at hlen ⊢
    exact (ncard_inversions_wordProd_le_length P b l).trans_eq hlen.symm

end RootPairing
