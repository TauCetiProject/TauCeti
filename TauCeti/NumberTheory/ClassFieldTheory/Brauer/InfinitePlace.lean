/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Congr
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Real
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Brauer invariants at archimedean completions

For an infinite place `w`, `infiniteInvMap w` is the invariant of the cohomological Brauer group
of Mathlib's completion `w.Completion`. At a real place it sends the unique nonzero class to
`1/2` in `ℚ/ℤ`; at a complex place the Brauer group vanishes. Its image is consequently the
two-torsion subgroup at a real place and zero at a complex place.

These maps provide the archimedean terms in sums of local Brauer invariants. The real value is
intrinsic: it depends only on whether the class vanishes, not on an identification of separable
closures used to transport the real Brauer-group calculation.
`infiniteInvMap_eq_realInv_comp` makes this independence explicit for every additive
identification with the real Brauer group.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1.
* J. S. Milne, *Class Field Theory*, Chapter VIII, §4.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K]

open scoped Classical in
/-- The archimedean Brauer invariant on the canonical completion: the normalized real invariant
at a real place, and the zero map at a complex place. -/
def infiniteInvMap (w : InfinitePlace K) : Br w.Completion →+ AddCircle (1 : ℚ) :=
  if hw : w.IsReal then
    realInv.comp (brCongr (Completion.ringEquivRealOfIsReal hw)).toAddMonoidHom
  else 0

/-- At a real place the archimedean invariant is the real invariant transported through
Mathlib's identification of the completion with `ℝ`. -/
@[simp]
theorem infiniteInvMap_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    infiniteInvMap w =
      realInv.comp (brCongr (Completion.ringEquivRealOfIsReal hw)).toAddMonoidHom := by
  simp [infiniteInvMap, hw]

/-- At a complex place the archimedean invariant is the zero homomorphism. -/
@[simp]
theorem infiniteInvMap_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    infiniteInvMap w = 0 := by
  simp [infiniteInvMap, not_isReal_iff_isComplex.mpr hw]

/-- The Brauer group of a complex completion is trivial. -/
theorem brCompletion_eq_zero_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex)
    (x : Br w.Completion) : x = 0 := by
  let e := brCongr (Completion.ringEquivComplexOfIsComplex hw)
  exact e.injective (Subsingleton.elim (e x) (e 0))

open scoped Classical in
/-- The real-place invariant is zero on the zero class and `1/2` on every nonzero class. -/
theorem infiniteInvMap_apply_of_isReal (w : InfinitePlace K) (hw : w.IsReal)
    (x : Br w.Completion) :
    infiniteInvMap w x = if x = 0 then 0 else ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [infiniteInvMap_of_isReal w hw, AddMonoidHom.comp_apply, realInv_apply]
  simp only [AddEquiv.coe_toAddMonoidHom, EmbeddingLike.map_eq_zero_iff]

/-- At a real place, every additive identification with the real Brauer group gives the same
normalized invariant. In particular, changing the lift of a field isomorphism to separable
closures does not change the invariant. -/
theorem infiniteInvMap_eq_realInv_comp (w : InfinitePlace K) (hw : w.IsReal)
    (e : Br w.Completion ≃+ Br ℝ) :
    infiniteInvMap w = realInv.comp e.toAddMonoidHom := by
  classical
  ext x
  rw [infiniteInvMap_apply_of_isReal w hw, AddMonoidHom.comp_apply, realInv_apply]
  by_cases hx : x = 0
  · subst x
    simp
  · have he : e.toAddMonoidHom x ≠ 0 := fun h => hx (e.injective (h.trans e.map_zero.symm))
    simp only [hx, he, ite_false]

/-- The invariant at a complex place always vanishes. -/
theorem infiniteInvMap_eq_zero_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex)
    (x : Br w.Completion) : infiniteInvMap w x = 0 := by
  rw [infiniteInvMap_of_isComplex w hw, AddMonoidHom.zero_apply]

/-- At a real place the image of the invariant is precisely the two-torsion of `ℚ/ℤ`. -/
theorem range_infiniteInvMap_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    Set.range (infiniteInvMap w) =
      (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (2 : ℤ) : Set (AddCircle (1 : ℚ))) := by
  rw [infiniteInvMap_of_isReal w hw, AddMonoidHom.coe_comp, Set.range_comp,
    AddEquiv.coe_toAddMonoidHom,
    (brCongr (Completion.ringEquivRealOfIsReal hw)).surjective.range_eq,
    Set.image_univ, range_realInv]

/-- At a complex place the image of the invariant is the singleton zero. -/
theorem range_infiniteInvMap_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    Set.range (infiniteInvMap w) = {0} := by
  rw [infiniteInvMap_of_isComplex w hw]
  simp

/-- Every archimedean invariant is injective, including at a complex place where its domain
is trivial. -/
theorem infiniteInvMap_injective (w : InfinitePlace K) : Function.Injective (infiniteInvMap w) := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [infiniteInvMap_of_isReal w hw]
    exact realInv_injective.comp (brCongr (Completion.ringEquivRealOfIsReal hw)).injective
  · intro x y _
    rw [brCompletion_eq_zero_of_isComplex w hw x, brCompletion_eq_zero_of_isComplex w hw y]

/-- An archimedean invariant vanishes exactly when its Brauer class vanishes. -/
@[simp]
theorem infiniteInvMap_eq_zero_iff (w : InfinitePlace K) (x : Br w.Completion) :
    infiniteInvMap w x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (infiniteInvMap_injective w)

/-- At every real place there is a Brauer class with invariant `1/2`. -/
theorem exists_infiniteInvMap_eq_half_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ x : Br w.Completion, infiniteInvMap w x = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨x, hx⟩ := (brCongr (Completion.ringEquivRealOfIsReal hw)).surjective
    (realClass (Additive.ofMul (-1 : ℝˣ)))
  refine ⟨x, ?_⟩
  rw [infiniteInvMap_of_isReal w hw, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hx,
    realInv_realClass]
  norm_num

end TauCeti.ClassFieldTheory
