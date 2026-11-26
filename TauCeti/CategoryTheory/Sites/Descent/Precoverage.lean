/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import TauCeti.CategoryTheory.Sites.Descent.IsStack

/-!
# Characterization of (pre)stacks for a small precoverage

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J : Precoverage C` a `t`-small
precoverage (`Precoverage.Small.{t} J`) satisfying `J.HasPullbacks` and
`J.IsStableUnderBaseChange`. This file proves that to show `F` is a prestack (resp. a stack) for
`J.toGrothendieck`, it suffices to check `F.IsPrestackFor E.presieve₀` (resp.
`F.IsStackFor E.presieve₀`) on `t`-small `0`-hypercovers `E` of `J`.

These are the prestack and stack versions of Christian Merten's sheaf criterion
`Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small`
(`Mathlib.CategoryTheory.Sites.Coverage`), and refine Joël Riou's `IsPrestack.of_precoverage` and
`IsStack.of_precoverage` (`Mathlib.CategoryTheory.Sites.Descent.Precoverage`) both to `t`-small
`0`-hypercovers and by dropping the `[HasPullbacks C]`, `[J.HasIsos]`, and
`[J.IsStableUnderComposition]` assumptions.

## Main results

* `CategoryTheory.Pseudofunctor.IsPrestack.of_precoverage_of_small`: for a `t`-small precoverage
  `J` with `J.HasPullbacks` and `J.IsStableUnderBaseChange`, checking `F.IsPrestackFor E.presieve₀`
  on `t`-small `0`-hypercovers `E` of `J` implies `F.IsPrestack J.toGrothendieck`.
* `CategoryTheory.Pseudofunctor.IsStack.of_precoverage_of_small`: for a `t`-small precoverage `J`
  with `J.HasPullbacks` and `J.IsStableUnderBaseChange`, checking `F.IsStackFor E.presieve₀` on
  `t`-small `0`-hypercovers `E` of `J` implies `F.IsStack J.toGrothendieck`.

## References

* Christian Merten, `Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small`
  in `Mathlib.CategoryTheory.Sites.Coverage`.
* Joël Riou, `IsPrestack.of_precoverage` and `IsStack.of_precoverage` in
  `Mathlib.CategoryTheory.Sites.Descent.Precoverage`.
* The Stacks Project, Section 8.4, *Stacks*, Tag 026F.
-/

public section

universe t v' v u' u

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- If `J` is a `t`-small precoverage satisfying `J.HasPullbacks` and `J.IsStableUnderBaseChange`,
then to show that `F` is a prestack for `J.toGrothendieck` it suffices to check
`F.IsPrestackFor E.presieve₀` on `t`-small `0`-hypercovers `E` of `J`. -/
theorem IsPrestack.of_precoverage_of_small {J : Precoverage C}
    [J.HasPullbacks] [J.IsStableUnderBaseChange] [Precoverage.Small.{t} J]
    (hF : ∀ (X : C) (E : Precoverage.ZeroHypercover.{t} J X), F.IsPrestackFor E.presieve₀) :
    F.IsPrestack J.toGrothendieck where
  isSheaf {S} M N := by
    rw [isSheaf_iff_isSheaf_of_type, over_toGrothendieck_eq_toGrothendieck_comap_forget,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{t}]
    intro X E
    rw [Presieve.isSheafFor_iff_generate]
    refine IsPrestackFor.isSheafFor' X ?_ M N
    rw [PreZeroHypercover.presieve₀, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows,
      Sieve.ofArrows, IsPrestackFor_generate_iff]
    exact hF X.left (E.map (Over.forget S) le_rfl)

/-- If `J` is a `t`-small precoverage satisfying `J.HasPullbacks` and `J.IsStableUnderBaseChange`,
then to show that `F` is a stack for `J.toGrothendieck` it suffices to check
`F.IsStackFor E.presieve₀` on `t`-small `0`-hypercovers `E` of `J`. -/
theorem IsStack.of_precoverage_of_small {J : Precoverage C}
    [J.HasPullbacks] [J.IsStableUnderBaseChange] [Precoverage.Small.{t} J]
    (hF : ∀ (X : C) (E : Precoverage.ZeroHypercover.{t} J X), F.IsStackFor E.presieve₀) :
    F.IsStack J.toGrothendieck := by
  have : F.IsPrestack J.toGrothendieck :=
    IsPrestack.of_precoverage_of_small fun X E ↦ (hF X E).isPrestackFor
  refine .of_isStackFor fun X R hR ↦ ?_
  rw [← Precoverage.toGrothendieck_toCoverage, Coverage.mem_toGrothendieck] at hR
  induction hR with
  | of X S hS =>
    obtain ⟨E₀, rfl⟩ := S.exists_eq_preZeroHypercover
    let E : Precoverage.ZeroHypercover J X := ⟨E₀, hS⟩
    let E' := E.restrictIndexOfSmall.{t}
    rw [IsStackFor_generate_iff]
    exact (hF X E').of_le F (Precoverage.generate_mem_toGrothendieck E'.mem₀) (by simp [E, E'])
  | top X =>
    exact F.isStackFor_top X
  | transitive X R S hR hS ihR ihS =>
    have hR' : R ∈ J.toGrothendieck X := by
      rwa [← Precoverage.toGrothendieck_toCoverage, Coverage.mem_toGrothendieck]
    have hS' : S ∈ J.toGrothendieck X := by
      rw [← Precoverage.toGrothendieck_toCoverage, Coverage.mem_toGrothendieck]
      exact .transitive X R S hR hS
    refine IsStackFor.of_pullback' (J := J.toGrothendieck) hS'
      (v := fun g : R.arrows.category ↦ g.obj.hom)
      (by rwa [Sieve.ofArrows_category]) (by rwa [Presieve.ofArrows_category])
      fun g ↦ ihS g.property

end CategoryTheory.Pseudofunctor
