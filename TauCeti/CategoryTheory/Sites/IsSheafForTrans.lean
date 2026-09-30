/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Opens

/-!
# Transitivity of the sheaf condition along a cover of an open set

Let `W` be an open set, `Y i ≤ W` opens for which a presheaf of types `F` satisfies the sheaf
condition, and `S` a sieve on `W` whose members each lie in some `Y i`. If `F` is a sheaf for the
restriction of `S` to each `Y i` and separated for the restriction of `S` to each `Y i ⊓ Y j`,
then `F` is a sheaf for `S`: sections over the members of `S` glue first over each `Y i`, the
gluings agree on the overlaps `Y i ⊓ Y j`, and so glue over `W`.

Mathlib's `CategoryTheory.Presieve.isSheafFor_trans` proves a transitivity statement of this
kind for sieves on an arbitrary category, but it asks for the sheaf condition of `S` restricted to
*every* open contained in some `Y i`. Since there is at most one morphism between two opens, two
sections over `Y i` and `Y j` are compatible as soon as they agree on `Y i ⊓ Y j`, so here the
hypotheses concern only the opens `Y i` and `Y i ⊓ Y j`. This makes the statement usable when the
sheaf condition is known only on a basis of opens closed under finite intersections, such as the
rational subsets of an adic spectrum, where a cover is refined by covering each of its members.

## Main results

* `TauCeti.TopologicalSpace.Opens.isSheafFor_trans` : the transitivity statement.
-/

public section

open CategoryTheory Opposite _root_.TopologicalSpace

universe u w

namespace TauCeti.TopologicalSpace.Opens

variable {X : Type u} [_root_.TopologicalSpace X] {F : (Opens X)ᵒᵖ ⥤ Type w}

/-- **Transitivity of the sheaf condition along a cover of an open set.** Let `Y i ≤ W` be opens
covering `W` in the sense that `F` is a sheaf for the family of inclusions `Y i ⟶ W`, and let `S`
be a sieve on `W` each of whose members lies in some `Y i`. If `F` is a sheaf for the restriction
of `S` to every `Y i`, and separated for the restriction of `S` to every `Y i ⊓ Y j`, then `F` is
a sheaf for `S`.

Compare `CategoryTheory.Presieve.isSheafFor_trans`, which instead asks for the sheaf condition of
the restriction of `S` to every open contained in some `Y i`. -/
theorem isSheafFor_trans {W : Opens X} {ι : Type*} (Y : ι → Opens X) (hY : ∀ i, Y i ≤ W)
    (S : Sieve W) (hR : (Presieve.ofArrows Y fun i ↦ homOfLE (hY i)).IsSheafFor F)
    (hS : ∀ i, (S.pullback (homOfLE (hY i))).arrows.IsSheafFor F)
    (hS₂ : ∀ i j, (S.pullback
      (homOfLE (inf_le_left.trans (hY i)) : Y i ⊓ Y j ⟶ W)).arrows.IsSeparatedFor F)
    (hSY : ∀ ⦃V : Opens X⦄ (f : V ⟶ W), S f → ∃ i, V ≤ Y i) :
    S.arrows.IsSheafFor F := by
  intro x hx
  -- glue the restriction of `x` to each `Y i`
  choose t ht ht' using fun i ↦ hS i (x.pullback (homOfLE (hY i))) (hx.pullback _)
  -- the glued sections restrict to amalgamations of `x` on `Y i ⊓ Y j`, so they agree there
  have hcompat : Presieve.Arrows.Compatible F (fun i ↦ homOfLE (hY i)) t := by
    intro i j Z gi gj _
    have hij : F.map (homOfLE inf_le_left : Y i ⊓ Y j ⟶ Y i).op (t i) =
        F.map (homOfLE inf_le_right : Y i ⊓ Y j ⟶ Y j).op (t j) := by
      refine hS₂ i j (x.pullback _) _ _ (fun V g hg ↦ ?_) (fun V g hg ↦ ?_)
      · rw [← Functor.map_comp_apply, ← op_comp,
          ht i (g ≫ homOfLE inf_le_left) (by simpa using hg)]
        exact TauCeti.CategoryTheory.familyOfElements_congr x _ _ _ _
      · rw [← Functor.map_comp_apply, ← op_comp,
          ht j (g ≫ homOfLE inf_le_right) (by simpa using hg)]
        exact TauCeti.CategoryTheory.familyOfElements_congr x _ _ _ _
    have hZ : Z ≤ Y i ⊓ Y j := le_inf gi.le gj.le
    -- Factor both arrows from `Z` through the meet's canonical inclusions; uniqueness of
    -- morphisms between opens then lets `hij` identify their restrictions.
    rw [show gi = homOfLE hZ ≫ homOfLE inf_le_left from Subsingleton.elim _ _,
      show gj = homOfLE hZ ≫ homOfLE inf_le_right from Subsingleton.elim _ _, op_comp, op_comp,
      Functor.map_comp_apply, Functor.map_comp_apply, hij]
  obtain ⟨s, hs, hs'⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hR t hcompat
  refine ⟨s, fun V f hf ↦ ?_, fun s' hs'' ↦ hs' s' fun i ↦ ht' i _ fun V g hg ↦ ?_⟩
  · -- `s` restricts to `x` on every member of `S`, through the `Y i` containing it
    obtain ⟨i, hi⟩ := hSY f hf
    obtain rfl : f = homOfLE hi ≫ homOfLE (hY i) := Subsingleton.elim _ _
    rw [op_comp, Functor.map_comp_apply, hs i]
    exact ht i _ hf
  · -- any other amalgamation restricts to the amalgamation of `x` on each `Y i`
    rw [← Functor.map_comp_apply, ← op_comp, hs'' _ hg]
    -- `FamilyOfElements.pullback` evaluates `x` at the composite arrow
    rfl

end TauCeti.TopologicalSpace.Opens
