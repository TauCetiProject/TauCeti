/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Checking sheaf pullbacks on a basis

For sheaves on a topological space, a commutative square is a pullback if it is a pullback on the
sections over the opens of a basis. Lifts on the basis are natural by uniqueness and extend
using `TopCat.Sheaf.restrictHomEquivHom`. No limits in the coefficient category are assumed.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

universe u v w t

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} {ι : Type t} {B : ι → Opens X}

/-- If a square of sheaves is a pullback on sections over a basis, then it is a pullback
of sheaves. In particular, commutativity can also be checked on the basis. -/
theorem isPullback_of_isPullback_app_of_isBasis {A D E F : X.Sheaf C}
    {a : A ⟶ D} {b : A ⟶ E} {f : D ⟶ F} {g : E ⟶ F} (hB : Opens.IsBasis (Set.range B))
    (h : ∀ j, IsPullback (a.hom.app (op (B j))) (b.hom.app (op (B j)))
      (f.hom.app (op (B j))) (g.hom.app (op (B j)))) : IsPullback a b f g := by
  have sq : CommSq a b f g := ⟨by
    ext1
    exact hom_ext _ _ hB fun j ↦ (h j).w⟩
  apply IsPullback.of_isLimit' sq
  have compatible (s : PullbackCone f g) (j : ι) :
      s.fst.hom.app (op (B j)) ≫ f.hom.app (op (B j)) =
        s.snd.hom.app (op (B j)) ≫ g.hom.app (op (B j)) :=
    congrArg (fun k : s.pt ⟶ F ↦ k.hom.app (op (B j))) s.condition
  let liftApp (s : PullbackCone f g) (j : ι) :=
    (h j).lift (s.fst.hom.app (op (B j))) (s.snd.hom.app (op (B j))) (compatible s j)
  have left (s : PullbackCone f g) (j : ι) :
      liftApp s j ≫ a.hom.app (op (B j)) = s.fst.hom.app (op (B j)) :=
    (h j).lift_fst _ _ (compatible s j)
  have right (s : PullbackCone f g) (j : ι) :
      liftApp s j ≫ b.hom.app (op (B j)) = s.snd.hom.app (op (B j)) :=
    (h j).lift_snd _ _ (compatible s j)
  let liftBasis (s : PullbackCone f g) : (inducedFunctor B).op ⋙ s.pt.obj ⟶
      (inducedFunctor B).op ⋙ A.obj :=
    { app j := liftApp s j.unop
      naturality j k r := by
        let r' : op (B j.unop) ⟶ op (B k.unop) := ((inducedFunctor B).map r.unop).op
        apply (h k.unop).hom_ext
        · simp only [Functor.comp_map, Functor.op_map, Category.assoc, left]
          rw [a.hom.naturality r', reassoc_of% (left s j.unop)]
          exact s.fst.hom.naturality r'
        · simp only [Functor.comp_map, Functor.op_map, Category.assoc, right]
          rw [b.hom.naturality r', reassoc_of% (right s j.unop)]
          exact s.snd.hom.naturality r' }
  let lift (s : PullbackCone f g) : s.pt ⟶ A :=
    ObjectProperty.homMk (restrictHomEquivHom s.pt.obj A hB (liftBasis s))
  have lift_app (s : PullbackCone f g) (j : ι) :
      (lift s).hom.app (op (B j)) = liftApp s j := extend_hom_app _ _ _ _ _
  refine PullbackCone.IsLimit.mk sq.w lift ?_ ?_ ?_
  · intro s
    ext1
    exact hom_ext _ _ hB (fun j ↦ (congrArg (· ≫ _) (lift_app s j)).trans (left s j))
  · intro s
    ext1
    exact hom_ext _ _ hB (fun j ↦ (congrArg (· ≫ _) (lift_app s j)).trans (right s j))
  · intro s m hm₁ hm₂
    ext1
    refine hom_ext _ _ hB fun j ↦ (Eq.trans ?_ (lift_app s j).symm)
    exact (h j).hom_ext
      ((congrArg (fun k : s.pt ⟶ D ↦ k.hom.app (op (B j))) hm₁).trans (left s j).symm)
      ((congrArg (fun k : s.pt ⟶ E ↦ k.hom.app (op (B j))) hm₂).trans (right s j).symm)

end TopCat.Sheaf
