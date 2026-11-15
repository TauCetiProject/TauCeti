/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Product.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Graded

/-!
# Products and internal grading on triangulated Grothendieck groups

For pretriangulated categories with chosen triangulated grading autoequivalences `e` and `e'`,
the componentwise autoequivalence `e.prod e'` grades their product. The canonical product
isomorphism on triangulated `K₀` intertwines its internal `ℤ`-action with the two component
actions, in both directions. In particular the product decomposition is an isomorphism of
graded additive invariants, not just an isomorphism of abelian groups.

The internal grading shifts here need not be the triangulated suspensions. The suspension acts
by a sign on `K₀`, whereas the internal grading is the action induced by the chosen
autoequivalence. The proof uses the equivariance of the two triangulated projection functors;
no choices of representatives or of zero objects fixed by the grading are needed.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Exercise 9.15, for triangulated `K₀`.
* Zsuzsanna Dancso and Anthony Licata, *Koszul algebras and flow lattices*, Section 2.2,
  for the internal shift action on graded Grothendieck groups.
-/

public section

namespace TauCeti.TriangulatedK0

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [EssentiallySmall.{w'} D]
  (e : C ≌ C) [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
  (e' : D ≌ D) [e'.functor.CommShift ℤ] [e'.functor.IsTriangulated]

/-- The product decomposition of triangulated `K₀` is equivariant for every internal degree.
The action on the product category is induced by the componentwise grading autoequivalence. -/
-- Not a simp lemma: `shiftZPow_apply` and `prodEquiv_apply` already normalize its left side.
theorem prodEquiv_shiftZPow (n : ℤ) (x : TriangulatedK0 (C × D)) :
    prodEquiv (shiftZPow (e.prod e') n x) =
      (shiftZPow e n (prodEquiv x).1, shiftZPow e' n (prodEquiv x).2) := by
  simp only [prodEquiv_apply]
  exact Prod.ext
    (map_shiftZPow (F := CategoryTheory.Prod.fst C D) (Iso.refl _) n x)
    (map_shiftZPow (F := CategoryTheory.Prod.snd C D) (Iso.refl _) n x)

/-- The inverse product decomposition also intertwines the internal grading actions.
Thus assembling a pair of classes commutes with every integer grading shift. -/
-- Not a simp lemma: `shiftZPow_apply` already unfolds the actions on its left side.
theorem prodEquiv_symm_shiftZPow (n : ℤ) (x : TriangulatedK0 C) (y : TriangulatedK0 D) :
    (prodEquiv (C := C) (D := D)).symm (shiftZPow e n x, shiftZPow e' n y) =
      shiftZPow (e.prod e') n ((prodEquiv (C := C) (D := D)).symm (x, y)) := by
  apply (prodEquiv (C := C) (D := D)).injective
  simp only [AddEquiv.apply_symm_apply, prodEquiv_shiftZPow]

end TauCeti.TriangulatedK0
