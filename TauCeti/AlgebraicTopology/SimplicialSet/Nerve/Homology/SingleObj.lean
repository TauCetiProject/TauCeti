/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Zero

/-!
# Category homology of a single-object category

For a monoid `G`, `SingleObj G` has object `SingleObj.star G` and endomorphisms `G` with
`f ≫ g = g * f` (`CategoryTheory.SingleObj.comp_as_mul`). This file records the low-degree chain
differentials (`TauCeti.ιCategoryChainComplex₁_d_singleObj`,
`TauCeti.ιCategoryChainComplex₂_d_singleObj`, `TauCeti.ιCategoryChainComplex₃_d_singleObj`,
`TauCeti.categoryChainComplex_const_d_one_zero_singleObj`) and coinvariant `H₀` universal property
(`TauCeti.epi_ιCategoryHomology₀_singleObj`, `TauCeti.descCategoryHomology₀SingleObj`).

## References

* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory* (1967), Appendix II, §3.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, §3.5.
-/

public section

noncomputable section

open CategoryTheory Category Limits

universe u u' v'

namespace TauCeti

variable {G : Type u} [Monoid G] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{u} A] [Preadditive A]

attribute [local simp] SingleObj.comp_as_mul

/-- On `SingleObj G`, the degree-`1` differential on `g : G` acts by `M(g) - 𝟙`. -/
@[reassoc] lemma ιCategoryChainComplex₁_d_singleObj (M : SingleObj G ⥤ A) (g : G) :
    ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom g) ≫ (categoryChainComplex M).d 1 0 =
      (M.map (Quiver.SingleObj.toHom g) - 𝟙 (M.obj (SingleObj.star G))) ≫
        ιCategoryChainComplex₀ M (SingleObj.star G) := by
  rw [ιCategoryChainComplex₁_d, Preadditive.sub_comp, id_comp]

/-- On `SingleObj G`, `d 2 1` sends `(f, g)` to `M(f)(g) - (g * f) + f`. -/
@[reassoc] lemma ιCategoryChainComplex₂_d_singleObj (M : SingleObj G ⥤ A) (f g : G) :
    ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g) ≫
        (categoryChainComplex M).d 2 1 =
      M.map (Quiver.SingleObj.toHom f) ≫ ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom g) -
        ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom (g * f)) +
        ιCategoryChainComplex₁ M (Quiver.SingleObj.toHom f) := by simp

/-- On `SingleObj G`, `d 3 2` is `M(f)(g, h) - (g * f, h) + (f, h * g) - (f, g)`. -/
@[reassoc] lemma ιCategoryChainComplex₃_d_singleObj (M : SingleObj G ⥤ A) (f g h : G) :
    ιCategoryChainComplex₃ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g)
        (Quiver.SingleObj.toHom h) ≫ (categoryChainComplex M).d 3 2 =
      M.map (Quiver.SingleObj.toHom f) ≫
          ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom g) (Quiver.SingleObj.toHom h) -
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom (g * f)) (Quiver.SingleObj.toHom h) +
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom (h * g)) -
        ιCategoryChainComplex₂ M (Quiver.SingleObj.toHom f) (Quiver.SingleObj.toHom g) := by simp

@[simp] lemma categoryChainComplex_const_d_one_zero_singleObj (G : Type u) [Monoid G] (X : A) :
    (categoryChainComplex ((Functor.const (SingleObj G)).obj X)).d 1 0 = 0 := by
  ext σ; obtain ⟨⟨⟩, ⟨⟩, g, rfl⟩ := ComposableArrows.mk₁_surjective σ; simp

section DegreeZero

variable [CategoryWithHomology A]

instance epi_ιCategoryHomology₀_singleObj (M : SingleObj G ⥤ A) :
    Epi (ιCategoryHomology₀ M (SingleObj.star G)) where
  left_cancellation _ _ h := categoryHomology₀_hom_ext fun ⟨⟩ ↦ h

/-- Universal coinvariant morphism `categoryHomology M 0 ⟶ T` from a `G`-invariant morphism `u`. -/
def descCategoryHomology₀SingleObj (M : SingleObj G ⥤ A) {T : A} (u : M.obj (SingleObj.star G) ⟶ T)
    (hu : ∀ g : SingleObj.star G ⟶ SingleObj.star G, M.map g ≫ u = u) : categoryHomology M 0 ⟶ T :=
  (isColimitCategoryHomology₀Cocone M).desc (Cocone.mk T
    { app _ := u, naturality _ _ g := (hu g).trans ((comp_id u).symm.trans (by simp)) })

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_descSingleObj (M : SingleObj G ⥤ A) {T : A}
    (u : M.obj (SingleObj.star G) ⟶ T)
    (hu : ∀ g : SingleObj.star G ⟶ SingleObj.star G, M.map g ≫ u = u) :
    ιCategoryHomology₀ M (SingleObj.star G) ≫ descCategoryHomology₀SingleObj M u hu = u :=
  (isColimitCategoryHomology₀Cocone M).fac _ (SingleObj.star G)

end DegreeZero

end TauCeti
