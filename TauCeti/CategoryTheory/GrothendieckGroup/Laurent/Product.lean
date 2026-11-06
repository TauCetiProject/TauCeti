/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.Product
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Product

/-!
# Laurent Grothendieck groups of product categories

For graded exact categories `E` and `E'`, the canonical equivalence
`LaurentK0 (E.prod E') ≃ₗ[LaurentPolynomial ℤ] LaurentK0 E × LaurentK0 E'` sends the class of
`(X, Y)` to `([X], [Y])`. Its inverse is the sum of the maps induced by inserting a zero object
in either coordinate. Thus a product decomposition of graded exact categories gives a product
decomposition of their Laurent modules, retaining the internal shift action.

The equivalence is natural in graded conflation-exact functors. On underlying additive groups,
it is the existing exact Grothendieck group product equivalence, rather than a new presentation.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Sections 6–7, for exact Grothendieck groups.
* Zsuzsanna Dancso and Anthony Licata, *Koszul algebras and flow lattices*, Section 2.2,
  for the Laurent action on graded Grothendieck groups.
-/

public section

namespace TauCeti.LaurentK0

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w₁ w₂ v v' v₁ v₂ u u' u₁ u₂

section Product

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
  (E : GradedExactStructure C) (E' : GradedExactStructure D)

private noncomputable def prodAddEquiv :
    LaurentK0 (E.prod E') ≃+ LaurentK0 E × LaurentK0 E' :=
  -- Compare conflation classes explicitly before using the ungraded product equivalence.
  (ofExactK0 (E.prod E')).symm.trans
    ((ExactK0.ofLEEquiv (E := (E.prod E').toExactStructure)
      (E'' := E.toExactStructure.prod E'.toExactStructure)
      (fun _ => by rw [GradedExactStructure.prod_toExactStructure])).trans
        ((ExactK0.prodEquiv E.toExactStructure E'.toExactStructure).trans
          ((ofExactK0 E).prodCongr (ofExactK0 E'))))

private theorem prodAddEquiv_of (X : C × D) :
    prodAddEquiv E E' (of (E.prod E') X) = (of E X.1, of E' X.2) := by
  simp [prodAddEquiv, ← ofExactK0_exactK0_of]

/-- Graded exact `K₀` takes a product of graded exact categories to the product of their Laurent
modules. Its two components are induced by the projection functors. -/
noncomputable def prodEquiv :
    LaurentK0 (E.prod E') ≃ₗ[LaurentPolynomial ℤ] LaurentK0 E × LaurentK0 E' :=
  LinearEquiv.ofBijective ((map (GradedConflationExact.fst E E')).prod
    (map (GradedConflationExact.snd E E'))) (by
      have he : ((map (GradedConflationExact.fst E E')).prod
          (map (GradedConflationExact.snd E E'))).toAddMonoidHom.comp
            (ofExactK0 (E.prod E')).toAddMonoidHom =
          (prodAddEquiv E E').toAddMonoidHom.comp
            (ofExactK0 (E.prod E')).toAddMonoidHom :=
        ExactK0.hom_ext fun X => by simp [prodAddEquiv_of]
      have hfun : ⇑((map (GradedConflationExact.fst E E')).prod
          (map (GradedConflationExact.snd E E'))) = ⇑(prodAddEquiv E E') := by
        funext x
        obtain ⟨x, rfl⟩ := (ofExactK0 (E.prod E')).surjective x
        exact DFunLike.congr_fun he x
      rw [hfun]
      exact (prodAddEquiv E E').bijective)

/-- The forward product equivalence is induced by the two graded projections. -/
@[simp]
theorem prodEquiv_apply (x : LaurentK0 (E.prod E')) :
    prodEquiv E E' x =
      (map (GradedConflationExact.fst E E') x, map (GradedConflationExact.snd E E') x) :=
  (rfl)

/-- The product equivalence sends an object class to the classes of its two components. -/
theorem prodEquiv_of (X : C × D) :
    prodEquiv E E' (of (E.prod E') X) = (of E X.1, of E' X.2) := by
  simp

/-- The inverse product equivalence is the sum of the two graded zero-section maps. -/
theorem prodEquiv_symm_apply (x : LaurentK0 E × LaurentK0 E') :
    (prodEquiv E E').symm x =
      map (GradedConflationExact.sectL E E') x.1 +
        map (GradedConflationExact.sectR E E') x.2 := by
  have hzC : of E (0 : C) = 0 := by
    rw [← ofExactK0_exactK0_of, ExactK0.of_zero, map_zero]
  have hzD : of E' (0 : D) = 0 := by
    rw [← ofExactK0_exactK0_of, ExactK0.of_zero, map_zero]
  have hL : (prodEquiv E E').toLinearMap.comp (map (GradedConflationExact.sectL E E')) =
      LinearMap.inl (LaurentPolynomial ℤ) (LaurentK0 E) (LaurentK0 E') := by
    apply hom_ext
    intro X
    simp [hzD]
  have hR : (prodEquiv E E').toLinearMap.comp (map (GradedConflationExact.sectR E E')) =
      LinearMap.inr (LaurentPolynomial ℤ) (LaurentK0 E) (LaurentK0 E') := by
    apply hom_ext
    intro X
    simp [hzC]
  apply (prodEquiv E E').injective
  rw [LinearEquiv.apply_symm_apply, map_add]
  simpa using (congrArg₂ (· + ·) (DFunLike.congr_fun hL x.1)
    (DFunLike.congr_fun hR x.2)).symm

/-- The inverse product equivalence sends the pair `([X], [Y])` to `[(X, Y)]`. -/
@[simp]
theorem prodEquiv_symm_of (X : C) (Y : D) :
    (prodEquiv E E').symm (of E X, of E' Y) = of (E.prod E') (X, Y) := by
  apply (prodEquiv E E').injective
  simp

end Product

section Naturality

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
  {C' : Type u₁} [Category.{v₁} C'] [Preadditive C'] [HasZeroObject C']
  [HasBinaryBiproducts C'] [EssentiallySmall.{w₁} C']
  {D' : Type u₂} [Category.{v₂} D'] [Preadditive D'] [HasZeroObject D']
  [HasBinaryBiproducts D'] [EssentiallySmall.{w₂} D']
  {E : GradedExactStructure C} {E' : GradedExactStructure D}
  {K : GradedExactStructure C'} {K' : GradedExactStructure D'}
  {F : C ⥤ C'} {G : D ⥤ D'} [F.Additive] [G.Additive]

/-- The product decomposition of Laurent `K₀` is natural in graded conflation-exact functors in
both variables. -/
theorem prodEquiv_naturality (hF : GradedConflationExact E K F)
    (hG : GradedConflationExact E' K' G) :
    (prodEquiv K K').toLinearMap.comp (map (hF.prod hG)) =
      ((map hF).prodMap (map hG)).comp (prodEquiv E E').toLinearMap := by
  apply hom_ext
  intro X
  simp

end Naturality

end TauCeti.LaurentK0
