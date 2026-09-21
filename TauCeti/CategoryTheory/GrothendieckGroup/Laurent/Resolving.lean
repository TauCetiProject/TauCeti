/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.FullSubcategory
public import TauCeti.CategoryTheory.GrothendieckGroup.Resolving

/-!
# The graded resolution theorem for resolving subcategories

Let `E` be a graded exact category and let `P` be a resolving property for its underlying exact
structure. If `P` is stable under the grading shift, then its induced exact structure is graded,
and the inclusion of `P` into the ambient category induces an isomorphism

```text
K₀^gr(P) ≃ K₀^gr(C)
```

of modules over `ℤ[q,q⁻¹]`. Its inverse sends the class of an object to the alternating class of
any finite `P`-resolution. In particular, shifting an object and its resolution multiplies the
Euler class by `q`.

The additive equivalence is the general resolution theorem of
`TauCeti.ExactStructure.IsResolving.resolutionEquiv`. Laurent-linearity follows because its
forward map is induced by the graded conflation-exact inclusion. Thus the common-refinement
argument establishing independence and additivity of the Euler class is inherited unchanged from
the ungraded theorem.

This differs from `TauCeti.GradedExactStructure.laurentResolutionEquiv`, which assumes that `P`
consists of projectives and compares it with the full subcategory of objects of finite
`P`-dimension. Here `P` is resolving, so every ambient object has a finite `P`-resolution, and the
comparison is with the whole category.

## Main definitions

* `TauCeti.GradedExactStructure.IsResolving.laurentResolutionEquiv`: the graded resolution theorem
  for a shift-stable resolving property.

## Main results

* `TauCeti.GradedExactStructure.IsResolving.laurentResolutionEquiv_toLinearMap`: the forward map is
  the map induced by the graded inclusion.
* `TauCeti.GradedExactStructure.IsResolving.laurentResolutionEquiv_of` and
  `TauCeti.GradedExactStructure.IsResolving.laurentResolutionEquiv_symm_of`: the values on object
  classes, with the inverse computed by any finite resolution.
* `TauCeti.GradedExactStructure.IsResolving.foldAlternating_shift_eq_T_one_smul`: shifting a
  resolved object multiplies its resolution Euler class by `q`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Theorem 7.6 and Lemma 7.6.1, for the resolution theorem.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups as
  `ℤ[q,q⁻¹]`-modules.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe w v u

namespace GradedExactStructure.IsResolving

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  (E : GradedExactStructure C) (P : ObjectProperty C)
  [E.toExactStructure.IsResolving P]

local instance : ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le (Q := ⊤) le_top

/-- The extension closure of the resolving property. -/
local notation "hP" =>
  (ExactStructure.IsResolving.isExtensionClosed (E := E.toExactStructure) (P := P))

variable (hshift : P.inverseImage E.shift.functor = P)

/-- The additive resolution equivalence transported to the graded Grothendieck groups. -/
private noncomputable def resolutionAddEquiv :
    LaurentK0 (E.fullSubcategory P hP hshift) ≃+ LaurentK0 E :=
  (LaurentK0.ofExactK0 _).symm.trans <| (GradedExactStructure.toUngraded E P hP hshift).trans <|
    (ExactStructure.IsResolving.resolutionEquiv E.toExactStructure P).trans
      (LaurentK0.ofExactK0 E)

/-- The transported resolution equivalence is the map induced by the graded inclusion. -/
private lemma resolutionAddEquiv_apply (x : LaurentK0 (E.fullSubcategory P hP hshift)) :
    resolutionAddEquiv E P hshift x =
      LaurentK0.map (GradedConflationExact.ι E P hP hshift) x := by
  obtain ⟨y, rfl⟩ := (LaurentK0.ofExactK0 _).surjective x
  have key : (resolutionAddEquiv E P hshift).toAddMonoidHom.comp
        (LaurentK0.ofExactK0 _).toAddMonoidHom =
      (LaurentK0.map (GradedConflationExact.ι E P hP hshift)).toAddMonoidHom.comp
        (LaurentK0.ofExactK0 _).toAddMonoidHom :=
    ExactK0.hom_ext fun X => by
      simp only [resolutionAddEquiv, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.trans_apply, AddEquiv.symm_apply_apply, GradedExactStructure.toUngraded_of,
        ExactStructure.IsResolving.resolutionEquiv_of, LinearMap.toAddMonoidHom_coe]
      rw [LaurentK0.ofExactK0_exactK0_of, LaurentK0.ofExactK0_exactK0_of, LaurentK0.map_of]
      exact congrArg _ (ObjectProperty.ι_obj P (X := X)).symm
  exact DFunLike.congr_fun key y

/-- **The graded resolution theorem for a resolving subcategory.** If `P` is resolving for the
underlying exact structure and stable under the grading shift, then inclusion induces an
isomorphism of graded Grothendieck groups as `ℤ[q,q⁻¹]`-modules. Its inverse is computed by the
Euler class of any finite `P`-resolution. -/
noncomputable def laurentResolutionEquiv :
    LaurentK0 (E.fullSubcategory P hP hshift) ≃ₗ[LaurentPolynomial ℤ] LaurentK0 E :=
  (resolutionAddEquiv E P hshift).toLinearEquiv fun c x => by
    simp only [resolutionAddEquiv_apply, map_smul]

/-- The forward map of the graded resolution theorem is induced by the graded conflation-exact
inclusion of the resolving subcategory. -/
@[simp]
theorem laurentResolutionEquiv_toLinearMap :
    (laurentResolutionEquiv E P hshift).toLinearMap =
      LaurentK0.map (GradedConflationExact.ι E P hP hshift) := by
  ext x
  simp [laurentResolutionEquiv, resolutionAddEquiv_apply]

/-- The graded resolution equivalence sends the class of a resolving object to its ambient
class. -/
@[simp]
theorem laurentResolutionEquiv_of (X : P.FullSubcategory) :
    laurentResolutionEquiv E P hshift
        (LaurentK0.of (E.fullSubcategory P hP hshift) X) =
      LaurentK0.of E X.obj := by
  rw [laurentResolutionEquiv, AddEquiv.coe_toLinearEquiv, resolutionAddEquiv_apply,
    LaurentK0.map_of]
  exact congrArg _ (ObjectProperty.ι_obj P (X := X))

/-- **The inverse of the graded resolution equivalence is the Euler class.** It sends the class
of an object to the alternating sum `[Q₀] - [Q₁] + ⋯ + (-1)ⁿ[Kₙ]` of the graded classes of
the terms of any finite `P`-resolution. -/
theorem laurentResolutionEquiv_symm_of {X : C}
    (r : E.toExactStructure.FiniteResolution P X) :
    (laurentResolutionEquiv E P hshift).symm (LaurentK0.of E X) =
      r.foldAlternating fun Z hZ =>
        LaurentK0.of (E.fullSubcategory P hP hshift) ⟨Z, hZ⟩ := by
  rw [← GradedExactStructure.ofExactK0_toUngraded_symm_eulerClassFullSubcategory,
    ← ExactStructure.IsResolving.eulerClassOf_eq
      (E := E.toExactStructure) (P := P) (ExactStructure.IsResolving.finiteResolution X) r,
    ← ExactStructure.IsResolving.resolutionEquiv_symm_of
      (E := E.toExactStructure) (P := P) X,
    LinearEquiv.symm_apply_eq, laurentResolutionEquiv, AddEquiv.coe_toLinearEquiv]
  simp only [resolutionAddEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply, LaurentK0.ofExactK0_exactK0_of]

/-- **Shift covariance of the graded Euler class.** The alternating class of any finite
`P`-resolution of `X{1}` is `q` times the alternating class of any finite `P`-resolution of `X`.
The two resolutions need not be related. -/
theorem foldAlternating_shift_eq_T_one_smul {X : C}
    (r : E.toExactStructure.FiniteResolution P X)
    (s : E.toExactStructure.FiniteResolution P (E.shift.functor.obj X)) :
    s.foldAlternating
        (fun Z hZ => LaurentK0.of (E.fullSubcategory P hP hshift) ⟨Z, hZ⟩) =
      (T 1 : LaurentPolynomial ℤ) •
        r.foldAlternating
          (fun Z hZ => LaurentK0.of (E.fullSubcategory P hP hshift) ⟨Z, hZ⟩) := by
  apply GradedExactStructure.foldAlternating_shift_eq_T_one_smul_of_linearMap E P hP hshift
    (laurentResolutionEquiv E P hshift).symm.toLinearMap r s (LaurentK0.of E X)
    (LaurentK0.of E (E.shift.functor.obj X))
  · exact laurentResolutionEquiv_symm_of E P hshift r
  · exact laurentResolutionEquiv_symm_of E P hshift s
  · exact (LaurentK0.T_one_smul_of E X).symm

end GradedExactStructure.IsResolving

end TauCeti
