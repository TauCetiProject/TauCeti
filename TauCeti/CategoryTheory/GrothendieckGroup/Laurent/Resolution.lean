/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.Resolution
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.FullSubcategory
public import TauCeti.CategoryTheory.GrothendieckGroup.ProjectiveResolution

/-!
# The graded resolution theorem

Let `E` be a graded exact category and `P` a class of `E`-projectives containing a zero object,
closed under binary biproducts, and stable under the grading shift `{1}`. The resolution theorem
`TauCeti.ExactStructure.resolutionEquiv` identifies the exact `K₀` of `P` with the exact `K₀` of
the objects of finite `P`-dimension, the inverse sending `[X]` to the alternating class of any
finite `P`-resolution of `X`.

Both full subcategories are shift-stable, so both carry induced graded exact structures and
their Grothendieck groups are modules over `ℤ[q,q⁻¹]`, with `q` acting by the shift. This file
proves that the resolution isomorphism is an isomorphism of `ℤ[q,q⁻¹]`-modules. The forward map
is induced by the graded conflation-exact inclusion, hence `q`-linear; the content is that the
inverse, the Euler class of a finite resolution, is `q`-linear as well: the alternating class of
any finite resolution of `X{1}` is `q` times the alternating class of any finite resolution of
`X`.

## Main definitions

* `TauCeti.GradedExactStructure.laurentResolutionEquiv`: the resolution isomorphism between the
  graded Grothendieck groups, as a `ℤ[q,q⁻¹]`-linear equivalence.

## Main results

* `TauCeti.GradedExactStructure.laurentResolutionEquiv_toLinearMap`: its forward map is the map
  induced by the graded inclusion.
* `TauCeti.GradedExactStructure.laurentResolutionEquiv_of` and
  `TauCeti.GradedExactStructure.laurentResolutionEquiv_symm_of`: its values on classes; the
  inverse sends `[X]` to the alternating sum of the graded classes of the terms of any finite
  `P`-resolution of `X`.
* `TauCeti.GradedExactStructure.foldAlternating_shift_eq_T_one_smul`: **the graded Euler class**:
  the Euler class of `X{1}` is `q` times that of `X`.

## Implementation notes

The underlying exact structure of `TauCeti.GradedExactStructure.fullSubcategory` equals the
ungraded induced structure `TauCeti.ExactStructure.fullSubcategory` only propositionally, by
`TauCeti.GradedExactStructure.fullSubcategory_toExactStructure`. The two exact `K₀` groups are
compared by the identity maps `TauCeti.ExactK0.ofLE` in both directions, and the ungraded
resolution theorem is transported along them.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Theorem 7.6:
  the resolution theorem.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups as
  `ℤ[q,q⁻¹]`-modules with `[M{1}] = q[M]`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe w v u

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : GradedExactStructure C)

variable [LocallySmall.{w} C] {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [ObjectProperty.EssentiallySmall.{w} (E.admitsFiniteResolution P)]
  (hproj : P ≤ E.isProjective) (hshift : P.inverseImage E.shift.functor = P)

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

local notation "hP" => E.isExtensionClosed_of_le_isProjective hproj

local notation "hR" => E.isExtensionClosed_admitsFiniteResolution hproj

local notation "hRshift" => E.admitsFiniteResolution_inverseImage_shift hshift

/-- The resolution isomorphism between graded Grothendieck groups, as an additive equivalence:
the ungraded one transported along `toUngraded`. -/
private noncomputable def resolutionAddEquiv :
    LaurentK0 (E.fullSubcategory P hP hshift) ≃+
      LaurentK0 (E.fullSubcategory (E.admitsFiniteResolution P) hR hRshift) :=
  (LaurentK0.ofExactK0 _).symm.trans <| (toUngraded E P hP hshift).trans <|
    (E.resolutionEquiv hproj).trans <|
      (toUngraded E (E.admitsFiniteResolution P) hR hRshift).symm.trans (LaurentK0.ofExactK0 _)

/-- The transported resolution isomorphism is the map induced by the graded inclusion. -/
private lemma resolutionAddEquiv_apply (x : LaurentK0 (E.fullSubcategory P hP hshift)) :
    E.resolutionAddEquiv hproj hshift x =
      LaurentK0.map (GradedConflationExact.ιOfLE E P hP hR hshift hRshift
        (E.le_admitsFiniteResolution P)) x := by
  obtain ⟨y, rfl⟩ := (LaurentK0.ofExactK0 _).surjective x
  have key : (E.resolutionAddEquiv hproj hshift).toAddMonoidHom.comp
        (LaurentK0.ofExactK0 _).toAddMonoidHom =
      (LaurentK0.map (GradedConflationExact.ιOfLE E P hP hR hshift hRshift
        (E.le_admitsFiniteResolution P))).toAddMonoidHom.comp
        (LaurentK0.ofExactK0 _).toAddMonoidHom :=
    ExactK0.hom_ext fun X => by
      simp only [resolutionAddEquiv, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.trans_apply, AddEquiv.symm_apply_apply, toUngraded_of,
        ExactStructure.resolutionEquiv_of, toUngraded_symm_of, LinearMap.toAddMonoidHom_coe]
      rw [LaurentK0.ofExactK0_exactK0_of, LaurentK0.ofExactK0_exactK0_of, LaurentK0.map_of]
      exact congrArg _ (ObjectProperty.FullSubcategory.ext (ObjectProperty.ιOfLE_obj_obj _ X).symm)
  exact DFunLike.congr_fun key y

/-- **The graded resolution theorem.** Let `P` be a class of `E`-projectives containing a zero
object, closed under binary biproducts, and stable under the grading shift. Then the inclusion of
`P` into the objects of finite `P`-dimension induces an isomorphism of graded Grothendieck groups
as `ℤ[q,q⁻¹]`-modules. Its inverse sends the class of an object to its Euler class, by
`TauCeti.GradedExactStructure.laurentResolutionEquiv_symm_of`. -/
noncomputable def laurentResolutionEquiv :
    LaurentK0 (E.fullSubcategory P hP hshift) ≃ₗ[LaurentPolynomial ℤ]
      LaurentK0 (E.fullSubcategory (E.admitsFiniteResolution P) hR hRshift) :=
  LaurentK0.linearEquivOfMap
    (GradedConflationExact.ιOfLE E P hP hR hshift hRshift (E.le_admitsFiniteResolution P))
    (E.resolutionAddEquiv hproj hshift) (E.resolutionAddEquiv_apply hproj hshift)

/-- The forward map of the graded resolution isomorphism is the map induced by the graded
conflation-exact inclusion of `P` into the objects of finite `P`-dimension. -/
theorem laurentResolutionEquiv_toLinearMap :
    (E.laurentResolutionEquiv hproj hshift).toLinearMap =
      LaurentK0.map (GradedConflationExact.ιOfLE E P hP hR hshift hRshift
        (E.le_admitsFiniteResolution P)) := by
  simp [laurentResolutionEquiv]

/-- The graded resolution isomorphism sends the class of a `P`-object to its class among the
objects of finite `P`-dimension. -/
@[simp]
theorem laurentResolutionEquiv_of (X : P.FullSubcategory) :
    E.laurentResolutionEquiv hproj hshift (LaurentK0.of _ X) =
      LaurentK0.of _ ⟨X.obj, E.le_admitsFiniteResolution P X.obj X.property⟩ := by
  rw [laurentResolutionEquiv, LaurentK0.linearEquivOfMap_apply, resolutionAddEquiv_apply,
    LaurentK0.map_of]
  exact congrArg _ (ObjectProperty.FullSubcategory.ext (ObjectProperty.ιOfLE_obj_obj _ X))

/-- **The inverse of the graded resolution isomorphism is the Euler class**: it sends the class
of an object of finite `P`-dimension to the alternating sum `[Q₀] - [Q₁] + ⋯ + (-1)ⁿ [Kₙ]` of the
graded classes of the terms of any of its finite `P`-resolutions. -/
theorem laurentResolutionEquiv_symm_of {X : C} (hX : E.admitsFiniteResolution P X)
    (r : E.toExactStructure.FiniteResolution P X) :
    (E.laurentResolutionEquiv hproj hshift).symm (LaurentK0.of _ ⟨X, hX⟩) =
      r.foldAlternating fun Z hZ => LaurentK0.of (E.fullSubcategory P hP hshift) ⟨Z, hZ⟩ := by
  rw [← ofExactK0_toUngraded_symm_eulerClassFullSubcategory, ← E.eulerClassOf_eq hproj hX r,
    ← ExactStructure.resolutionEquiv_symm_of hproj hX, LinearEquiv.symm_apply_eq,
    laurentResolutionEquiv, LaurentK0.linearEquivOfMap_apply]
  simp only [resolutionAddEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.apply_symm_apply, toUngraded_symm_of, LaurentK0.ofExactK0_exactK0_of]

/-- **The graded Euler class.** The alternating class of a finite `P`-resolution of `X{1}` is `q`
times the alternating class of a finite `P`-resolution of `X`, in the graded Grothendieck group of
`P`. The two resolutions are arbitrary: neither need be the shift of the other. -/
theorem foldAlternating_shift_eq_T_one_smul {X : C} (r : E.toExactStructure.FiniteResolution P X)
    (s : E.toExactStructure.FiniteResolution P (E.shift.functor.obj X)) :
    (s.foldAlternating fun Z hZ => LaurentK0.of (E.fullSubcategory P hP hshift) ⟨Z, hZ⟩) =
      (T 1 : LaurentPolynomial ℤ) •
        r.foldAlternating fun Z hZ => LaurentK0.of (E.fullSubcategory P hP hshift) ⟨Z, hZ⟩ := by
  have hX : E.admitsFiniteResolution P X := (E.admitsFiniteResolution_iff P).mpr ⟨r⟩
  have hX' : E.admitsFiniteResolution P (E.shift.functor.obj X) :=
    (E.admitsFiniteResolution_iff P).mpr ⟨s⟩
  have e : (E.fullSubcategoryShift _ hRshift).functor.obj ⟨X, hX⟩ ≅
      ⟨E.shift.functor.obj X, hX'⟩ :=
    ObjectProperty.isoMk _ ((E.fullSubcategoryShiftFunctorCompιIso _ hRshift).app ⟨X, hX⟩)
  apply foldAlternating_shift_eq_T_one_smul_of_linearEquiv E P hP hshift
    (E.laurentResolutionEquiv hproj hshift) r s
    (LaurentK0.of _ ⟨X, hX⟩) (LaurentK0.of _ ⟨E.shift.functor.obj X, hX'⟩)
  · exact E.laurentResolutionEquiv_symm_of hproj hshift hX r
  · exact E.laurentResolutionEquiv_symm_of hproj hshift hX' s
  · rw [LaurentK0.T_one_smul_of, fullSubcategory_shift]
    exact LaurentK0.of_congr _ e.symm

end GradedExactStructure

end TauCeti
