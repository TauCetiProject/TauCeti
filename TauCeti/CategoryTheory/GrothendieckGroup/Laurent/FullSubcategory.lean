/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.FullSubcategory
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Resolution

/-!
# Graded Grothendieck groups of full subcategories

This file compares the exact Grothendieck groups associated to the graded and ungraded exact
structures induced on a shift-stable, extension-closed full subcategory. It also records the
transport of the Euler class of a finite resolution across this comparison, and the compatibility
of that Euler class with forgetting the grading along a conflation-exact functor into an ungraded
exact category.

## Main results

* `TauCeti.GradedExactStructure.ofExactK0_toUngraded_symm_eulerClassFullSubcategory`: the graded
  Euler class of a finite resolution is the alternating sum of the graded classes of its terms.
* `TauCeti.GradedExactStructure.forgetGrading_foldAlternating`: at `q = 1`, forgetting the grading
  carries the graded Euler class of a finite resolution to the Euler class of its image
  resolution.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe w w' v v' u u'

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [LocallySmall.{w} C]
  (E : GradedExactStructure C) (R : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} R]
  [R.ContainsZero] [R.IsClosedUnderBinaryProducts] (hR : E.toExactStructure.IsExtensionClosed R)
  (hRshift : R.inverseImage E.shift.functor = R)

/-- The graded and the ungraded induced exact structures on a full subcategory have the same
conflations, so the identity functor compares their exact Grothendieck groups. -/
noncomputable def toUngraded :
    ExactK0 (E.fullSubcategory R hR hRshift).toExactStructure ≃+
      ExactK0 (E.toExactStructure.fullSubcategory R hR) :=
  ExactK0.ofLEEquiv fun _ => by rw [fullSubcategory_toExactStructure]

/-- The comparison with the ungraded induced structure fixes every object class. -/
@[simp]
lemma toUngraded_of (X : R.FullSubcategory) :
    toUngraded E R hR hRshift (ExactK0.of X) = ExactK0.of X :=
  ExactK0.ofLEEquiv_of _ X

/-- The inverse comparison with the ungraded induced structure fixes every object class. -/
@[simp]
lemma toUngraded_symm_of (X : R.FullSubcategory) :
    (toUngraded E R hR hRshift).symm (ExactK0.of X) = ExactK0.of X :=
  ExactK0.ofLEEquiv_symm_of _ X

/-- Transported to the graded Grothendieck group, the Euler class of a finite `R`-resolution is
the alternating sum of the graded classes of its terms. -/
lemma ofExactK0_toUngraded_symm_eulerClassFullSubcategory {X : C}
    (r : E.toExactStructure.FiniteResolution R X) :
    LaurentK0.ofExactK0 _ ((toUngraded E R hR hRshift).symm (r.eulerClassFullSubcategory hR)) =
      r.foldAlternating fun Z hZ => LaurentK0.of (E.fullSubcategory R hR hRshift) ⟨Z, hZ⟩ := by
  induction r with
  | base hX => simp
  | step hQ i p zero hp r ih => simp [ih]

/-- A linear map transports shift covariance from two target classes to the Euler classes of
finite resolutions that it computes. -/
theorem foldAlternating_shift_eq_T_one_smul_of_linearMap
    {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]
    (f : N →ₗ[LaurentPolynomial ℤ] LaurentK0 (E.fullSubcategory R hR hRshift))
    {X : C} (r : E.toExactStructure.FiniteResolution R X)
    (s : E.toExactStructure.FiniteResolution R (E.shift.functor.obj X)) (x x' : N)
    (hr : f x = r.foldAlternating fun Z hZ =>
      LaurentK0.of (E.fullSubcategory R hR hRshift) ⟨Z, hZ⟩)
    (hs : f x' = s.foldAlternating fun Z hZ =>
      LaurentK0.of (E.fullSubcategory R hR hRshift) ⟨Z, hZ⟩)
    (hshift : x' = (T 1 : LaurentPolynomial ℤ) • x) :
    s.foldAlternating
        (fun Z hZ => LaurentK0.of (E.fullSubcategory R hR hRshift) ⟨Z, hZ⟩) =
      (T 1 : LaurentPolynomial ℤ) •
        r.foldAlternating
          (fun Z hZ => LaurentK0.of (E.fullSubcategory R hR hRshift) ⟨Z, hZ⟩) := by
  rw [← hs, ← hr, ← map_smul, hshift]

section ForgetGrading

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [LocallySmall.{w'} D]
  {E' : ExactStructure D} {Q : ObjectProperty D} [ObjectProperty.EssentiallySmall.{w'} Q]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts] (hQ : E'.IsExtensionClosed Q)
  {F : C ⥤ D} [F.Additive] (hF : E.toExactStructure.IsConflationExact E' F)
  (comm : E.shift.functor ⋙ F ≅ F) (hRQ : ∀ Y : R.FullSubcategory, Q (F.obj Y.obj))

/-- **Forgetting the grading of a finite resolution.** Let `F` be a conflation-exact functor into
an ungraded exact category with `{1} ⋙ F ≅ F`, carrying the shift-stable extension-closed
property `R` into an extension-closed property `Q`. Applying `F` to a finite `R`-resolution of `X`
gives a finite `Q`-resolution of `F X`, and the graded Euler class of the first, specialized at
`q = 1`, is the Euler class of the second.

Both alternating sums are computed termwise, and forgetting the grading sends the graded class of
each term to the ungraded class of its image. -/
theorem forgetGrading_foldAlternating {X : C} (r : E.toExactStructure.FiniteResolution R X) :
    LaurentK0.forgetGrading
        (E.isConflationExact_lift R hR hRshift hRQ hQ hF)
        (E.liftCommShift R hR hRshift hRQ comm)
        (LaurentSpecialization.mk 1
          (r.foldAlternating fun Z hZ => LaurentK0.of (E.fullSubcategory R hR hRshift) ⟨Z, hZ⟩)) =
      (r.map hF fun Z hZ => hRQ ⟨Z, hZ⟩).eulerClassFullSubcategory hQ := by
  rw [ExactStructure.FiniteResolution.eulerClassFullSubcategory_map hQ hF
    fun Z hZ => hRQ ⟨Z, hZ⟩]
  induction r with
  | base hX =>
    rw [ExactStructure.FiniteResolution.foldAlternating_base,
      ExactStructure.FiniteResolution.foldAlternating_base, LaurentK0.forgetGrading_mk_of]
    -- `Q.lift (R.ι ⋙ F) hRQ` sends `⟨Z, hZ⟩` to `⟨F.obj Z, _⟩` by definition.
    rfl
  | step hZ i p zero hp r ih =>
    rw [ExactStructure.FiniteResolution.foldAlternating_step,
      ExactStructure.FiniteResolution.foldAlternating_step, map_sub, map_sub, ih,
      LaurentK0.forgetGrading_mk_of]
    -- `Q.lift (R.ι ⋙ F) hRQ` sends `⟨Z, hZ⟩` to `⟨F.obj Z, _⟩` by definition.
    rfl

end ForgetGrading

end GradedExactStructure

end TauCeti
