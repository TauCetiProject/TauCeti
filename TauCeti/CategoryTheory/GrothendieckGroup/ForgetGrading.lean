/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent

/-!
# Forgetting the grading on a Grothendieck group

Let `E` be a graded exact category and let `F` be a conflation-exact functor from its underlying
exact category to an ungraded exact category.  If `F` identifies the grading shift with itself,
then the induced map on exact Grothendieck groups identifies `[M{1}]` with `[M]`.  Consequently it
factors through the specialization of graded `K₀` at `q = 1`.

This file constructs that factorization and records its exact algebraic boundary.  It is
surjective precisely when the original map on exact `K₀` is surjective, and it is injective
precisely when the only relations introduced by forgetting the grading are the relations killed
by specialization at `q = 1`.  Thus the two conditions together give the comparison isomorphism;
shift compatibility by itself does not.

## Main definitions

* `TauCeti.LaurentK0.forgetGradingMap`: the map from graded `K₀` specialized at `q = 1` to the
  exact `K₀` of an ungraded target.
* `TauCeti.LaurentK0.forgetGradingEquiv`: the resulting linear equivalence when the induced map is
  surjective and has exactly the specialization relations as its kernel.

## Main results

* `TauCeti.LaurentK0.forgetGradingMap_mk_of`: forgetting the grading sends the specialized class
  of `M` to the class of `F(M)`.
* `TauCeti.LaurentK0.forgetGradingMap_surjective_iff`: the factor map is surjective exactly when
  the map before specialization is.
* `TauCeti.LaurentK0.forgetGradingMap_injective_iff`: the factor map is injective exactly when
  forgetting introduces no relations beyond specialization at `q = 1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups and
  specialization at `q = 1`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe v v' u u' w w'

namespace LaurentK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
variable {E : GradedExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

/-- The map on underlying exact Grothendieck groups, viewed as a `ℤ`-linear map whose source is
graded `K₀`.  This is the map which factors through specialization at `q = 1`. -/
noncomputable def forgetGradingUnderlyingMap
    (hF : E.toExactStructure.IsConflationExact E' F) :
    LaurentK0 E →ₗ[ℤ] ExactK0 E' :=
  ((ExactK0.map F hF).comp (ofExactK0 E).symm.toAddMonoidHom).toIntLinearMap

@[simp]
lemma forgetGradingUnderlyingMap_ofExactK0
    (hF : E.toExactStructure.IsConflationExact E' F) (x : ExactK0 E.toExactStructure) :
    forgetGradingUnderlyingMap hF (ofExactK0 E x) = ExactK0.map F hF x := by
  simp [forgetGradingUnderlyingMap]

@[simp]
lemma forgetGradingUnderlyingMap_of
    (hF : E.toExactStructure.IsConflationExact E' F) (X : C) :
    forgetGradingUnderlyingMap hF (of E X) = ExactK0.of (F.obj X) := by
  rw [← ofExactK0_exactK0_of, forgetGradingUnderlyingMap_ofExactK0, ExactK0.map_of]

/-- If the functor identifies the grading shift with itself, its map on `K₀` sends multiplication
by `q` to the identity. -/
theorem forgetGradingUnderlyingMap_T_one
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F)
    (x : LaurentK0 E) :
    forgetGradingUnderlyingMap hF ((T 1 : LaurentPolynomial ℤ) • x) =
      forgetGradingUnderlyingMap hF x := by
  obtain ⟨y, rfl⟩ := (ofExactK0 E).surjective x
  rw [T_smul, forgetGradingUnderlyingMap_ofExactK0,
    GradedExactStructure.shiftZPow_apply, one_smul,
    GradedExactStructure.map_shiftEquiv_of_commShift hF comm,
    forgetGradingUnderlyingMap_ofExactK0]

/-- **The comparison after forgetting the grading.**  A conflation-exact functor which identifies
its composite with the grading shift with itself induces a map from graded `K₀` specialized at
`q = 1` to the exact Grothendieck group of its ungraded target. -/
noncomputable def forgetGradingMap
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    LaurentSpecialization (1 : ℤˣ) (LaurentK0 E) →ₗ[ℤ] ExactK0 E' :=
  LaurentSpecialization.lift 1 (forgetGradingUnderlyingMap hF)
    (fun x ↦ by simpa using forgetGradingUnderlyingMap_T_one hF comm x)

/-- The comparison is the expected map before passing to specialization. -/
@[simp]
theorem forgetGradingMap_mk
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F)
    (x : LaurentK0 E) :
    forgetGradingMap hF comm (LaurentSpecialization.mk 1 x) =
      forgetGradingUnderlyingMap hF x := by
  rw [forgetGradingMap, LaurentSpecialization.lift_mk]

/-- Forgetting the grading sends the specialized class of an object to the class of its image. -/
theorem forgetGradingMap_mk_of
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F)
    (X : C) :
    forgetGradingMap hF comm (LaurentSpecialization.mk 1 (of E X)) =
      ExactK0.of (F.obj X) := by
  rw [forgetGradingMap_mk, forgetGradingUnderlyingMap_of]

/-- The comparison after forgetting grading is the unique linear map with its prescribed values
on object classes. -/
theorem forgetGradingMap_unique
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F)
    (f : LaurentSpecialization (1 : ℤˣ) (LaurentK0 E) →ₗ[ℤ] ExactK0 E')
    (hf : ∀ X : C, f (LaurentSpecialization.mk 1 (of E X)) = ExactK0.of (F.obj X)) :
    f = forgetGradingMap hF comm := by
  apply hom_ext_laurentSpecialization
  intro X
  rw [hf, forgetGradingMap_mk_of]

/-- The comparison after forgetting grading is surjective exactly when the original map on exact
Grothendieck groups is surjective. -/
theorem forgetGradingMap_surjective_iff
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    Function.Surjective (forgetGradingMap hF comm) ↔
      Function.Surjective (ExactK0.map F hF) := by
  constructor
  · intro h y
    obtain ⟨z, hz⟩ := h y
    obtain ⟨x, rfl⟩ := LaurentSpecialization.mk_surjective 1 z
    obtain ⟨x, rfl⟩ := (ofExactK0 E).surjective x
    exact ⟨x, by simpa using hz⟩
  · intro h y
    obtain ⟨x, rfl⟩ := h y
    exact ⟨LaurentSpecialization.mk 1 (ofExactK0 E x), by simp⟩

/-- The comparison after forgetting grading is injective exactly when the kernel of the original
map consists of the relations imposed by specialization at `q = 1`.  This is the precise
additional hypothesis needed beyond shift compatibility. -/
theorem forgetGradingMap_injective_iff
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    Function.Injective (forgetGradingMap hF comm) ↔
      LinearMap.ker (forgetGradingUnderlyingMap hF) =
        ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
          Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ) := by
  constructor
  · intro hinj
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      have hzero : LaurentSpecialization.mk 1 x = 0 := hinj (by simpa using hx)
      rwa [LaurentSpecialization.mk_apply, Submodule.Quotient.mk_eq_zero] at hzero
    · intro x hx
      rw [LinearMap.mem_ker]
      have hzero : (LaurentSpecialization.mk (R := ℤ) 1 x :
          LaurentSpecialization (1 : ℤˣ) (LaurentK0 E)) = 0 := by
        rw [LaurentSpecialization.mk_apply, Submodule.Quotient.mk_eq_zero]
        exact hx
      have := congrArg (forgetGradingMap hF comm) hzero
      simpa using this
  · intro hker
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨x, rfl⟩ := LaurentSpecialization.mk_surjective 1 z
      rw [LinearMap.mem_ker, forgetGradingMap_mk] at hz
      have hx : x ∈ LinearMap.ker (forgetGradingUnderlyingMap hF) :=
        LinearMap.mem_ker.mpr hz
      rw [hker] at hx
      rw [LaurentSpecialization.mk_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    · exact bot_le

/-- **The `q = 1` comparison isomorphism.**  If every ungraded `K₀` class is represented after
forgetting and forgetting introduces exactly the specialization relations, then specialized
graded `K₀` is the ungraded exact Grothendieck group. -/
noncomputable def forgetGradingEquiv
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F)
    (hsurj : Function.Surjective (ExactK0.map F hF))
    (hker : LinearMap.ker (forgetGradingUnderlyingMap hF) =
      ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
        Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ)) :
    LaurentSpecialization (1 : ℤˣ) (LaurentK0 E) ≃ₗ[ℤ] ExactK0 E' :=
  LinearEquiv.ofBijective (forgetGradingMap hF comm)
    ⟨(forgetGradingMap_injective_iff hF comm).mpr hker,
      (forgetGradingMap_surjective_iff hF comm).mpr hsurj⟩

/-- The comparison equivalence sends a specialized object class to its ungraded class. -/
@[simp]
theorem forgetGradingEquiv_mk_of
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F)
    (hsurj : Function.Surjective (ExactK0.map F hF))
    (hker : LinearMap.ker (forgetGradingUnderlyingMap hF) =
      ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
        Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ))
    (X : C) :
    forgetGradingEquiv hF comm hsurj hker (LaurentSpecialization.mk 1 (of E X)) =
      ExactK0.of (F.obj X) := by
  unfold forgetGradingEquiv
  exact forgetGradingMap_mk_of hF comm X

end LaurentK0

end TauCeti
