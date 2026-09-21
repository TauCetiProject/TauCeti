/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Basic

/-!
# Forgetting the grading on a Grothendieck group

Let `E` be a graded exact category and let `F` be a conflation-exact functor from its underlying
exact category to an ungraded exact category.  If `F` identifies the grading shift with itself,
then the induced map on exact Grothendieck groups identifies `[M{1}]` with `[M]`.  Consequently it
factors through the specialization of graded `K₀` at `q = 1`.

This file constructs that factorization.  It also characterizes surjectivity in terms of the
original map on exact `K₀`, and injectivity in terms of the relations introduced by forgetting the
grading.  Establishing independently checkable hypotheses that imply these conditions requires
additional structure and is not attempted here; shift compatibility by itself is not sufficient.

## Main definitions

* `TauCeti.LaurentK0.forgetGradingMap`: the map from graded `K₀` specialized at `q = 1` to the
  exact `K₀` of an ungraded target.

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
  have hcomp : forgetGradingMap hF comm ∘ LaurentSpecialization.mk 1 =
      forgetGradingUnderlyingMap hF := by
    funext x
    exact forgetGradingMap_mk hF comm x
  calc
    Function.Surjective (forgetGradingMap hF comm) ↔
        Function.Surjective (forgetGradingMap hF comm ∘ LaurentSpecialization.mk 1) :=
      (Function.Surjective.of_comp_iff _ (LaurentSpecialization.mk_surjective 1)).symm
    _ ↔ Function.Surjective (forgetGradingUnderlyingMap hF) := by
      rw [hcomp]
    _ ↔ Function.Surjective (ExactK0.map F hF) := by
      rw [← Function.Surjective.of_comp_iff
        (ExactK0.map F hF) (ofExactK0 E).symm.surjective]
      rfl

/-- The comparison after forgetting grading is injective exactly when the kernel of the original
map consists of the relations imposed by specialization at `q = 1`. -/
theorem forgetGradingMap_injective_iff
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    Function.Injective (forgetGradingMap hF comm) ↔
      LinearMap.ker (forgetGradingUnderlyingMap hF) =
        ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
          Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ) := by
  let p := ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
    Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ)
  have hp : p ≤ LinearMap.ker (forgetGradingUnderlyingMap hF) := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hzero : (LaurentSpecialization.mk (R := ℤ) 1 x :
        LaurentSpecialization (1 : ℤˣ) (LaurentK0 E)) = 0 := by
      rw [LaurentSpecialization.mk_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    have := congrArg (forgetGradingMap hF comm) hzero
    simpa using this
  let g := p.liftQ (forgetGradingUnderlyingMap hF)
    (fun x hx ↦ LinearMap.mem_ker.mp (hp hx))
  let e := Submodule.Quotient.restrictScalarsEquiv ℤ
    (RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
      Submodule (LaurentPolynomial ℤ) (LaurentK0 E))
  have hmap : forgetGradingMap hF comm = g.comp e.symm.toLinearMap := by
    apply LaurentSpecialization.hom_ext
    intro x
    rw [forgetGradingMap_mk, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LaurentSpecialization.mk_apply, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
    exact (Submodule.liftQ_apply p (forgetGradingUnderlyingMap hF) x).symm
  have hinjective : Function.Injective (g.comp e.symm.toLinearMap) ↔
      Function.Injective g := by
    rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
    exact Function.Injective.of_comp_iff' g e.symm.bijective
  rw [hmap]
  rw [hinjective, ← LinearMap.ker_eq_bot]
  constructor
  · intro hbot
    apply le_antisymm
    · intro x hx
      have hmk : Submodule.mkQ p x ∈
          (LinearMap.ker (forgetGradingUnderlyingMap hF)).map (Submodule.mkQ p) :=
        ⟨x, hx, rfl⟩
      rw [← Submodule.ker_liftQ p (forgetGradingUnderlyingMap hF)
          (fun y hy ↦ LinearMap.mem_ker.mp (hp hy)),
        hbot, Submodule.mem_bot] at hmk
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
    · exact hp
  · intro hker
    exact Submodule.ker_liftQ_eq_bot' p (forgetGradingUnderlyingMap hF) hker.symm

end LaurentK0

end TauCeti
