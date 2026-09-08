/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Basic

/-!
# Algebraic specializations of the graded Grothendieck group

The graded Grothendieck group of a graded exact category is a module over
`ℤ[q,q⁻¹]`.  Evaluating `q` at a unit `u : ℤˣ` makes `ℤ` a module over this Laurent
coefficient ring, and extension of scalars gives

`ℤ ⊗[ℤ[q,q⁻¹]] LaurentK0 E`.

This file records what that base change does to the classes of objects.  The scalar extension
itself, its universal property and its extensionality lemma are `TauCeti.LaurentSpecialization`
and its API, which are stated for an arbitrary `ℤ[q,q⁻¹]`-module.

The only integer units are `1` and `-1`.  At `q = 1`, a grading shift has the same class as the
original object.  At `q = -1`, one grading shift negates its class, and an `n`-fold shift acts by
`n.negOnePow`.

A conflation-exact functor which forgets grading and identifies the grading shift with itself
therefore factors canonically through specialization at `q = 1`.  No claim is made that this
factor is an isomorphism: that requires additional hypotheses on the graded and ungraded
categories.

## Main definitions

* `TauCeti.LaurentK0.Specialization`: extension of scalars along evaluation at an integer unit.
* `TauCeti.LaurentK0.SpecializationAtOne` and
  `TauCeti.LaurentK0.SpecializationAtNegOne`: the specializations at `q = 1` and `q = -1`.
* `TauCeti.LaurentK0.Specialization.of`: the specialized class of an object.
* `TauCeti.LaurentK0.Specialization.mapForgettingAtOne`: the factor of a grading-forgetful map.

## Main results

* `TauCeti.LaurentK0.Specialization.of_conflation`: the defining relation `[M₂] = [M₁] + [M₃]`
  of a conflation, in a specialization.
* `TauCeti.LaurentK0.Specialization.atOne_mk_shiftZPow`: every shift is unchanged at `q = 1`.
* `TauCeti.LaurentK0.Specialization.atNegOne_mk_shiftZPow`: an `n`-fold shift has sign
  `n.negOnePow` at `q = -1`.
* `TauCeti.LaurentK0.Specialization.hom_ext`: an additive map out of a specialization is
  determined by the specialized classes of objects.
* `TauCeti.LaurentK0.Specialization.mapForgettingAtOne_comp_mk`: the induced ungraded `K₀` map
  factors through specialization at `q = 1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 2.2 and Proposition 2.7.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open LaurentPolynomial hiding C

universe w w' v v' u u'

namespace LaurentK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- **The graded Grothendieck group specialized at the integer unit `a`.**  This is extension of
scalars from `ℤ[q,q⁻¹]` to `ℤ` along evaluation at `q = a`. -/
noncomputable abbrev Specialization (E : GradedExactStructure C) (a : ℤˣ) : Type w :=
  LaurentSpecialization (LaurentK0 E) a

/-- The graded Grothendieck group specialized at `q = 1`. -/
noncomputable abbrev SpecializationAtOne (E : GradedExactStructure C) : Type w :=
  Specialization E 1

/-- The graded Grothendieck group specialized at `q = -1`. -/
noncomputable abbrev SpecializationAtNegOne (E : GradedExactStructure C) : Type w :=
  Specialization E (-1)

namespace Specialization

variable (E : GradedExactStructure C) (a : ℤˣ)

/-- The specialized class of an object. -/
noncomputable def of (X : C) : Specialization E a :=
  LaurentSpecialization.mk (LaurentK0 E) a (LaurentK0.of E X)

theorem of_eq_mk (X : C) :
    of E a X = LaurentSpecialization.mk (LaurentK0 E) a (LaurentK0.of E X) :=
  (rfl)

/-- Isomorphic objects have the same specialized class. -/
theorem of_congr {X Y : C} (e : X ≅ Y) : of E a X = of E a Y := by
  rw [of_eq_mk, of_eq_mk, LaurentK0.of_congr E e]

/-- **The defining relation of a specialized graded `K₀`**: the specialized class of the middle
term of a conflation is the sum of the specialized classes of its outer terms. -/
theorem of_conflation {S : ShortComplex C} (hS : E.toExactStructure.Conflation S) :
    of E a S.X₂ = of E a S.X₁ + of E a S.X₃ := by
  rw [of_eq_mk, of_eq_mk, of_eq_mk, LaurentK0.of_conflation E hS, map_add]

/-- Specialization sends the `n`-fold grading shift to multiplication by `aⁿ`. -/
theorem mk_shiftZPow (n : ℤ) (x : ExactK0 E.toExactStructure) :
    LaurentSpecialization.mk (LaurentK0 E) a (LaurentK0.ofExactK0 E (E.shiftZPow n x)) =
      ((a ^ n : ℤˣ) : ℤ) •
        LaurentSpecialization.mk (LaurentK0 E) a (LaurentK0.ofExactK0 E x) := by
  rw [← LaurentK0.T_smul, LaurentSpecialization.mk_smul, laurentEval_T]

/-- At `q = 1`, every iterated grading shift has the same specialized class. -/
theorem atOne_mk_shiftZPow (n : ℤ) (x : ExactK0 E.toExactStructure) :
    LaurentSpecialization.mk (LaurentK0 E) 1 (LaurentK0.ofExactK0 E (E.shiftZPow n x)) =
      LaurentSpecialization.mk (LaurentK0 E) 1 (LaurentK0.ofExactK0 E x) := by
  rw [mk_shiftZPow]
  simp

/-- At `q = -1`, an `n`-fold grading shift multiplies the specialized class by
`n.negOnePow`. -/
theorem atNegOne_mk_shiftZPow (n : ℤ) (x : ExactK0 E.toExactStructure) :
    LaurentSpecialization.mk (LaurentK0 E) (-1) (LaurentK0.ofExactK0 E (E.shiftZPow n x)) =
      (n.negOnePow : ℤ) •
        LaurentSpecialization.mk (LaurentK0 E) (-1) (LaurentK0.ofExactK0 E x) := by
  simpa only [Int.negOnePow] using mk_shiftZPow E (-1) n x

/-- At `q = 1`, shifting an object once does not change its specialized class. -/
@[simp]
theorem atOne_of_shift (X : C) : of E 1 (E.shift.functor.obj X) = of E 1 X := by
  rw [of_eq_mk, of_eq_mk, ← LaurentK0.T_one_smul_of, LaurentSpecialization.mk_smul]
  simp

/-- At `q = -1`, shifting an object once negates its specialized class. -/
@[simp]
theorem atNegOne_of_shift (X : C) : of E (-1) (E.shift.functor.obj X) = -of E (-1) X := by
  rw [of_eq_mk, of_eq_mk, ← LaurentK0.T_one_smul_of, LaurentSpecialization.mk_smul]
  simp

section UniversalProperty

variable {G : Type*} [AddCommGroup G]

/-- Additive maps out of a specialized graded `K₀` are determined by specialized object classes. -/
theorem hom_ext {f g : Specialization E a →+ G} (h : ∀ X : C, f (of E a X) = g (of E a X)) :
    f = g := by
  apply LaurentSpecialization.hom_ext_mk (LaurentK0 E) a
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, LaurentK0.ofExactK0 E y = x :=
    ⟨(LaurentK0.ofExactK0 E).symm x, by simp⟩
  have key :
      (f.comp (LaurentSpecialization.mk (LaurentK0 E) a)).comp
          (LaurentK0.ofExactK0 E).toAddMonoidHom =
        (g.comp (LaurentSpecialization.mk (LaurentK0 E) a)).comp
          (LaurentK0.ofExactK0 E).toAddMonoidHom :=
    ExactK0.hom_ext fun X => by simpa [of] using h X
  simpa using DFunLike.congr_fun key y

end UniversalProperty

section ForgetGrading

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
variable {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

/-- The ungraded Grothendieck group as a `ℤ[q,q⁻¹]`-module in which `q` acts trivially: it is the
coefficient ring evaluated at `q = 1` that acts, and this is the target against which a
grading-forgetful invariant is compared. -/
private noncomputable abbrev forgetModule : Module (LaurentPolynomial ℤ) (ExactK0 E') :=
  laurentEvalModule (R := ℤ) (1 : ℤˣ) (ExactK0 E')

attribute [local instance] forgetModule

/-- A Laurent scalar acts on the ungraded Grothendieck group by its value at `q = 1`. -/
private theorem forgetModule_smul (p : LaurentPolynomial ℤ) (y : ExactK0 E') :
    p • y = (laurentEval (1 : ℤˣ) p : ℤ) • y :=
  laurentEvalModule_smul (R := ℤ) 1 p y

/-- The map on graded `K₀` induced by a conflation-exact functor which forgets grading, obtained
from the universal property of `LaurentK0` over the coefficient ring acting through `q = 1`. -/
private noncomputable def forgetMap (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) : LaurentK0 E →+ ExactK0 E' :=
  (LaurentK0.lift E
    { obj := fun X => ExactK0.of (F.obj X)
      map_iso := fun {_ _} e => ExactK0.of_congr (F.mapIso e)
      map_conflation := fun {_} hS => ExactK0.of_conflation (hU.map_conflation hS)
      map_shift := fun X => by
        rw [laurentTAut_apply, forgetModule_smul, laurentEval_T_one]
        simpa using ExactK0.of_congr (E := E') (comm.app X) }).toAddMonoidHom

@[simp]
private theorem forgetMap_of (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (X : C) :
    forgetMap E hU comm (LaurentK0.of E X) = ExactK0.of (F.obj X) := by
  simp [forgetMap]

private theorem forgetMap_smul (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (p : LaurentPolynomial ℤ) (x : LaurentK0 E) :
    forgetMap E hU comm (p • x) =
      (laurentEval (1 : ℤˣ) p : ℤ) • forgetMap E hU comm x := by
  simp only [forgetMap, LinearMap.toAddMonoidHom_coe, map_smul, forgetModule_smul]

/-- **The map on `K₀` induced by forgetting grading factors through specialization at `q = 1`.**

The commuting isomorphism says that a grading shift becomes invisible after applying `F`; it does
not imply that this factor is an isomorphism. -/
noncomputable def mapForgettingAtOne
    (hU : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    SpecializationAtOne E →+ ExactK0 E' :=
  LaurentSpecialization.desc (LaurentK0 E) 1 (forgetMap E hU comm) (forgetMap_smul E hU comm)

/-- **The factor through specialization at `q = 1` sends a specialized object class to the
ungraded class of its image**: `[X]` at `q = 1` maps to `[F X]` in the ungraded `K₀`. -/
@[simp]
theorem mapForgettingAtOne_of (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (X : C) :
    mapForgettingAtOne E hU comm (of E 1 X) = ExactK0.of (F.obj X) := by
  rw [of_eq_mk, mapForgettingAtOne, LaurentSpecialization.desc_mk, forgetMap_of]

/-- The explicit factorization equation for the grading-forgetful map. -/
theorem mapForgettingAtOne_comp_mk (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) :
    (mapForgettingAtOne E hU comm).comp (LaurentSpecialization.mk (LaurentK0 E) 1) =
      (ExactK0.map F hU).comp (LaurentK0.ofExactK0 E).symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, LaurentK0.ofExactK0 E y = x :=
    ⟨(LaurentK0.ofExactK0 E).symm x, by simp⟩
  rw [AddMonoidHom.comp_apply, mapForgettingAtOne, LaurentSpecialization.desc_mk]
  have key :
      (forgetMap E hU comm).comp (LaurentK0.ofExactK0 E).toAddMonoidHom = ExactK0.map F hU :=
    ExactK0.hom_ext fun X => by simp
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply] using DFunLike.congr_fun key y

/-- The factor through specialization at `q = 1` is characterized by its values on object
classes. -/
theorem mapForgettingAtOne_unique (hU : E.toExactStructure.IsConflationExact E' F)
    (comm : E.shift.functor ⋙ F ≅ F) (g : SpecializationAtOne E →+ ExactK0 E')
    (hg : ∀ X : C, g (of E 1 X) = ExactK0.of (F.obj X)) :
    g = mapForgettingAtOne E hU comm := by
  apply hom_ext E 1
  intro X
  rw [hg, mapForgettingAtOne_of]

end ForgetGrading

end Specialization

end LaurentK0

end TauCeti
