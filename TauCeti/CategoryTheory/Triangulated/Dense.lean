/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty.StableClasses
public import TauCeti.CategoryTheory.Triangulated.FullSubcategory
import TauCeti.CategoryTheory.Triangulated.Biproduct

/-!
# Dense triangulated subcategories and stable object classes

In a pretriangulated category `C`, if `P` is a strictly full triangulated subcategory and `X` lies
in the retract closure `P.retractClosure`, then `X ⊞ X⟦1⟧` lies in `P`
(`CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_retractClosure`), and for any
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` whose outer terms lie in `P.retractClosure`, the
stabilized middle term `Y ⊞ (X⟦1⟧ ⊞ Z⟦1⟧)` lies in `P`
(`CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_distTriang`).

For a strictly full triangulated subcategory `A`, the zero-class criterion holds in
`TauCeti.StableClasses A`: `StableClasses.mk A X = 0` if and only if `A X`
(`TauCeti.StableClasses.mk_eq_zero_iff`). When `A` is moreover dense (`A.retractClosure = ⊤`), the
shift `X ↦ X⟦1⟧` supplies additive inverses (`TauCeti.StableClasses.addCommGroup`) and the
distinguished triangle relation `[Y] = [X] + [Z]` holds in `TauCeti.StableClasses A`
(`TauCeti.StableClasses.mk_distTriang`).

## Main definitions

* `TauCeti.StableClasses.addCommGroup`: the abelian group structure on `TauCeti.StableClasses A`
  when `A` is a dense strictly full triangulated subcategory.

## Main results

* `CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_retractClosure` and
  `CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_distTriang`: Thomason's stabilization
  lemmas for retracts of objects in a strictly full triangulated subcategory.
* `TauCeti.StableClasses.mk_eq_zero_iff`: the zero-class criterion `mk A X = 0 ↔ A X`.
* `TauCeti.StableClasses.mk_distTriang`: distinguished triangle additivity in
  `TauCeti.StableClasses A`.

## References

* R. W. Thomason, *The classification of triangulated subcategories*, Compositio Math. **105**
  (1997), no. 1, 1–27, Lemma 2.2.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulatedClosed₂] [P.IsStableUnderShiftBy (1 : ℤ)]
  [P.IsClosedUnderIsomorphisms]

/-- **Thomason's shift stabilization lemma**: if `X` is a retract of an object in a strictly full
extension-closed subcategory `P` stable under `⟦1⟧`, then `X ⊞ X⟦1⟧` belongs to `P`. -/
theorem prop_biprod_shift_one_of_retractClosure {X : C} (hX : P.retractClosure X) :
    P (X ⊞ X⟦(1 : ℤ)⟧) := by
  obtain ⟨Z, hXZ⟩ := (P.prop_retractClosure_iff_exists_biprod X).1 hX
  let : PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have hXZ₁ : P (X⟦(1 : ℤ)⟧ ⊞ Z⟦(1 : ℤ)⟧) :=
    P.prop_of_iso ((shiftFunctor C (1 : ℤ)).mapBiprod X Z) (P.le_shift (1 : ℤ) _ hXZ)
  have hmid : P ((X ⊞ X⟦(1 : ℤ)⟧) ⊞ (0 : C)) :=
    P.prop_biprod_obj₂_of_distTriang
      (binaryBiproductTriangle_distinguished X (X⟦(1 : ℤ)⟧))
      (contractible_distinguished₂ Z) hXZ hXZ₁
  exact P.prop_of_iso (isoBiprodZero (isZero_zero C)).symm hmid

/-- **Thomason's triangle stabilization lemma**: if `T` is a distinguished triangle whose outer
terms lie in the retract closure of a strictly full extension-closed subcategory `P` stable under
`⟦1⟧`, then `T.obj₂ ⊞ (T.obj₁⟦1⟧ ⊞ T.obj₃⟦1⟧)` belongs to `P`. -/
theorem prop_biprod_shift_one_of_distTriang {T : Triangle C} (hT : T ∈ distTriang C)
    (h₁ : P.retractClosure T.obj₁) (h₃ : P.retractClosure T.obj₃) :
    P (T.obj₂ ⊞ (T.obj₁⟦(1 : ℤ)⟧ ⊞ T.obj₃⟦(1 : ℤ)⟧)) :=
  P.prop_biprod_obj₂_of_distTriang hT
    (binaryBiproductTriangle_distinguished (T.obj₁⟦(1 : ℤ)⟧) (T.obj₃⟦(1 : ℤ)⟧))
    (P.prop_biprod_shift_one_of_retractClosure h₁)
    (P.prop_biprod_shift_one_of_retractClosure h₃)

end CategoryTheory.ObjectProperty

namespace TauCeti.StableClasses

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Zero-class criterion**: in a pretriangulated category, an object has zero stable class modulo
a strictly full triangulated subcategory `A` if and only if it belongs to `A`. -/
@[simp, grind =]
theorem mk_eq_zero_iff {A : ObjectProperty C} [A.Nonempty] [A.IsClosedUnderIsomorphisms]
    [A.IsClosedUnderBinaryProducts] [A.IsTriangulatedClosed₁] {X : C} :
    mk A X = 0 ↔ A X := by
  refine ⟨fun h => ?_, mk_eq_zero_of_prop⟩
  rw [← mk_zero, mk_eq_iff, stableEquiv_iff] at h
  obtain ⟨A₁, A₂, hA₁, hA₂, ⟨e⟩⟩ := h
  have hXA₁ : A (X ⊞ A₁) :=
    A.prop_of_iso ((isoZeroBiprod (isZero_zero C)).trans e.symm) hA₂
  exact A.prop_left_of_biprod hXA₁ hA₁

variable {A : ObjectProperty C} [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]

/-- If `X` lies in the retract closure of a strictly full triangulated subcategory `A`, then
`mk A X + mk A (X⟦1⟧) = 0`. -/
theorem mk_add_mk_shift_one {X : C} (hX : A.retractClosure X) :
    mk A X + mk A (X⟦(1 : ℤ)⟧) = 0 := by
  rw [← mk_biprod]
  exact mk_eq_zero_of_prop (A.prop_biprod_shift_one_of_retractClosure hX)

/-- **Distinguished triangle additivity in `TauCeti.StableClasses A`**: for a distinguished triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` whose outer terms lie in the retract closure of a strictly full triangulated
subcategory `A`, `mk A Y = mk A X + mk A Z`. -/
theorem mk_distTriang {T : Triangle C} (hT : T ∈ distTriang C)
    (h₁ : A.retractClosure T.obj₁) (h₃ : A.retractClosure T.obj₃) :
    mk A T.obj₂ = mk A T.obj₁ + mk A T.obj₃ := by
  have hmid : mk A T.obj₂ + (mk A (T.obj₁⟦(1 : ℤ)⟧) + mk A (T.obj₃⟦(1 : ℤ)⟧)) = 0 := by
    simp only [← mk_biprod]
    exact mk_eq_zero_of_prop (A.prop_biprod_shift_one_of_distTriang hT h₁ h₃)
  have h₁' : mk A (T.obj₁⟦(1 : ℤ)⟧) + mk A T.obj₁ = 0 := by
    simpa only [add_comm] using mk_add_mk_shift_one h₁
  have h₃' : mk A (T.obj₃⟦(1 : ℤ)⟧) + mk A T.obj₃ = 0 := by
    simpa only [add_comm] using mk_add_mk_shift_one h₃
  exact left_neg_eq_right_neg hmid <| by
    rw [add_add_add_comm, h₁', h₃', zero_add]

variable (A) in
/-- **Abelian group structure on stable classes modulo a dense triangulated subcategory**
(Thomason 1997, Lemma 2.2): when `A` is a dense strictly full triangulated subcategory of `C`,
`TauCeti.StableClasses A` is an abelian group whose negation sends `mk A X` to `mk A (X⟦1⟧)`.

Exposed alongside `instance_reducible` so that downstream callers installing this instance locally
get definitional agreement of its underlying `AddCommMonoid` with the global instance. -/
@[expose, instance_reducible]
noncomputable def addCommGroup (hdense : A.retractClosure = ⊤) : AddCommGroup (StableClasses A) :=
  let _ : Neg (StableClasses A) := ⟨shift (1 : ℤ)⟩
  { (inferInstance : AddCommMonoid (StableClasses A)) with
    neg := shift (1 : ℤ)
    sub := fun x y => x + shift (1 : ℤ) y
    sub_eq_add_neg := fun _ _ => rfl
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      induction x using induction_on with | h X =>
      simpa only [shift_mk, add_comm] using mk_add_mk_shift_one (hdense.ge X trivial) }

/-- In the abelian group structure `TauCeti.StableClasses.addCommGroup`, negation sends the class
of `X` to the class of `X⟦1⟧`. -/
@[simp]
theorem addCommGroup_neg_mk (hdense : A.retractClosure = ⊤) (X : C) :
    letI := addCommGroup A hdense;
    -mk A X = mk A (X⟦(1 : ℤ)⟧) :=
  shift_mk (1 : ℤ) X

end TauCeti.StableClasses
