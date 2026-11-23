/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split.Dense
public import TauCeti.CategoryTheory.GrothendieckGroup.Triangulated
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
public import TauCeti.CategoryTheory.Triangulated.Biproduct
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Dense triangulated subcategories are classified by triangulated `K₀`

Let `C` be an essentially small pretriangulated category. A triangulated subcategory `A` of `C`,
closed under isomorphisms, is *dense* if every object of `C` is a retract (equivalently, by
`CategoryTheory.Retract.exists_iso_biprod`, a direct summand) of an object of `A`; in Mathlib's
language, `A.retractClosure = ⊤`. Thomason's theorem says that such subcategories are exactly the
subgroups of triangulated `K₀`:

* an object `X` lies in `A` exactly when its class lies in the image of `K₀(A) → K₀(C)`;
* the map `K₀(A) → K₀(C)` induced by the inclusion is injective;
* conversely, for every subgroup `H` of `K₀(C)`, the objects whose classes lie in `H` form a dense
  triangulated subcategory, closed under isomorphisms, whose `K₀` has image exactly `H`.

Density cannot be dropped: for instance, in the bounded derived category of a field `k`, the zero
subcategory is triangulated but not dense, and the nonzero object `k ⊕ k[1]` has class zero.

## Implementation notes

An equality of classes in `K₀(C)` is not by itself an isomorphism of objects, so membership in `A`
cannot be read off directly from `K₀(C)`. Thomason passes instead through *stable* classes: two
objects are identified when they become isomorphic after adding objects of `A`. We record the
stable class of `X` together with a correction in `K₀(A)`, in the abelian group
`(SplitK0 C × K₀(A)) / {([B], -[B]) : B ∈ split K₀(A)}`. In this group:

* every object `X` has an inverse, since density provides `X'` with `X ⊞ X'` in `A`;
* an element `(0, a)` vanishes only when `a = 0`, because split `K₀` of `A` injects into split
  `K₀` of `C` (`TauCeti.SplitK0.map_ι_injective_of_retractClosure_eq_top`);
* the stable class `X ↦ ([X], 0)` is additive on distinguished triangles. When the third vertex
  of the triangle lies in `A`, adding a complement of the middle vertex produces a triangle with
  all vertices in `A`, whose relation holds in `K₀(A)`; the general case reduces to this one by
  adding a complement of the third vertex.

The induced homomorphism out of `K₀(C)` restricts on `K₀(A)` to the injective map `a ↦ (0, a)`,
which gives injectivity, and a class `[X]` coming from `K₀(A)` gives a stable isomorphism
`X ⊞ B₁ ≅ B₂` with `B₁, B₂` in `A`, which puts `X` in `A`.

## Main definitions

* `TauCeti.TriangulatedK0.classSubcategory H`: the objects whose class lies in the subgroup `H` of
  triangulated `K₀`. It is a dense triangulated subcategory closed under isomorphisms.

## Main results

* `TauCeti.TriangulatedK0.of_mem_range_map_ι_iff`: for a dense triangulated subcategory `A` closed
  under isomorphisms, `[X]` lies in the image of `K₀(A)` if and only if `X` lies in `A`.
* `TauCeti.TriangulatedK0.map_ι_injective`: for such `A`, the map `K₀(A) → K₀(C)` is injective.
* `TauCeti.TriangulatedK0.retractClosure_classSubcategory_eq_top`: the subcategory attached to a
  subgroup is dense.
* `TauCeti.TriangulatedK0.classSubcategory_range_map_ι` and
  `TauCeti.TriangulatedK0.range_map_ι_classSubcategory`: the two assignments `A ↦ im K₀(A)` and
  `H ↦ classSubcategory H` are mutually inverse.
* `TauCeti.TriangulatedK0.existsUnique_classSubcategory`: every subgroup of triangulated `K₀`
  determines a unique dense triangulated subcategory, closed under isomorphisms, whose objects are
  those with class in the subgroup.

## References

* R. W. Thomason, *The classification of triangulated subcategories*, Compositio Mathematica
  **105** (1997), 1–27, Lemma 2.2, Theorem 2.1 and Corollary 2.3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe w w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace TriangulatedK0

section Dense

variable (A : ObjectProperty C) [A.IsClosedUnderIsomorphisms]

variable [A.IsTriangulated] [EssentiallySmall.{w} C] [EssentiallySmall.{w'} A.FullSubcategory]

/-- The relations of the stable group: a split class `s` of `A` is identified with its image in
split `K₀` of `C`, corrected by its class in triangulated `K₀` of `A`. -/
private noncomputable def stableRel :
    SplitK0 A.FullSubcategory →+ SplitK0 C × TriangulatedK0 A.FullSubcategory :=
  (SplitK0.map A.ι).prod (-fromSplit A.FullSubcategory)

/-- The stable group of `C` relative to `A`: stable classes of objects of `C` together with a
correction in triangulated `K₀` of `A`. -/
private abbrev StableK0 :=
  (SplitK0 C × TriangulatedK0 A.FullSubcategory) ⧸ (stableRel A).range

/-- The stable class of a split class of `C`. -/
private noncomputable def toStable₁ : SplitK0 C →+ StableK0 A :=
  (QuotientAddGroup.mk' _).comp (AddMonoidHom.inl _ _)

/-- The correction term attached to a class of triangulated `K₀` of `A`. -/
private noncomputable def toStable₂ : TriangulatedK0 A.FullSubcategory →+ StableK0 A :=
  (QuotientAddGroup.mk' _).comp (AddMonoidHom.inr _ _)

omit [A.IsClosedUnderIsomorphisms] in
/-- An element of the stable group vanishes exactly when it is the image of a relation. -/
private lemma toStable₁_add_toStable₂_eq_zero_iff (s : SplitK0 C)
    (a : TriangulatedK0 A.FullSubcategory) :
    toStable₁ A s + toStable₂ A a = 0 ↔ ∃ t, stableRel A t = (s, a) := by
  rw [toStable₁, toStable₂, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← map_add,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  simp

omit [A.IsClosedUnderIsomorphisms] in
/-- The defining relation of the stable group. -/
private lemma toStable₁_map (s : SplitK0 A.FullSubcategory) :
    toStable₁ A (SplitK0.map A.ι s) = toStable₂ A (fromSplit _ s) := by
  rw [← sub_eq_zero, sub_eq_add_neg, ← map_neg, toStable₁_add_toStable₂_eq_zero_iff]
  exact ⟨s, rfl⟩

omit [A.IsClosedUnderIsomorphisms] in
/-- On an object of `A`, the stable class is the correction term of its class in `K₀(A)`. -/
private lemma toStable₁_of_prop {X : C} (hX : A X) :
    toStable₁ A (SplitK0.of X) = toStable₂ A (of (⟨X, hX⟩ : A.FullSubcategory)) := by
  rw [← fromSplit_of, ← toStable₁_map, SplitK0.map_of, ObjectProperty.ι_obj]

/-- The correction term is injective: this is where density enters, through
`SplitK0.map_ι_injective_of_retractClosure_eq_top`. -/
private lemma toStable₂_injective (hA : A.retractClosure = ⊤) :
    Function.Injective (toStable₂ A) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨s, hs⟩ := (toStable₁_add_toStable₂_eq_zero_iff A 0 a).1 (by rw [map_zero, zero_add, ha])
  simp only [stableRel, AddMonoidHom.prod_apply, Prod.mk.injEq] at hs
  obtain rfl : s = 0 :=
    SplitK0.map_ι_injective_of_retractClosure_eq_top A hA (by rw [hs.1, map_zero])
  simpa using hs.2.symm

/-- The stable class is additive on a distinguished triangle whose third vertex lies in `A`:
adding a complement `Y'` of the middle vertex produces a distinguished triangle with all three
vertices in `A`, whose relation holds in `K₀(A)`. -/
private lemma toStable₁_of_distTriang_of_prop₃ (hA : A.retractClosure = ⊤) {T : Triangle C}
    (hT : T ∈ distTriang C) (h₃ : A T.obj₃) :
    toStable₁ A (SplitK0.of T.obj₂) =
      toStable₁ A (SplitK0.of T.obj₁) + toStable₁ A (SplitK0.of T.obj₃) := by
  obtain ⟨Y', hY'⟩ := A.exists_prop_biprod_of_retractClosure_eq_top hA T.obj₂
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_iso_biprod T _ hT (contractible_distinguished Y')
  have hS₂ : A S.obj₂ := A.prop_of_iso e₂.symm hY'
  have hS₃ : A S.obj₃ := A.prop_of_iso e₃.symm
    (A.prop_biprod_of_isClosedUnderBinaryProducts h₃ A.prop_zero)
  have hS₁ : A S.obj₁ := A.ext_of_isTriangulatedClosed₁ _ hS hS₂ hS₃
  have h := congrArg (toStable₂ A) (of_fullSubcategory_distTriang A hS hS₁ hS₂ hS₃)
  rw [map_add, ← toStable₁_of_prop, ← toStable₁_of_prop, ← toStable₁_of_prop,
    SplitK0.of_congr e₁, SplitK0.of_congr e₂, SplitK0.of_congr e₃] at h
  simp only [contractibleTriangle_obj₁, contractibleTriangle_obj₂, contractibleTriangle_obj₃,
    SplitK0.of_biprod, SplitK0.of_zero, add_zero, map_add] at h
  rw [add_right_comm] at h
  exact add_right_cancel h

/-- **The stable class is additive on distinguished triangles**: adding a complement `Z'` of the
third vertex reduces to `toStable₁_of_distTriang_of_prop₃`. -/
private lemma toStable₁_of_distTriang (hA : A.retractClosure = ⊤) {T : Triangle C}
    (hT : T ∈ distTriang C) :
    toStable₁ A (SplitK0.of T.obj₂) =
      toStable₁ A (SplitK0.of T.obj₁) + toStable₁ A (SplitK0.of T.obj₃) := by
  obtain ⟨Z', hZ'⟩ := A.exists_prop_biprod_of_retractClosure_eq_top hA T.obj₃
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_iso_biprod T _ hT (contractible_distinguished₁ Z')
  have h := toStable₁_of_distTriang_of_prop₃ A hA hS (A.prop_of_iso e₃.symm hZ')
  rw [SplitK0.of_congr e₁, SplitK0.of_congr e₂, SplitK0.of_congr e₃] at h
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃, SplitK0.of_biprod,
    SplitK0.of_zero, add_zero, map_add] at h
  rw [← add_assoc] at h
  exact add_right_cancel h

/-- The homomorphism from triangulated `K₀` of `C` to the stable group induced by the stable
class. -/
private noncomputable def toStable (hA : A.retractClosure = ⊤) :
    TriangulatedK0 C →+ StableK0 A :=
  lift
    { obj := fun X => toStable₁ A (SplitK0.of X)
      map_distTriang := fun _ hT => toStable₁_of_distTriang A hA hT }

private lemma toStable_of (hA : A.retractClosure = ⊤) (X : C) :
    toStable A hA (of X) = toStable₁ A (SplitK0.of X) :=
  lift_of _ X

/-- On `K₀(A)`, the homomorphism to the stable group is the correction term. -/
private lemma toStable_comp_map (hA : A.retractClosure = ⊤) :
    (toStable A hA).comp (map A.ι) = toStable₂ A :=
  hom_ext fun X => by
    rw [AddMonoidHom.comp_apply, map_of, toStable_of]
    exact toStable₁_of_prop A X.property

/-- **Thomason's injectivity theorem**: for a dense triangulated subcategory `A` closed under
isomorphisms, the homomorphism `K₀(A) → K₀(C)` induced by the inclusion is injective. -/
theorem map_ι_injective (hA : A.retractClosure = ⊤) : Function.Injective (map A.ι) := by
  have h := toStable₂_injective A hA
  rw [← toStable_comp_map A hA, AddMonoidHom.coe_comp] at h
  exact h.of_comp

/-- **Thomason's membership criterion**: for a dense triangulated subcategory `A` closed under
isomorphisms, the class of an object `X` lies in the image of `K₀(A) → K₀(C)` if and only if `X`
lies in `A`. -/
theorem of_mem_range_map_ι_iff (hA : A.retractClosure = ⊤) (X : C) :
    of X ∈ (map A.ι).range ↔ A X := by
  refine ⟨fun ⟨a, ha⟩ => ?_, fun hX => ⟨of ⟨X, hX⟩, map_of _ _⟩⟩
  -- In the stable group, `(0, a)` and `([X], 0)` agree, so `([X], -a)` is a relation.
  have h := congrArg (toStable A hA) ha
  rw [← AddMonoidHom.comp_apply, toStable_comp_map, toStable_of] at h
  obtain ⟨s, hs⟩ := (toStable₁_add_toStable₂_eq_zero_iff A (SplitK0.of X) (-a)).1
    (by rw [map_neg, ← h, add_neg_cancel])
  have hs₁ := congrArg Prod.fst hs
  simp only [stableRel, AddMonoidHom.prod_apply] at hs₁
  -- Writing `s = [P] - [Q]` and using density gives `P ⊞ B ≅ (X ⊞ Q) ⊞ B` with `B` in `A`.
  obtain ⟨P, Q, rfl⟩ := SplitK0.exists_eq_sub s
  rw [map_sub, SplitK0.map_of, SplitK0.map_of, ObjectProperty.ι_obj, ObjectProperty.ι_obj,
    sub_eq_iff_eq_add, ← SplitK0.of_biprod,
    SplitK0.of_eq_of_iff_of_retractClosure_eq_top A hA] at hs₁
  obtain ⟨B, hB, ⟨e⟩⟩ := hs₁
  have e' : P.obj ⊞ B ≅ X ⊞ (Q.obj ⊞ B) := e ≪≫ biprod.associator _ _ _
  have hP : A (P.obj ⊞ B) := A.prop_biprod_of_isClosedUnderBinaryProducts P.property hB
  have hQ : A (Q.obj ⊞ B) := A.prop_biprod_of_isClosedUnderBinaryProducts Q.property hB
  -- The split triangle `X ⟶ X ⊞ B₁ ⟶ B₁ ⟶ X⟦1⟧` has its last two vertices in `A`.
  exact A.ext_of_isTriangulatedClosed₁ _ (binaryBiproductTriangle_distinguished _ _)
    (A.prop_of_iso e' hP) hQ

end Dense

section Classification

variable [EssentiallySmall.{w} C]

/-- The objects of `C` whose class in triangulated `K₀` lies in the subgroup `H`. This is a dense
triangulated subcategory closed under isomorphisms (`retractClosure_classSubcategory_eq_top`),
and every such subcategory arises in this way (`classSubcategory_range_map_ι`). -/
def classSubcategory (H : AddSubgroup (TriangulatedK0 C)) : ObjectProperty C :=
  fun X => of X ∈ H

variable (H : AddSubgroup (TriangulatedK0 C))

@[simp]
lemma prop_classSubcategory_iff (X : C) : classSubcategory H X ↔ of X ∈ H := Iff.rfl

instance : (classSubcategory H).IsClosedUnderIsomorphisms where
  of_iso e h := by rwa [prop_classSubcategory_iff, ← of_congr e]

instance : (classSubcategory H).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, by simp⟩
  isStableUnderShiftBy n := ⟨fun X hX => by
    rw [ObjectProperty.prop_shift_iff, prop_classSubcategory_iff, of_shift]
    exact AddSubgroup.zsmul_mem _ hX _⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ => by
    rw [prop_classSubcategory_iff, of_distTriang hT]
    exact add_mem h₁ h₃

/-- **The subcategory attached to a subgroup is dense**: every object `X` is a retract of
`X ⊞ X⟦1⟧`, whose class `[X] - [X]` vanishes. -/
@[simp]
theorem retractClosure_classSubcategory_eq_top : (classSubcategory H).retractClosure = ⊤ :=
  eq_top_iff.2 fun X _ => ((classSubcategory H).prop_retractClosure_iff_exists_biprod X).2
    ⟨X⟦(1 : ℤ)⟧, by simp [zero_mem]⟩

/-- The image of `K₀` of the subcategory attached to a subgroup `H` is `H` itself. -/
@[simp]
theorem range_map_ι_classSubcategory
    [EssentiallySmall.{w'} (classSubcategory H).FullSubcategory] :
    (map (classSubcategory H).ι).range = H := by
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨a, rfl⟩
    induction a using induction_on with
    | zero => simp
    | of B => simpa using B.property
    | add a b ha hb => simpa using add_mem ha hb
    | neg a ha => simpa using neg_mem ha
  · obtain ⟨X, rfl⟩ := exists_eq_of x
    exact ⟨of ⟨X, hx⟩, map_of _ _⟩

/-- **Thomason's classification**, in the other direction: a dense triangulated subcategory
closed under isomorphisms is the subcategory attached to the image of its `K₀`. -/
theorem classSubcategory_range_map_ι (A : ObjectProperty C) [A.IsTriangulated]
    [A.IsClosedUnderIsomorphisms] [EssentiallySmall.{w'} A.FullSubcategory]
    (hA : A.retractClosure = ⊤) : classSubcategory (map A.ι).range = A :=
  funext fun X => propext (of_mem_range_map_ι_iff A hA X)

/-- **Thomason's classification**: every subgroup `H` of triangulated `K₀` determines a unique
dense triangulated subcategory, closed under isomorphisms, whose objects are those with class in
`H`; it is `classSubcategory H`. -/
theorem existsUnique_classSubcategory :
    ∃! A : ObjectProperty C, A.IsTriangulated ∧ A.IsClosedUnderIsomorphisms ∧
      A.retractClosure = ⊤ ∧ ∀ X : C, A X ↔ of X ∈ H :=
  ⟨classSubcategory H, ⟨inferInstance, inferInstance, retractClosure_classSubcategory_eq_top H,
    prop_classSubcategory_iff H⟩, fun _ ⟨_, _, _, h⟩ => funext fun X => propext (h X)⟩

end Classification

end TriangulatedK0

end TauCeti
