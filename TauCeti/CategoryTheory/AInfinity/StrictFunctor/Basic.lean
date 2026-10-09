/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Basic

/-!
# Strict functors of A-infinity categories

A strict functor of nonunital `A∞` categories consists of an object map and degree-zero
linear maps on Hom modules preserving every operation on composable strings. Its higher
functor components are zero. No identity-preservation condition is imposed here.

The operation equation is required only on composable strings. In particular, the object map
need not be injective: two arrows that are not composable can become composable after applying
it. Requiring a morphism of the total morphism algebras would incorrectly exclude such functors.

We provide extensionality, identity, composition, the degreewise operation equation, and the
chain-map and binary-composition equations. Composition has no additional Koszul sign because
all Hom maps have degree zero.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 7.1.
-/

public section

namespace TauCeti

open GradedLinearQuiver

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w

variable {R : Type w} [CommRing R]
  {C : Type u₁} {D : Type u₂} {E : Type u₃} {K : Type u₄}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]
  [GradedLinearQuiver.{u₃, v₃, w} R E] [GradedLinearQuiver.{u₄, v₄, w} R K]

/-- A strict functor between nonunital `A∞` categories: an arbitrary object map and
degree-zero linear Hom maps commuting with all operations on composable strings.
There is no unit-preservation condition. -/
structure AInfinityStrictFunctor (𝒞 : AInfinityCategory R C) (𝒟 : AInfinityCategory R D) where
  /-- The map on objects. -/
  obj : C → D
  /-- The linear map on each Hom module. -/
  map (X Y : C) : homModule (R := R) X Y →ₗ[R] homModule (R := R) (obj X) (obj Y)
  /-- Each Hom map preserves degree. -/
  map_mem' : ∀ (X Y : C) {p : ℤ} {f : homModule (R := R) X Y},
    f ∈ (grading (R := R) X Y).piece p →
      map X Y f ∈ (grading (R := R) (obj X) (obj Y)).piece p
  /-- Each operation is preserved on every composable string, in Keller's input order. -/
  map_operation' : ∀ {n : ℕ} (X : Fin (n + 1) → C)
    (f : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)),
    map (X 0) (X (Fin.last n))
        (homProjection (X 0) (X (Fin.last n))
          (𝒞.m n fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i))) =
      homProjection (obj (X 0)) (obj (X (Fin.last n)))
        (𝒟.m n fun i ↦ homInclusion (obj (X i.rev.castSucc)) (obj (X i.rev.succ))
          (map (X i.rev.castSucc) (X i.rev.succ) (f i)))

namespace AInfinityStrictFunctor

variable {𝒞 : AInfinityCategory R C} {𝒟 : AInfinityCategory R D}
  {ℰ : AInfinityCategory R E} {𝒦 : AInfinityCategory R K}

/-- Strict functors are determined by their object and Hom maps. The heterogeneous equality
accounts only for the endpoints of the target Hom modules. -/
@[ext]
theorem ext {F G : AInfinityStrictFunctor 𝒞 𝒟} (hobj : F.obj = G.obj)
    (hmap : HEq F.map G.map) : F = G := by
  cases F
  cases G
  cases hobj
  cases hmap
  rfl

/-- Strict functors with equal object maps are equal if their Hom maps agree pointwise,
after transporting the target endpoints along the object-map equality. -/
@[ext (iff := false)]
theorem ext_of_obj_eq {F G : AInfinityStrictFunctor 𝒞 𝒟} (hobj : F.obj = G.obj)
    (hmap : ∀ (X Y : C) (f : homModule (R := R) X Y),
      (hobj ▸ F.map X Y f) = G.map X Y f) : F = G := by
  cases F
  cases G
  cases hobj
  apply ext
  · rfl
  · apply heq_of_eq
    funext X Y
    exact LinearMap.ext (hmap X Y)

/-- The Hom map of a strict functor preserves degree. -/
@[grind =>]
theorem map_mem (F : AInfinityStrictFunctor 𝒞 𝒟) (X Y : C) {p : ℤ}
    {f : homModule (R := R) X Y} (hf : f ∈ (grading (R := R) X Y).piece p) :
    F.map X Y f ∈ (grading (R := R) (F.obj X) (F.obj Y)).piece p :=
  F.map_mem' X Y hf

/-- A strict functor preserves operations on composable strings of arbitrary morphisms. -/
theorem map_operation (F : AInfinityStrictFunctor 𝒞 𝒟) {n : ℕ}
    (X : Fin (n + 1) → C)
    (f : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    F.map (X 0) (X (Fin.last n))
        (homProjection (X 0) (X (Fin.last n))
          (𝒞.m n fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i))) =
      homProjection (F.obj (X 0)) (F.obj (X (Fin.last n)))
        (𝒟.m n fun i ↦ homInclusion (F.obj (X i.rev.castSucc)) (F.obj (X i.rev.succ))
          (F.map (X i.rev.castSucc) (X i.rev.succ) (f i))) :=
  F.map_operation' X f

/-- The map of a strict functor on the degree-`p` piece of a Hom module. -/
def gradedMap (F : AInfinityStrictFunctor 𝒞 𝒟) (X Y : C) (p : ℤ) :
    grHom R X Y p →ₗ[R] grHom R (F.obj X) (F.obj Y) p :=
  (F.map X Y ∘ₗ ((grading (R := R) X Y).piece p).subtype).codRestrict _
    (fun f ↦ F.map_mem X Y f.property)

@[simp]
theorem coe_gradedMap (F : AInfinityStrictFunctor 𝒞 𝒟) (X Y : C) (p : ℤ)
    (f : grHom R X Y p) :
    (F.gradedMap X Y p f : homModule (R := R) (F.obj X) (F.obj Y)) = F.map X Y f :=
  (rfl)

/-- A strict functor preserves the degreewise operations on composable homogeneous morphisms. -/
@[simp]
theorem map_pathOperation (F : AInfinityStrictFunctor 𝒞 𝒟) {n : ℕ}
    (X : Fin (n + 1) → C) (d : Fin n → ℤ)
    (f : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    F.gradedMap (X 0) (X (Fin.last n)) ((∑ i, d i) + (2 - n))
        (𝒞.pathOperation X d f) =
      𝒟.pathOperation (F.obj ∘ X) d
        (fun i ↦ F.gradedMap (X i.rev.castSucc) (X i.rev.succ) (d i) (f i)) := by
  apply Subtype.ext
  simpa only [coe_gradedMap, AInfinityCategory.coe_pathOperation_apply, Function.comp_apply]
    using F.map_operation X (fun i ↦ (f i).val)

/-- A strict functor commutes with the differential of every Hom module. -/
@[simp]
theorem map_homDifferential (F : AInfinityStrictFunctor 𝒞 𝒟) (X Y : C)
    (f : homModule (R := R) X Y) :
    F.map X Y (𝒞.homDifferential X Y f) =
      𝒟.homDifferential (F.obj X) (F.obj Y) (F.map X Y f) := by
  have h := F.map_operation ![X, Y]
    (Fin.cases (motive := fun i ↦ homModule (R := R)
      (![X, Y] i.rev.castSucc) (![X, Y] i.rev.succ)) f fun i ↦ i.elim0)
  simp only [AInfinityCategory.homDifferential_apply]
  convert h using 1 <;> congr 3 <;> funext i <;> fin_cases i <;> rfl

/-- A strict functor preserves the binary composition `m₂(g,f)`. -/
@[simp]
theorem map_comp (F : AInfinityStrictFunctor 𝒞 𝒟) (X Y Z : C)
    (g : homModule (R := R) Y Z) (f : homModule (R := R) X Y) :
    F.map X Z (𝒞.comp X Y Z g f) =
      𝒟.comp (F.obj X) (F.obj Y) (F.obj Z) (F.map Y Z g) (F.map X Y f) := by
  have h := F.map_operation ![X, Y, Z]
    (Fin.cases (motive := fun i ↦ homModule (R := R)
      (![X, Y, Z] i.rev.castSucc) (![X, Y, Z] i.rev.succ))
      g (Fin.cases f fun i ↦ i.elim0))
  simp only [AInfinityCategory.comp_apply]
  convert h using 1 <;> congr 3 <;> funext i <;> fin_cases i <;> rfl

/-- The identity strict functor of a nonunital `A∞` category. -/
-- Expose the object map so the types of the characteristic Hom-map equations reduce.
@[expose]
protected def id (𝒞 : AInfinityCategory R C) : AInfinityStrictFunctor 𝒞 𝒞 where
  obj := _root_.id
  map _ _ := LinearMap.id
  map_mem' _ _ {_} {_} hf := hf
  map_operation' _ _ := rfl

@[simp]
theorem id_obj (𝒞 : AInfinityCategory R C) (X : C) :
    (AInfinityStrictFunctor.id 𝒞).obj X = X := (rfl)

@[simp]
theorem id_map (𝒞 : AInfinityCategory R C) (X Y : C) :
    (AInfinityStrictFunctor.id 𝒞).map X Y = LinearMap.id := (rfl)

/-- Composition of strict functors: apply the first Hom map, then the second. -/
-- As for identity, the object map determines the types of the Hom-map equations.
@[expose]
def comp (G : AInfinityStrictFunctor 𝒟 ℰ) (F : AInfinityStrictFunctor 𝒞 𝒟) :
    AInfinityStrictFunctor 𝒞 ℰ where
  obj := G.obj ∘ F.obj
  map X Y := G.map (F.obj X) (F.obj Y) ∘ₗ F.map X Y
  map_mem' X Y {_} {_} hf := G.map_mem _ _ (F.map_mem X Y hf)
  map_operation' X f := by
    simp only [LinearMap.comp_apply, Function.comp_apply]
    rw [F.map_operation]
    exact G.map_operation (F.obj ∘ X) (fun i ↦ F.map _ _ (f i))

@[simp]
theorem comp_obj (G : AInfinityStrictFunctor 𝒟 ℰ) (F : AInfinityStrictFunctor 𝒞 𝒟)
    (X : C) : (G.comp F).obj X = G.obj (F.obj X) := (rfl)

@[simp]
theorem comp_map (G : AInfinityStrictFunctor 𝒟 ℰ) (F : AInfinityStrictFunctor 𝒞 𝒟)
    (X Y : C) :
    (G.comp F).map X Y = G.map (F.obj X) (F.obj Y) ∘ₗ F.map X Y := (rfl)

@[simp]
theorem comp_id (F : AInfinityStrictFunctor 𝒞 𝒟) :
    F.comp (AInfinityStrictFunctor.id 𝒞) = F := by
  apply ext_of_obj_eq rfl
  intro X Y f
  simp only [comp_map, id_map]

@[simp]
theorem id_comp (F : AInfinityStrictFunctor 𝒞 𝒟) :
    (AInfinityStrictFunctor.id 𝒟).comp F = F := by
  apply ext_of_obj_eq rfl
  intro X Y f
  simp only [comp_map, id_map]

/-- Composition of strict functors is associative. -/
@[simp]
theorem comp_assoc (H : AInfinityStrictFunctor ℰ 𝒦) (G : AInfinityStrictFunctor 𝒟 ℰ)
    (F : AInfinityStrictFunctor 𝒞 𝒟) : (H.comp G).comp F = H.comp (G.comp F) := by
  apply ext_of_obj_eq rfl
  intro X Y f
  simp only [comp_map]

end AInfinityStrictFunctor

end TauCeti
