/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.Ring

/-!
# Orbit categories of integral shifts

Let `D` be a preadditive category with an additive `ℤ`-shift and let `n : ℤ`. The orbit
category `D/[n]` has the objects of `D` and hom groups

`Hom_{D/[n]}(X, Y) = ⨁_{j : ℤ} Hom_D(X, Y⟦n * j⟧)`.

Homogeneous pieces `f : X ⟶ Y⟦n * i⟧` and `g : Y ⟶ Z⟦n * j⟧` compose to
`f ≫ g⟦n * i⟧' ≫ (Z⟦n * j⟧⟦n * i⟧ ≅ Z⟦n * (i + j)⟧)`, which is the composition
`ShiftedHom.comp` of shifted morphisms; composition is extended biadditively to the direct
sums. The coherence of `shiftFunctorAdd'` makes this associative.

This file constructs the orbit category with its preadditive structure, the additive and
faithful projection `D ⥤ D/[n]` (the identity on objects and the degree-zero inclusion on
morphisms), and the periodicity isomorphism `[n] ⋙ π ≅ π`. Its component at `X` is the
identity of `X⟦n⟧`, read as a morphism `X⟦n⟧ ⟶ X` of degree `1`, with inverse in degree `-1`.
More generally `X⟦n * i⟧ ≅ X` in `D/[n]` for every `i`.

The orbit category is constructed rather than axiomatized: its hom groups are the displayed
direct sums, so additive maps out of them are determined by their values on homogeneous
pieces (`DirectSum.addHom_ext`, with `TauCeti.OrbitCategory.homOf_def`). Keller and Stai use it
to compare bounded derived categories with periodic derived categories.

## Main definitions

* `TauCeti.OrbitCategory D n`: the orbit category `D/[n]`.
* `TauCeti.OrbitCategory.homOf`: the inclusion of a homogeneous piece into an orbit hom group.
* `TauCeti.OrbitCategory.projection`: the projection functor `D ⥤ D/[n]`.
* `TauCeti.OrbitCategory.shiftNatIso`: the isomorphism `[n * i] ⋙ π ≅ π`.
* `TauCeti.OrbitCategory.periodicity`: the periodicity isomorphism `[n] ⋙ π ≅ π`.

## Main results

* `TauCeti.OrbitCategory.homOf_comp_homOf`: homogeneous pieces compose by `ShiftedHom.comp`.

## References

* B. Keller, *On triangulated orbit categories*, Documenta Mathematica **10** (2005),
  551–581, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3.
-/

-- Only the representation of morphisms is exposed: the hom groups `Hom` and the instances, so
-- that downstream morphisms of `D/[n]` are visibly elements of the direct sums and additive
-- functors out of `D/[n]` can be defined summand by summand. The homogeneous inclusion `homOf`
-- and the shift isomorphisms are used through their characteristic lemmas.
public section

noncomputable section

universe v u

open CategoryTheory Category

namespace TauCeti

/-- The orbit category `D/[n]` of a category with an integral shift. Its objects are those of
`D`; the wrapper keeps the orbit category and `D` apart for instance resolution. The morphisms
are constructed in the `Category` instance below, when `D` is preadditive with an additive
shift. -/
structure OrbitCategory (D : Type u) [Category.{v} D] (n : ℤ) where
  /-- The underlying object of `D`. -/
  obj : D

namespace OrbitCategory

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [∀ a : ℤ, (shiftFunctor D a).Additive] {n : ℤ}

/-- The orbit hom group `⨁_{j : ℤ} Hom_D(X, Y⟦n * j⟧)`. -/
abbrev Hom (X Y : OrbitCategory D n) : Type v :=
  DirectSum ℤ fun j : ℤ ↦ ShiftedHom X.obj Y.obj (n * j)

-- Composition places the composite of homogeneous pieces of degrees `i` and `j` in degree
-- `i + j`, and is extended biadditively to the direct sums.
instance : CategoryStruct.{v} (OrbitCategory D n) where
  Hom := Hom
  id X := DirectSum.of (fun j : ℤ ↦ ShiftedHom X.obj X.obj (n * j)) 0
    (ShiftedHom.mk₀ (n * 0) (by simp) (𝟙 X.obj))
  comp {X Y Z} f g := (DirectSum.toAddMonoid fun i ↦ AddMonoidHom.flip <|
    DirectSum.toAddMonoid fun j ↦ AddMonoidHom.flip <| AddMonoidHom.mk'
      (fun a : ShiftedHom X.obj Y.obj (n * i) ↦
        (DirectSum.of (fun k : ℤ ↦ ShiftedHom X.obj Z.obj (n * k)) (i + j)).comp <|
          AddMonoidHom.mk' (fun b : ShiftedHom Y.obj Z.obj (n * j) ↦ a.comp b (by ring))
            fun _ _ ↦ by simp)
      fun _ _ ↦ by ext; simp : Hom X Y →+ Hom Y Z →+ Hom X Z) f g

instance (X Y : OrbitCategory D n) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (Hom X Y))

private theorem of_comp_of {X Y Z : OrbitCategory D n} {i j k : ℤ} (h : i + j = k)
    (f : ShiftedHom X.obj Y.obj (n * i)) (g : ShiftedHom Y.obj Z.obj (n * j)) :
    @Eq (X ⟶ Z) ((DirectSum.of (fun j : ℤ ↦ ShiftedHom X.obj Y.obj (n * j)) i f : X ⟶ Y) ≫
        (DirectSum.of (fun k : ℤ ↦ ShiftedHom Y.obj Z.obj (n * k)) j g : Y ⟶ Z))
      (DirectSum.of (fun l : ℤ ↦ ShiftedHom X.obj Z.obj (n * l)) k
        (f.comp g (by subst h; ring))) := by
  subst h
  simp [CategoryStruct.comp]

instance : Category.{v} (OrbitCategory D n) where
  id_comp {X Y} f := by
    induction f using DirectSum.induction_on with
    | zero => simp [CategoryStruct.comp]
    | of j g => simp [CategoryStruct.id, of_comp_of (zero_add j)]
    | add f₁ f₂ h₁ h₂ => simp_all only [CategoryStruct.comp, map_add]
  comp_id {X Y} f := by
    induction f using DirectSum.induction_on with
    | zero => simp [CategoryStruct.comp]
    | of j g => simp [CategoryStruct.id, of_comp_of (add_zero j)]
    | add f₁ f₂ h₁ h₂ => simp_all only [CategoryStruct.comp, map_add, AddMonoidHom.add_apply]
  assoc {X Y Z T} f g h := by
    induction f using DirectSum.induction_on with
    | zero => simp [CategoryStruct.comp]
    | add f₁ f₂ h₁ h₂ => simp_all only [CategoryStruct.comp, map_add, AddMonoidHom.add_apply]
    | of i f =>
      induction g using DirectSum.induction_on with
      | zero => simp [CategoryStruct.comp]
      | add g₁ g₂ h₁ h₂ => simp_all only [CategoryStruct.comp, map_add, AddMonoidHom.add_apply]
      | of j g =>
        induction h using DirectSum.induction_on with
        | zero => simp [CategoryStruct.comp]
        | add h₁ h₂ k₁ k₂ => simp_all only [CategoryStruct.comp, map_add]
        | of k h =>
          rw [of_comp_of (rfl : i + j = _), of_comp_of (rfl : j + k = _),
            of_comp_of (add_assoc i j k).symm, of_comp_of (rfl : i + j + k = _)]
          congr 1
          exact ShiftedHom.comp_assoc _ _ _ _ _ (by ring)

instance : Preadditive (OrbitCategory D n) where
  add_comp _ _ _ f f' g := DFunLike.congr_fun (map_add _ f f') g
  comp_add _ _ _ f g g' := map_add _ g g'

/-- The inclusion of the homogeneous piece of degree `i`, the morphisms `X ⟶ Y⟦n * i⟧` of `D`,
into the orbit hom group from `X` to `Y`. -/
def homOf {X Y : D} (i : ℤ) :
    ShiftedHom X Y (n * i) →+ ((⟨X⟩ : OrbitCategory D n) ⟶ ⟨Y⟩) :=
  DirectSum.of (fun j : ℤ ↦ ShiftedHom X Y (n * j)) i

/-- `homOf i` is the inclusion `DirectSum.of` of the summand of degree `i`. -/
theorem homOf_def {X Y : D} (i : ℤ) :
    homOf (n := n) (X := X) (Y := Y) i = DirectSum.of (fun j : ℤ ↦ ShiftedHom X Y (n * j)) i := by
  rfl

/-- An additive map out of an orbit hom group defined summand by summand sends a homogeneous
piece to the value of the corresponding summand. -/
@[simp]
theorem toAddMonoid_homOf {X Y : D} {A : Type*} [AddCommMonoid A]
    (φ : ∀ j : ℤ, ShiftedHom X Y (n * j) →+ A) (i : ℤ) (f : ShiftedHom X Y (n * i)) :
    DirectSum.toAddMonoid φ (homOf i f) = φ i f := by
  rw [homOf_def, DirectSum.toAddMonoid_of]

theorem homOf_comp_homOf_eq {X Y Z : D} {i j k : ℤ} (h : i + j = k)
    (f : ShiftedHom X Y (n * i)) (g : ShiftedHom Y Z (n * j)) :
    (homOf i f ≫ homOf j g : (⟨X⟩ : OrbitCategory D n) ⟶ ⟨Z⟩) =
      homOf k (f.comp g (by subst h; ring)) :=
  of_comp_of (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) h f g

/-- Homogeneous pieces compose by the composition of shifted morphisms, adding degrees. This has
low priority so that the degree-zero special cases below, which avoid indices `0 + j`, apply
first. -/
@[simp low]
theorem homOf_comp_homOf {X Y Z : D} {i j : ℤ}
    (f : ShiftedHom X Y (n * i)) (g : ShiftedHom Y Z (n * j)) :
    (homOf i f ≫ homOf j g : (⟨X⟩ : OrbitCategory D n) ⟶ ⟨Z⟩) =
      homOf (i + j) (f.comp g (by ring)) :=
  homOf_comp_homOf_eq rfl f g

theorem id_def (X : D) :
    𝟙 (⟨X⟩ : OrbitCategory D n) = homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) (𝟙 X)) := by
  rfl

/-- Precomposition with a degree-zero piece is composition in `D`. -/
@[simp]
theorem homOf_mk₀_comp_homOf {X Y Z : D} {j : ℤ} (f : X ⟶ Y) (g : ShiftedHom Y Z (n * j)) :
    (homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) f) ≫ homOf j g :
      (⟨X⟩ : OrbitCategory D n) ⟶ ⟨Z⟩) = homOf j (f ≫ g) := by
  rw [homOf_comp_homOf_eq (zero_add j), ShiftedHom.mk₀_comp]

/-- Postcomposition with a degree-zero piece shifts it into the degree of the first piece. -/
@[simp]
theorem homOf_comp_homOf_mk₀ {X Y Z : D} {i : ℤ} (f : ShiftedHom X Y (n * i)) (g : Y ⟶ Z) :
    (homOf i f ≫ homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) g) :
      (⟨X⟩ : OrbitCategory D n) ⟶ ⟨Z⟩) = homOf i (f ≫ g⟦n * i⟧') := by
  rw [homOf_comp_homOf_eq (add_zero i), ShiftedHom.comp_mk₀]

/-- The projection `D ⥤ D/[n]`: the identity on objects and the degree-zero inclusion on
morphisms. -/
-- Reducible so that `projection.obj X` is reducibly `⟨X⟩`: morphisms between projected objects
-- are then literally sums of the pieces `homOf i f`, and the lemmas about `homOf` apply to them.
abbrev projection : D ⥤ OrbitCategory D n where
  obj X := ⟨X⟩
  map f := homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) f)
  map_id X := (id_def X).symm
  map_comp f g := by rw [homOf_comp_homOf_eq (add_zero 0), ShiftedHom.mk₀_comp_mk₀]

theorem projection_map {X Y : D} (f : X ⟶ Y) :
    (projection (n := n)).map f = homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) f) := rfl

instance : (projection (D := D) (n := n)).Additive where
  map_add := by simp

instance : (projection (D := D) (n := n)).Faithful where
  map_injective h := (ShiftedHom.homEquiv _ (by simp)).injective (DirectSum.of_injective
    (β := fun j : ℤ ↦ ShiftedHom _ _ (n * j)) 0 (by simp only [homOf_def] at h; exact h))

/-- For `m = n * i`, the objects `X⟦m⟧` and `X` are isomorphic in the orbit category: the
identity of `X⟦m⟧` is a homogeneous morphism `X⟦m⟧ ⟶ X` of degree `i`. Its inverse has
degree `-i`. -/
def shiftIso (X : D) (m i : ℤ) (h : n * i = m) :
    (projection (n := n)).obj (X⟦m⟧) ≅ projection.obj X where
  hom := homOf i (eqToHom (by rw [h]))
  inv := homOf (-i) ((shiftFunctorCompIsoId D m (n * -i) (by rw [← h]; ring)).inv.app X)
  -- The composites land in degree `0`, whose shift `n * 0` is only propositionally `0`;
  -- generalizing it lets `shiftFunctorZero'` and `shiftFunctorAdd'` at `0` cancel.
  hom_inv_id := by
    subst h
    rw [homOf_comp_homOf_eq (add_neg_cancel i), id_def]
    congr 1
    generalize_proofs
    generalize n * 0 = c at *
    obtain rfl : c = 0 := by assumption
    simp only [ShiftedHom.comp, ShiftedHom.mk₀, shift_shiftFunctorCompIsoId_inv_app]
    simp [shiftFunctorCompIsoId, shiftFunctorZero']
  inv_hom_id := by
    subst h
    rw [homOf_comp_homOf_eq (neg_add_cancel i), id_def]
    congr 1
    generalize_proofs
    generalize n * 0 = c at *
    obtain rfl : c = 0 := by assumption
    simp [ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorCompIsoId, shiftFunctorZero']

-- The bodies of `shiftIso` and `shiftNatIso` are not exposed, so these lemmas are proved by
-- tactic `rfl` inside this module rather than exported as definitional lemmas.
@[simp]
theorem shiftIso_hom (X : D) (m i : ℤ) (h : n * i = m) :
    (shiftIso (n := n) X m i h).hom = homOf i (eqToHom (by rw [h])) := by
  rfl

@[simp]
theorem shiftIso_inv (X : D) (m i : ℤ) (h : n * i = m) :
    (shiftIso (n := n) X m i h).inv =
      homOf (-i) ((shiftFunctorCompIsoId D m (n * -i) (by rw [← h]; ring)).inv.app X) := by
  rfl

/-- For `m = n * i`, the shift by `m` becomes isomorphic to the identity in the orbit
category, with components `shiftIso`. -/
def shiftNatIso (m i : ℤ) (h : n * i = m) :
    shiftFunctor D m ⋙ projection (n := n) ≅ projection :=
  NatIso.ofComponents (fun X ↦ shiftIso X m i h) fun f ↦ by
    subst h
    simp

@[simp]
theorem shiftNatIso_hom_app (m i : ℤ) (h : n * i = m) (X : D) :
    (shiftNatIso m i h).hom.app X = (shiftIso X m i h).hom := by
  rfl

@[simp]
theorem shiftNatIso_inv_app (m i : ℤ) (h : n * i = m) (X : D) :
    (shiftNatIso m i h).inv.app X = (shiftIso X m i h).inv := by
  rfl

/-- The periodicity isomorphism `[n] ⋙ π ≅ π` of the projection to the orbit category. Its
component at `X` is the identity of `X⟦n⟧`, viewed as a morphism `X⟦n⟧ ⟶ X` of degree `1`. -/
abbrev periodicity : shiftFunctor D n ⋙ projection (n := n) ≅ projection :=
  shiftNatIso n 1 (mul_one n)

end OrbitCategory

end TauCeti
