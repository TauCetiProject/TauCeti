/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
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
direct sums, so additive maps out of them are determined by their values on homogeneous pieces
(`TauCeti.OrbitCategory.addMonoidHom_ext`). Keller and Stai use it to compare bounded derived
categories with periodic derived categories.

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

-- Bodies are exposed: morphisms of the orbit category must be visibly elements of the direct
-- sums `Hom X Y` downstream, where additive functors out of `D/[n]` are defined summand by
-- summand, and the projection and periodicity are computed from their homogeneous pieces.
@[expose] public section

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

/-- Composition of homogeneous pieces of degrees `i` and `j`, placed in degree `i + j`. -/
def compPiece (X Y Z : OrbitCategory D n) (i j : ℤ) :
    ShiftedHom X.obj Y.obj (n * i) →+ ShiftedHom Y.obj Z.obj (n * j) →+ Hom X Z where
  toFun f := (DirectSum.of (fun k : ℤ ↦ ShiftedHom X.obj Z.obj (n * k)) (i + j)).comp
    { toFun g := f.comp g (by ring)
      map_zero' := by simp
      map_add' := by simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- Composition in the orbit category, as a biadditive map. -/
def compHom (X Y Z : OrbitCategory D n) : Hom X Y →+ Hom Y Z →+ Hom X Z :=
  DirectSum.toAddMonoid fun i ↦ AddMonoidHom.flip <|
    DirectSum.toAddMonoid fun j ↦ (compPiece X Y Z i j).flip

/-- The identity of `X` in the orbit category: the identity of `X.obj` placed in degree zero. -/
def idHom (X : OrbitCategory D n) : Hom X X :=
  DirectSum.of (fun j : ℤ ↦ ShiftedHom X.obj X.obj (n * j)) 0
    (ShiftedHom.mk₀ (n * 0) (by simp) (𝟙 X.obj))

theorem compHom_of_of {X Y Z : OrbitCategory D n} {i j k : ℤ} (h : i + j = k)
    (f : ShiftedHom X.obj Y.obj (n * i)) (g : ShiftedHom Y.obj Z.obj (n * j)) :
    compHom X Y Z (DirectSum.of (fun j : ℤ ↦ ShiftedHom X.obj Y.obj (n * j)) i f)
        (DirectSum.of (fun k : ℤ ↦ ShiftedHom Y.obj Z.obj (n * k)) j g) =
      DirectSum.of (fun l : ℤ ↦ ShiftedHom X.obj Z.obj (n * l)) k
        (f.comp g (by subst h; ring)) := by
  subst h
  simp [compHom, compPiece]

instance : Category.{v} (OrbitCategory D n) where
  Hom := Hom
  id := idHom
  comp f g := compHom _ _ _ f g
  id_comp {X Y} f := by
    induction f using DirectSum.induction_on with
    | zero => simp
    | of j g => simp [idHom, compHom_of_of (zero_add j)]
    | add f₁ f₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  comp_id {X Y} f := by
    induction f using DirectSum.induction_on with
    | zero => simp
    | of j g => simp [idHom, compHom_of_of (add_zero j)]
    | add f₁ f₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
  assoc {X Y Z T} f g h := by
    induction f using DirectSum.induction_on with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
    | of i f =>
      induction g using DirectSum.induction_on with
      | zero => simp
      | add g₁ g₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
      | of j g =>
        induction h using DirectSum.induction_on with
        | zero => simp
        | add h₁ h₂ k₁ k₂ => simp only [map_add, k₁, k₂]
        | of k h =>
          rw [compHom_of_of (rfl : i + j = _), compHom_of_of (rfl : j + k = _),
            compHom_of_of (add_assoc i j k).symm, compHom_of_of (rfl : i + j + k = _)]
          congr 1
          exact ShiftedHom.comp_assoc _ _ _ _ _ (by ring)

instance (X Y : OrbitCategory D n) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (Hom X Y))

-- `X ⟶ Y` is `Hom X Y` by definition; the ascriptions let `map_add` see the direct-sum addition.
instance : Preadditive (OrbitCategory D n) where
  add_comp X Y Z f f' g := by
    exact (DFunLike.congr_fun (map_add (compHom X Y Z) (f : Hom X Y) f') g : _)
  comp_add X Y Z f g g' := by exact (map_add (compHom X Y Z f) (g : Hom Y Z) g' : _)

/-- The inclusion of the homogeneous piece of degree `i`, the morphisms `X ⟶ Y⟦n * i⟧` of `D`,
into the orbit hom group from `X` to `Y`. -/
def homOf {X Y : D} (i : ℤ) :
    ShiftedHom X Y (n * i) →+ ((⟨X⟩ : OrbitCategory D n) ⟶ ⟨Y⟩) :=
  DirectSum.of (fun j : ℤ ↦ ShiftedHom X Y (n * j)) i

theorem homOf_injective {X Y : D} (i : ℤ) :
    Function.Injective (homOf (n := n) (X := X) (Y := Y) i) :=
  DirectSum.of_injective (β := fun j : ℤ ↦ ShiftedHom X Y (n * j)) i

/-- Additive maps out of an orbit hom group agree when they agree on all homogeneous pieces. -/
@[ext]
theorem addMonoidHom_ext {X Y : D} {A : Type*} [AddZeroClass A]
    {φ ψ : ((⟨X⟩ : OrbitCategory D n) ⟶ ⟨Y⟩) →+ A}
    (h : ∀ i (f : ShiftedHom X Y (n * i)), φ (homOf i f) = ψ (homOf i f)) : φ = ψ :=
  DirectSum.addHom_ext h

theorem homOf_comp_homOf_eq {X Y Z : D} {i j k : ℤ} (h : i + j = k)
    (f : ShiftedHom X Y (n * i)) (g : ShiftedHom Y Z (n * j)) :
    (homOf i f ≫ homOf j g : (⟨X⟩ : OrbitCategory D n) ⟶ ⟨Z⟩) =
      homOf k (f.comp g (by subst h; ring)) :=
  compHom_of_of (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) h f g

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
    𝟙 (⟨X⟩ : OrbitCategory D n) = homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) (𝟙 X)) := rfl

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
  map_id _ := rfl
  map_comp f g := by rw [homOf_comp_homOf_eq (add_zero 0), ShiftedHom.mk₀_comp_mk₀]

theorem projection_map {X Y : D} (f : X ⟶ Y) :
    (projection (n := n)).map f = homOf 0 (ShiftedHom.mk₀ (n * 0) (by simp) f) := rfl

instance : (projection (D := D) (n := n)).Additive where
  map_add := by simp

instance : (projection (D := D) (n := n)).Faithful where
  map_injective h := (ShiftedHom.homEquiv _ (by simp)).injective (homOf_injective 0 h)

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

theorem shiftIso_hom (X : D) (m i : ℤ) (h : n * i = m) :
    (shiftIso (n := n) X m i h).hom = homOf i (eqToHom (by rw [h])) := rfl

theorem shiftIso_inv (X : D) (m i : ℤ) (h : n * i = m) :
    (shiftIso (n := n) X m i h).inv =
      homOf (-i) ((shiftFunctorCompIsoId D m (n * -i) (by rw [← h]; ring)).inv.app X) := rfl

/-- For `m = n * i`, the shift by `m` becomes isomorphic to the identity in the orbit
category, with components `shiftIso`. -/
def shiftNatIso (m i : ℤ) (h : n * i = m) :
    shiftFunctor D m ⋙ projection (n := n) ≅ projection :=
  NatIso.ofComponents (fun X ↦ shiftIso X m i h) fun f ↦ by
    subst h
    simp [shiftIso_hom]

@[simp]
theorem shiftNatIso_hom_app (m i : ℤ) (h : n * i = m) (X : D) :
    (shiftNatIso m i h).hom.app X = (shiftIso X m i h).hom := rfl

@[simp]
theorem shiftNatIso_inv_app (m i : ℤ) (h : n * i = m) (X : D) :
    (shiftNatIso m i h).inv.app X = (shiftIso X m i h).inv := rfl

/-- The periodicity isomorphism `[n] ⋙ π ≅ π` of the projection to the orbit category. Its
component at `X` is the identity of `X⟦n⟧`, viewed as a morphism `X⟦n⟧ ⟶ X` of degree `1`. -/
abbrev periodicity : shiftFunctor D n ⋙ projection (n := n) ≅ projection :=
  shiftNatIso n 1 (mul_one n)

end OrbitCategory

end TauCeti
