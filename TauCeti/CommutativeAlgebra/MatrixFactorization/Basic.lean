/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Finite-projective matrix factorizations

A matrix factorization of `w : S` is a curved duplex of `S`-modules with finitely generated
projective components. We use `FGModuleCat S` for finite generation and take the full
subcategory on the objects whose components are projective. Thus its morphisms are exactly
the closed even maps of curved duplexes, and its forgetful functor is fully faithful.

The parity shift preserves matrix factorizations. The elementary factorization
`P --𝟙--> P --w--> P` supplies contractible objects whenever `P` is finitely generated
projective. These constructions are used in the homotopy and triangulated categories of
matrix factorizations.

The finite-projective convention follows D. Eisenbud, *Homological algebra on a complete
intersection, with an application to group representations*, Trans. Amer. Math. Soc. **260**
(1980), Section 5. The ambient curved-duplex convention follows
`TauCeti.Algebra.Homology.Curved.Duplex`.
-/

public section

universe u

namespace TauCeti

open CategoryTheory

variable (S : Type u) [CommRing S] (w : S)

/-- Curved duplexes whose even and odd components are projective modules. Finite generation is
already part of the objects of `FGModuleCat S`. -/
@[expose, implicit_reducible] def MatrixFactorization.isProjective :
    ObjectProperty (CurvedDuplex (FGModuleCat.{u} S) w) :=
  fun X ↦ Module.Projective S X.X₀ ∧ Module.Projective S X.X₁

/-- The category of finite-projective matrix factorizations of the potential `w` over `S`.
Its arrows are pairs of module maps commuting with both differentials. -/
abbrev MatrixFactorization := (MatrixFactorization.isProjective S w).FullSubcategory

namespace MatrixFactorization

variable {S w}

/-- The even component of a matrix factorization is projective. -/
instance (X : MatrixFactorization S w) : Module.Projective S X.obj.X₀ := X.property.1

/-- The odd component of a matrix factorization is projective. -/
instance (X : MatrixFactorization S w) : Module.Projective S X.obj.X₁ := X.property.2

/-- Construct a finite-projective matrix factorization from a curved duplex and
projectivity of its two components. -/
@[expose] def ofCurvedDuplex (X : CurvedDuplex (FGModuleCat.{u} S) w)
    (h₀ : Module.Projective S X.X₀) (h₁ : Module.Projective S X.X₁) :
    MatrixFactorization S w := ⟨X, h₀, h₁⟩

@[simp] theorem ofCurvedDuplex_obj (X : CurvedDuplex (FGModuleCat.{u} S) w)
    (h₀ : Module.Projective S X.X₀) (h₁ : Module.Projective S X.X₁) :
    (ofCurvedDuplex X h₀ h₁).obj = X := rfl

/-- The fully faithful inclusion of finite-projective matrix factorizations into curved
duplexes of finitely generated modules. -/
abbrev inclusion : MatrixFactorization S w ⥤ CurvedDuplex (FGModuleCat.{u} S) w :=
  ObjectProperty.ι _

/-- The parity shift swaps the projective components and negates both differentials. -/
@[expose, implicit_reducible] def parityShift :
    MatrixFactorization S w ⥤ MatrixFactorization S w where
  obj X := ofCurvedDuplex ((CurvedDuplex.parityShift (FGModuleCat.{u} S) w).obj X.obj)
    X.property.2 X.property.1
  map f := ObjectProperty.homMk
    ((CurvedDuplex.parityShift (FGModuleCat.{u} S) w).map f.hom)

@[simp] theorem parityShift_obj_even (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.X₀ = X.obj.X₁ := rfl

@[simp] theorem parityShift_obj_odd (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.X₁ = X.obj.X₀ := rfl

@[simp] theorem parityShift_obj_d₀ (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.d₀ = -X.obj.d₁ := rfl

@[simp] theorem parityShift_obj_d₁ (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.d₁ = -X.obj.d₀ := rfl

@[simp] theorem parityShift_map_f₀ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    ((parityShift (S := S) (w := w)).map f).hom.f₀ = f.hom.f₁ := rfl

@[simp] theorem parityShift_map_f₁ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    ((parityShift (S := S) (w := w)).map f).hom.f₁ = f.hom.f₀ := rfl

/-- The elementary contractible factorization on a finitely generated projective module. -/
@[expose] def disk (P : FGModuleCat.{u} S) [Module.Projective S P] :
    MatrixFactorization S w :=
  ofCurvedDuplex (CurvedDuplex.disk w P)
    (by simpa only [CurvedDuplex.disk_X₀] using (inferInstance : Module.Projective S P))
    (by simpa only [CurvedDuplex.disk_X₁] using (inferInstance : Module.Projective S P))

@[simp] theorem disk_obj (P : FGModuleCat.{u} S) [Module.Projective S P] :
    (disk (w := w) P).obj = CurvedDuplex.disk w P := rfl

/-- The rank-one matrix factorization `S --a--> S --b--> S` of `w = a b`.
Its components are finite free, with no regularity assumption on `S` or `w`. -/
@[expose] def rankOne (a b : S) (h : a * b = w) : MatrixFactorization S w :=
  let P : FGModuleCat.{u} S := FGModuleCat.of S S
  ofCurvedDuplex
    { X₀ := P
      X₁ := P
      d₀ := a • 𝟙 P
      d₁ := b • 𝟙 P
      d₀_comp_d₁ := by simp [← mul_smul, mul_comm, h]
      d₁_comp_d₀ := by simp [← mul_smul, h] }
    (by infer_instance) (by infer_instance)

@[simp] theorem rankOne_d₀ (a b : S) (h : a * b = w) :
    (rankOne a b h).obj.d₀ = a • 𝟙 (FGModuleCat.of S S) := rfl

@[simp] theorem rankOne_d₁ (a b : S) (h : a * b = w) :
    (rankOne a b h).obj.d₁ = b • 𝟙 (FGModuleCat.of S S) := rfl

@[simp] theorem rankOne_X₀ (a b : S) (h : a * b = w) :
    (rankOne a b h).obj.X₀ = FGModuleCat.of S S := rfl

@[simp] theorem rankOne_X₁ (a b : S) (h : a * b = w) :
    (rankOne a b h).obj.X₁ = FGModuleCat.of S S := rfl

/-- The polynomial factorization `S[X] --X^i--> S[X] --X^(n-i)--> S[X]`
of `X^n`. The indices are allowed to lie at either endpoint; the interesting stable
factorizations have `0 < i < n`. -/
@[expose] noncomputable def power (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    MatrixFactorization (Polynomial S) (Polynomial.X ^ n) :=
  rankOne (Polynomial.X ^ i) (Polynomial.X ^ (n - i)) (by
    rw [← pow_add, Nat.add_sub_of_le hi])

@[simp] theorem power_d₀ (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    (power S n i hi).obj.d₀ =
      (Polynomial.X ^ i : Polynomial S) • 𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₀ ..

@[simp] theorem power_d₁ (S : Type u) [CommRing S] (n i : ℕ) (hi : i ≤ n) :
    (power S n i hi).obj.d₁ =
      (Polynomial.X ^ (n - i) : Polynomial S) •
        𝟙 (FGModuleCat.of (Polynomial S) (Polynomial S)) :=
  rankOne_d₁ ..

/-! ### Homotopies -/

/-- The ideal of morphisms of finite-projective matrix factorizations that are null-homotopic
as curved duplex maps. Since the subcategory is full, these are exactly the boundaries of
odd maps between the underlying finite projective components. -/
def nullHomotopic : MorphismIdeal (MatrixFactorization S w) :=
  (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).comap inclusion

/-- The homotopy category of finite-projective matrix factorizations. -/
abbrev HomotopyCategory : Type _ := (nullHomotopic (S := S) (w := w)).Quotient

/-- A closed even map is null-homotopic precisely when it is the boundary of an odd map. -/
@[simp] theorem mem_nullHomotopic_iff {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    f ∈ (nullHomotopic (S := S) (w := w)).hom X Y ↔
      ∃ h₀ : X.obj.X₀ ⟶ Y.obj.X₁, ∃ h₁ : X.obj.X₁ ⟶ Y.obj.X₀,
        CurvedDuplex.nullHomotopicMap h₀ h₁ = f.hom := by
  simp [nullHomotopic]

/-- Two morphisms of finite-projective matrix factorizations have the same image in the
homotopy category exactly when their difference is the boundary of an odd map. -/
theorem quotientFunctor_map_eq_iff {X Y : MatrixFactorization S w} (f g : X ⟶ Y) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor.map f =
      (nullHomotopic (S := S) (w := w)).quotientFunctor.map g ↔
        ∃ h₀ : X.obj.X₀ ⟶ Y.obj.X₁, ∃ h₁ : X.obj.X₁ ⟶ Y.obj.X₀,
          CurvedDuplex.nullHomotopicMap h₀ h₁ = (f - g).hom := by
  rw [MorphismIdeal.quotientFunctor_map_eq_iff, mem_nullHomotopic_iff]

end MatrixFactorization

end TauCeti
