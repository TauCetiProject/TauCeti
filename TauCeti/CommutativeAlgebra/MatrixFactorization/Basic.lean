/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import Mathlib.Algebra.Category.FGModuleCat.Basic

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

The matrix-factorization equations follow D. Eisenbud, *Homological algebra on a complete
intersection, with an application to group representations*, Trans. Amer. Math. Soc. **260**
(1980), Section 5, where the components are finite free. The finite-projective formulation
follows D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg
models*, Proc. Steklov Inst. Math. **246** (2004), Sections 1.2 and 3. The ambient
curved-duplex convention follows
`TauCeti.Algebra.Homology.Curved.Duplex`.
-/

public section

universe u

namespace TauCeti

open CategoryTheory Limits

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
    MatrixFactorization S w ⥤ MatrixFactorization S w :=
  ObjectProperty.lift _ (inclusion ⋙ CurvedDuplex.parityShift (FGModuleCat.{u} S) w)
    fun X ↦ ⟨X.property.2, X.property.1⟩

/-- The parity shift commutes with the inclusion into curved duplexes. -/
theorem parityShift_comp_inclusion :
    parityShift (S := S) (w := w) ⋙ inclusion =
      inclusion ⋙ CurvedDuplex.parityShift (FGModuleCat.{u} S) w := rfl

@[simp] theorem parityShift_obj_X₀ (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.X₀ = X.obj.X₁ := rfl

@[simp] theorem parityShift_obj_X₁ (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.X₁ = X.obj.X₀ := rfl

@[simp] theorem parityShift_obj_d₀ (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.d₀ = -X.obj.d₁ := rfl

@[simp] theorem parityShift_obj_d₁ (X : MatrixFactorization S w) :
    ((parityShift (S := S) (w := w)).obj X).obj.d₁ = -X.obj.d₀ := rfl

@[simp] theorem parityShift_map_f₀ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    ((parityShift (S := S) (w := w)).map f).hom.f₀ = f.hom.f₁ := rfl

@[simp] theorem parityShift_map_f₁ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    ((parityShift (S := S) (w := w)).map f).hom.f₁ = f.hom.f₀ := rfl

instance : (parityShift (S := S) (w := w)).Additive where

/-- Applying the parity shift twice gives the original matrix factorization. -/
def parityShiftCompParityShiftIso :
    parityShift (S := S) (w := w) ⋙ parityShift (S := S) (w := w) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk (P := MatrixFactorization.isProjective S w)
      ((CurvedDuplex.parityShiftCompParityShiftIso (FGModuleCat.{u} S) w).app X.obj))
    (fun _ ↦ by ext <;> rfl)

@[simp] theorem parityShiftCompParityShiftIso_hom_app_hom (X : MatrixFactorization S w) :
    (parityShiftCompParityShiftIso.hom.app X).hom =
      (CurvedDuplex.parityShiftCompParityShiftIso (FGModuleCat.{u} S) w).hom.app X.obj := by
  simp [parityShiftCompParityShiftIso]

@[simp] theorem parityShiftCompParityShiftIso_inv_app_hom (X : MatrixFactorization S w) :
    (parityShiftCompParityShiftIso.inv.app X).hom =
      (CurvedDuplex.parityShiftCompParityShiftIso (FGModuleCat.{u} S) w).inv.app X.obj := by
  simp [parityShiftCompParityShiftIso]

/-- The parity shift is a self-equivalence of finite-projective matrix factorizations. -/
@[expose, simps]
def parityShiftEquivalence : MatrixFactorization S w ≌ MatrixFactorization S w where
  functor := parityShift (S := S) (w := w)
  inverse := parityShift (S := S) (w := w)
  unitIso := parityShiftCompParityShiftIso.symm
  counitIso := parityShiftCompParityShiftIso
  functor_unitIso_comp _ := by ext <;> rfl

instance : (parityShiftEquivalence (S := S) (w := w)).functor.Additive :=
  inferInstanceAs (parityShift (S := S) (w := w)).Additive

/-- The elementary contractible factorization on a finitely generated projective module. -/
@[expose] def disk (P : FGModuleCat.{u} S) [Module.Projective S P] :
    MatrixFactorization S w :=
  ofCurvedDuplex (CurvedDuplex.disk w P)
    (by simpa only [CurvedDuplex.disk_X₀] using (inferInstance : Module.Projective S P))
    (by simpa only [CurvedDuplex.disk_X₁] using (inferInstance : Module.Projective S P))

@[simp] theorem disk_obj (P : FGModuleCat.{u} S) [Module.Projective S P] :
    (disk (w := w) P).obj = CurvedDuplex.disk w P := rfl

/-- A map from an elementary disk is determined by its even component. -/
def diskHomEquiv (P : FGModuleCat.{u} S) [Module.Projective S P]
    (X : MatrixFactorization S w) :
    (disk (w := w) P ⟶ X) ≃ₗ[S] (P ⟶ X.obj.X₀) :=
  InducedCategory.homLinearEquiv.trans (CurvedDuplex.diskHomEquiv P X.obj)

-- The induced hom equivalence removes the full-subcategory wrapper definitionally; after
-- this reduction, the application formulas are those of `CurvedDuplex.diskHomEquiv`.
@[simp] theorem diskHomEquiv_apply (P : FGModuleCat.{u} S) [Module.Projective S P]
    (X : MatrixFactorization S w) (f : disk (w := w) P ⟶ X) :
    diskHomEquiv P X f = f.hom.f₀ := by
  change CurvedDuplex.diskHomEquiv P X.obj f.hom = f.hom.f₀
  exact CurvedDuplex.diskHomEquiv_apply P X.obj f.hom

@[simp] theorem diskHomEquiv_symm_apply_hom_f₀ (P : FGModuleCat.{u} S)
    [Module.Projective S P] (X : MatrixFactorization S w) (g : P ⟶ X.obj.X₀) :
    ((diskHomEquiv P X).symm g).hom.f₀ = g := by
  change ((CurvedDuplex.diskHomEquiv P X.obj).symm g).f₀ = g
  exact CurvedDuplex.diskHomEquiv_symm_apply_f₀ P X.obj g

@[simp] theorem diskHomEquiv_symm_apply_hom_f₁ (P : FGModuleCat.{u} S)
    [Module.Projective S P] (X : MatrixFactorization S w) (g : P ⟶ X.obj.X₀) :
    ((diskHomEquiv P X).symm g).hom.f₁ = g ≫ X.obj.d₀ := by
  change ((CurvedDuplex.diskHomEquiv P X.obj).symm g).f₁ = g ≫ X.obj.d₀
  exact CurvedDuplex.diskHomEquiv_symm_apply_f₁ P X.obj g

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

/-! ### Homotopies -/

/-- The ideal of morphisms of finite-projective matrix factorizations that are null-homotopic
as curved duplex maps. Since the subcategory is full, these are exactly the boundaries of
odd maps between the underlying finite projective components. -/
def nullHomotopic : MorphismIdeal (MatrixFactorization S w) :=
  (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).comap inclusion

/-- Null-homotopic maps are exactly the maps whose parity shifts are null-homotopic. -/
theorem comap_parityShift_nullHomotopic :
    (nullHomotopic (S := S) (w := w)).comap (parityShift (S := S) (w := w)) =
      nullHomotopic (S := S) (w := w) := by
  rw [nullHomotopic, ← MorphismIdeal.comap_comp,
    MorphismIdeal.comap_eq_of_iso _ (eqToIso parityShift_comp_inclusion),
    MorphismIdeal.comap_comp, CurvedDuplex.comap_parityShift_nullHomotopic]

/-- The homotopy category of finite-projective matrix factorizations. -/
abbrev HomotopyCategory : Type _ := (nullHomotopic (S := S) (w := w)).Quotient

/-- The parity shift induces an equivalence of matrix-factorization homotopy categories. -/
noncomputable def HomotopyCategory.parityShiftEquivalence :
    HomotopyCategory (S := S) (w := w) ≌ HomotopyCategory (S := S) (w := w) :=
  MorphismIdeal.mapEquivalence
    (TauCeti.MatrixFactorization.parityShiftEquivalence (S := S) (w := w)) _ _
    comap_parityShift_nullHomotopic.symm

/-- Parity shift commutes with the quotient functor. -/
theorem HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
      (HomotopyCategory.parityShiftEquivalence (S := S) (w := w)).functor =
    parityShift (S := S) (w := w) ⋙
      (nullHomotopic (S := S) (w := w)).quotientFunctor := by
  rw [HomotopyCategory.parityShiftEquivalence]
  rw [MorphismIdeal.mapEquivalence_functor
    (e := TauCeti.MatrixFactorization.parityShiftEquivalence (S := S) (w := w))
    (I := nullHomotopic (S := S) (w := w))
    (J := nullHomotopic (S := S) (w := w)) comap_parityShift_nullHomotopic.symm]
  exact MorphismIdeal.quotientFunctor_comp_map ..

/-- A closed even map is null-homotopic precisely when it is the boundary of an odd map. -/
@[simp] theorem mem_nullHomotopic_iff {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    f ∈ (nullHomotopic (S := S) (w := w)).hom X Y ↔
      ∃ h₀ : X.obj.X₀ ⟶ Y.obj.X₁, ∃ h₁ : X.obj.X₁ ⟶ Y.obj.X₀,
        CurvedDuplex.nullHomotopicMap h₀ h₁ = f.hom := by
  simp [nullHomotopic]

/-- The identity of an elementary disk is null-homotopic. -/
theorem id_disk_mem_nullHomotopic (P : FGModuleCat.{u} S) [Module.Projective S P] :
    𝟙 (disk (w := w) P) ∈ (nullHomotopic (S := S) (w := w)).hom _ _ := by
  rw [mem_nullHomotopic_iff, ObjectProperty.FullSubcategory.id_hom, disk_obj]
  exact ⟨0, 𝟙 P, CurvedDuplex.nullHomotopicMap_disk P⟩

/-- An elementary disk is zero in the homotopy category. -/
theorem isZero_quotientFunctor_obj_disk (P : FGModuleCat.{u} S) [Module.Projective S P] :
    IsZero ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj (disk (w := w) P)) := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff]
  exact id_disk_mem_nullHomotopic P

/-- Two morphisms of finite-projective matrix factorizations have the same image in the
homotopy category exactly when their difference is the boundary of an odd map. -/
theorem quotientFunctor_map_eq_quotientFunctor_map_iff
    {X Y : MatrixFactorization S w} (f g : X ⟶ Y) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor.map f =
      (nullHomotopic (S := S) (w := w)).quotientFunctor.map g ↔
        ∃ h₀ : X.obj.X₀ ⟶ Y.obj.X₁, ∃ h₁ : X.obj.X₁ ⟶ Y.obj.X₀,
          CurvedDuplex.nullHomotopicMap h₀ h₁ = (f - g).hom := by
  rw [MorphismIdeal.quotientFunctor_map_eq_iff, mem_nullHomotopic_iff]

end MatrixFactorization

end TauCeti
