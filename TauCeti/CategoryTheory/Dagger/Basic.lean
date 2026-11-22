/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Tactic.Module

/-!
# Dagger categories

A dagger is chosen identity-on-objects, contravariant involutive data on a native category.
Additive and conjugate-linear compatibility are separate properties of this data; in particular,
none of these interfaces imposes norm, completeness, or positivity assumptions.

Unitary arrows have their dagger as a two-sided inverse. They compose, and define native
categorical isomorphisms. Isometries `v`, with `v ≫ dagger v = 𝟙`, that have the same
range projection `dagger v ≫ v` differ by a unique unitary. Complex-linear dagger categories
satisfy the four-term polarization identities. Endomorphisms inherit the usual algebraic star
structures, with Mathlib's operator-order multiplication on `CategoryTheory.End`, and induced and
full subcategories inherit the dagger and its additive and scalar compatibilities.
-/

public section

open CategoryTheory

universe w v u

namespace TauCeti

/-- An identity-on-objects contravariant involution on a category. -/
class DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The dagger reverses the direction of an arrow. -/
  dagger : {X Y : C} → (X ⟶ Y) → (Y ⟶ X)
  /-- The dagger fixes identity arrows. -/
  dagger_id : ∀ X : C, dagger (𝟙 X) = 𝟙 X
  /-- The dagger reverses composition. -/
  dagger_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    dagger (f ≫ g) = dagger g ≫ dagger f
  /-- Applying the dagger twice recovers the original arrow. -/
  dagger_dagger : ∀ {X Y : C} (f : X ⟶ Y), dagger (dagger f) = f

export DaggerCategory (dagger dagger_id dagger_comp dagger_dagger)

attribute [simp] dagger_id dagger_comp dagger_dagger
attribute [grind =] dagger_id dagger_dagger
attribute [grind _=_] dagger_comp

namespace DaggerCategory

/-- Postfix notation for the chosen dagger. -/
scoped postfix:max "†" => TauCeti.DaggerCategory.dagger

end DaggerCategory

variable {C : Type u} [Category.{v} C] [DaggerCategory C]
variable {W X Y Z : C}

/-- Taking daggers is a bijection between opposite Hom spaces. -/
def daggerEquiv (X Y : C) : (X ⟶ Y) ≃ (Y ⟶ X) where
  toFun := dagger
  invFun := dagger
  left_inv := dagger_dagger
  right_inv := dagger_dagger

/-- Evaluation of the dagger bijection. -/
@[simp] theorem daggerEquiv_apply (f : X ⟶ Y) : daggerEquiv X Y f = dagger f := (rfl)

/-- The inverse dagger bijection also takes daggers. -/
theorem daggerEquiv_symm_apply (f : Y ⟶ X) :
    (daggerEquiv X Y).symm f = dagger f := (rfl)

/-- The inverse dagger bijection reverses its endpoints. -/
@[simp] theorem daggerEquiv_symm : (daggerEquiv X Y).symm = daggerEquiv Y X := (rfl)

/-- Taking the dagger reverses an equality arrow. -/
@[simp, grind =] theorem dagger_eqToHom (h : X = Y) :
    dagger (eqToHom h) = eqToHom h.symm := by
  cases h
  simp

/-- Taking daggers detects equality. -/
@[simp] theorem dagger_inj {f g : X ⟶ Y} : dagger f = dagger g ↔ f = g :=
  (daggerEquiv X Y).injective.eq_iff

/-- Taking the dagger preserves invertibility. -/
instance isIso_dagger (f : X ⟶ Y) [IsIso f] : IsIso (dagger f) where
  out := ⟨dagger (inv f), by
    rw [← dagger_comp, IsIso.inv_hom_id, dagger_id], by
    rw [← dagger_comp, IsIso.hom_inv_id, dagger_id]⟩

/-- Taking the dagger preserves and reflects invertibility. -/
@[simp] theorem isIso_dagger_iff (f : X ⟶ Y) : IsIso (dagger f) ↔ IsIso f := by
  constructor
  · intro h
    have := h
    simpa only [dagger_dagger] using (isIso_dagger (dagger f))
  · intro h
    have := h
    infer_instance

/-- Taking the dagger commutes with the inverse of an invertible arrow. -/
@[simp] theorem dagger_inv (f : X ⟶ Y) [IsIso f] :
    dagger (inv f) = inv (dagger f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← dagger_comp, IsIso.inv_hom_id, dagger_id]

/-- Additive compatibility of the chosen dagger on a preadditive category. -/
class DaggerPreadditive (C : Type u) [Category.{v} C] [DaggerCategory C]
    [Preadditive C] : Prop where
  /-- Taking daggers commutes with addition. -/
  dagger_add : ∀ {X Y : C} (f g : X ⟶ Y), dagger (f + g) = dagger f + dagger g

export DaggerPreadditive (dagger_add)
attribute [simp, grind =] dagger_add

section Preadditive

variable [Preadditive C] [DaggerPreadditive C]

/-- The dagger as an additive equivalence of Hom groups. -/
def daggerAddEquiv (X Y : C) : (X ⟶ Y) ≃+ (Y ⟶ X) where
  toEquiv := daggerEquiv X Y
  map_add' := dagger_add

/-- Evaluation of the additive dagger equivalence. -/
@[simp] theorem daggerAddEquiv_apply (f : X ⟶ Y) :
    daggerAddEquiv X Y f = dagger f := (rfl)

/-- The inverse additive dagger equivalence reverses its endpoints. -/
@[simp] theorem daggerAddEquiv_symm : (daggerAddEquiv X Y).symm = daggerAddEquiv Y X := (rfl)

/-- Forgetting additivity recovers the dagger bijection. -/
@[simp] theorem daggerAddEquiv_toEquiv :
    (daggerAddEquiv X Y : (X ⟶ Y) ≃ (Y ⟶ X)) = daggerEquiv X Y := (rfl)

/-- The dagger fixes the zero arrow. -/
@[simp, grind =] theorem dagger_zero : dagger (0 : X ⟶ Y) = 0 :=
  (daggerAddEquiv X Y).map_zero

/-- An arrow has zero dagger precisely when it is zero. -/
@[simp] theorem dagger_eq_zero (f : X ⟶ Y) : dagger f = 0 ↔ f = 0 :=
  (daggerAddEquiv X Y).map_eq_zero_iff

/-- The dagger commutes with negation. -/
@[simp, grind =] theorem dagger_neg (f : X ⟶ Y) : dagger (-f) = -dagger f :=
  (daggerAddEquiv X Y).map_neg f

/-- The dagger commutes with subtraction. -/
@[simp, grind =] theorem dagger_sub (f g : X ⟶ Y) : dagger (f - g) = dagger f - dagger g :=
  (daggerAddEquiv X Y).map_sub f g

/-- Taking daggers commutes with natural scalar multiplication. -/
@[simp, grind =] theorem dagger_nsmul (n : ℕ) (f : X ⟶ Y) :
    dagger (n • f) = n • dagger f :=
  map_nsmul (daggerAddEquiv X Y) n f

/-- Taking daggers commutes with integer scalar multiplication. -/
@[simp, grind =] theorem dagger_zsmul (n : ℤ) (f : X ⟶ Y) :
    dagger (n • f) = n • dagger f :=
  map_zsmul (daggerAddEquiv X Y) n f

/-- Taking daggers commutes with finite sums of arrows. -/
@[simp] theorem dagger_sum {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    dagger (∑ i ∈ s, f i) = ∑ i ∈ s, dagger (f i) :=
  map_sum (daggerAddEquiv X Y) f s

end Preadditive

/-- Conjugate-scalar compatibility for a dagger on a native linear category.
The scalar star operation is arbitrary; complex conjugation is its standard specialization. -/
class DaggerLinear (R : Type w) [Semiring R] [Star R]
    (C : Type u) [Category.{v} C] [DaggerCategory C] [Preadditive C]
    [Linear R C] : Prop where
  /-- Taking daggers conjugates the scalar. -/
  dagger_smul : ∀ {X Y : C} (r : R) (f : X ⟶ Y),
    dagger (r • f) = star r • dagger f

export DaggerLinear (dagger_smul)
attribute [simp, grind =] dagger_smul

section Semilinear

variable (R : Type w) [CommSemiring R] [StarRing R] [Preadditive C] [Linear R C]
  [DaggerPreadditive C] [DaggerLinear R C]

/-- The dagger as a conjugate-linear equivalence between opposite Hom modules. -/
def daggerLinearEquiv (A B : C) : (A ⟶ B) ≃ₛₗ[starRingEnd R] (B ⟶ A) where
  __ := daggerAddEquiv A B
  map_smul' := dagger_smul

/-- Evaluation of the conjugate-linear dagger equivalence. -/
@[simp] theorem daggerLinearEquiv_apply (f : X ⟶ Y) :
    daggerLinearEquiv R X Y f = dagger f := (rfl)

/-- The inverse conjugate-linear dagger equivalence reverses its endpoints. -/
@[simp] theorem daggerLinearEquiv_symm :
    (daggerLinearEquiv R X Y).symm = daggerLinearEquiv R Y X := (rfl)

/-- Forgetting scalar linearity recovers the additive dagger equivalence. -/
@[simp] theorem daggerLinearEquiv_toAddEquiv :
    (daggerLinearEquiv R X Y).toAddEquiv = daggerAddEquiv X Y := (rfl)

end Semilinear

section Polarization

variable [Preadditive C] [Linear ℂ C] [DaggerPreadditive C] [DaggerLinear ℂ C]

/-- Scaled complex polarization identity for `f ≫ dagger g` in a complex-linear dagger category. -/
theorem four_smul_comp_dagger (f g : X ⟶ Y) :
    (4 : ℂ) • (f ≫ dagger g) =
      (f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
          (f - Complex.I • g) ≫ dagger (f - Complex.I • g)) := by
  simp only [dagger_add, dagger_sub, dagger_smul, Complex.star_def, Complex.conj_I,
    Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Linear.smul_comp, Linear.comp_smul, neg_smul, Preadditive.comp_neg,
    smul_sub, smul_add, smul_neg, smul_smul, Complex.I_mul_I, one_smul]
  module

/-- Complex polarization expresses `f ≫ dagger g` as a linear combination of four positive-form
endomorphisms `(f + c • g) ≫ dagger (f + c • g)`. -/
theorem comp_dagger_eq_polarization (f g : X ⟶ Y) :
    f ≫ dagger g =
      (4 : ℂ)⁻¹ • ((f + g) ≫ dagger (f + g) - (f - g) ≫ dagger (f - g) +
        Complex.I • ((f + Complex.I • g) ≫ dagger (f + Complex.I • g) -
          (f - Complex.I • g) ≫ dagger (f - Complex.I • g))) := by
  rw [← four_smul_comp_dagger, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/-- Scaled complex polarization identity for `dagger f ≫ g` in a complex-linear dagger category. -/
theorem four_smul_dagger_comp (f g : X ⟶ Y) :
    (4 : ℂ) • (dagger f ≫ g) =
      dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g) -
          dagger (f - Complex.I • g) ≫ (f - Complex.I • g)) := by
  have h := four_smul_comp_dagger (dagger f) (dagger g)
  have hplus : dagger f + Complex.I • dagger g = dagger (f - Complex.I • g) := by
    simp [dagger_sub, dagger_smul, Complex.star_def]
  have hminus : dagger f - Complex.I • dagger g = dagger (f + Complex.I • g) := by
    simp [dagger_add, dagger_smul, Complex.star_def, sub_eq_add_neg]
  rw [← dagger_add, ← dagger_sub, hplus, hminus] at h
  simp only [dagger_dagger] at h
  rw [h, sub_eq_add_neg (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g)), ← smul_neg, neg_sub]

/-- Complex polarization expresses `dagger f ≫ g` as a linear combination of four endomorphisms
`dagger (f + c • g) ≫ (f + c • g)`. -/
theorem dagger_comp_eq_polarization (f g : X ⟶ Y) :
    dagger f ≫ g =
      (4 : ℂ)⁻¹ • (dagger (f + g) ≫ (f + g) - dagger (f - g) ≫ (f - g) -
        Complex.I • (dagger (f + Complex.I • g) ≫ (f + Complex.I • g) -
          dagger (f - Complex.I • g) ≫ (f - Complex.I • g))) := by
  rw [← four_smul_dagger_comp, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

end Polarization

/-- An arrow is unitary when its dagger is its two-sided inverse. -/
def IsUnitary (f : X ⟶ Y) : Prop :=
  f ≫ dagger f = 𝟙 X ∧ dagger f ≫ f = 𝟙 Y

/-- The two inverse equations characterize a unitary arrow. -/
theorem isUnitary_iff (f : X ⟶ Y) :
    IsUnitary f ↔ f ≫ dagger f = 𝟙 X ∧ dagger f ≫ f = 𝟙 Y := Iff.rfl

namespace IsUnitary

/-- A unitary arrow composed with its dagger is the identity. -/
@[reassoc (attr := simp), grind =] theorem hom_dagger_id {f : X ⟶ Y} (hf : IsUnitary f) :
    f ≫ dagger f = 𝟙 X := hf.1

/-- The dagger of a unitary arrow composed with that arrow is the identity. -/
@[reassoc (attr := simp), grind =] theorem dagger_hom_id {f : X ⟶ Y} (hf : IsUnitary f) :
    dagger f ≫ f = 𝟙 Y := hf.2

/-- Identity arrows are unitary. -/
@[simp] theorem id (X : C) : IsUnitary (𝟙 X) := by
  simp [isUnitary_iff]

/-- The dagger of a unitary arrow is unitary. -/
theorem dagger {f : X ⟶ Y} (hf : IsUnitary f) : IsUnitary (TauCeti.dagger f) := by
  simpa only [isUnitary_iff, dagger_dagger] using And.intro hf.2 hf.1

/-- Composites of unitary arrows are unitary. -/
theorem comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ≫ g) := by
  constructor <;> simp [Category.assoc, hg.hom_dagger_id_assoc, hf.dagger_hom_id_assoc,
    hf.hom_dagger_id, hg.dagger_hom_id]

/-- A unitary arrow determines an isomorphism whose inverse is its dagger. -/
def toIso {f : X ⟶ Y} (hf : IsUnitary f) : X ≅ Y where
  hom := f
  inv := TauCeti.dagger f
  hom_inv_id := hf.1
  inv_hom_id := hf.2

/-- The isomorphism of a unitary arrow has the original arrow as its forward map. -/
@[simp, grind =] theorem toIso_hom {f : X ⟶ Y} (hf : IsUnitary f) : hf.toIso.hom = f := (rfl)

/-- The isomorphism of a unitary arrow has the dagger as its inverse. -/
@[simp, grind =] theorem toIso_inv {f : X ⟶ Y} (hf : IsUnitary f) :
    hf.toIso.inv = TauCeti.dagger f := (rfl)

/-- A unitary arrow is invertible. -/
theorem isIso {f : X ⟶ Y} (hf : IsUnitary f) : IsIso f := hf.toIso.isIso_hom

end IsUnitary

/-- Equality arrows are unitary. -/
@[simp] theorem isUnitary_eqToHom (h : X = Y) : IsUnitary (eqToHom h) := by
  cases h
  simp

/-- Taking the dagger preserves and reflects unitarity. -/
@[simp] theorem isUnitary_dagger_iff (f : X ⟶ Y) : IsUnitary (dagger f) ↔ IsUnitary f :=
  ⟨fun h => by simpa using h.dagger, IsUnitary.dagger⟩

/-- Taking inverses preserves and reflects unitarity. -/
@[simp] theorem isUnitary_inv_iff (f : X ⟶ Y) [IsIso f] :
    IsUnitary (inv f) ↔ IsUnitary f := by
  constructor
  · intro h
    have hd : dagger (inv f) = f := by
      simpa only [IsIso.inv_inv] using IsIso.eq_inv_of_hom_inv_id h.hom_dagger_id
    simpa only [hd] using h.dagger
  · intro h
    have hd : dagger f = inv f := IsIso.eq_inv_of_hom_inv_id h.hom_dagger_id
    simpa only [hd] using h.dagger

/-- An arrow `u` through which an isometry `v` factors as `u ≫ w = v`, for an isometry `w`, is
`v ≫ dagger w`. Here `w` is an isometry when `w ≫ dagger w = 𝟙`, that is `w† w = 1`. -/
theorem eq_comp_dagger_of_comp_eq {u : Y ⟶ Z} {v : Y ⟶ X} {w : Z ⟶ X}
    (hw : w ≫ dagger w = 𝟙 Z) (h : u ≫ w = v) : u = v ≫ dagger w := by
  rw [← h, Category.assoc, hw, Category.comp_id]

/-- Isometries `v : Y ⟶ X` and `w : Z ⟶ X` with the same range projection
`dagger v ≫ v = dagger w ≫ w` differ by the unitary `v ≫ dagger w`; by
`TauCeti.eq_comp_dagger_of_comp_eq` it is the only arrow `u` with `u ≫ w = v`. -/
theorem isUnitary_comp_dagger_of_dagger_comp_eq {v : Y ⟶ X} {w : Z ⟶ X}
    (hv : v ≫ dagger v = 𝟙 Y) (hw : w ≫ dagger w = 𝟙 Z) (h : dagger v ≫ v = dagger w ≫ w) :
    IsUnitary (v ≫ dagger w) := by
  constructor
  · rw [dagger_comp, dagger_dagger, Category.assoc, reassoc_of% h.symm, hv, Category.comp_id, hv]
  · rw [dagger_comp, dagger_dagger, Category.assoc, reassoc_of% h, hw, Category.comp_id, hw]

/-- Isometries `v : Y ⟶ X` and `w : Z ⟶ X` with the same range projection satisfy
`(v ≫ dagger w) ≫ w = v`. -/
@[reassoc] theorem comp_dagger_comp_of_dagger_comp_eq {v : Y ⟶ X} {w : Z ⟶ X}
    (hv : v ≫ dagger v = 𝟙 Y) (h : dagger v ≫ v = dagger w ≫ w) :
    (v ≫ dagger w) ≫ w = v := by
  rw [Category.assoc, ← h, reassoc_of% hv]

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}

/-- An isomorphism is unitary precisely when its inverse is its dagger. -/
theorem isUnitary_hom_iff (e : X ≅ Y) : IsUnitary e.hom ↔ dagger e.hom = e.inv := by
  constructor
  · intro h
    exact (cancel_epi e.hom).mp (h.1.trans e.hom_inv_id.symm)
  · intro h
    simp [isUnitary_iff, h]

/-- The inverse of a unitary isomorphism is its dagger. -/
theorem dagger_hom_eq_inv_of_isUnitary (e : X ≅ Y) (h : IsUnitary e.hom) :
    dagger e.hom = e.inv :=
  e.isUnitary_hom_iff.mp h

end CategoryTheory.Iso

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {X : C}

/-- The dagger is the star operation on endomorphisms. -/
instance daggerStar : Star (End X) where
  star f := .of (dagger f.asHom)

/-- The endomorphism star acts by the dagger on its underlying arrow. -/
@[simp, grind =] theorem star_asHom (f : End X) : (star f).asHom = dagger f.asHom := (rfl)

/-- Bundling the dagger of an endomorphism arrow gives the star of the bundled endomorphism. -/
@[simp, grind =] theorem of_dagger (f : X ⟶ X) : End.of (dagger f) = star (End.of f) := (rfl)

/-- The endomorphism dagger is involutive. -/
instance daggerInvolutiveStar : InvolutiveStar (End X) where
  star_involutive f := by ext; simp

/-- Operator-order multiplication makes endomorphisms a star monoid. -/
instance daggerStarMul : StarMul (End X) where
  star_mul f g := by ext; simp

/-- In an additive dagger category the endomorphism ring is a star ring. -/
instance [Preadditive C] [DaggerPreadditive C] : StarRing (End X) where
  star_add f g := by ext; simp

/-- The scalar action on endomorphisms is compatible with the dagger involution. -/
instance {R : Type w} [Semiring R] [Star R] [Preadditive C] [Linear R C]
    [DaggerLinear R C] : StarModule R (End X) where
  star_smul r f := by ext; simp

end CategoryTheory.End

namespace CategoryTheory.InducedCategory

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {D : Type w}

/-- A category induced along a map on objects inherits the ambient dagger. -/
instance instDaggerCategory (F : D → C) : DaggerCategory (InducedCategory C F) where
  dagger f := homMk (dagger f.hom)
  dagger_id _ := by ext; simp
  dagger_comp _ _ := by ext; simp
  dagger_dagger _ := by ext; simp

/-- The underlying arrow of a dagger in an induced category is the dagger of the underlying
arrow. -/
@[simp, grind =] theorem dagger_hom {F : D → C} {X Y : InducedCategory C F} (f : X ⟶ Y) :
    (dagger f).hom = dagger f.hom := (rfl)

/-- Bundling an arrow in an induced category commutes with taking daggers. -/
@[simp, grind =] theorem homMk_dagger {F : D → C} {X Y : InducedCategory C F} (f : F X ⟶ F Y) :
    homMk (F := F) (dagger f) = dagger (homMk (F := F) f) := (rfl)

/-- An induced category inherits additive compatibility of the ambient dagger. -/
instance instDaggerPreadditive (F : D → C) [Preadditive C] [DaggerPreadditive C] :
    DaggerPreadditive (InducedCategory C F) where
  dagger_add f g := hom_ext (dagger_add f.hom g.hom)

/-- An induced category inherits conjugate-linear compatibility of the ambient dagger. -/
instance instDaggerLinear {R : Type*} [Semiring R] [Star R] (F : D → C)
    [Preadditive C] [Linear R C] [DaggerLinear R C] :
    DaggerLinear R (InducedCategory C F) where
  dagger_smul r f := hom_ext (dagger_smul r f.hom)

end CategoryTheory.InducedCategory

namespace CategoryTheory.ObjectProperty

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C]

/-- A full subcategory inherits the ambient dagger. -/
instance instDaggerCategoryFullSubcategory (P : ObjectProperty C) :
    DaggerCategory P.FullSubcategory :=
  InducedCategory.instDaggerCategory FullSubcategory.obj

/-- The underlying arrow of a dagger in a full subcategory is the dagger of the underlying
arrow. -/
@[simp, grind =] theorem dagger_hom {P : ObjectProperty C} {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (dagger f).hom = dagger f.hom := (rfl)

/-- Bundling an arrow in a full subcategory commutes with taking daggers. -/
@[simp, grind =] theorem homMk_dagger {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (f : X.obj ⟶ Y.obj) :
    homMk (dagger f) = dagger (homMk f : X ⟶ Y) := (rfl)

/-- A full subcategory inherits additive compatibility of the ambient dagger. -/
instance instDaggerPreadditiveFullSubcategory (P : ObjectProperty C)
    [Preadditive C] [DaggerPreadditive C] :
    DaggerPreadditive P.FullSubcategory :=
  InducedCategory.instDaggerPreadditive FullSubcategory.obj

/-- A full subcategory inherits conjugate-linear compatibility of the ambient dagger. -/
instance instDaggerLinearFullSubcategory {R : Type w} [Semiring R] [Star R] (P : ObjectProperty C)
    [Preadditive C] [Linear R C] [DaggerLinear R C] :
    DaggerLinear R P.FullSubcategory :=
  InducedCategory.instDaggerLinear FullSubcategory.obj

end CategoryTheory.ObjectProperty
