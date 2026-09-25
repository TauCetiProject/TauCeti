/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# Curved duplexes and their homotopy category

Let `C` be an `R`-linear category and `w : R`. A **curved duplex** of curvature `w` in `C` is a
pair of objects with maps in both directions
```
X₀ --d₀--> X₁ --d₁--> X₀
```
whose two composites are both `w • 𝟙`. Since `w` acts through the linear structure, it commutes
with every morphism of `C`; this is the central, parity-graded case of a curved module, in which
the square of the differential is multiplication by the curvature. For `C = ModuleCat S` over a
commutative ring `S`, a curved duplex whose two components are finitely generated projective is a
matrix factorization of `w`. For `w = 0` the two equations say that both composites vanish: a
curved duplex of curvature zero is a genuine two-periodic complex. For `w ≠ 0` a curved duplex
has no homology in general, so homotopy is its primitive notion of equivalence.

This file sets up

* the category `CurvedDuplex C w` of curved duplexes and even closed morphisms (pairs of maps
  commuting with both differentials), which is preadditive and `R`-linear, with the two
  evaluation functors to `C`;
* the parity shift `CurvedDuplex.parityShift`, which swaps the two components and negates both
  differentials, and the natural isomorphism exhibiting it as an involution;
* the null-homotopic morphisms `d h + h d` for odd maps `h = (h₀, h₁)`, which form a two-sided
  ideal `CurvedDuplex.nullHomotopic` because source and target have the same curvature;
* the homotopy category `CurvedDuplex.HomotopyCategory C w`, the quotient by that ideal, which is
  preadditive and `R`-linear, together with the parity shift it inherits;
* the elementary disk `A --𝟙--> A --w•𝟙--> A` on an object `A`, whose morphisms to a duplex are
  the morphisms from `A` to its even component, and which is contractible and therefore zero in
  the homotopy category.

## Main definitions

* `TauCeti.CurvedDuplex C w`: curved duplexes of curvature `w` in the linear category `C`.
* `TauCeti.CurvedDuplex.parityShift`: the parity shift, and
  `TauCeti.CurvedDuplex.parityShiftEquivalence` the resulting self-equivalence.
* `TauCeti.CurvedDuplex.nullHomotopicMap`: the morphism `d h + h d` of an odd map `(h₀, h₁)`.
* `TauCeti.CurvedDuplex.nullHomotopic`: the ideal of null-homotopic morphisms.
* `TauCeti.CurvedDuplex.HomotopyCategory`: the homotopy category of curved duplexes.
* `TauCeti.CurvedDuplex.disk`: the elementary disk on an object.

## Main results

* `TauCeti.CurvedDuplex.quotientFunctor_map_eq_quotientFunctor_map_iff`: two morphisms become
  equal in the homotopy category exactly when their difference is `d h + h d` for an odd map `h`.
* `TauCeti.CurvedDuplex.diskHomEquiv`: morphisms out of the disk on `A` correspond to morphisms
  from `A` to the even component.
* `TauCeti.CurvedDuplex.isZero_quotientFunctor_obj_disk`: the disk is zero in the homotopy
  category.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), 35–64, Section 5.
* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3 (curved complexes and
  duplexes and their homotopy categories).
* The category structure follows Joël Riou's `CategoryTheory.ShortComplex` in
  `Mathlib.Algebra.Homology.ShortComplex.Basic`.
-/

public section

universe w' v u

namespace TauCeti

open CategoryTheory Category Limits Preadditive

-- The category structure, functors and constructors below are exposed, as for Mathlib's short
-- complexes: a morphism `X ⟶ Y` of curved duplexes must unfold to a `CurvedDuplex.Hom X Y`, and
-- they are used through their definitional component formulas. The null-homotopic morphisms,
-- their ideal and the disk correspondence below are used through their component and membership
-- lemmas instead, so their bodies stay hidden.
@[expose] public section

variable (C : Type u) [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]

/-- A **curved duplex** of curvature `w` in an `R`-linear category `C`: objects `X₀` and `X₁`
with maps `d₀ : X₀ ⟶ X₁` and `d₁ : X₁ ⟶ X₀` whose composites `d₀ ≫ d₁` and `d₁ ≫ d₀` are both
`w • 𝟙`. At `w = 0` this is a two-periodic complex. -/
structure CurvedDuplex (w : R) where
  /-- The even component. -/
  X₀ : C
  /-- The odd component. -/
  X₁ : C
  /-- The differential from the even to the odd component. -/
  d₀ : X₀ ⟶ X₁
  /-- The differential from the odd to the even component. -/
  d₁ : X₁ ⟶ X₀
  /-- The square of the differential on the even component is the curvature. -/
  d₀_comp_d₁ : d₀ ≫ d₁ = w • 𝟙 X₀
  /-- The square of the differential on the odd component is the curvature. -/
  d₁_comp_d₀ : d₁ ≫ d₀ = w • 𝟙 X₁

namespace CurvedDuplex

attribute [reassoc (attr := simp)] d₀_comp_d₁ d₁_comp_d₀

variable {C} {w : R}

/-- A morphism of curved duplexes: an even closed map, that is a pair of maps between the
components commuting with both differentials. -/
@[ext]
structure Hom (X Y : CurvedDuplex C w) where
  /-- The component on the even objects. -/
  f₀ : X.X₀ ⟶ Y.X₀
  /-- The component on the odd objects. -/
  f₁ : X.X₁ ⟶ Y.X₁
  /-- The morphism commutes with the even differentials. -/
  comm₀ : f₀ ≫ Y.d₀ = X.d₀ ≫ f₁ := by cat_disch
  /-- The morphism commutes with the odd differentials. -/
  comm₁ : f₁ ≫ Y.d₁ = X.d₁ ≫ f₀ := by cat_disch

attribute [reassoc] Hom.comm₀ Hom.comm₁
attribute [local simp] Hom.comm₀ Hom.comm₁ Hom.comm₀_assoc Hom.comm₁_assoc

/-- The identity morphism of a curved duplex. -/
@[simps]
def Hom.id (X : CurvedDuplex C w) : Hom X X where
  f₀ := 𝟙 _
  f₁ := 𝟙 _

/-- The composition of morphisms of curved duplexes. -/
@[simps]
def Hom.comp {X Y Z : CurvedDuplex C w} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f₀ := f.f₀ ≫ g.f₀
  f₁ := f.f₁ ≫ g.f₁

instance : Category (CurvedDuplex C w) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {X Y Z : CurvedDuplex C w}

-- Register extensionality for categorical morphisms `X ⟶ Y`; `Hom.ext` alone does not let
-- `ext` recognize that these morphisms are `CurvedDuplex.Hom` structures.
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h₀ : f.f₀ = g.f₀) (h₁ : f.f₁ = g.f₁) : f = g :=
  Hom.ext h₀ h₁

@[simp] theorem id_f₀ (X : CurvedDuplex C w) : Hom.f₀ (𝟙 X) = 𝟙 _ := rfl
@[simp] theorem id_f₁ (X : CurvedDuplex C w) : Hom.f₁ (𝟙 X) = 𝟙 _ := rfl
@[simp, reassoc] theorem comp_f₀ (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f₀ = f.f₀ ≫ g.f₀ := rfl
@[simp, reassoc] theorem comp_f₁ (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f₁ = f.f₁ ≫ g.f₁ := rfl

/-- A constructor for morphisms of curved duplexes when the commutativity conditions are not
obvious. -/
@[simps]
def homMk (f₀ : X.X₀ ⟶ Y.X₀) (f₁ : X.X₁ ⟶ Y.X₁) (comm₀ : f₀ ≫ Y.d₀ = X.d₀ ≫ f₁)
    (comm₁ : f₁ ≫ Y.d₁ = X.d₁ ≫ f₀) : X ⟶ Y :=
  ⟨f₀, f₁, comm₀, comm₁⟩

instance : Add (X ⟶ Y) where
  add f g := { f₀ := f.f₀ + g.f₀, f₁ := f.f₁ + g.f₁ }

instance : Sub (X ⟶ Y) where
  sub f g := { f₀ := f.f₀ - g.f₀, f₁ := f.f₁ - g.f₁ }

instance : Neg (X ⟶ Y) where
  neg f := { f₀ := -f.f₀, f₁ := -f.f₁ }

instance : Zero (X ⟶ Y) where
  zero := { f₀ := 0, f₁ := 0 }

@[simp] theorem add_f₀ (f g : X ⟶ Y) : (f + g).f₀ = f.f₀ + g.f₀ := rfl
@[simp] theorem add_f₁ (f g : X ⟶ Y) : (f + g).f₁ = f.f₁ + g.f₁ := rfl
@[simp] theorem sub_f₀ (f g : X ⟶ Y) : (f - g).f₀ = f.f₀ - g.f₀ := rfl
@[simp] theorem sub_f₁ (f g : X ⟶ Y) : (f - g).f₁ = f.f₁ - g.f₁ := rfl
@[simp] theorem neg_f₀ (f : X ⟶ Y) : (-f).f₀ = -f.f₀ := rfl
@[simp] theorem neg_f₁ (f : X ⟶ Y) : (-f).f₁ = -f.f₁ := rfl
@[simp] theorem zero_f₀ : (0 : X ⟶ Y).f₀ = 0 := rfl
@[simp] theorem zero_f₁ : (0 : X ⟶ Y).f₁ = 0 := rfl

instance : AddCommGroup (X ⟶ Y) where
  add_assoc _ _ _ := by ext <;> apply add_assoc
  add_zero _ := by ext <;> apply add_zero
  zero_add _ := by ext <;> apply zero_add
  neg_add_cancel _ := by ext <;> apply neg_add_cancel
  add_comm _ _ := by ext <;> apply add_comm
  sub_eq_add_neg _ _ := by ext <;> apply sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Preadditive (CurvedDuplex C w) where

instance : SMul R (X ⟶ Y) where
  smul a f := { f₀ := a • f.f₀, f₁ := a • f.f₁ }

@[simp] theorem smul_f₀ (a : R) (f : X ⟶ Y) : (a • f).f₀ = a • f.f₀ := rfl
@[simp] theorem smul_f₁ (a : R) (f : X ⟶ Y) : (a • f).f₁ = a • f.f₁ := rfl

attribute [local simp] mul_smul add_smul in
instance : Module R (X ⟶ Y) where
  zero_smul := by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch

instance : Linear R (CurvedDuplex C w) where

/-! ### Evaluation functors -/

variable (C w) in
/-- The functor sending a curved duplex to its even component. -/
@[simps]
def eval₀ : CurvedDuplex C w ⥤ C where
  obj X := X.X₀
  map f := f.f₀

variable (C w) in
/-- The functor sending a curved duplex to its odd component. -/
@[simps]
def eval₁ : CurvedDuplex C w ⥤ C where
  obj X := X.X₁
  map f := f.f₁

instance : (eval₀ C w).Additive where
instance : (eval₁ C w).Additive where
instance : (eval₀ C w).Linear R where
instance : (eval₁ C w).Linear R where

instance (f : X ⟶ Y) [IsIso f] : IsIso f.f₀ := (eval₀ C w).map_isIso f
instance (f : X ⟶ Y) [IsIso f] : IsIso f.f₁ := (eval₁ C w).map_isIso f

/-- A constructor for isomorphisms of curved duplexes from isomorphisms of their components
commuting with the differentials. -/
@[simps]
def isoMk (e₀ : X.X₀ ≅ Y.X₀) (e₁ : X.X₁ ≅ Y.X₁) (comm₀ : e₀.hom ≫ Y.d₀ = X.d₀ ≫ e₁.hom)
    (comm₁ : e₁.hom ≫ Y.d₁ = X.d₁ ≫ e₀.hom) : X ≅ Y where
  hom := homMk e₀.hom e₁.hom comm₀ comm₁
  inv := homMk e₀.inv e₁.inv (by rw [e₀.inv_comp_eq, reassoc_of% comm₀, e₁.hom_inv_id,
    comp_id]) (by rw [e₁.inv_comp_eq, reassoc_of% comm₁, e₀.hom_inv_id, comp_id])

/-- A morphism of curved duplexes is an isomorphism exactly when both of its components are. -/
theorem isIso_iff (f : X ⟶ Y) : IsIso f ↔ IsIso f.f₀ ∧ IsIso f.f₁ := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  exact (isoMk (asIso f.f₀) (asIso f.f₁) f.comm₀ f.comm₁).isIso_hom

/-! ### The parity shift -/

variable (C w) in
/-- The **parity shift** of curved duplexes: it swaps the even and odd components and negates
both differentials, `(X₁ --(-d₁)--> X₀ --(-d₀)--> X₁)`. -/
@[implicit_reducible, simps]
def parityShift : CurvedDuplex C w ⥤ CurvedDuplex C w where
  obj X :=
    { X₀ := X.X₁
      X₁ := X.X₀
      d₀ := -X.d₁
      d₁ := -X.d₀
      d₀_comp_d₁ := by simp
      d₁_comp_d₀ := by simp }
  map f :=
    { f₀ := f.f₁
      f₁ := f.f₀ }

instance : (parityShift C w).Additive where
instance : (parityShift C w).Linear R where

variable (C w) in
/-- Applying the parity shift twice gives back the original duplex: the components are the
same, and the differentials are negated twice. -/
@[simps!]
def parityShiftCompParityShiftIso : parityShift C w ⋙ parityShift C w ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X ↦ isoMk (Iso.refl _) (Iso.refl _) (by simp) (by simp))
    (fun _ ↦ by ext <;> simp)

variable (C w) in
/-- The parity shift is a self-equivalence of the category of curved duplexes. -/
@[implicit_reducible, simps]
def parityShiftEquivalence : CurvedDuplex C w ≌ CurvedDuplex C w where
  functor := parityShift C w
  inverse := parityShift C w
  unitIso := (parityShiftCompParityShiftIso C w).symm
  counitIso := parityShiftCompParityShiftIso C w
  functor_unitIso_comp _ := by ext <;> simp

instance : (parityShiftEquivalence C w).functor.Additive :=
  inferInstanceAs (parityShift C w).Additive

end CurvedDuplex

end

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]
  {w : R} {X Y Z : CurvedDuplex C w}

attribute [local simp] Hom.comm₀ Hom.comm₁ Hom.comm₀_assoc Hom.comm₁_assoc

/-! ### Null-homotopic morphisms -/

/-- The **null-homotopic morphism** `d h + h d` attached to an odd map `h = (h₀, h₁)` from `X` to
`Y`. It commutes with the differentials because `X` and `Y` have the same curvature. -/
def nullHomotopicMap (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) : X ⟶ Y where
  f₀ := X.d₀ ≫ h₁ + h₀ ≫ Y.d₁
  f₁ := X.d₁ ≫ h₀ + h₁ ≫ Y.d₀
  comm₀ := by simp [add_comm]
  comm₁ := by simp [add_comm]

@[simp]
theorem nullHomotopicMap_f₀ (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    (nullHomotopicMap h₀ h₁).f₀ = X.d₀ ≫ h₁ + h₀ ≫ Y.d₁ := by
  unfold nullHomotopicMap; rfl

@[simp]
theorem nullHomotopicMap_f₁ (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    (nullHomotopicMap h₀ h₁).f₁ = X.d₁ ≫ h₀ + h₁ ≫ Y.d₀ := by
  unfold nullHomotopicMap; rfl

@[simp]
theorem nullHomotopicMap_zero : nullHomotopicMap (0 : X.X₀ ⟶ Y.X₁) 0 = 0 := by
  ext <;> simp

theorem nullHomotopicMap_add (h₀ h₀' : X.X₀ ⟶ Y.X₁) (h₁ h₁' : X.X₁ ⟶ Y.X₀) :
    nullHomotopicMap (h₀ + h₀') (h₁ + h₁') = nullHomotopicMap h₀ h₁ + nullHomotopicMap h₀' h₁' := by
  ext <;> simp only [nullHomotopicMap_f₀, nullHomotopicMap_f₁, add_f₀, add_f₁, comp_add,
    add_comp] <;> abel

theorem nullHomotopicMap_neg (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    nullHomotopicMap (-h₀) (-h₁) = -nullHomotopicMap h₀ h₁ := by
  ext <;> simp [add_comm]

@[reassoc]
theorem comp_nullHomotopicMap (f : X ⟶ Y) (h₀ : Y.X₀ ⟶ Z.X₁) (h₁ : Y.X₁ ⟶ Z.X₀) :
    f ≫ nullHomotopicMap h₀ h₁ = nullHomotopicMap (f.f₀ ≫ h₀) (f.f₁ ≫ h₁) := by
  ext <;> simp [comp_add]

@[reassoc]
theorem nullHomotopicMap_comp (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) (g : Y ⟶ Z) :
    nullHomotopicMap h₀ h₁ ≫ g = nullHomotopicMap (h₀ ≫ g.f₁) (h₁ ≫ g.f₀) := by
  ext <;> simp [add_comp]

@[simp]
theorem parityShift_map_nullHomotopicMap (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    (parityShift C w).map (nullHomotopicMap h₀ h₁) = nullHomotopicMap (-h₁) (-h₀) := by
  ext <;> simp

variable (C w) in
/-- The two-sided ideal of **null-homotopic** morphisms of curved duplexes: those of the form
`d h + h d` for an odd map `h`. -/
def nullHomotopic : MorphismIdeal (CurvedDuplex C w) where
  hom X Y :=
    { carrier := {f | ∃ h₀ h₁, nullHomotopicMap h₀ h₁ = f}
      add_mem' := by
        rintro _ _ ⟨h₀, h₁, rfl⟩ ⟨h₀', h₁', rfl⟩
        exact ⟨h₀ + h₀', h₁ + h₁', nullHomotopicMap_add ..⟩
      zero_mem' := ⟨0, 0, nullHomotopicMap_zero⟩
      neg_mem' := by
        rintro _ ⟨h₀, h₁, rfl⟩
        exact ⟨-h₀, -h₁, nullHomotopicMap_neg ..⟩ }
  comp_mem_left := by
    intro _ _ _ f _ ⟨h₀, h₁, hg⟩
    exact ⟨_, _, hg ▸ (comp_nullHomotopicMap ..).symm⟩
  comp_mem_right := by
    intro _ _ _ _ g ⟨h₀, h₁, hf⟩
    exact ⟨_, _, hf ▸ (nullHomotopicMap_comp ..).symm⟩

@[simp]
theorem mem_nullHomotopic_iff {f : X ⟶ Y} :
    f ∈ (nullHomotopic C w).hom X Y ↔ ∃ h₀ h₁, nullHomotopicMap h₀ h₁ = f :=
  Iff.rfl

theorem nullHomotopicMap_mem_nullHomotopic (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    nullHomotopicMap h₀ h₁ ∈ (nullHomotopic C w).hom X Y :=
  ⟨h₀, h₁, rfl⟩

/-- The null-homotopic morphisms are exactly those whose parity shift is null-homotopic. -/
theorem comap_parityShift_nullHomotopic :
    (nullHomotopic C w).comap (parityShift C w) = nullHomotopic C w := by
  ext X Y f
  rw [MorphismIdeal.mem_comap_hom]
  refine ⟨fun ⟨k₀, k₁, hk⟩ ↦ ⟨-k₁, -k₀, ?_⟩, fun ⟨h₀, h₁, hh⟩ ↦ ⟨-h₁, -h₀, ?_⟩⟩
  · ext
    · simpa using congrArg Hom.f₁ hk
    · simpa using congrArg Hom.f₀ hk
  · rw [← hh, parityShift_map_nullHomotopicMap]

/-! ### Elementary disks -/

variable (w) in
/-- The **elementary disk** `A --𝟙--> A --w•𝟙--> A` on an object `A`. It is exposed so that its
components unfold to `A`. -/
@[expose, implicit_reducible, simps]
def disk (A : C) : CurvedDuplex C w where
  X₀ := A
  X₁ := A
  d₀ := 𝟙 A
  d₁ := w • 𝟙 A
  d₀_comp_d₁ := by simp
  d₁_comp_d₀ := by simp

/-- A morphism out of the disk on `A` is determined by its even component, which is an arbitrary
morphism `A ⟶ X₀`; this correspondence is `R`-linear. -/
def diskHomEquiv (A : C) (X : CurvedDuplex C w) : (disk w A ⟶ X) ≃ₗ[R] (A ⟶ X.X₀) where
  toFun f := f.f₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g :=
    { f₀ := g
      f₁ := g ≫ X.d₀ }
  left_inv f := by
    ext
    · rfl
    · simp
  right_inv _ := rfl

@[simp]
theorem diskHomEquiv_apply (A : C) (X : CurvedDuplex C w) (f : disk w A ⟶ X) :
    diskHomEquiv A X f = f.f₀ := by
  unfold diskHomEquiv; rfl

@[simp]
theorem diskHomEquiv_symm_apply_f₀ (A : C) (X : CurvedDuplex C w) (g : A ⟶ X.X₀) :
    ((diskHomEquiv A X).symm g).f₀ = g := by
  unfold diskHomEquiv; rfl

@[simp]
theorem diskHomEquiv_symm_apply_f₁ (A : C) (X : CurvedDuplex C w) (g : A ⟶ X.X₀) :
    ((diskHomEquiv A X).symm g).f₁ = g ≫ X.d₀ := by
  unfold diskHomEquiv; rfl

/-- The identity of the disk on `A` is null-homotopic: it is `d h + h d` for the odd map which is
the identity from the odd to the even component. -/
theorem nullHomotopicMap_disk (A : C) :
    nullHomotopicMap (X := disk w A) (Y := disk w A) 0 (𝟙 A) = 𝟙 (disk w A) := by
  ext <;> simp

/-! ### The homotopy category -/

variable (C w) in
/-- The **homotopy category** of curved duplexes of curvature `w`: the quotient of the category
of curved duplexes by the ideal of null-homotopic morphisms. It is preadditive and `R`-linear. -/
abbrev HomotopyCategory : Type _ :=
  (nullHomotopic C w).Quotient

/-- Two morphisms of curved duplexes become equal in the homotopy category exactly when they are
homotopic, that is when their difference is `d h + h d` for an odd map `h`. -/
theorem quotientFunctor_map_eq_quotientFunctor_map_iff {f g : X ⟶ Y} :
    (nullHomotopic C w).quotientFunctor.map f = (nullHomotopic C w).quotientFunctor.map g ↔
      ∃ h₀ h₁, nullHomotopicMap h₀ h₁ = f - g := by
  rw [MorphismIdeal.quotientFunctor_map_eq_iff, mem_nullHomotopic_iff]

variable (C w) in
/-- The parity shift of the homotopy category of curved duplexes, a self-equivalence induced by
the parity shift of curved duplexes. -/
noncomputable def HomotopyCategory.parityShiftEquivalence :
    HomotopyCategory C w ≌ HomotopyCategory C w :=
  MorphismIdeal.mapEquivalence (CurvedDuplex.parityShiftEquivalence C w) _ _
    comap_parityShift_nullHomotopic.symm

/-- The parity shift of the homotopy category is induced by the parity shift of curved
duplexes. -/
theorem HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor :
    (nullHomotopic C w).quotientFunctor ⋙ (HomotopyCategory.parityShiftEquivalence C w).functor =
      parityShift C w ⋙ (nullHomotopic C w).quotientFunctor := by
  rw [HomotopyCategory.parityShiftEquivalence, MorphismIdeal.mapEquivalence_functor]
  exact MorphismIdeal.quotientFunctor_comp_map ..

/-- On the image of a curved duplex, the parity shift of the homotopy category is the image of its
parity shift. -/
@[simp]
theorem HomotopyCategory.parityShiftEquivalence_functor_obj_quotientFunctor_obj
    (X : CurvedDuplex C w) :
    (HomotopyCategory.parityShiftEquivalence C w).functor.obj
        ((nullHomotopic C w).quotientFunctor.obj X) =
      (nullHomotopic C w).quotientFunctor.obj ((parityShift C w).obj X) :=
  Functor.congr_obj HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor X

/-- On the image of a morphism of curved duplexes, the parity shift of the homotopy category is
the image of its parity shift, up to the identification of objects
`HomotopyCategory.parityShiftEquivalence_functor_obj_quotientFunctor_obj`. -/
@[simp]
theorem HomotopyCategory.parityShiftEquivalence_functor_map_quotientFunctor_map (f : X ⟶ Y) :
    (HomotopyCategory.parityShiftEquivalence C w).functor.map
        ((nullHomotopic C w).quotientFunctor.map f) ≫
        eqToHom (HomotopyCategory.parityShiftEquivalence_functor_obj_quotientFunctor_obj Y) =
      eqToHom (HomotopyCategory.parityShiftEquivalence_functor_obj_quotientFunctor_obj X) ≫
        (nullHomotopic C w).quotientFunctor.map ((parityShift C w).map f) := by
  have h := Functor.congr_hom HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor f
  simp only [Functor.comp_map] at h
  simp [h]

/-- The disk on `A` is contractible, hence a zero object of the homotopy category. -/
theorem isZero_quotientFunctor_obj_disk (A : C) :
    IsZero ((nullHomotopic C w).quotientFunctor.obj (disk w A)) := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff]
  exact ⟨0, 𝟙 A, nullHomotopicMap_disk A⟩

end CurvedDuplex

end TauCeti
