/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.DifferentialObject
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.ZMod.Defs

/-!
# Differential modules

A **differential module** in a category `C` with zero morphisms is an object `X` together with an
endomorphism `d : X ⟶ X` such that `d ≫ d = 0`. For `C = ModuleCat Rᵐᵒᵖ` this is a right
`R`-module with a square-zero right-linear endomorphism, in the sense of Avramov, Buchweitz and
Iyengar. A differential module is a *one-periodic* object: there is a single object and a single
differential, with no grading.

This file builds the category of differential modules, with its preadditive and linear structures
and its forgetful functor, and relates it to the neighbouring notions without identifying them:

* `DifferentialModule.onePeriodicComplexEquivalence`: differential modules are equivalent to
  homological complexes of shape `ComplexShape.up (ZMod 1)`, the one-periodic complexes, so that
  Mathlib's homotopies, homotopy category and homology of complexes, and the periodic shift of
  `TauCeti.PeriodicComplex`, apply to differential modules through this equivalence (the
  one-object complex `TauCeti.oneObjectHomologicalComplex` uses the shape
  `ComplexShape.refl Unit` instead, which carries no periodic shift);
* `DifferentialModule.differentialObjectEquivalence`: for a shift on `C` together with a natural
  isomorphism `e : shiftFunctor C 1 ≅ 𝟭 C`, differential modules are equivalent to Mathlib's
  differential objects `DifferentialObject S C`, whose differentials are `d : X ⟶ X⟦1⟧` with
  `d ≫ d⟦1⟧' = 0`; the shifted-square law is derived from `d ≫ d = 0` using naturality of `e`;
* `DifferentialModule.forgetParity`: forgetting the parity of a two-periodic complex
  `X₀ ⇄ X₁` gives the differential module `X₀ ⊞ X₁` whose differential has off-diagonal
  components the two differentials of the complex.

A two-periodic complex is a different object from a differential module: `forgetParity`
forgets the decomposition of the underlying object into its even and odd parts, which a
differential module does not carry.

## Main definitions

* `TauCeti.DifferentialModule`: an object with a square-zero endomorphism.
* `TauCeti.DifferentialModule.forget`: the underlying object.
* `TauCeti.DifferentialModule.onePeriodicComplexEquivalence`: the equivalence with one-periodic
  complexes.
* `TauCeti.DifferentialModule.differentialObjectEquivalence`: the equivalence with differential
  objects for a shift whose shift by `1` is identified with the identity.
* `TauCeti.DifferentialModule.forgetParity`: the differential module of a two-periodic complex.

## References

* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of
  differential modules*, Invent. Math. **169** (2007), 1–35, Section 1.
* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3.
* The category structure follows Kim Morrison's `CategoryTheory.DifferentialObject` in
  `Mathlib.CategoryTheory.DifferentialObject`.
-/

public section

universe w' v u

namespace TauCeti

open CategoryTheory Category Limits Preadditive

variable (C : Type u) [Category.{v} C]

/-- A **differential module** in a category `C` with zero morphisms: an object `X` with an
endomorphism `d : X ⟶ X` such that `d ≫ d = 0`. -/
structure DifferentialModule [HasZeroMorphisms C] where
  /-- The underlying object. -/
  X : C
  /-- The differential. -/
  d : X ⟶ X
  /-- The differential squares to zero. -/
  d_comp_d : d ≫ d = 0

namespace DifferentialModule

attribute [reassoc (attr := simp)] d_comp_d

variable {C}

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- A morphism of differential modules: a morphism of the underlying objects commuting with the
differentials. -/
@[ext]
structure Hom (M N : DifferentialModule C) where
  /-- The morphism of underlying objects. -/
  f : M.X ⟶ N.X
  /-- The morphism commutes with the differentials. -/
  comm : f ≫ N.d = M.d ≫ f := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity morphism of a differential module. -/
def Hom.id (M : DifferentialModule C) : Hom M M where
  f := 𝟙 _

/-- The composition of morphisms of differential modules. -/
def Hom.comp {M N P : DifferentialModule C} (φ : Hom M N) (ψ : Hom N P) : Hom M P where
  f := φ.f ≫ ψ.f

instance : Category (DifferentialModule C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; apply Hom.ext; simp [Hom.id, Hom.comp]
  comp_id := by intros; apply Hom.ext; simp [Hom.id, Hom.comp]
  assoc := by intros; apply Hom.ext; simp [Hom.comp, Category.assoc]

variable {M N P : DifferentialModule C}

-- Register extensionality for categorical morphisms `M ⟶ N`; `Hom.ext` alone does not let
-- `ext` recognize that these morphisms are `DifferentialModule.Hom` structures.
@[ext]
theorem hom_ext {φ ψ : M ⟶ N} (h : φ.f = ψ.f) : φ = ψ :=
  Hom.ext h

@[simp] theorem id_f (M : DifferentialModule C) : Hom.f (𝟙 M) = 𝟙 M.X := by
  -- Reduce the categorical identity to its constructor before opening the opaque body.
  change (Hom.id M).f = _
  simp [Hom.id]
@[simp, reassoc] theorem comp_f (φ : M ⟶ N) (ψ : N ⟶ P) :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := by
  -- Reduce categorical composition to its constructor before opening the opaque body.
  change (Hom.comp φ ψ).f = _
  simp [Hom.comp]

/-- A constructor for morphisms of differential modules when the commutativity condition is not
obvious. -/
def homMk (f : M.X ⟶ N.X) (comm : f ≫ N.d = M.d ≫ f) : M ⟶ N :=
  ⟨f, comm⟩

@[simp] theorem homMk_f (f : M.X ⟶ N.X) (comm : f ≫ N.d = M.d ≫ f) :
    (homMk f comm).f = f := by simp [homMk]

instance : Zero (M ⟶ N) where
  zero := { f := 0 }

@[simp] theorem zero_f : (0 : M ⟶ N).f = 0 := rfl

instance : HasZeroMorphisms (DifferentialModule C) where

variable (C) in
/-- The forgetful functor sending a differential module to its underlying object. -/
@[expose, simps]
def forget : DifferentialModule C ⥤ C where
  obj M := M.X
  map φ := φ.f

instance : (forget C).Faithful where
  map_injective h := hom_ext h

instance (φ : M ⟶ N) [IsIso φ] : IsIso φ.f := (forget C).map_isIso φ

/-- A constructor for isomorphisms of differential modules from an isomorphism of the underlying
objects commuting with the differentials. -/
def isoMk (e : M.X ≅ N.X) (comm : e.hom ≫ N.d = M.d ≫ e.hom) : M ≅ N where
  hom := homMk e.hom comm
  inv := homMk e.inv (by rw [e.inv_comp_eq, reassoc_of% comm, e.hom_inv_id, comp_id])

@[simp] theorem isoMk_hom (e : M.X ≅ N.X)
    (comm : e.hom ≫ N.d = M.d ≫ e.hom) :
    (isoMk e comm).hom = homMk e.hom comm := by
  simp [isoMk]

@[simp] theorem isoMk_inv (e : M.X ≅ N.X)
    (comm : e.hom ≫ N.d = M.d ≫ e.hom) :
    (isoMk e comm).inv =
      homMk e.inv (by rw [e.inv_comp_eq, reassoc_of% comm, e.hom_inv_id, comp_id]) := by
  simp [isoMk]

/-- A morphism of differential modules is an isomorphism exactly when its underlying morphism
is. -/
theorem isIso_iff (φ : M ⟶ N) : IsIso φ ↔ IsIso φ.f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ (isoMk (asIso φ.f) φ.comm).isIso_hom⟩

end HasZeroMorphisms

/-! ### The preadditive and linear structures -/

section Preadditive

variable [Preadditive C] {M N : DifferentialModule C}

instance : Add (M ⟶ N) where
  add φ ψ := { f := φ.f + ψ.f }

instance : Sub (M ⟶ N) where
  sub φ ψ := { f := φ.f - ψ.f }

instance : Neg (M ⟶ N) where
  neg φ := { f := -φ.f }

@[simp] theorem add_f (φ ψ : M ⟶ N) : (φ + ψ).f = φ.f + ψ.f := rfl
@[simp] theorem sub_f (φ ψ : M ⟶ N) : (φ - ψ).f = φ.f - ψ.f := rfl
@[simp] theorem neg_f (φ : M ⟶ N) : (-φ).f = -φ.f := rfl

instance : AddCommGroup (M ⟶ N) where
  add_assoc _ _ _ := by ext; apply add_assoc
  add_zero _ := by ext; apply add_zero
  zero_add _ := by ext; apply zero_add
  neg_add_cancel _ := by ext; apply neg_add_cancel
  add_comm _ _ := by ext; apply add_comm
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Preadditive (DifferentialModule C) where

instance : (forget C).Additive where

variable {R : Type w'} [Semiring R] [Linear R C]

instance : SMul R (M ⟶ N) where
  smul a φ := { f := a • φ.f }

@[simp] theorem smul_f (a : R) (φ : M ⟶ N) : (a • φ).f = a • φ.f := rfl

attribute [local simp] mul_smul add_smul in
instance : Module R (M ⟶ N) where
  zero_smul := by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch

instance : Linear R (DifferentialModule C) where

instance : (forget C).Linear R where

end Preadditive

/-! ### One-periodic complexes -/

section OnePeriodic

variable [HasZeroMorphisms C]

variable (C) in
/-- The one-periodic complex of a differential module: the object and the differential in the
unique degree of `ZMod 1`. -/
@[expose, implicit_reducible, simps]
def toOnePeriodicComplex :
    DifferentialModule C ⥤ HomologicalComplex C (ComplexShape.up (ZMod 1)) where
  obj M :=
    { X := fun _ ↦ M.X
      d := fun _ _ ↦ M.d
      shape := fun i j h ↦ absurd (Subsingleton.elim _ _) h
      d_comp_d' := fun _ _ _ _ _ ↦ M.d_comp_d }
  map φ :=
    { f := fun _ ↦ φ.f
      comm' := fun _ _ _ ↦ φ.comm }

variable (C) in
/-- The differential module of a one-periodic complex `K`: the object `K.X 0` with the
differential `K.d 0 0`. -/
@[expose, implicit_reducible, simps]
def ofOnePeriodicComplex :
    HomologicalComplex C (ComplexShape.up (ZMod 1)) ⥤ DifferentialModule C where
  obj K :=
    { X := K.X 0
      d := K.d 0 0
      d_comp_d := K.d_comp_d 0 0 0 }
  map φ :=
    { f := φ.f 0
      comm := φ.comm 0 0 }

variable (C) in
/-- Differential modules are equivalent to one-periodic complexes, that is to homological
complexes of shape `ComplexShape.up (ZMod 1)`. -/
def onePeriodicComplexEquivalence :
    DifferentialModule C ≌ HomologicalComplex C (ComplexShape.up (ZMod 1)) where
  functor := toOnePeriodicComplex C
  inverse := ofOnePeriodicComplex C
  unitIso := NatIso.ofComponents (fun M ↦ isoMk (Iso.refl M.X) (by simp))
    (fun φ ↦ by ext; simp [isoMk, homMk])
  counitIso := NatIso.ofComponents
    (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ K.XIsoOfEq (Subsingleton.elim _ _))
      (fun i j _ ↦ by
        obtain rfl := Subsingleton.elim i 0
        obtain rfl := Subsingleton.elim j 0
        simp))
    (fun φ ↦ by
      ext i
      obtain rfl := Subsingleton.elim i 0
      simp)
  functor_unitIso_comp := by
    intro M
    ext i
    obtain rfl := Subsingleton.elim i 0
    simp [isoMk, homMk]

@[simp] theorem onePeriodicComplexEquivalence_functor :
    (onePeriodicComplexEquivalence C).functor = toOnePeriodicComplex C := by
  simp [onePeriodicComplexEquivalence]

@[simp] theorem onePeriodicComplexEquivalence_inverse :
    (onePeriodicComplexEquivalence C).inverse = ofOnePeriodicComplex C := by
  simp [onePeriodicComplexEquivalence]

end OnePeriodic

section OnePeriodicPreadditive

variable [Preadditive C]

instance : (toOnePeriodicComplex C).Additive where
instance : (ofOnePeriodicComplex C).Additive where

variable {R : Type w'} [Semiring R] [Linear R C]

instance : (toOnePeriodicComplex C).Linear R where
instance : (ofOnePeriodicComplex C).Linear R where

end OnePeriodicPreadditive

/-! ### Differential objects for a shift identified with the identity -/

section DifferentialObject

variable [HasZeroMorphisms C] {S : Type*} [AddMonoidWithOne S] [HasShift C S]
  (e : shiftFunctor C (1 : S) ≅ 𝟭 C)

/-- The differential object of a differential module `M`, for a natural isomorphism
`e : shiftFunctor C 1 ≅ 𝟭 C`: the differential is `M.d ≫ e.inv.app M.X : M.X ⟶ M.X⟦1⟧`, and its
shifted square vanishes because `M.d ≫ M.d = 0`. -/
@[expose, implicit_reducible, simps]
def toDifferentialObject : DifferentialModule C ⥤ DifferentialObject S C where
  obj M :=
    { obj := M.X
      d := M.d ≫ e.inv.app M.X
      d_squared := by
        rw [Functor.map_comp, assoc, ← e.inv.naturality_assoc]
        simp }
  map φ :=
    { f := φ.f
      comm := by
        rw [assoc, ← e.inv.naturality]
        simp }

/-- The differential module of a differential object `Y`, for a natural isomorphism
`e : shiftFunctor C 1 ≅ 𝟭 C`: the differential is `Y.d ≫ e.hom.app Y.obj : Y.obj ⟶ Y.obj`. -/
@[expose, implicit_reducible, simps]
def ofDifferentialObject : DifferentialObject S C ⥤ DifferentialModule C where
  obj Y :=
    { X := Y.obj
      d := Y.d ≫ e.hom.app Y.obj
      d_comp_d := by
        have := e.hom.naturality Y.d
        simp only [Functor.id_obj, Functor.id_map] at this
        rw [assoc, ← reassoc_of% this, DifferentialObject.d_squared_assoc, zero_comp] }
  map φ :=
    { f := φ.f
      comm := by
        have := e.hom.naturality φ.f
        simp only [Functor.id_obj, Functor.id_map] at this
        rw [assoc, ← this, DifferentialObject.Hom.comm_assoc] }

/-- For a natural isomorphism `e : shiftFunctor C 1 ≅ 𝟭 C`, differential modules are equivalent to
Mathlib's differential objects `DifferentialObject S C`. -/
def differentialObjectEquivalence : DifferentialModule C ≌ DifferentialObject S C where
  functor := toDifferentialObject e
  inverse := ofDifferentialObject e
  unitIso := NatIso.ofComponents (fun M ↦ isoMk (Iso.refl M.X) (by simp))
    (fun φ ↦ by ext; simp [isoMk, homMk])
  counitIso := NatIso.ofComponents (fun Y ↦ DifferentialObject.mkIso (Iso.refl Y.obj) (by simp))

@[simp] theorem differentialObjectEquivalence_functor :
    (differentialObjectEquivalence e).functor = toDifferentialObject e := by
  simp [differentialObjectEquivalence]

@[simp] theorem differentialObjectEquivalence_inverse :
    (differentialObjectEquivalence e).inverse = ofDifferentialObject e := by
  simp [differentialObjectEquivalence]

end DifferentialObject

/-! ### Forgetting the parity of a two-periodic complex -/

section ForgetParity

variable [HasZeroMorphisms C] [HasBinaryBiproducts C]

variable (C) in
/-- The differential module obtained by forgetting the parity of a two-periodic complex `K`: the
object `K.X 0 ⊞ K.X 1`, with the differential whose components are `K.d 0 1 : K.X 0 ⟶ K.X 1`
and `K.d 1 0 : K.X 1 ⟶ K.X 0`. -/
@[expose, implicit_reducible, simps obj_X map_f]
noncomputable def forgetParity :
    HomologicalComplex C (ComplexShape.up (ZMod 2)) ⥤ DifferentialModule C where
  obj K :=
    { X := K.X 0 ⊞ K.X 1
      d := biprod.desc (K.d 0 1 ≫ biprod.inr) (K.d 1 0 ≫ biprod.inl)
      d_comp_d := by ext <;> simp }
  map φ :=
    { f := biprod.map (φ.f 0) (φ.f 1)
      comm := by ext <;> simp }

/-- Precomposing the differential after forgetting parity with the left inclusion recovers the
differential from degree zero to degree one. -/
@[reassoc (attr := simp)]
theorem inl_forgetParity_obj_d (K : HomologicalComplex C (ComplexShape.up (ZMod 2))) :
    biprod.inl ≫ ((forgetParity C).obj K).d = K.d 0 1 ≫ biprod.inr :=
  biprod.inl_desc _ _

/-- Precomposing the differential after forgetting parity with the right inclusion recovers the
differential from degree one to degree zero. -/
@[reassoc (attr := simp)]
theorem inr_forgetParity_obj_d (K : HomologicalComplex C (ComplexShape.up (ZMod 2))) :
    biprod.inr ≫ ((forgetParity C).obj K).d = K.d 1 0 ≫ biprod.inl :=
  biprod.inr_desc _ _

end ForgetParity

section ForgetParityPreadditive

variable [Preadditive C] [HasBinaryBiproducts C]

instance : (forgetParity C).Additive where
  map_add {_ _ _ _} := by ext : 1; apply biprod.hom_ext' <;> simp

instance {R : Type w'} [Semiring R] [Linear R C] : (forgetParity C).Linear R where
  map_smul {_ _} _ _ := by ext : 1; apply biprod.hom_ext' <;> simp

end ForgetParityPreadditive

end DifferentialModule

end TauCeti
