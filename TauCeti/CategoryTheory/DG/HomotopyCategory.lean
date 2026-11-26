/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.DG.GradedHomology

/-!
# The homotopy category of a differential graded category

For a differential graded category `C`, the morphisms in its homotopy category are the
degree-zero cocycles in each Hom complex, modulo the degree-zero coboundaries. Specializing the
graded cohomology calculus of `TauCeti.CategoryTheory.DG.GradedHomology` to degree zero defines
`TauCeti.dgHomotopyClass` and `TauCeti.dgHomotopyComp` on Mathlib's canonical degree-zero homology
object `TauCeti.DGHomotopyClass`, assembling into the `R`-linear category
`TauCeti.DGHomotopyCategory`.

## Main definitions

* `TauCeti.dgCycles`: the degree-zero cocycles in a DG Hom complex.
* `TauCeti.dgBoundaries`: the degree-zero coboundaries in a DG Hom complex.
* `TauCeti.DGHomotopyClass`: the canonical degree-zero homology of a DG Hom complex.
* `TauCeti.dgHomotopyComp`: composition of homotopy classes.
* `TauCeti.DGHomotopyCategory`: the category with the objects of a DG category and morphisms
  given by `DGHomotopyClass`.

## Main results

* `TauCeti.exactAt_iff_forall_exists_dgDifferential_eq`: a Hom complex is exact in a degree
  exactly when every cycle of that degree is a boundary.
* `TauCeti.dgHomotopyClass_eq_iff`: two cocycles have the same class exactly when their difference
  is a coboundary.
* `TauCeti.dgHomotopyClass_eq_homologyπ`: a homotopy class is the image of any lifting cycle under
  Mathlib's `HomologicalComplex.homologyπ`.
* `TauCeti.homologyMap_dgHomotopyClass`: a chain map of Hom complexes sends the class of `f` to the
  class of the image of `f`.
* `TauCeti.DGHomotopyCategory.isZero_of_iff_dgId_mem_dgBoundaries`: an object is zero in the
  homotopy category exactly when its identity is a coboundary.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

noncomputable section

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Cycles, boundaries, and homotopy classes -/

/-- The degree-zero cocycles in the Hom complex from X to Y. -/
def dgCycles (X Y : C) : Submodule R (DGHom R 0 X Y) :=
  LinearMap.ker (dgDifferential R 0)

/-- A degree-zero morphism is a cocycle exactly when its differential vanishes. -/
@[simp]
theorem mem_dgCycles {X Y : C} {f : DGHom R 0 X Y} :
    f ∈ dgCycles R X Y ↔ dgDifferential R 0 f = 0 :=
  LinearMap.mem_ker

/-- The degree-zero coboundaries in the Hom complex from X to Y. -/
def dgBoundaries (X Y : C) : Submodule R (DGHom R 0 X Y) :=
  LinearMap.range (dgDifferential R (-1))

/-- A degree-zero morphism is a coboundary exactly when it is the differential of a
degree-minus-one morphism. -/
@[simp]
theorem mem_dgBoundaries {X Y : C} {f : DGHom R 0 X Y} :
    f ∈ dgBoundaries R X Y ↔
      ∃ h : DGHom R (-1) X Y, dgDifferential R (-1) h = f :=
  LinearMap.mem_range

/-- Every degree-zero coboundary is a cocycle. -/
theorem dgBoundaries_le_dgCycles (X Y : C) :
    dgBoundaries R X Y ≤ dgCycles R X Y := by
  rintro _ ⟨h, rfl⟩
  exact dgDifferential_dgDifferential R h

/-- A Hom complex is exact in degree `p + 1` exactly when every cycle of degree `p + 1` is a
boundary. -/
theorem exactAt_iff_forall_exists_dgDifferential_eq {X Y : C} {p : ℤ} :
    (dgHomComplex R X Y).ExactAt (p + 1) ↔ ∀ z : DGHom R (p + 1) X Y,
      dgDifferential R (p + 1) z = 0 → ∃ g : DGHom R p X Y, dgDifferential R p g = z := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  -- The maps of the short complex `sc'` are the differentials, by definition.
  rfl

/-- A morphism in H⁰(C), using the canonical Mathlib homology object of the DG Hom complex. -/
noncomputable abbrev DGHomotopyClass (X Y : C) :=
  (dgHomComplex R X Y).homology 0

/-- The linear quotient map from degree-zero cocycles to homotopy classes. -/
noncomputable def dgHomotopyClassLinearMap (X Y : C) :
    dgCycles R X Y →ₗ[R] DGHomotopyClass R X Y :=
  dgHomologyClassLinearMap R 0 X Y

/-- The homotopy class represented by a closed degree-zero morphism. -/
def dgHomotopyClass {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    DGHomotopyClass R X Y :=
  dgHomologyClass R f ((mem_dgCycles R).mp hf)

/-- `TauCeti.dgHomotopyClass` is the degree-zero specialization of `TauCeti.dgHomologyClass`. -/
theorem dgHomotopyClass_eq_dgHomologyClass {X Y : C} (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = dgHomologyClass R f ((mem_dgCycles R).mp hf) :=
  (rfl)

/-- `TauCeti.dgHomotopyClassLinearMap` evaluates a cocycle subtype to `TauCeti.dgHomotopyClass`. -/
@[simp]
theorem dgHomotopyClassLinearMap_apply (X Y : C) (f : dgCycles R X Y) :
    dgHomotopyClassLinearMap R X Y f = dgHomotopyClass R f.val f.property :=
  dgHomologyClassLinearMap_apply R 0 X Y f

/-- Zero represents zero as a homotopy class. -/
@[simp]
theorem dgHomotopyClass_zero (X Y : C) :
    dgHomotopyClass R (0 : DGHom R 0 X Y) (dgCycles R X Y).zero_mem = 0 :=
  dgHomologyClass_zero R 0 X Y

/-- The class of a sum of cocycles is the sum of their classes. -/
@[simp]
theorem dgHomotopyClass_add {X Y : C} (f g : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    dgHomotopyClass R (f + g) ((dgCycles R X Y).add_mem hf hg) =
      dgHomotopyClass R f hf + dgHomotopyClass R g hg :=
  dgHomologyClass_add R f g ((mem_dgCycles R).mp hf) ((mem_dgCycles R).mp hg)

/-- The class of a scalar multiple of a cocycle is the scalar multiple of its class. -/
@[simp]
theorem dgHomotopyClass_smul {X Y : C} (r : R) (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R (r • f) ((dgCycles R X Y).smul_mem r hf) =
      r • dgHomotopyClass R f hf :=
  dgHomologyClass_smul R r f ((mem_dgCycles R).mp hf)

/-- Every homotopy class has a closed degree-zero representative. -/
theorem exists_dgHomotopyClass_eq {X Y : C} (c : DGHomotopyClass R X Y) :
    ∃ (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y), dgHomotopyClass R f hf = c :=
  let ⟨f, hf, h⟩ := exists_dgHomologyClass_eq R c
  ⟨f, (mem_dgCycles R).mpr hf, h⟩

/-- Two closed degree-zero morphisms represent the same homotopy class exactly when their
difference is a coboundary. -/
@[simp]
theorem dgHomotopyClass_eq_iff {X Y : C} {f g : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = dgHomotopyClass R g hg ↔
      f - g ∈ dgBoundaries R X Y := by
  rw [dgHomotopyClass_eq_dgHomologyClass, dgHomotopyClass_eq_dgHomologyClass,
    dgHomologyClass_eq_iff, mem_dgBoundaries]
  -- Closed integer arithmetic reduces `0 - 1` to `-1` and `-1 + 1` to `0` in `dgDifferential`.
  rfl

/-- A closed degree-zero morphism represents zero exactly when it is a coboundary. -/
@[simp]
theorem dgHomotopyClass_eq_zero_iff {X Y : C} {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = 0 ↔ f ∈ dgBoundaries R X Y := by
  rw [← dgHomotopyClass_zero R X Y]
  simpa only [sub_zero] using dgHomotopyClass_eq_iff R hf (dgCycles R X Y).zero_mem

/-! ### Comparison with Mathlib's homology projection -/

/-- The homotopy class of a closed degree-zero morphism `f` is the image, under Mathlib's
projection `HomologicalComplex.homologyπ` from cycles to homology, of any cycle lifting `f`. -/
theorem dgHomotopyClass_eq_homologyπ {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgCycles R X Y)
    (x : (dgHomComplex R X Y).cycles 0) (hx : ((dgHomComplex R X Y).iCycles 0).hom x = f) :
    dgHomotopyClass R f hf = ((dgHomComplex R X Y).homologyπ 0).hom x :=
  dgHomologyClass_eq_homologyπ R ((mem_dgCycles R).mp hf) x hx

/-- A closed degree-zero morphism stays closed under a chain map of Hom complexes. -/
theorem map_mem_dgCycles {C' : Type*} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) : (φ.f 0).hom f ∈ dgCycles R X' Y' :=
  (mem_dgCycles R).mpr (map_dgDifferential_eq_zero R φ ((mem_dgCycles R).mp hf))

/-- The map induced on homotopy classes by a chain map of Hom complexes sends the class of a
closed degree-zero morphism to the class of its image. -/
@[simp]
theorem homologyMap_dgHomotopyClass {C' : Type*} [DGCategory R C'] {X Y : C} {X' Y' : C'}
    (φ : dgHomComplex R X Y ⟶ dgHomComplex R X' Y') {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) :
    (HomologicalComplex.homologyMap φ 0).hom (dgHomotopyClass R f hf) =
      dgHomotopyClass R ((φ.f 0).hom f) (map_mem_dgCycles R φ hf) :=
  homologyMap_dgHomologyClass R φ ((mem_dgCycles R).mp hf)

/-! ### Composition on homotopy classes -/

/-- Composition of two degree-zero DG morphisms. -/
def dgCompZero {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    DGHom R 0 X Z :=
  dgComp R f g (zero_add 0)

/-- Composition of degree-zero DG morphisms is homogeneous DG composition in degree zero. -/
theorem dgCompZero_def {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R f g = dgComp R f g (zero_add 0) :=
  (rfl)

/-- Composition of degree-zero DG morphisms is additive in its first argument. -/
@[simp]
theorem add_dgCompZero {X Y Z : C} (f f' : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R (f + f') g = dgCompZero R f g + dgCompZero R f' g := by
  simp only [dgCompZero_def, add_dgComp]

/-- Composition of degree-zero DG morphisms respects scalar multiplication in its first
argument. -/
@[simp]
theorem smul_dgCompZero {X Y Z : C} (r : R) (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R (r • f) g = r • dgCompZero R f g := by
  simp only [dgCompZero_def, smul_dgComp]

/-- Composition of degree-zero DG morphisms is additive in its second argument. -/
@[simp]
theorem dgCompZero_add {X Y Z : C} (f : DGHom R 0 X Y) (g g' : DGHom R 0 Y Z) :
    dgCompZero R f (g + g') = dgCompZero R f g + dgCompZero R f g' := by
  simp only [dgCompZero_def, dgComp_add]

/-- Composition of degree-zero DG morphisms respects scalar multiplication in its second
argument. -/
@[simp]
theorem dgCompZero_smul {X Y Z : C} (r : R) (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z) :
    dgCompZero R f (r • g) = r • dgCompZero R f g := by
  simp only [dgCompZero_def, dgComp_smul]

/-- The composite of two degree-zero cocycles is a degree-zero cocycle. -/
theorem dgCompZero_mem_dgCycles {X Y Z : C} {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgCompZero R f g ∈ dgCycles R X Z :=
  (mem_dgCycles R).mpr
    (dgDifferential_dgComp_eq_zero R ((mem_dgCycles R).mp hf) ((mem_dgCycles R).mp hg) (zero_add 0))

/-- Composing a degree-zero boundary on the left with a degree-zero cocycle gives a boundary. -/
theorem dgCompZero_mem_dgBoundaries_of_left {X Y Z : C}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgBoundaries R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgCompZero R f g ∈ dgBoundaries R X Z := by
  obtain ⟨h, rfl⟩ := hf
  refine ⟨dgComp R h g (add_zero (-1)), ?_⟩
  rw [dgDifferential_dgComp_of_dgDifferential_eq_zero_right R h ((mem_dgCycles R).mp hg),
    dgCompZero_def]

/-- Composing a degree-zero cocycle on the left with a degree-zero boundary gives a boundary. -/
theorem dgCompZero_mem_dgBoundaries_of_right {X Y Z : C}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgBoundaries R Y Z) :
    dgCompZero R f g ∈ dgBoundaries R X Z := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨dgComp R f h (zero_add (-1)), ?_⟩
  rw [dgDifferential_dgComp_of_dgDifferential_eq_zero_left R ((mem_dgCycles R).mp hf) h,
    dgCompZero_def]

/-- Composition restricted to degree-zero cocycles. -/
def dgCyclesComp (X Y Z : C) :
    dgCycles R X Y →ₗ[R] dgCycles R Y Z →ₗ[R] dgCycles R X Z :=
  LinearMap.mk₂ R
    (fun (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦
      ⟨dgCompZero R (X := X) (Y := Y) (Z := Z)
        (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z), dgCompZero_mem_dgCycles R f.property g.property⟩)
    (fun (f f' : dgCycles R X Y) (g : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_add, add_dgCompZero])
    (fun r (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_smul, smul_dgCompZero])
    (fun (f : dgCycles R X Y) (g g' : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_add, dgCompZero_add])
    (fun r (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦ by
      apply Subtype.ext
      simp only [Submodule.coe_smul, dgCompZero_smul])

/-- The underlying morphism of the composite of two cocycles is their DG composition. -/
@[simp]
theorem coe_dgCyclesComp {X Y Z : C} (f : dgCycles R X Y) (g : dgCycles R Y Z) :
    (dgCyclesComp R X Y Z f g : DGHom R 0 X Z) =
      dgCompZero R (X := X) (Y := Y) (Z := Z) f g :=
  (rfl)

/-- The bilinear composition of homotopy classes induced by DG composition. -/
noncomputable def dgHomotopyComp (X Y Z : C) :
    DGHomotopyClass R X Y →ₗ[R] DGHomotopyClass R Y Z →ₗ[R]
      DGHomotopyClass R X Z :=
  dgHomologyComp R X Y Z (zero_add 0)

/-- `TauCeti.dgHomotopyComp` is the degree-zero specialization of `TauCeti.dgHomologyComp`. -/
theorem dgHomotopyComp_eq_dgHomologyComp (X Y Z : C) :
    dgHomotopyComp R X Y Z = dgHomologyComp R X Y Z (zero_add 0) :=
  (rfl)

/-- The composite of classes is represented by the DG composite of their representatives. -/
@[simp]
theorem dgHomotopyComp_dgHomotopyClass {X Y Z : C}
    (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgHomotopyComp R X Y Z (dgHomotopyClass R f hf) (dgHomotopyClass R g hg) =
      dgHomotopyClass R (dgCompZero R f g) (dgCompZero_mem_dgCycles R hf hg) :=
  dgHomologyComp_dgHomologyClass R (zero_add 0) f g ((mem_dgCycles R).mp hf)
    ((mem_dgCycles R).mp hg)

/-- Composition of homotopy classes is associative. -/
theorem dgHomotopyComp_assoc {W X Y Z : C}
    (f : DGHomotopyClass R W X) (g : DGHomotopyClass R X Y)
    (h : DGHomotopyClass R Y Z) :
    dgHomotopyComp R W Y Z (dgHomotopyComp R W X Y f g) h =
      dgHomotopyComp R W X Z f (dgHomotopyComp R X Y Z g h) :=
  dgHomologyComp_assoc R (zero_add 0) (zero_add 0) (zero_add 0) (zero_add 0) f g h

/-! ### The category H⁰(C) -/

/-- The homotopy category of a differential graded category. It has the same objects as C and
the zeroth cohomology of each DG Hom complex as its morphisms. -/
structure DGHomotopyCategory (R : Type v) (C : Type u) where
  /-- The underlying object of the differential graded category. -/
  obj : C

namespace DGHomotopyCategory

/-- Regard an object of a DG category as an object of its homotopy category. -/
@[expose] def of (X : C) : DGHomotopyCategory R C := ⟨X⟩

/-- Regard an object of a DG homotopy category as an object of the underlying DG category. -/
@[expose] def underlying (X : DGHomotopyCategory R C) : C := X.obj

omit [CommRing R] [DGCategory R C] in
@[simp]
theorem underlying_of (X : C) : underlying R (of R X) = X := (rfl)

omit [CommRing R] [DGCategory R C] in
@[simp]
theorem of_underlying (X : DGHomotopyCategory R C) : of R (underlying R X) = X := by
  cases X
  rfl

omit [CommRing R] [DGCategory R C] in
/-- Every object of the DG homotopy category comes from an object of the DG category. -/
theorem of_surjective : Function.Surjective (of R : C → DGHomotopyCategory R C) :=
  fun X ↦ ⟨underlying R X, of_underlying R X⟩

omit [CommRing R] [DGCategory R C] in
/-- Objects of the DG homotopy category are equal when their underlying DG objects are equal. -/
@[ext]
theorem ext {X Y : DGHomotopyCategory R C} (h : underlying R X = underlying R Y) : X = Y := by
  rw [← of_underlying R X, ← of_underlying R Y, h]

instance : Quiver (DGHomotopyCategory R C) where
  Hom X Y := DGHomotopyClass R (underlying R X) (underlying R Y)

noncomputable instance : Category (DGHomotopyCategory R C) where
  id X := dgHomotopyClass R (dgId R (underlying R X))
    ((mem_dgCycles R).mpr (dgDifferential_dgId R (underlying R X)))
  comp {X Y Z} f g :=
    dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f g
  id_comp {_ _} f := by
    rw [dgHomotopyComp_eq_dgHomologyComp, dgHomotopyClass_eq_dgHomologyClass, ← dgHomologyId_def,
      dgHomologyId_dgHomologyComp]
  comp_id {_ _} f := by
    rw [dgHomotopyComp_eq_dgHomologyComp, dgHomotopyClass_eq_dgHomologyClass, ← dgHomologyId_def,
      dgHomologyComp_dgHomologyId]
  assoc {_ _ _ _} f g h := dgHomotopyComp_assoc R f g h

noncomputable instance : Preadditive (DGHomotopyCategory R C) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (DGHomotopyClass R (underlying R X) (underlying R Y)))
  add_comp X Y Z f f' g :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z)).map_add₂ f f' g
  comp_add X Y Z f g g' :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f).map_add g g'

noncomputable instance : Linear R (DGHomotopyCategory R C) where
  homModule X Y := inferInstanceAs
    (Module R (DGHomotopyClass R (underlying R X) (underlying R Y)))
  smul_comp X Y Z r f g :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z)).map_smul₂ r f g
  comp_smul X Y Z f r g :=
    (dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f).map_smul r g

/-- Composition in the homotopy category is the composition `TauCeti.dgHomotopyComp` of homotopy
classes. -/
theorem comp_def {X Y Z : DGHomotopyCategory R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f g :=
  (rfl)

/-- The identity of the homotopy category is the homotopy class of the DG identity. -/
theorem id_def (X : DGHomotopyCategory R C) :
    𝟙 X = dgHomotopyClass R (dgId R (underlying R X))
      ((mem_dgCycles R).mpr (dgDifferential_dgId R (underlying R X))) :=
  (rfl)

/-- The forward and inverse morphisms of an isomorphism in `DGHomotopyCategory R C` compose under
`TauCeti.dgHomologyComp` to `TauCeti.dgHomologyId`. -/
@[simp]
theorem dgHomologyComp_hom_inv {X Y : C} (e : of R X ≅ of R Y) :
    dgHomologyComp R X Y X (zero_add 0) e.hom e.inv = dgHomologyId R X := by
  rw [dgHomologyId_def, ← dgHomotopyClass_eq_dgHomologyClass, ← dgHomotopyComp_eq_dgHomologyComp]
  exact e.hom_inv_id

/-- The inverse and forward morphisms of an isomorphism in `DGHomotopyCategory R C` compose under
`TauCeti.dgHomologyComp` to `TauCeti.dgHomologyId`. -/
@[simp]
theorem dgHomologyComp_inv_hom {X Y : C} (e : of R X ≅ of R Y) :
    dgHomologyComp R Y X Y (zero_add 0) e.inv e.hom = dgHomologyId R Y := by
  rw [dgHomologyId_def, ← dgHomotopyClass_eq_dgHomologyClass, ← dgHomotopyComp_eq_dgHomologyComp]
  exact e.inv_hom_id

/-- A closed degree-zero DG morphism, regarded as a morphism in the homotopy category. -/
def homOf {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    of R X ⟶ of R Y :=
  dgHomotopyClass R f hf

/-- A closed degree-zero DG morphism, regarded in the homotopy category, is its homotopy
class. -/
theorem homOf_def {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    homOf R f hf = dgHomotopyClass R f hf :=
  (rfl)

/-- The zero DG morphism represents the zero morphism in the homotopy category. -/
@[simp]
theorem homOf_zero (X Y : C) :
    homOf R (0 : DGHom R 0 X Y) (dgCycles R X Y).zero_mem = 0 :=
  dgHomotopyClass_zero R X Y

/-- Taking a morphism to the homotopy category preserves addition. -/
@[simp]
theorem homOf_add {X Y : C} (f g : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    homOf R (f + g) ((dgCycles R X Y).add_mem hf hg) = homOf R f hf + homOf R g hg :=
  dgHomotopyClass_add R f g hf hg

/-- Taking a morphism to the homotopy category preserves scalar multiplication. -/
@[simp]
theorem homOf_smul {X Y : C} (r : R) (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    homOf R (r • f) ((dgCycles R X Y).smul_mem r hf) = r • homOf R f hf :=
  dgHomotopyClass_smul R r f hf

/-- Every morphism of the homotopy category is the class of a closed degree-zero DG morphism. -/
theorem exists_homOf_eq {X Y : C} (f : of R X ⟶ of R Y) :
    ∃ (g : DGHom R 0 X Y) (hg : g ∈ dgCycles R X Y), homOf R g hg = f :=
  exists_dgHomotopyClass_eq R f

/-- Taking a morphism to the homotopy category preserves negation. -/
@[simp]
theorem homOf_neg {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    homOf R (-f) ((dgCycles R X Y).neg_mem hf) = -homOf R f hf := by
  rw [eq_neg_iff_add_eq_zero, ← homOf_add, ← homOf_zero]
  congr 1
  exact neg_add_cancel f

/-- Taking a morphism to the homotopy category preserves multiplication by a sign. -/
@[simp]
theorem homOf_units_smul {X Y : C} (u : ℤˣ) (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    homOf R (u • f) ((dgCycles R X Y).toAddSubgroup.zsmul_mem hf (u : ℤ)) = u • homOf R f hf := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    exact homOf_neg R f hf

/-- A closed degree-zero DG morphism represents zero precisely when it is a boundary. -/
@[simp]
theorem homOf_eq_zero_iff {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgCycles R X Y) :
    homOf R f hf = 0 ↔ f ∈ dgBoundaries R X Y :=
  dgHomotopyClass_eq_zero_iff R hf

/-- The DG identity represents the identity in the homotopy category. -/
@[simp]
theorem homOf_dgId (X : C) :
    homOf R (dgId R X) ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) = 𝟙 (of R X) :=
  (rfl)

/-- Two closed degree-zero DG morphisms define the same morphism in the homotopy category exactly
when their difference is a coboundary. -/
@[simp]
theorem homOf_eq_iff {X Y : C} {f g : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    homOf R f hf = homOf R g hg ↔ f - g ∈ dgBoundaries R X Y :=
  dgHomotopyClass_eq_iff R hf hg

/-- Composition in the homotopy category is represented by DG composition. -/
@[simp]
theorem homOf_comp {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    homOf R f hf ≫ homOf R g hg =
      homOf R (dgCompZero R f g) (dgCompZero_mem_dgCycles R hf hg) :=
  dgHomotopyComp_dgHomotopyClass R f g hf hg

/-- If the DG composite of `f` and `g` is `k`, then the composite of their classes in the homotopy
category is the class of `k`. -/
theorem homOf_comp_eq_homOf_of_dgComp_eq {X Y Z : C} {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    {k : DGHom R 0 X Z} (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z)
    (hk : k ∈ dgCycles R X Z) (e : dgComp R f g (add_zero 0) = k) :
    homOf R f hf ≫ homOf R g hg = homOf R k hk := by
  subst e
  exact homOf_comp R f g hf hg

/-- If the DG composite of `f` and `g` is the identity, then so is the composite of their classes
in the homotopy category. -/
theorem homOf_comp_eq_id_of_dgComp_eq_dgId {X Y : C} {f : DGHom R 0 X Y} {g : DGHom R 0 Y X}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y X) (e : dgComp R f g (add_zero 0) = dgId R X) :
    homOf R f hf ≫ homOf R g hg = 𝟙 (of R X) :=
  (homOf_comp_eq_homOf_of_dgComp_eq R hf hg
    ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) e).trans (homOf_dgId R X)

/-- If the differential of a degree-minus-one morphism `k` is minus the composite of `f` and `g`,
then the composite of `f` and `g` vanishes in the homotopy category. -/
theorem homOf_comp_eq_zero_of_dgDifferential_eq_neg {X Y Z : C} {f : DGHom R 0 X Y}
    {g : DGHom R 0 Y Z} (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z)
    {k : DGHom R (-1) X Z} (hk : dgDifferential R (-1) k = -dgComp R f g (add_zero 0)) :
    homOf R f hf ≫ homOf R g hg = 0 := by
  rw [homOf_comp, homOf_eq_zero_iff, mem_dgBoundaries, dgCompZero_def]
  exact ⟨-k, by rw [map_neg, hk, neg_neg]⟩

/-- An object is a zero object of the homotopy category exactly when it is **contractible**: its
identity is the differential of a degree-minus-one endomorphism. -/
theorem isZero_of_iff_dgId_mem_dgBoundaries (X : C) :
    Limits.IsZero (of R X) ↔ dgId R X ∈ dgBoundaries R X X := by
  rw [Limits.IsZero.iff_id_eq_zero, ← homOf_dgId, homOf_eq_zero_iff]

end DGHomotopyCategory

end

end TauCeti
