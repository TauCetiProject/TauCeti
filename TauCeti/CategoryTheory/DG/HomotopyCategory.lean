/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.CategoryTheory.DG.Basic

/-!
# The homotopy category of a differential graded category

For a differential graded category C, the morphisms in its homotopy category are the
degree-zero cocycles in each Hom complex, modulo the degree-zero coboundaries. Composition is
induced by differential graded composition. The Leibniz rule shows that composing a boundary
with a cycle on either side is again a boundary, so composition descends to cohomology classes.

This file constructs that quotient directly. In particular, it records the concrete criterion
that two closed degree-zero morphisms determine the same morphism precisely when their difference
is the differential of a degree-minus-one morphism. The resulting category is naturally
preadditive and linear over the ground ring.

## Main definitions

* TauCeti.dgCycles: the degree-zero cocycles in a DG Hom complex.
* TauCeti.dgBoundaries: the degree-zero coboundaries in a DG Hom complex.
* TauCeti.DGHomotopyClass: cocycles modulo coboundaries.
* TauCeti.dgHomotopyComp: composition of homotopy classes.
* TauCeti.DGHomotopyCategory: the category with the objects of a DG category and morphisms
  given by DGHomotopyClass.

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

/-- Degree-zero coboundaries, regarded as a submodule of degree-zero cocycles. -/
def dgBoundariesInCycles (X Y : C) : Submodule R (dgCycles R X Y) :=
  (dgBoundaries R X Y).submoduleOf (dgCycles R X Y)

/-- A cocycle belongs to dgBoundariesInCycles exactly when its underlying morphism is a
coboundary. -/
@[simp]
theorem mem_dgBoundariesInCycles {X Y : C} {f : dgCycles R X Y} :
    f ∈ dgBoundariesInCycles R X Y ↔ (f : DGHom R 0 X Y) ∈ dgBoundaries R X Y := by
  rw [dgBoundariesInCycles, Submodule.submoduleOf, Submodule.mem_comap]
  rfl

/-- A morphism in H⁰(C): a degree-zero cocycle modulo degree-zero coboundaries. -/
abbrev DGHomotopyClass (X Y : C) :=
  dgCycles R X Y ⧸ dgBoundariesInCycles R X Y

/-- The linear quotient map from degree-zero cocycles to homotopy classes. -/
def dgHomotopyClassLinearMap (X Y : C) :
    dgCycles R X Y →ₗ[R] DGHomotopyClass R X Y :=
  (dgBoundariesInCycles R X Y).mkQ

/-- The homotopy class represented by a closed degree-zero morphism. -/
def dgHomotopyClass {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    DGHomotopyClass R X Y :=
  dgHomotopyClassLinearMap R X Y ⟨f, hf⟩

/-- A homotopy class is the quotient class of its cocycle representative. -/
theorem dgHomotopyClass_eq_mk {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = Submodule.Quotient.mk ⟨f, hf⟩ :=
  (rfl)

/-- Zero represents zero as a homotopy class. -/
@[simp]
theorem dgHomotopyClass_zero (X Y : C) :
    dgHomotopyClass R (0 : DGHom R 0 X Y) (dgCycles R X Y).zero_mem = 0 :=
  (dgHomotopyClassLinearMap R X Y).map_zero

/-- The class of a sum of cocycles is the sum of their classes. -/
@[simp]
theorem dgHomotopyClass_add {X Y : C} (f g : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    dgHomotopyClass R (f + g) ((dgCycles R X Y).add_mem hf hg) =
      dgHomotopyClass R f hf + dgHomotopyClass R g hg :=
  (dgHomotopyClassLinearMap R X Y).map_add ⟨f, hf⟩ ⟨g, hg⟩

/-- The class of a scalar multiple of a cocycle is the scalar multiple of its class. -/
@[simp]
theorem dgHomotopyClass_smul {X Y : C} (r : R) (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R (r • f) ((dgCycles R X Y).smul_mem r hf) =
      r • dgHomotopyClass R f hf :=
  (dgHomotopyClassLinearMap R X Y).map_smul r ⟨f, hf⟩

/-- Every homotopy class has a closed degree-zero representative. -/
theorem exists_dgHomotopyClass_eq {X Y : C} (c : DGHomotopyClass R X Y) :
    ∃ (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y), dgHomotopyClass R f hf = c := by
  induction c using Submodule.Quotient.induction_on with
  | H f => exact ⟨f, f.2, rfl⟩

/-- Two closed degree-zero morphisms represent the same homotopy class exactly when their
difference is a coboundary. -/
@[simp]
theorem dgHomotopyClass_eq_iff {X Y : C} {f g : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = dgHomotopyClass R g hg ↔
      f - g ∈ dgBoundaries R X Y := by
  simp only [dgHomotopyClass, dgHomotopyClassLinearMap, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, mem_dgBoundariesInCycles]
  rfl

/-- A closed degree-zero morphism represents zero exactly when it is a coboundary. -/
@[simp]
theorem dgHomotopyClass_eq_zero_iff {X Y : C} {f : DGHom R 0 X Y}
    (hf : f ∈ dgCycles R X Y) :
    dgHomotopyClass R f hf = 0 ↔ f ∈ dgBoundaries R X Y := by
  simp only [dgHomotopyClass, dgHomotopyClassLinearMap, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero, mem_dgBoundariesInCycles]

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
    dgCompZero R f g ∈ dgCycles R X Z := by
  rw [dgCompZero_def, mem_dgCycles, dgDifferential_dgComp,
    (mem_dgCycles R).mp hf, (mem_dgCycles R).mp hg]
  simp

/-- Composing a degree-zero boundary on the left with a degree-zero cocycle gives a boundary. -/
theorem dgCompZero_mem_dgBoundaries_of_left {X Y Z : C}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgBoundaries R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgCompZero R f g ∈ dgBoundaries R X Z := by
  obtain ⟨h, rfl⟩ := hf
  refine ⟨dgComp R h g (add_zero (-1)), ?_⟩
  rw [dgDifferential_dgComp, (mem_dgCycles R).mp hg]
  simp only [dgComp_zero, smul_zero, add_zero, dgCompZero_def]

/-- Composing a degree-zero cocycle on the left with a degree-zero boundary gives a boundary. -/
theorem dgCompZero_mem_dgBoundaries_of_right {X Y Z : C}
    {f : DGHom R 0 X Y} {g : DGHom R 0 Y Z}
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgBoundaries R Y Z) :
    dgCompZero R f g ∈ dgBoundaries R X Z := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨dgComp R f h (zero_add (-1)), ?_⟩
  rw [dgDifferential_dgComp, (mem_dgCycles R).mp hf]
  simp only [zero_dgComp, zero_add, Int.negOnePow_zero, one_smul, dgCompZero_def]

/-- Composition restricted to degree-zero cocycles. -/
def dgCyclesComp (X Y Z : C) :
    dgCycles R X Y →ₗ[R] dgCycles R Y Z →ₗ[R] dgCycles R X Z :=
  LinearMap.mk₂ R
    (fun (f : dgCycles R X Y) (g : dgCycles R Y Z) ↦
      ⟨dgCompZero R (X := X) (Y := Y) (Z := Z)
        (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z), dgCompZero_mem_dgCycles R f.2 g.2⟩)
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

/-- Composition of homotopy classes, obtained by descending DG composition through the
coboundary quotients. -/
def dgHomotopyComp (X Y Z : C) :
    DGHomotopyClass R X Y →ₗ[R] DGHomotopyClass R Y Z →ₗ[R]
      DGHomotopyClass R X Z :=
  ((dgCyclesComp R X Y Z).compr₂ (dgBoundariesInCycles R X Z).mkQ).liftQ₂ _ _
    (fun _ hf ↦ LinearMap.ext fun g ↦ (Submodule.Quotient.mk_eq_zero _).mpr <| by
      rw [mem_dgBoundariesInCycles] at hf ⊢
      exact dgCompZero_mem_dgBoundaries_of_left R hf g.2)
    (fun _ hg ↦ LinearMap.ext fun f ↦ (Submodule.Quotient.mk_eq_zero _).mpr <| by
      rw [mem_dgBoundariesInCycles] at hg ⊢
      exact dgCompZero_mem_dgBoundaries_of_right R f.2 hg)

/-- The composite of classes is represented by the DG composite of their representatives. -/
@[simp]
theorem dgHomotopyComp_dgHomotopyClass {X Y Z : C}
    (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgHomotopyComp R X Y Z (dgHomotopyClass R f hf) (dgHomotopyClass R g hg) =
      dgHomotopyClass R (dgCompZero R f g) (dgCompZero_mem_dgCycles R hf hg) := by
  exact LinearMap.liftQ₂_mk _ _ (⟨f, hf⟩ : dgCycles R X Y)
    (⟨g, hg⟩ : dgCycles R Y Z)

/-- Composition of homotopy classes is associative. -/
theorem dgHomotopyComp_assoc {W X Y Z : C}
    (f : DGHomotopyClass R W X) (g : DGHomotopyClass R X Y)
    (h : DGHomotopyClass R Y Z) :
    dgHomotopyComp R W Y Z (dgHomotopyComp R W X Y f g) h =
      dgHomotopyComp R W X Z f (dgHomotopyComp R X Y Z g h) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
  obtain ⟨g, hg, rfl⟩ := exists_dgHomotopyClass_eq R g
  obtain ⟨h, hh, rfl⟩ := exists_dgHomotopyClass_eq R h
  simp only [dgHomotopyComp_dgHomotopyClass]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact dgComp_assoc R f g h rfl rfl rfl

/-! ### The category H⁰(C) -/

/-- The homotopy category of a differential graded category. It has the same objects as C and
the zeroth cohomology of each DG Hom complex as its morphisms. -/
structure DGHomotopyCategory (R : Type v) (C : Type u) where
  /-- The underlying object of the differential graded category. -/
  obj : C

namespace DGHomotopyCategory

/-- Regard an object of a DG category as an object of its homotopy category. -/
@[expose]
def of (X : C) : DGHomotopyCategory R C := ⟨X⟩

/-- Regard an object of a DG homotopy category as an object of the underlying DG category. -/
@[expose]
def underlying (X : DGHomotopyCategory R C) : C := X.obj

omit [CommRing R] [DGCategory R C] in
@[simp]
theorem underlying_of (X : C) : underlying R (of R X) = X := rfl

omit [CommRing R] [DGCategory R C] in
@[simp]
theorem of_underlying (X : DGHomotopyCategory R C) : of R (underlying R X) = X := by
  cases X
  rfl

instance : Quiver (DGHomotopyCategory R C) where
  Hom X Y := DGHomotopyClass R (underlying R X) (underlying R Y)

noncomputable instance : Category (DGHomotopyCategory R C) where
  id X := dgHomotopyClass R (dgId R (underlying R X))
    ((mem_dgCycles R).mpr (dgDifferential_dgId R (underlying R X)))
  comp {X Y Z} f g :=
    dgHomotopyComp R (underlying R X) (underlying R Y) (underlying R Z) f g
  id_comp {X Y} f := by
    obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
    simp only [dgHomotopyComp_dgHomotopyClass]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact dgId_dgComp R f
  comp_id {X Y} f := by
    obtain ⟨f, hf, rfl⟩ := exists_dgHomotopyClass_eq R f
    simp only [dgHomotopyComp_dgHomotopyClass]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact dgComp_dgId R f
  assoc {W X Y Z} f g h := dgHomotopyComp_assoc R f g h

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

/-- A closed degree-zero DG morphism, regarded as a morphism in the homotopy category. -/
def homOf {X Y : C} (f : DGHom R 0 X Y) (hf : f ∈ dgCycles R X Y) :
    of R X ⟶ of R Y :=
  dgHomotopyClass R f hf

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

/-- A closed degree-zero DG morphism represents zero precisely when it is a boundary. -/
@[simp]
theorem homOf_eq_zero_iff {X Y : C} {f : DGHom R 0 X Y} (hf : f ∈ dgCycles R X Y) :
    homOf R f hf = 0 ↔ f ∈ dgBoundaries R X Y :=
  dgHomotopyClass_eq_zero_iff R hf

private theorem homOf_dgId_aux (X : C) :
    homOf R (dgId R X) ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) = 𝟙 (of R X) :=
  rfl

/-- The DG identity represents the identity in the homotopy category. -/
@[simp]
theorem homOf_dgId (X : C) :
    homOf R (dgId R X) ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) = 𝟙 (of R X) :=
  homOf_dgId_aux R X

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

end DGHomotopyCategory

end

end TauCeti
