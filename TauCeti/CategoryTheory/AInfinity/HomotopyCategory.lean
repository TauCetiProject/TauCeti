/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Basic
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# The homotopy category of an A-infinity category

The morphisms in `H⁰(𝒞)` are closed degree-zero morphisms modulo differentials of
degree-minus-one morphisms. Composition is induced by `m₂(g,f)`. Although `m₂` need not be
associative on chains, its associator on cycles is the boundary of `-m₃`, so composition of
classes is associative. Cohomological units suffice to make these classes a category; no
chain-level strict unit or vanishing of higher operations is assumed.

We realize each Hom space as a submodule of the cohomology of the total morphism algebra.
This reuses `AInfinityAlgebra.cohomologyMul` and its associativity rather than descending the
same product a second time. The representative criterion proves that this realization is
exactly the usual degree-zero cycles modulo degree-zero boundaries. In particular, equality
of supported classes cannot introduce boundaries from other Hom spaces or other degrees.

The resulting category is preadditive and linear over the ground ring. Its identities are
independent of the chosen representatives of cohomological units.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
* `TauCeti.Algebra.Homology.AInfinity.Algebra.Cohomology`, for the descended product and
  the arity-three associativity argument.
* `TauCeti.CategoryTheory.DG.HomotopyCategory`, for the categorical representative API.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- The closed degree-zero morphisms from `X` to `Y`. -/
noncomputable def homCyclesZero (X Y : C) : Submodule R (homModule (R := R) X Y) :=
  (grading (R := R) X Y).piece 0 ⊓ LinearMap.ker (𝒞.homDifferential X Y)

/-- A degree-zero cycle is a degree-zero morphism killed by `m₁`. -/
@[simp]
theorem mem_homCyclesZero {X Y : C} {f : homModule (R := R) X Y} :
    f ∈ 𝒞.homCyclesZero X Y ↔
      f ∈ (grading (R := R) X Y).piece 0 ∧ 𝒞.homDifferential X Y f = 0 :=
  Iff.rfl

/-- Including a closed morphism gives a cycle in the total morphism algebra. -/
theorem homInclusion_mem_cycles {X Y : C} {f : homModule (R := R) X Y}
    (hf : 𝒞.homDifferential X Y f = 0) :
    homInclusion X Y f ∈ 𝒞.toAInfinityAlgebra.cycles := by
  rw [𝒞.toAInfinityAlgebra.cycles_def, LinearMap.mem_ker,
    ← 𝒞.homInclusion_homDifferential, hf, map_zero]

/-- The linear map sending a closed degree-zero morphism to its total cohomology class. -/
noncomputable def homClassLinearMap (X Y : C) :
    𝒞.homCyclesZero X Y →ₗ[R] 𝒞.toAInfinityAlgebra.Cohomology :=
  𝒞.toAInfinityAlgebra.cohomologyClassLinearMap ∘ₗ
    (homInclusion X Y ∘ₗ (𝒞.homCyclesZero X Y).subtype).codRestrict _
      (fun f ↦ 𝒞.homInclusion_mem_cycles ((𝒞.mem_homCyclesZero).mp f.property).2)

/-- The class map sends a closed degree-zero morphism to the class of its inclusion. -/
@[simp]
theorem homClassLinearMap_apply {X Y : C} (f : 𝒞.homCyclesZero X Y) :
    𝒞.homClassLinearMap X Y f = 𝒞.toAInfinityAlgebra.cohomologyClass
      (𝒞.homInclusion_mem_cycles ((𝒞.mem_homCyclesZero).mp f.property).2) := by
  rw [homClassLinearMap, LinearMap.comp_apply,
    𝒞.toAInfinityAlgebra.cohomologyClassLinearMap_apply]
  rfl

/-- The image of closed degree-zero morphisms in total cohomology. This is the Hom space
of the homotopy category, realized without a second quotient construction. -/
noncomputable def homCohomologyZero (X Y : C) :
    Submodule R 𝒞.toAInfinityAlgebra.Cohomology :=
  LinearMap.range (𝒞.homClassLinearMap X Y)

/-- The class of a closed degree-zero morphism, in its own Hom space. -/
noncomputable def homClass {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) : 𝒞.homCohomologyZero X Y :=
  ⟨𝒞.homClassLinearMap X Y ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩⟩

/-- The underlying total cohomology class of a Hom class. -/
@[simp]
theorem coe_homClass {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    (𝒞.homClass f hf : 𝒞.toAInfinityAlgebra.Cohomology) =
      𝒞.toAInfinityAlgebra.cohomologyClass
        (𝒞.homInclusion_mem_cycles ((𝒞.mem_homCyclesZero).mp hf).2) := by
  dsimp only [homClass]
  exact 𝒞.homClassLinearMap_apply ⟨f, hf⟩

/-- A total class belongs to a Hom space precisely when it has a closed degree-zero
representative in that Hom module. -/
theorem mem_homCohomologyZero_iff {X Y : C} {a : 𝒞.toAInfinityAlgebra.Cohomology} :
    a ∈ 𝒞.homCohomologyZero X Y ↔
      ∃ (f : homModule (R := R) X Y) (hf : f ∈ 𝒞.homCyclesZero X Y),
        𝒞.toAInfinityAlgebra.cohomologyClass
          (𝒞.homInclusion_mem_cycles ((𝒞.mem_homCyclesZero).mp hf).2) = a := by
  rw [homCohomologyZero, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, f.property, (𝒞.homClassLinearMap_apply f).symm.trans hf⟩
  · rintro ⟨f, hf, ha⟩
    exact ⟨⟨f, hf⟩, (𝒞.homClassLinearMap_apply ⟨f, hf⟩).trans ha⟩

/-- Every Hom class has a closed degree-zero representative. -/
theorem exists_homClass_eq {X Y : C} (a : 𝒞.homCohomologyZero X Y) :
    ∃ (f : homModule (R := R) X Y) (hf : f ∈ 𝒞.homCyclesZero X Y),
      𝒞.homClass f hf = a := by
  obtain ⟨f, hf⟩ := a.property
  exact ⟨f, f.property, Subtype.ext hf⟩

/-- Zero represents the zero Hom class. -/
@[simp]
theorem homClass_zero (X Y : C) :
    𝒞.homClass (0 : homModule (R := R) X Y) (𝒞.homCyclesZero X Y).zero_mem = 0 := by
  apply Subtype.ext
  exact (𝒞.homClassLinearMap X Y).map_zero

/-- Taking a Hom class respects addition. -/
@[simp]
theorem homClass_add {X Y : C} (f g : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) (hg : g ∈ 𝒞.homCyclesZero X Y) :
    𝒞.homClass (f + g) ((𝒞.homCyclesZero X Y).add_mem hf hg) =
      𝒞.homClass f hf + 𝒞.homClass g hg := by
  apply Subtype.ext
  exact (𝒞.homClassLinearMap X Y).map_add ⟨f, hf⟩ ⟨g, hg⟩

/-- Taking a Hom class respects negation. -/
@[simp]
theorem homClass_neg {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    𝒞.homClass (-f) ((𝒞.homCyclesZero X Y).neg_mem hf) = -𝒞.homClass f hf := by
  apply Subtype.ext
  exact (𝒞.homClassLinearMap X Y).map_neg ⟨f, hf⟩

/-- Taking a Hom class respects subtraction. -/
@[simp]
theorem homClass_sub {X Y : C} (f g : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) (hg : g ∈ 𝒞.homCyclesZero X Y) :
    𝒞.homClass (f - g) ((𝒞.homCyclesZero X Y).sub_mem hf hg) =
      𝒞.homClass f hf - 𝒞.homClass g hg := by
  apply Subtype.ext
  exact (𝒞.homClassLinearMap X Y).map_sub ⟨f, hf⟩ ⟨g, hg⟩

/-- Taking a Hom class respects scalar multiplication. -/
@[simp]
theorem homClass_smul {X Y : C} (r : R) (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    𝒞.homClass (r • f) ((𝒞.homCyclesZero X Y).smul_mem r hf) =
      r • 𝒞.homClass f hf := by
  apply Subtype.ext
  exact (𝒞.homClassLinearMap X Y).map_smul r ⟨f, hf⟩

/-- Two closed degree-zero morphisms represent the same Hom class exactly when their
difference is the differential of a degree-minus-one morphism. -/
@[simp]
theorem homClass_eq_iff {X Y : C} {f g : homModule (R := R) X Y}
    (hf : f ∈ 𝒞.homCyclesZero X Y) (hg : g ∈ 𝒞.homCyclesZero X Y) :
    𝒞.homClass f hf = 𝒞.homClass g hg ↔
      ∃ h : grHom R X Y (-1), 𝒞.homDifferential X Y h = f - g := by
  rw [Subtype.ext_iff, coe_homClass, coe_homClass,
    𝒞.toAInfinityAlgebra.cohomologyClass_eq_iff, ← map_sub,
    𝒞.toAInfinityAlgebra.boundaries_def, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    -- Keep only the degree-minus-one part of a total primitive, then its `(X,Y)` component.
    let z := (DirectSum.decompose 𝒞.grading.piece y (-1) : TotalHom R C)
    have hz : z ∈ (totalGrading R C).piece (-1) := by
      rw [← 𝒞.grading_eq]
      exact (DirectSum.decompose 𝒞.grading.piece y (-1)).property
    have hdeg : homInclusion X Y (f - g) ∈ 𝒞.grading.piece 0 := by
      rw [𝒞.grading_eq, homInclusion_mem_totalGrading_piece_iff]
      exact ((grading (R := R) X Y).piece 0).sub_mem hf.1 hg.1
    have hdz : 𝒞.differential z = homInclusion X Y (f - g) := by
      rw [𝒞.toAInfinityAlgebra.differential_decompose, hy]
      exact DirectSum.decompose_of_mem_same _ hdeg
    refine ⟨⟨homProjection X Y z, homProjection_mem_piece hz X Y⟩, ?_⟩
    rw [← 𝒞.homProjection_differential, hdz, homProjection_homInclusion]
  · rintro ⟨h, hh⟩
    exact ⟨homInclusion X Y h, by rw [← 𝒞.homInclusion_homDifferential, hh]⟩

/-- A closed degree-zero morphism represents zero exactly when it is a boundary. -/
@[simp]
theorem homClass_eq_zero_iff {X Y : C} {f : homModule (R := R) X Y}
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    𝒞.homClass f hf = 0 ↔
      ∃ h : grHom R X Y (-1), 𝒞.homDifferential X Y h = f := by
  rw [← 𝒞.homClass_zero X Y, 𝒞.homClass_eq_iff]
  simp only [sub_zero]

/-- The composite of two closed degree-zero morphisms is closed of degree zero. -/
theorem comp_mem_homCyclesZero {X Y Z : C} {g : homModule (R := R) Y Z}
    {f : homModule (R := R) X Y} (hg : g ∈ 𝒞.homCyclesZero Y Z)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    𝒞.comp X Y Z g f ∈ 𝒞.homCyclesZero X Z := by
  rw [𝒞.mem_homCyclesZero] at hg hf ⊢
  constructor
  · simpa using 𝒞.comp_mem_piece hg.1 hf.1
  · rw [𝒞.homDifferential_comp hg.1, hg.2, hf.2]
    simp

/-- Multiplication in total cohomology computes the class of a composite in Keller order. -/
theorem cohomologyMul_homClass {X Y Z : C} (g : homModule (R := R) Y Z)
    (f : homModule (R := R) X Y) (hg : g ∈ 𝒞.homCyclesZero Y Z)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    𝒞.toAInfinityAlgebra.cohomologyMul (𝒞.homClass g hg) (𝒞.homClass f hf) =
      (𝒞.homClass (𝒞.comp X Y Z g f) (𝒞.comp_mem_homCyclesZero hg hf) :
        𝒞.toAInfinityAlgebra.Cohomology) := by
  rw [coe_homClass, coe_homClass,
    𝒞.toAInfinityAlgebra.cohomologyMul_cohomologyClass, coe_homClass]
  congr 1
  exact (𝒞.homInclusion_comp X Y Z g f).symm

/-- Total cohomology multiplication carries composable Hom classes to their endpoint Hom space. -/
theorem cohomologyMul_mem_homCohomologyZero {X Y Z : C}
    (g : 𝒞.homCohomologyZero Y Z) (f : 𝒞.homCohomologyZero X Y) :
    𝒞.toAInfinityAlgebra.cohomologyMul g f ∈ 𝒞.homCohomologyZero X Z := by
  obtain ⟨g, hg, rfl⟩ := 𝒞.exists_homClass_eq g
  obtain ⟨f, hf, rfl⟩ := 𝒞.exists_homClass_eq f
  rw [𝒞.cohomologyMul_homClass]
  exact (𝒞.homClass _ _).property

/-- Bilinear composition of Hom classes, in categorical order `f` followed by `g`. -/
noncomputable def homCohomologyComp (X Y Z : C) :
    𝒞.homCohomologyZero X Y →ₗ[R] 𝒞.homCohomologyZero Y Z →ₗ[R]
      𝒞.homCohomologyZero X Z :=
  LinearMap.mk₂ R
    (fun f g ↦ ⟨𝒞.toAInfinityAlgebra.cohomologyMul g f,
      𝒞.cohomologyMul_mem_homCohomologyZero g f⟩)
    (fun f f' g ↦ Subtype.ext <| (𝒞.toAInfinityAlgebra.cohomologyMul g).map_add f f')
    (fun r f g ↦ Subtype.ext <| (𝒞.toAInfinityAlgebra.cohomologyMul g).map_smul r f)
    (fun f g g' ↦ Subtype.ext <| 𝒞.toAInfinityAlgebra.cohomologyMul.map_add₂ g g' f)
    (fun r f g ↦ Subtype.ext <| 𝒞.toAInfinityAlgebra.cohomologyMul.map_smul₂ r g f)

/-- The underlying total class of composition is multiplication with the factors reversed. -/
@[simp]
theorem coe_homCohomologyComp {X Y Z : C}
    (f : 𝒞.homCohomologyZero X Y) (g : 𝒞.homCohomologyZero Y Z) :
    (𝒞.homCohomologyComp X Y Z f g : 𝒞.toAInfinityAlgebra.Cohomology) =
      𝒞.toAInfinityAlgebra.cohomologyMul g f :=
  (rfl)

/-- Composition is represented by `m₂(g,f)`. -/
@[simp]
theorem homCohomologyComp_homClass {X Y Z : C} (f : homModule (R := R) X Y)
    (g : homModule (R := R) Y Z) (hf : f ∈ 𝒞.homCyclesZero X Y)
    (hg : g ∈ 𝒞.homCyclesZero Y Z) :
    𝒞.homCohomologyComp X Y Z (𝒞.homClass f hf) (𝒞.homClass g hg) =
      𝒞.homClass (𝒞.comp X Y Z g f) (𝒞.comp_mem_homCyclesZero hg hf) := by
  apply Subtype.ext
  exact 𝒞.cohomologyMul_homClass g f hg hf

/-- Composition of classes is associative, even when `m₂` on chains is not. -/
theorem homCohomologyComp_assoc {W X Y Z : C} (f : 𝒞.homCohomologyZero W X)
    (g : 𝒞.homCohomologyZero X Y) (h : 𝒞.homCohomologyZero Y Z) :
    𝒞.homCohomologyComp W Y Z (𝒞.homCohomologyComp W X Y f g) h =
      𝒞.homCohomologyComp W X Z f (𝒞.homCohomologyComp X Y Z g h) := by
  apply Subtype.ext
  simp only [coe_homCohomologyComp]
  exact (𝒞.toAInfinityAlgebra.cohomologyMul_assoc h g f).symm

/-- A family of cohomological-unit representatives. Each is a closed degree-zero endomorphism;
its left and right products with every closed morphism are identities modulo boundaries.
There are no strict chain-level unit equations or conditions on higher operations. -/
structure CohomologicalUnits (e : ∀ X : C, homModule (R := R) X X) : Prop where
  /-- The chosen endomorphisms are closed of degree zero. -/
  cycle : ∀ X, e X ∈ 𝒞.homCyclesZero X X
  /-- Left multiplication acts as the identity on cohomology in every degree. -/
  left_unit : ∀ (X Y : C) (f : homModule (R := R) X Y), 𝒞.homDifferential X Y f = 0 →
    𝒞.comp X Y Y (e Y) f - f ∈ LinearMap.range (𝒞.homDifferential X Y)
  /-- Right multiplication acts as the identity on cohomology in every degree. -/
  right_unit : ∀ (X Y : C) (f : homModule (R := R) X Y), 𝒞.homDifferential X Y f = 0 →
    𝒞.comp X X Y f (e X) - f ∈ LinearMap.range (𝒞.homDifferential X Y)

namespace CohomologicalUnits

variable {𝒞} {e e' : ∀ X : C, homModule (R := R) X X}

/-- A chosen cohomological unit gives a left identity on Hom classes. -/
@[simp]
theorem id_comp (he : 𝒞.CohomologicalUnits e) {X Y : C}
    (f : 𝒞.homCohomologyZero X Y) :
    𝒞.homCohomologyComp X X Y (𝒞.homClass (e X) (he.cycle X)) f = f := by
  obtain ⟨f, hf, rfl⟩ := 𝒞.exists_homClass_eq f
  apply Subtype.ext
  rw [coe_homCohomologyComp, cohomologyMul_homClass,
    coe_homClass, coe_homClass, 𝒞.toAInfinityAlgebra.cohomologyClass_eq_iff, ← map_sub,
    𝒞.toAInfinityAlgebra.boundaries_def, LinearMap.mem_range]
  obtain ⟨h, hh⟩ := he.right_unit X Y f ((𝒞.mem_homCyclesZero).mp hf).2
  exact ⟨homInclusion X Y h, by rw [← 𝒞.homInclusion_homDifferential, hh]⟩

/-- A chosen cohomological unit gives a right identity on Hom classes. -/
@[simp]
theorem comp_id (he : 𝒞.CohomologicalUnits e) {X Y : C}
    (f : 𝒞.homCohomologyZero X Y) :
    𝒞.homCohomologyComp X Y Y f (𝒞.homClass (e Y) (he.cycle Y)) = f := by
  obtain ⟨f, hf, rfl⟩ := 𝒞.exists_homClass_eq f
  apply Subtype.ext
  rw [coe_homCohomologyComp, cohomologyMul_homClass,
    coe_homClass, coe_homClass, 𝒞.toAInfinityAlgebra.cohomologyClass_eq_iff, ← map_sub,
    𝒞.toAInfinityAlgebra.boundaries_def, LinearMap.mem_range]
  obtain ⟨h, hh⟩ := he.left_unit X Y f ((𝒞.mem_homCyclesZero).mp hf).2
  exact ⟨homInclusion X Y h, by rw [← 𝒞.homInclusion_homDifferential, hh]⟩

/-- The identity class is independent of its cohomological-unit representative. -/
theorem homClass_eq (he : 𝒞.CohomologicalUnits e) (he' : 𝒞.CohomologicalUnits e') (X : C) :
    𝒞.homClass (e X) (he.cycle X) = 𝒞.homClass (e' X) (he'.cycle X) := by
  have h := he.id_comp (𝒞.homClass (e' X) (he'.cycle X))
  rw [he'.comp_id] at h
  exact h

end CohomologicalUnits

/-- An `A∞` category is cohomologically unital if it has cohomological-unit representatives. -/
def CohomologicallyUnital : Prop :=
  ∃ e, 𝒞.CohomologicalUnits e

/-- Cohomological unitality is the existence of unit representatives. -/
theorem cohomologicallyUnital_iff :
    𝒞.CohomologicallyUnital ↔ ∃ e, 𝒞.CohomologicalUnits e := by
  rw [CohomologicallyUnital]

end AInfinityCategory

/-- The objects of the homotopy category of a cohomologically unital `A∞` category. -/
structure AInfinityHomotopyCategory {R : Type w} [CommRing R] {C : Type u}
    [GradedLinearQuiver.{u, v, w} R C] (𝒞 : AInfinityCategory R C)
    (h𝒞 : 𝒞.CohomologicallyUnital) where
  /-- The underlying object. -/
  obj : C

namespace AInfinityHomotopyCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  {𝒞 : AInfinityCategory R C} {h𝒞 : 𝒞.CohomologicallyUnital}

/-- Regard an object as an object of its `A∞` homotopy category. -/
abbrev of (X : C) : AInfinityHomotopyCategory 𝒞 h𝒞 := ⟨X⟩

@[simp]
theorem obj_of (X : C) : (of (𝒞 := 𝒞) (h𝒞 := h𝒞) X).obj = X :=
  (rfl)

@[simp]
theorem of_obj (X : AInfinityHomotopyCategory 𝒞 h𝒞) : of X.obj = X := by
  cases X
  rfl

/-- Objects of `H⁰(𝒞)` are determined by their underlying objects. -/
@[ext]
theorem ext {X Y : AInfinityHomotopyCategory 𝒞 h𝒞} (h : X.obj = Y.obj) : X = Y := by
  rw [← of_obj X, ← of_obj Y, h]

noncomputable instance : Category (AInfinityHomotopyCategory 𝒞 h𝒞) where
  Hom X Y := 𝒞.homCohomologyZero X.obj Y.obj
  id X := 𝒞.homClass ((𝒞.cohomologicallyUnital_iff.mp h𝒞).choose X.obj)
    ((𝒞.cohomologicallyUnital_iff.mp h𝒞).choose_spec.cycle X.obj)
  comp {X Y Z} f g := 𝒞.homCohomologyComp X.obj Y.obj Z.obj f g
  id_comp f := (𝒞.cohomologicallyUnital_iff.mp h𝒞).choose_spec.id_comp f
  comp_id f := (𝒞.cohomologicallyUnital_iff.mp h𝒞).choose_spec.comp_id f
  assoc f g h := 𝒞.homCohomologyComp_assoc f g h

noncomputable instance : Preadditive (AInfinityHomotopyCategory 𝒞 h𝒞) where
  homGroup X Y := inferInstanceAs (AddCommGroup (𝒞.homCohomologyZero X.obj Y.obj))
  add_comp X Y Z f f' g := (𝒞.homCohomologyComp X.obj Y.obj Z.obj).map_add₂ f f' g
  comp_add X Y Z f g g' := (𝒞.homCohomologyComp X.obj Y.obj Z.obj f).map_add g g'

noncomputable instance : Linear R (AInfinityHomotopyCategory 𝒞 h𝒞) where
  homModule X Y := inferInstanceAs (Module R (𝒞.homCohomologyZero X.obj Y.obj))
  smul_comp X Y Z r f g := (𝒞.homCohomologyComp X.obj Y.obj Z.obj).map_smul₂ r f g
  comp_smul X Y Z f r g := (𝒞.homCohomologyComp X.obj Y.obj Z.obj f).map_smul r g

/-- Composition in `H⁰(𝒞)` is the descended binary operation in categorical order. -/
theorem comp_def {X Y Z : AInfinityHomotopyCategory 𝒞 h𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = 𝒞.homCohomologyComp X.obj Y.obj Z.obj f g :=
  (rfl)

/-- Any cohomological-unit representative gives the categorical identity. -/
theorem id_eq_homClass {e : ∀ X : C, homModule (R := R) X X}
    (he : 𝒞.CohomologicalUnits e) (X : AInfinityHomotopyCategory 𝒞 h𝒞) :
    𝟙 X = 𝒞.homClass (e X.obj) (he.cycle X.obj) :=
  (𝒞.cohomologicallyUnital_iff.mp h𝒞).choose_spec.homClass_eq he X.obj

/-- A closed degree-zero morphism defines a morphism in `H⁰(𝒞)`. -/
noncomputable def homOf {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    of (𝒞 := 𝒞) (h𝒞 := h𝒞) X ⟶ of Y :=
  𝒞.homClass f hf

/-- Taking a morphism to `H⁰(𝒞)` is taking its Hom class. -/
theorem homOf_def {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) f hf = 𝒞.homClass f hf :=
  (rfl)

/-- Every morphism in `H⁰(𝒞)` has a closed degree-zero representative. -/
theorem exists_homOf_eq {X Y : C} (a : of (𝒞 := 𝒞) (h𝒞 := h𝒞) X ⟶ of Y) :
    ∃ (f : homModule (R := R) X Y) (hf : f ∈ 𝒞.homCyclesZero X Y), homOf f hf = a :=
  𝒞.exists_homClass_eq a

/-- The zero morphism represents zero in `H⁰(𝒞)`. -/
@[simp]
theorem homOf_zero (X Y : C) :
    homOf (h𝒞 := h𝒞) (0 : homModule (R := R) X Y) (𝒞.homCyclesZero X Y).zero_mem = 0 :=
  𝒞.homClass_zero X Y

/-- Taking a morphism to `H⁰(𝒞)` preserves addition. -/
@[simp]
theorem homOf_add {X Y : C} (f g : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) (hg : g ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) (f + g) ((𝒞.homCyclesZero X Y).add_mem hf hg) =
      homOf f hf + homOf g hg :=
  𝒞.homClass_add f g hf hg

/-- Taking a morphism to `H⁰(𝒞)` preserves negation. -/
@[simp]
theorem homOf_neg {X Y : C} (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) (-f) ((𝒞.homCyclesZero X Y).neg_mem hf) = -homOf f hf :=
  𝒞.homClass_neg f hf

/-- Taking a morphism to `H⁰(𝒞)` preserves subtraction. -/
@[simp]
theorem homOf_sub {X Y : C} (f g : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) (hg : g ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) (f - g) ((𝒞.homCyclesZero X Y).sub_mem hf hg) =
      homOf f hf - homOf g hg :=
  𝒞.homClass_sub f g hf hg

/-- Taking a morphism to `H⁰(𝒞)` preserves scalar multiplication. -/
@[simp]
theorem homOf_smul {X Y : C} (r : R) (f : homModule (R := R) X Y)
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) (r • f) ((𝒞.homCyclesZero X Y).smul_mem r hf) =
      r • homOf f hf :=
  𝒞.homClass_smul r f hf

/-- A closed morphism represents zero in `H⁰(𝒞)` exactly when it is a boundary. -/
@[simp]
theorem homOf_eq_zero_iff {X Y : C} {f : homModule (R := R) X Y}
    (hf : f ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) f hf = 0 ↔
      ∃ h : grHom R X Y (-1), 𝒞.homDifferential X Y h = f :=
  𝒞.homClass_eq_zero_iff hf

/-- Composition in `H⁰(𝒞)` is represented by `m₂(g,f)`. -/
@[simp]
theorem homOf_comp {X Y Z : C} (f : homModule (R := R) X Y)
    (g : homModule (R := R) Y Z) (hf : f ∈ 𝒞.homCyclesZero X Y)
    (hg : g ∈ 𝒞.homCyclesZero Y Z) :
    homOf (h𝒞 := h𝒞) f hf ≫ homOf g hg =
      homOf (𝒞.comp X Y Z g f) (𝒞.comp_mem_homCyclesZero hg hf) :=
  𝒞.homCohomologyComp_homClass f g hf hg

/-- A cohomological-unit representative gives the identity of `H⁰(𝒞)`. -/
@[simp]
theorem homOf_unit {e : ∀ X : C, homModule (R := R) X X}
    (he : 𝒞.CohomologicalUnits e) (X : C) :
    homOf (h𝒞 := h𝒞) (e X) (he.cycle X) = 𝟙 (of X) :=
  (id_eq_homClass he (of X)).symm

/-- Equality in `H⁰(𝒞)` is homotopy by a degree-minus-one morphism. -/
@[simp]
theorem homOf_eq_iff {X Y : C} {f g : homModule (R := R) X Y}
    (hf : f ∈ 𝒞.homCyclesZero X Y) (hg : g ∈ 𝒞.homCyclesZero X Y) :
    homOf (h𝒞 := h𝒞) f hf = homOf g hg ↔
      ∃ h : grHom R X Y (-1), 𝒞.homDifferential X Y h = f - g :=
  𝒞.homClass_eq_iff hf hg

end AInfinityHomotopyCategory

end TauCeti
