/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Biproduct
public import Mathlib.CategoryTheory.Retract

/-!
# Null-homotopic maps factor through elementary disks

For curved duplexes of the same curvature, the boundary of an odd map factors through the
direct sum of a disk and a parity-shifted disk. Conversely, this direct sum is contractible,
so every morphism factoring through it is null-homotopic. In particular, a contractible duplex
is a retract of the disk sum on its two components. This gives the concrete factorization
needed to compare the homotopy quotient with a stable quotient of a split exact category.

The disk sum is functorial (`diskSumMap`), and the projection `diskSumToParityShift` from the
disk sum onto the parity shift kills the inclusion `toDiskSum`. The resulting sequence
`X ⟶ diskSum X ⟶ X[1]` splits in both components; it presents the stable suspension of `X` as
its parity shift.

The disk construction and its role in the homotopy category follow Frenkel, Khovanov and
Schiffmann, *Homological realization of Nakajima varieties and Weyl group actions*, Sections 2–3.
-/

public section

universe w' v u

namespace TauCeti.CurvedDuplex

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w'} [Semiring R] [Linear R C] {w : R}
  {X Y : CurvedDuplex C w}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The two elementary disks associated to the components of a duplex, with the disk on the
even component shifted in parity. -/
-- The component types in the public map formulas require this constructor to be exposed.
@[expose] noncomputable def diskSum (X : CurvedDuplex C w) : CurvedDuplex C w :=
  biprod (disk w X.X₁) ((parityShift C w).obj (disk w X.X₀))

@[simp] theorem diskSum_X₀ (X : CurvedDuplex C w) :
    (diskSum X).X₀ = (X.X₁ ⊞ X.X₀) := rfl

@[simp] theorem diskSum_X₁ (X : CurvedDuplex C w) :
    (diskSum X).X₁ = (X.X₁ ⊞ X.X₀) := rfl

@[simp] theorem diskSum_d₀ (X : CurvedDuplex C w) :
    (diskSum X).d₀ = CategoryTheory.Limits.biprod.map (𝟙 X.X₁) (-(w • 𝟙 X.X₀)) := rfl

@[simp] theorem diskSum_d₁ (X : CurvedDuplex C w) :
    (diskSum X).d₁ = CategoryTheory.Limits.biprod.map (w • 𝟙 X.X₁) (-𝟙 X.X₀) := rfl

/-- The canonical map from a duplex to the disk on its odd component. -/
def toOddDisk (X : CurvedDuplex C w) : X ⟶ disk w X.X₁ where
  f₀ := X.d₀
  f₁ := 𝟙 X.X₁
  comm₀ := by simp
  comm₁ := by simp

/-- The canonical map from a duplex to the shifted disk on its even component. -/
def toEvenShiftedDisk (X : CurvedDuplex C w) :
    X ⟶ (parityShift C w).obj (disk w X.X₀) where
  f₀ := 𝟙 X.X₀
  f₁ := -X.d₁
  comm₀ := by simp
  comm₁ := by simp

/-- The map out of the odd disk determined by the odd-to-even part of a homotopy. -/
def fromOddDisk (h₁ : X.X₁ ⟶ Y.X₀) : disk w X.X₁ ⟶ Y :=
  (diskHomEquiv X.X₁ Y).symm h₁

/-- The map out of the shifted even disk determined by the even-to-odd part of a homotopy. -/
def fromEvenShiftedDisk (h₀ : X.X₀ ⟶ Y.X₁) :
    (parityShift C w).obj (disk w X.X₀) ⟶ Y where
  f₀ := h₀ ≫ Y.d₁
  f₁ := -h₀
  comm₀ := by simp
  comm₁ := by simp

omit [HasBinaryBiproducts C] in
@[simp] theorem toOddDisk_f₀ (X : CurvedDuplex C w) :
    (toOddDisk X).f₀ = X.d₀ := by rfl

omit [HasBinaryBiproducts C] in
@[simp] theorem toOddDisk_f₁ (X : CurvedDuplex C w) :
    (toOddDisk X).f₁ = 𝟙 X.X₁ := by rfl

omit [HasBinaryBiproducts C] in
@[simp] theorem toEvenShiftedDisk_f₀ (X : CurvedDuplex C w) :
    (toEvenShiftedDisk X).f₀ = 𝟙 X.X₀ := by rfl

omit [HasBinaryBiproducts C] in
@[simp] theorem toEvenShiftedDisk_f₁ (X : CurvedDuplex C w) :
    (toEvenShiftedDisk X).f₁ = -X.d₁ := by rfl

omit [HasBinaryBiproducts C] in
@[simp] theorem fromOddDisk_f₀ (h₁ : X.X₁ ⟶ Y.X₀) :
    (fromOddDisk h₁).f₀ = h₁ := by simp [fromOddDisk]

omit [HasBinaryBiproducts C] in
@[simp] theorem fromOddDisk_f₁ (h₁ : X.X₁ ⟶ Y.X₀) :
    (fromOddDisk h₁).f₁ = h₁ ≫ Y.d₀ := by simp [fromOddDisk]

omit [HasBinaryBiproducts C] in
@[simp] theorem fromEvenShiftedDisk_f₀ (h₀ : X.X₀ ⟶ Y.X₁) :
    (fromEvenShiftedDisk h₀).f₀ = h₀ ≫ Y.d₁ := by rfl

omit [HasBinaryBiproducts C] in
@[simp] theorem fromEvenShiftedDisk_f₁ (h₀ : X.X₀ ⟶ Y.X₁) :
    (fromEvenShiftedDisk h₀).f₁ = -h₀ := by rfl

/-- The map into the two disks determined by the source duplex. -/
noncomputable def toDiskSum (X : CurvedDuplex C w) : X ⟶ diskSum X :=
  biprodLift (toOddDisk X) (toEvenShiftedDisk X)

/-- The map out of the two disks determined by an odd homotopy. -/
noncomputable def fromDiskSum (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    diskSum X ⟶ Y :=
  biprodDesc (fromOddDisk h₁) (fromEvenShiftedDisk h₀)

@[simp] theorem toDiskSum_f₀ (X : CurvedDuplex C w) :
    (toDiskSum X).f₀ = CategoryTheory.Limits.biprod.lift X.d₀ (𝟙 X.X₀) := by
  simp [toDiskSum, toOddDisk, toEvenShiftedDisk]

@[simp] theorem toDiskSum_f₁ (X : CurvedDuplex C w) :
    (toDiskSum X).f₁ = CategoryTheory.Limits.biprod.lift (𝟙 X.X₁) (-X.d₁) := by
  simp [toDiskSum, toOddDisk, toEvenShiftedDisk]

@[simp] theorem fromDiskSum_f₀ (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    (fromDiskSum h₀ h₁).f₀ =
      CategoryTheory.Limits.biprod.desc h₁ (h₀ ≫ Y.d₁) := by
  simp [fromDiskSum, fromOddDisk, fromEvenShiftedDisk]

@[simp] theorem fromDiskSum_f₁ (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    (fromDiskSum h₀ h₁).f₁ =
      CategoryTheory.Limits.biprod.desc (h₁ ≫ Y.d₀) (-h₀) := by
  simp [fromDiskSum, fromOddDisk, fromEvenShiftedDisk]

/-- A homotopy boundary factors through the direct sum of two elementary disks. -/
@[simp] theorem toDiskSum_comp_fromDiskSum (h₀ : X.X₀ ⟶ Y.X₁) (h₁ : X.X₁ ⟶ Y.X₀) :
    toDiskSum X ≫ fromDiskSum h₀ h₁ = nullHomotopicMap h₀ h₁ := by
  ext <;> simp [toDiskSum, fromDiskSum, fromOddDisk, fromEvenShiftedDisk,
    toOddDisk, toEvenShiftedDisk, diskSum, biprod.lift_desc, add_comm]

/-- The map from the disk sum on the components of `X` onto the parity shift of `X`. Together with
`toDiskSum X` it forms a short complex `X ⟶ diskSum X ⟶ X[1]` which splits in both components. -/
noncomputable def diskSumToParityShift (X : CurvedDuplex C w) :
    diskSum X ⟶ (parityShift C w).obj X where
  f₀ := biprod.desc (𝟙 X.X₁) (-X.d₀)
  f₁ := biprod.desc (-X.d₁) (-𝟙 X.X₀)
  comm₀ := by apply biprod.hom_ext' <;> simp
  comm₁ := by apply biprod.hom_ext' <;> simp

@[simp]
theorem diskSumToParityShift_f₀ (X : CurvedDuplex C w) :
    (diskSumToParityShift X).f₀ = biprod.desc (𝟙 X.X₁) (-X.d₀) := (rfl)

@[simp]
theorem diskSumToParityShift_f₁ (X : CurvedDuplex C w) :
    (diskSumToParityShift X).f₁ = biprod.desc (-X.d₁) (-𝟙 X.X₀) := (rfl)

/-- The inclusion of a duplex into its disk sum, followed by the projection onto its parity shift,
vanishes. -/
@[reassoc (attr := simp)]
theorem toDiskSum_comp_diskSumToParityShift (X : CurvedDuplex C w) :
    toDiskSum X ≫ diskSumToParityShift X = 0 := by
  ext <;> simp [diskSumToParityShift]

/-- The map induced on disk sums by a morphism of curved duplexes. -/
noncomputable def diskSumMap {X Y : CurvedDuplex C w} (f : X ⟶ Y) : diskSum X ⟶ diskSum Y where
  f₀ := biprod.map f.f₁ f.f₀
  f₁ := biprod.map f.f₁ f.f₀
  comm₀ := by apply biprod.hom_ext' <;> simp
  comm₁ := by apply biprod.hom_ext' <;> simp

@[simp]
theorem diskSumMap_f₀ {X Y : CurvedDuplex C w} (f : X ⟶ Y) :
    (diskSumMap f).f₀ = biprod.map f.f₁ f.f₀ := (rfl)

@[simp]
theorem diskSumMap_f₁ {X Y : CurvedDuplex C w} (f : X ⟶ Y) :
    (diskSumMap f).f₁ = biprod.map f.f₁ f.f₀ := (rfl)

/-- The inclusion into the disk sum is natural. -/
@[reassoc (attr := simp)]
theorem toDiskSum_comp_diskSumMap {X Y : CurvedDuplex C w} (f : X ⟶ Y) :
    toDiskSum X ≫ diskSumMap f = f ≫ toDiskSum Y := by
  ext <;> apply biprod.hom_ext <;> simp [Hom.comm₀, Hom.comm₁]

/-- The projection from the disk sum onto the parity shift is natural. -/
@[reassoc (attr := simp)]
theorem diskSumToParityShift_comp_parityShift_map {X Y : CurvedDuplex C w} (f : X ⟶ Y) :
    diskSumToParityShift X ≫ (parityShift C w).map f = diskSumMap f ≫ diskSumToParityShift Y := by
  ext <;> apply biprod.hom_ext' <;> simp [Hom.comm₀, Hom.comm₁]

/-- The disk sum itself is contractible. -/
theorem id_diskSum_mem_nullHomotopic (X : CurvedDuplex C w) :
    𝟙 (diskSum X) ∈ (nullHomotopic C w).hom _ _ := by
  rw [mem_nullHomotopic_iff]
  refine ⟨biprod.map (0 : X.X₁ ⟶ X.X₁) (-𝟙 X.X₀),
    biprod.map (𝟙 X.X₁) (0 : X.X₀ ⟶ X.X₀), ?_⟩
  ext <;> apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
    simp [diskSum, biprod]

/-- A map is null-homotopic exactly when it factors through the disk sum on its source. -/
theorem mem_nullHomotopic_iff_factors_diskSum (f : X ⟶ Y) :
    f ∈ (nullHomotopic C w).hom X Y ↔
      ∃ (a : X ⟶ diskSum X) (b : diskSum X ⟶ Y), a ≫ b = f := by
  constructor
  · rw [mem_nullHomotopic_iff]
    rintro ⟨h₀, h₁, rfl⟩
    exact ⟨toDiskSum X, fromDiskSum h₀ h₁, toDiskSum_comp_fromDiskSum h₀ h₁⟩
  · rintro ⟨a, b, rfl⟩
    have h := id_diskSum_mem_nullHomotopic X
    simpa only [Category.comp_id, Category.id_comp] using
      (nullHomotopic C w).comp_mem_right b ((nullHomotopic C w).comp_mem_left a h)

/-- A contractible duplex is a retract of the direct sum of the disks on its components. -/
noncomputable def retractDiskSum (X : CurvedDuplex C w)
    (h : 𝟙 X ∈ (nullHomotopic C w).hom X X) : Retract X (diskSum X) := by
  let e := (mem_nullHomotopic_iff_factors_diskSum (𝟙 X)).mp h
  exact ⟨Classical.choose e, Classical.choose (Classical.choose_spec e),
    Classical.choose_spec (Classical.choose_spec e)⟩

end TauCeti.CurvedDuplex
