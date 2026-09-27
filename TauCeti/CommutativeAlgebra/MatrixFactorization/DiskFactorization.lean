/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Biproduct
public import TauCeti.Algebra.Homology.Curved.DiskFactorization

/-!
# Factoring matrix-factorization homotopies through disks

The disk sum on the two components of a finite-projective matrix factorization is again
finite projective. Every null-homotopic morphism factors through this contractible object,
and every map factoring through it is null-homotopic. A contractible factorization is
therefore a retract of such a sum. These facts are the factorization input for comparing
the homotopy category with the stable category of the componentwise split exact structure.

The disk construction follows Frenkel, Khovanov and Schiffmann,
*Homological realization of Nakajima varieties and Weyl group actions*, Sections 2–3.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S} {X Y : MatrixFactorization S w}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The direct sum of the odd disk and the parity-shifted even disk of a matrix factorization.
Both components are the finite projective module `X₁ ⊞ X₀`. -/
-- The component types in the public map formulas require this constructor to be exposed.
@[expose] noncomputable def diskSum (X : MatrixFactorization S w) : MatrixFactorization S w :=
  ofCurvedDuplex (CurvedDuplex.diskSum X.obj)
    -- The full-subcategory property sees the underlying carrier of the component biproduct.
    (by change Module.Projective S (X.obj.X₁ ⊞ X.obj.X₀ : FGModuleCat S)
        exact FGModuleCat.projective_biprod S X.obj.X₁ X.obj.X₀)
    (by change Module.Projective S (X.obj.X₁ ⊞ X.obj.X₀ : FGModuleCat S)
        exact FGModuleCat.projective_biprod S X.obj.X₁ X.obj.X₀)

@[simp] theorem diskSum_obj (X : MatrixFactorization S w) :
    (diskSum X).obj = CurvedDuplex.diskSum X.obj := rfl

@[simp] theorem diskSum_X₀ (X : MatrixFactorization S w) :
    (diskSum X).obj.X₀ = (X.obj.X₁ ⊞ X.obj.X₀) := rfl

@[simp] theorem diskSum_X₁ (X : MatrixFactorization S w) :
    (diskSum X).obj.X₁ = (X.obj.X₁ ⊞ X.obj.X₀) := rfl

@[simp] theorem diskSum_d₀ (X : MatrixFactorization S w) :
    (diskSum X).obj.d₀ =
      CategoryTheory.Limits.biprod.map (𝟙 X.obj.X₁) (-(w • 𝟙 X.obj.X₀)) := rfl

@[simp] theorem diskSum_d₁ (X : MatrixFactorization S w) :
    (diskSum X).obj.d₁ =
      CategoryTheory.Limits.biprod.map (w • 𝟙 X.obj.X₁) (-𝟙 X.obj.X₀) := rfl

/-- The canonical map from a factorization into its disk sum. -/
noncomputable def toDiskSum (X : MatrixFactorization S w) : X ⟶ diskSum X :=
  ⟨CurvedDuplex.toDiskSum X.obj⟩

/-- An odd homotopy determines a map from the disk sum to its target. -/
noncomputable def fromDiskSum (h₀ : X.obj.X₀ ⟶ Y.obj.X₁)
    (h₁ : X.obj.X₁ ⟶ Y.obj.X₀) : diskSum X ⟶ Y :=
  ⟨CurvedDuplex.fromDiskSum h₀ h₁⟩

@[simp] theorem toDiskSum_hom_f₀ (X : MatrixFactorization S w) :
    (toDiskSum X).hom.f₀ = CategoryTheory.Limits.biprod.lift X.obj.d₀ (𝟙 X.obj.X₀) := by
  simp [toDiskSum]

@[simp] theorem toDiskSum_hom_f₁ (X : MatrixFactorization S w) :
    (toDiskSum X).hom.f₁ = CategoryTheory.Limits.biprod.lift (𝟙 X.obj.X₁) (-X.obj.d₁) := by
  simp [toDiskSum]

@[simp] theorem fromDiskSum_hom_f₀ (h₀ : X.obj.X₀ ⟶ Y.obj.X₁)
    (h₁ : X.obj.X₁ ⟶ Y.obj.X₀) :
    (fromDiskSum h₀ h₁).hom.f₀ =
      CategoryTheory.Limits.biprod.desc h₁ (h₀ ≫ Y.obj.d₁) := by
  simp [fromDiskSum]

@[simp] theorem fromDiskSum_hom_f₁ (h₀ : X.obj.X₀ ⟶ Y.obj.X₁)
    (h₁ : X.obj.X₁ ⟶ Y.obj.X₀) :
    (fromDiskSum h₀ h₁).hom.f₁ =
      CategoryTheory.Limits.biprod.desc (h₁ ≫ Y.obj.d₀) (-h₀) := by
  simp [fromDiskSum]

/-- The composite through the disk sum is the boundary of the given odd homotopy. -/
@[simp] theorem toDiskSum_comp_fromDiskSum (h₀ : X.obj.X₀ ⟶ Y.obj.X₁)
    (h₁ : X.obj.X₁ ⟶ Y.obj.X₀) :
    toDiskSum X ≫ fromDiskSum h₀ h₁ =
      ⟨CurvedDuplex.nullHomotopicMap h₀ h₁⟩ :=
  by
    apply ObjectProperty.hom_ext
    exact CurvedDuplex.toDiskSum_comp_fromDiskSum h₀ h₁

/-- The disk sum is contractible in the matrix-factorization homotopy category. -/
theorem id_diskSum_mem_nullHomotopic (X : MatrixFactorization S w) :
    𝟙 (diskSum X) ∈ (nullHomotopic (S := S) (w := w)).hom _ _ := by
  rw [mem_nullHomotopic_iff]
  exact (CurvedDuplex.mem_nullHomotopic_iff).mp
    (CurvedDuplex.id_diskSum_mem_nullHomotopic X.obj)

/-- A map of matrix factorizations is null-homotopic exactly when it factors through the disk
sum on its source. -/
theorem mem_nullHomotopic_iff_factors_diskSum (f : X ⟶ Y) :
    f ∈ (nullHomotopic (S := S) (w := w)).hom X Y ↔
      ∃ (a : X ⟶ diskSum X) (b : diskSum X ⟶ Y), a ≫ b = f := by
  constructor
  · rw [mem_nullHomotopic_iff]
    rintro ⟨h₀, h₁, hf⟩
    exact ⟨toDiskSum X, fromDiskSum h₀ h₁,
      by rw [toDiskSum_comp_fromDiskSum]; apply ObjectProperty.hom_ext; exact hf⟩
  · rintro ⟨a, b, rfl⟩
    have h := id_diskSum_mem_nullHomotopic X
    simpa only [Category.comp_id, Category.id_comp] using
      (nullHomotopic (S := S) (w := w)).comp_mem_right b
        ((nullHomotopic (S := S) (w := w)).comp_mem_left a h)

/-- A contractible finite-projective matrix factorization is a retract of the disk sum on its
two components. -/
noncomputable def retractDiskSum (X : MatrixFactorization S w)
    (h : 𝟙 X ∈ (nullHomotopic (S := S) (w := w)).hom X X) :
    Retract X (diskSum X) := by
  let e := (mem_nullHomotopic_iff_factors_diskSum (𝟙 X)).mp h
  exact ⟨Classical.choose e, Classical.choose (Classical.choose_spec e),
    Classical.choose_spec (Classical.choose_spec e)⟩

end TauCeti.MatrixFactorization
