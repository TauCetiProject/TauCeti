/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import TauCeti.Algebra.Homology.Curved.Biproduct
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.Algebra.Category.FGModuleCat.Zero

/-!
# Direct sums of finite-projective matrix factorizations

The componentwise direct sum of finite-projective matrix factorizations is again finite
projective. Its projections exhibit it as a categorical product and hence, in this
preadditive category, a binary biproduct. This provides the additive sums used by the
homotopy and Frobenius structures on matrix factorizations.

The direct-sum operation is the finite-projective case of the direct sum of curved duplexes;
the matrix-factorization convention follows Eisenbud, *Homological algebra on a complete
intersection*, Section 5.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The componentwise direct sum of two finite-projective matrix factorizations. -/
-- The component types of the public morphism formulas require the constructor to be exposed.
@[expose] noncomputable def biprod (X Y : MatrixFactorization S w) : MatrixFactorization S w :=
  ofCurvedDuplex (CurvedDuplex.biprod X.obj Y.obj)
    (FGModuleCat.projective_biprod S X.obj.X₀ Y.obj.X₀)
    (FGModuleCat.projective_biprod S X.obj.X₁ Y.obj.X₁)

@[simp] theorem biprod_obj (X Y : MatrixFactorization S w) :
    (biprod X Y).obj = CurvedDuplex.biprod X.obj Y.obj := rfl

@[simp] theorem biprod_X₀ (X Y : MatrixFactorization S w) :
    (biprod X Y).obj.X₀ = (X.obj.X₀ ⊞ Y.obj.X₀) := rfl

@[simp] theorem biprod_X₁ (X Y : MatrixFactorization S w) :
    (biprod X Y).obj.X₁ = (X.obj.X₁ ⊞ Y.obj.X₁) := rfl

@[simp] theorem biprod_d₀ (X Y : MatrixFactorization S w) :
    (biprod X Y).obj.d₀ = CategoryTheory.Limits.biprod.map X.obj.d₀ Y.obj.d₀ := rfl

@[simp] theorem biprod_d₁ (X Y : MatrixFactorization S w) :
    (biprod X Y).obj.d₁ = CategoryTheory.Limits.biprod.map X.obj.d₁ Y.obj.d₁ := rfl

/-- Projection to the first summand. -/
noncomputable def biprodFst (X Y : MatrixFactorization S w) : biprod X Y ⟶ X :=
  ⟨CurvedDuplex.biprodFst X.obj Y.obj⟩

/-- Projection to the second summand. -/
noncomputable def biprodSnd (X Y : MatrixFactorization S w) : biprod X Y ⟶ Y :=
  ⟨CurvedDuplex.biprodSnd X.obj Y.obj⟩

/-- The map into a direct sum induced by maps into its summands. -/
noncomputable def biprodLift {Z X Y : MatrixFactorization S w}
    (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ biprod X Y :=
  ⟨CurvedDuplex.biprodLift f.hom g.hom⟩

@[simp] theorem biprodFst_hom_f₀ (X Y : MatrixFactorization S w) :
    (biprodFst X Y).hom.f₀ = CategoryTheory.Limits.biprod.fst := by
  simpa only [biprodFst, biprod_obj] using CurvedDuplex.biprodFst_f₀ X.obj Y.obj

@[simp] theorem biprodFst_hom_f₁ (X Y : MatrixFactorization S w) :
    (biprodFst X Y).hom.f₁ = CategoryTheory.Limits.biprod.fst := by
  simpa only [biprodFst, biprod_obj] using CurvedDuplex.biprodFst_f₁ X.obj Y.obj

@[simp] theorem biprodSnd_hom_f₀ (X Y : MatrixFactorization S w) :
    (biprodSnd X Y).hom.f₀ = CategoryTheory.Limits.biprod.snd := by
  simpa only [biprodSnd, biprod_obj] using CurvedDuplex.biprodSnd_f₀ X.obj Y.obj

@[simp] theorem biprodSnd_hom_f₁ (X Y : MatrixFactorization S w) :
    (biprodSnd X Y).hom.f₁ = CategoryTheory.Limits.biprod.snd := by
  simpa only [biprodSnd, biprod_obj] using CurvedDuplex.biprodSnd_f₁ X.obj Y.obj

@[simp] theorem biprodLift_hom_f₀ {Z X Y : MatrixFactorization S w}
    (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprodLift f g).hom.f₀ = CategoryTheory.Limits.biprod.lift f.hom.f₀ g.hom.f₀ := by
  simpa only [biprodLift, biprod_obj] using CurvedDuplex.biprodLift_f₀ f.hom g.hom

@[simp] theorem biprodLift_hom_f₁ {Z X Y : MatrixFactorization S w}
    (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprodLift f g).hom.f₁ = CategoryTheory.Limits.biprod.lift f.hom.f₁ g.hom.f₁ := by
  simpa only [biprodLift, biprod_obj] using CurvedDuplex.biprodLift_f₁ f.hom g.hom

@[simp] theorem biprodLift_fst {Z X Y : MatrixFactorization S w}
    (f : Z ⟶ X) (g : Z ⟶ Y) : biprodLift f g ≫ biprodFst X Y = f := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodLift_fst f.hom g.hom

@[simp] theorem biprodLift_snd {Z X Y : MatrixFactorization S w}
    (f : Z ⟶ X) (g : Z ⟶ Y) : biprodLift f g ≫ biprodSnd X Y = g := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodLift_snd f.hom g.hom

/-- Maps into a direct sum are determined by their projections. -/
theorem biprod_hom_ext {Z X Y : MatrixFactorization S w} {f g : Z ⟶ biprod X Y}
    (h₀ : f ≫ biprodFst X Y = g ≫ biprodFst X Y)
    (h₁ : f ≫ biprodSnd X Y = g ≫ biprodSnd X Y) : f = g := by
  apply ObjectProperty.hom_ext
  apply CurvedDuplex.biprod_hom_ext
  · exact congrArg (·.hom) h₀
  · exact congrArg (·.hom) h₁

/-- Inclusion of the first matrix factorization into the componentwise direct sum. -/
noncomputable def biprodInl (X Y : MatrixFactorization S w) : X ⟶ biprod X Y :=
  ⟨CurvedDuplex.biprodInl X.obj Y.obj⟩

/-- Inclusion of the second matrix factorization into the componentwise direct sum. -/
noncomputable def biprodInr (X Y : MatrixFactorization S w) : Y ⟶ biprod X Y :=
  ⟨CurvedDuplex.biprodInr X.obj Y.obj⟩

/-- Maps out of both summands induce a map out of their direct sum. -/
noncomputable def biprodDesc {X Y Z : MatrixFactorization S w}
    (f : X ⟶ Z) (g : Y ⟶ Z) : biprod X Y ⟶ Z :=
  ⟨CurvedDuplex.biprodDesc f.hom g.hom⟩

@[simp] theorem biprodInl_hom_f₀ (X Y : MatrixFactorization S w) :
    (biprodInl X Y).hom.f₀ = CategoryTheory.Limits.biprod.inl := by
  simpa only [biprodInl, biprod_obj] using CurvedDuplex.biprodInl_f₀ X.obj Y.obj

@[simp] theorem biprodInl_hom_f₁ (X Y : MatrixFactorization S w) :
    (biprodInl X Y).hom.f₁ = CategoryTheory.Limits.biprod.inl := by
  simpa only [biprodInl, biprod_obj] using CurvedDuplex.biprodInl_f₁ X.obj Y.obj

@[simp] theorem biprodInr_hom_f₀ (X Y : MatrixFactorization S w) :
    (biprodInr X Y).hom.f₀ = CategoryTheory.Limits.biprod.inr := by
  simpa only [biprodInr, biprod_obj] using CurvedDuplex.biprodInr_f₀ X.obj Y.obj

@[simp] theorem biprodInr_hom_f₁ (X Y : MatrixFactorization S w) :
    (biprodInr X Y).hom.f₁ = CategoryTheory.Limits.biprod.inr := by
  simpa only [biprodInr, biprod_obj] using CurvedDuplex.biprodInr_f₁ X.obj Y.obj

@[simp] theorem biprodDesc_hom_f₀ {X Y Z : MatrixFactorization S w}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprodDesc f g).hom.f₀ = CategoryTheory.Limits.biprod.desc f.hom.f₀ g.hom.f₀ := by
  simpa only [biprodDesc, biprod_obj] using CurvedDuplex.biprodDesc_f₀ f.hom g.hom

@[simp] theorem biprodDesc_hom_f₁ {X Y Z : MatrixFactorization S w}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprodDesc f g).hom.f₁ = CategoryTheory.Limits.biprod.desc f.hom.f₁ g.hom.f₁ := by
  simpa only [biprodDesc, biprod_obj] using CurvedDuplex.biprodDesc_f₁ f.hom g.hom

@[simp] theorem biprodInl_desc {X Y Z : MatrixFactorization S w}
    (f : X ⟶ Z) (g : Y ⟶ Z) : biprodInl X Y ≫ biprodDesc f g = f := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodInl_desc f.hom g.hom

@[simp] theorem biprodInr_desc {X Y Z : MatrixFactorization S w}
    (f : X ⟶ Z) (g : Y ⟶ Z) : biprodInr X Y ≫ biprodDesc f g = g := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodInr_desc f.hom g.hom

@[simp] theorem biprodInl_fst (X Y : MatrixFactorization S w) :
    biprodInl X Y ≫ biprodFst X Y = 𝟙 X := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodInl_fst X.obj Y.obj

@[simp] theorem biprodInl_snd (X Y : MatrixFactorization S w) :
    biprodInl X Y ≫ biprodSnd X Y = 0 := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodInl_snd X.obj Y.obj

@[simp] theorem biprodInr_fst (X Y : MatrixFactorization S w) :
    biprodInr X Y ≫ biprodFst X Y = 0 := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodInr_fst X.obj Y.obj

@[simp] theorem biprodInr_snd (X Y : MatrixFactorization S w) :
    biprodInr X Y ≫ biprodSnd X Y = 𝟙 Y := by
  apply ObjectProperty.hom_ext
  exact CurvedDuplex.biprodInr_snd X.obj Y.obj

/-- Maps from a direct sum are determined by their restrictions to both summands. -/
theorem biprod_hom_ext' {X Y Z : MatrixFactorization S w} {f g : biprod X Y ⟶ Z}
    (h₀ : biprodInl X Y ≫ f = biprodInl X Y ≫ g)
    (h₁ : biprodInr X Y ≫ f = biprodInr X Y ≫ g) : f = g := by
  apply ObjectProperty.hom_ext
  apply CurvedDuplex.biprod_hom_ext'
  · exact congrArg (·.hom) h₀
  · exact congrArg (·.hom) h₁

/-- Finite-projective matrix factorizations have componentwise binary products. -/
instance hasBinaryProduct (X Y : MatrixFactorization S w) : HasBinaryProduct X Y :=
  HasLimit.mk ⟨BinaryFan.mk (biprodFst X Y) (biprodSnd X Y),
    BinaryFan.IsLimit.mk _ (fun f g ↦ biprodLift f g)
      (fun f g ↦ biprodLift_fst f g) (fun f g ↦ biprodLift_snd f g)
      (fun f g _ h₀ h₁ ↦ biprod_hom_ext
        (h₀.trans (biprodLift_fst f g).symm)
        (h₁.trans (biprodLift_snd f g).symm))⟩

/-- Finite-projective matrix factorizations have binary products. -/
instance hasBinaryProducts : HasBinaryProducts (MatrixFactorization S w) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- Finite-projective matrix factorizations have binary biproducts. -/
instance hasBinaryBiproducts : HasBinaryBiproducts (MatrixFactorization S w) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The zero matrix factorization has the zero module in both parities. -/
noncomputable def zero : MatrixFactorization S w :=
  let P := FGModuleCat.of S PUnit
  -- The carrier of `FGModuleCat.of S PUnit` is definitionally `PUnit`.
  let hP : IsZero P := FGModuleCat.isZero_of_subsingleton P (by
    change Subsingleton PUnit
    infer_instance)
  ofCurvedDuplex
    { X₀ := P
      X₁ := P
      d₀ := 0
      d₁ := 0
      d₀_comp_d₁ := by exact hP.eq_of_src _ _
      d₁_comp_d₀ := by exact hP.eq_of_src _ _ }
    (by infer_instance) (by infer_instance)

@[simp] theorem zero_X₀ : (zero (S := S) (w := w)).obj.X₀ = FGModuleCat.of S PUnit := (rfl)

@[simp] theorem zero_X₁ : (zero (S := S) (w := w)).obj.X₁ = FGModuleCat.of S PUnit := (rfl)

@[simp] theorem zero_d₀ : (zero (S := S) (w := w)).obj.d₀ = 0 := (rfl)

@[simp] theorem zero_d₁ : (zero (S := S) (w := w)).obj.d₁ = 0 := (rfl)

/-- The zero matrix factorization is both initial and terminal. -/
theorem isZero_zero : IsZero (zero (S := S) (w := w)) := by
  -- The carrier of `FGModuleCat.of S PUnit` is definitionally `PUnit`.
  have hP : IsZero (FGModuleCat.of S PUnit) :=
    FGModuleCat.isZero_of_subsingleton _ (by change Subsingleton PUnit; infer_instance)
  apply IsZero.of_full_of_faithful_of_isZero (inclusion (S := S) (w := w))
  exact CurvedDuplex.isZero_of_components _ (by simpa using hP) (by simpa using hP)

/-- Finite-projective matrix factorizations have a zero object. -/
instance hasZeroObject : HasZeroObject (MatrixFactorization S w) :=
  ⟨⟨zero, isZero_zero⟩⟩

/-- Finite-projective matrix factorizations have finite products. -/
instance hasFiniteProducts : HasFiniteProducts (MatrixFactorization S w) := by
  let : HasTerminal (MatrixFactorization S w) := HasZeroObject.hasTerminal
  exact CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

/-- Finite-projective matrix factorizations have finite biproducts. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (MatrixFactorization S w) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end TauCeti.MatrixFactorization
