/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Biproduct
public import TauCeti.RepresentationTheory.Quiver.Representation.VertexSimpleModule
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.ExtEuler
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent

/-!
# The Ext-Euler characteristic of a vertex simple

The first-arrow exact sequence `0 ⟶ ⨁_{i ⟶ j} Pⱼ ⟶ Pᵢ ⟶ Sᵢ ⟶ 0` computes the
Ext-Euler characteristic of a vertex simple against a module with finite-dimensional
spaces at that vertex and the heads of its outgoing arrows. The result is the
combinatorial Euler form with the simple's dimension vector on the left. Cycles are
allowed: the finite-arrow condition gives the short resolution, while only
finite-dimensionality at these target vertex spaces is needed for the Hom dimensions.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, Chapter III, Section 3, and Derksen--Weyman, *An Introduction to Quiver
Representations*, Chapter 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat

universe v w

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

private theorem finiteDimensional_hom_vertexSimpleModuleResolution_X₁ (i : Q)
    [Finite ((j : Q) × (i ⟶ j))]
    (Y : ModuleCat (pathAlgebra k Q))
    (hY : ∀ (j : Q), (i ⟶ j) → FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj j))) :
    FiniteDimensional k ((vertexSimpleModuleResolution k i).X₁ ⟶ Y) := by
  let J := (j : Q) × (i ⟶ j)
  let P : J → ModuleCat (pathAlgebra k Q) := fun a ↦ indecProjModule k Q a.1
  let e := vertexSimpleModuleResolutionX₁Iso k i
  have hf : ∀ a : J, FiniteDimensional k (P a ⟶ Y) := fun a ↦
    finiteDimensional_hom_indecProjModule k Q a.1 Y (hY a.1 a.2)
  have hp := finiteDimensional_hom_biproduct k P Y hf
  exact Module.Finite.equiv (CategoryTheory.Linear.homCongr k e (Iso.refl Y)).symm

/-- A vertex simple is Euler-admissible when the target has finite-dimensional spaces at
the chosen vertex and at the heads of its outgoing arrows. The first-arrow resolution
bounds Ext above degree one. -/
theorem isEulerAdmissible_vertexSimpleModule (i : Q)
    [Finite ((j : Q) × (i ⟶ j))]
    (Y : ModuleCat (pathAlgebra k Q))
    (hYi : FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i)))
    (hY : ∀ (j : Q), (i ⟶ j) → FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj j))) :
    IsEulerAdmissible k (vertexSimpleModule k Q i) Y := by
  let S := vertexSimpleModuleResolution k i
  have hS : S.ShortExact := shortExact_vertexSimpleModuleResolution k i
  have h₁hom : FiniteDimensional k (S.X₁ ⟶ Y) :=
    finiteDimensional_hom_vertexSimpleModuleResolution_X₁ k Q i Y hY
  have h₂hom : FiniteDimensional k (S.X₂ ⟶ Y) := by
    have hp := finiteDimensional_hom_indecProjModule k Q i Y hYi
    exact Module.Finite.equiv
      (CategoryTheory.Linear.homCongr k (vertexSimpleModuleResolutionX₂Iso k i)
        (Iso.refl Y)).symm
  have h₁ : IsExtFinite k S.X₁ Y := by
    let _ := h₁hom
    exact isExtFinite_of_projective k S.X₁ Y
  have h₂ : IsExtFinite k S.X₂ Y := by
    let _ := h₂hom
    exact isExtFinite_of_projective k S.X₂ Y
  have hd : HasProjectiveDimensionLT S.X₃ 2 :=
    hS.hasProjectiveDimensionLT_X₃ (n := 1)
      (hasProjectiveDimensionLT_of_ge _ 1 1 (by omega))
      (hasProjectiveDimensionLT_of_ge _ 1 2 (by omega))
  have h₃ : IsEulerAdmissible k S.X₃ Y := by
    let _ := hd
    exact ⟨h₁.of_shortExact₃' hS h₂,
      (⟨fun _ hn ↦ HasProjectiveDimensionLT.subsingleton S.X₃ 2 _ hn Y⟩ :
        IsExtBoundedBy S.X₃ Y 2).isExtBounded⟩
  exact h₃.of_iso (vertexSimpleModuleResolutionX₃Iso k i) (Iso.refl Y)

private theorem finrank_hom_vertexSimpleModuleResolution_X₁ (i : Q)
    [Fintype ((j : Q) × (i ⟶ j))]
    (Y : ModuleCat (pathAlgebra k Q))
    (hY : ∀ (j : Q), (i ⟶ j) → FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj j))) :
    Module.finrank k ((vertexSimpleModuleResolution k i).X₁ ⟶ Y) =
      ∑ a : (j : Q) × (i ⟶ j),
        dimVector ((quiverRepFunctor k Q).obj Y) a.1 := by
  let J := (j : Q) × (i ⟶ j)
  let P : J → ModuleCat (pathAlgebra k Q) := fun a ↦ indecProjModule k Q a.1
  let e := vertexSimpleModuleResolutionX₁Iso k i
  have hf : ∀ a : J, FiniteDimensional k (P a ⟶ Y) := fun a ↦
    finiteDimensional_hom_indecProjModule k Q a.1 Y (hY a.1 a.2)
  calc
    _ = Module.finrank k (⨁ P ⟶ Y) :=
      (CategoryTheory.Linear.homCongr k e (Iso.refl Y)).finrank_eq
    _ = ∑ a : J, Module.finrank k (P a ⟶ Y) := finrank_hom_biproduct k P Y hf
    _ = _ := by
      simp only [P, finrank_hom_indecProjModule]
      apply Finset.sum_congr
      · ext
        simp
      · intro a _
        rfl

/-- The Ext-Euler value of a vertex simple is its vertex coordinate minus the
dimensions at the heads of all arrows leaving that vertex. -/
theorem extEuler_vertexSimpleModule (i : Q)
    [Fintype ((j : Q) × (i ⟶ j))] (Y : ModuleCat (pathAlgebra k Q))
    (hYi : FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i)))
    (hY : ∀ (j : Q), (i ⟶ j) → FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj j))) :
    extEuler k (isEulerAdmissible_vertexSimpleModule k Q i Y hYi hY) =
      (dimVector ((quiverRepFunctor k Q).obj Y) i : ℤ) -
        ∑ a : (j : Q) × (i ⟶ j),
          (dimVector ((quiverRepFunctor k Q).obj Y) a.1 : ℤ) := by
  let S := vertexSimpleModuleResolution k i
  have hS : S.ShortExact := shortExact_vertexSimpleModuleResolution k i
  have h₁hom := finiteDimensional_hom_vertexSimpleModuleResolution_X₁ k Q i Y hY
  have h₂hom : FiniteDimensional k (S.X₂ ⟶ Y) := by
    have hp := finiteDimensional_hom_indecProjModule k Q i Y hYi
    exact Module.Finite.equiv
      (CategoryTheory.Linear.homCongr k (vertexSimpleModuleResolutionX₂Iso k i)
        (Iso.refl Y)).symm
  let _ := h₁hom
  let _ := h₂hom
  have h₁ : IsEulerAdmissible k S.X₁ Y := isEulerAdmissible_of_projective k S.X₁ Y
  have h₂ : IsEulerAdmissible k S.X₂ Y := isEulerAdmissible_of_projective k S.X₂ Y
  have h₃ : IsEulerAdmissible k S.X₃ Y :=
    (isEulerAdmissible_vertexSimpleModule k Q i Y hYi hY).of_iso
      (vertexSimpleModuleResolutionX₃Iso k i).symm (Iso.refl Y)
  have hadd := extEuler_shortExact₁ hS Y h₁ h₂ h₃
  have h₃eq := extEuler_of_iso h₃
    (isEulerAdmissible_vertexSimpleModule k Q i Y hYi hY)
    (vertexSimpleModuleResolutionX₃Iso k i) (Iso.refl Y)
  have h₂rank : Module.finrank k (S.X₂ ⟶ Y) =
      dimVector ((quiverRepFunctor k Q).obj Y) i := by
    rw [(CategoryTheory.Linear.homCongr k
      (vertexSimpleModuleResolutionX₂Iso k i) (Iso.refl Y)).finrank_eq,
      finrank_hom_indecProjModule]
  rw [extEuler_projective k h₁, extEuler_projective k h₂,
    finrank_hom_vertexSimpleModuleResolution_X₁ k Q i Y hY, h₂rank] at hadd
  rw [h₃eq] at hadd
  rw [← h₂rank]
  simp only [Nat.cast_sum] at hadd ⊢
  omega

section EulerForm

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- The Ext-Euler characteristic of a vertex simple is the quiver Euler form of its
dimension vector against that of the target module. -/
theorem extEuler_vertexSimpleModule_eq_eulerForm (i : Q)
    (Y : ModuleCat (pathAlgebra k Q))
    (hYi : FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i)))
    (hY : ∀ (j : Q), (i ⟶ j) → FiniteDimensional k
      (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj j))) :
    extEuler k (isEulerAdmissible_vertexSimpleModule k Q i Y hYi hY) =
      eulerForm Q
        (fun j ↦ (dimVector ((quiverRepFunctor k Q).obj (vertexSimpleModule k Q i)) j : ℤ))
        (fun j ↦ (dimVector ((quiverRepFunctor k Q).obj Y) j : ℤ)) := by
  classical
  rw [extEuler_vertexSimpleModule k Q i Y hYi hY,
    dimVector_eq_of_iso (vertexSimpleModuleIso k Q i),
    dimVector_simpleRep]
  have hsingle : (fun j ↦ ((Pi.single i 1 : Q → ℕ) j : ℤ)) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply]
  rw [hsingle, eulerForm_single_left]
  congr 1
  rw [Fintype.sum_sigma]
  simp [Finset.sum_const]

end EulerForm

open scoped Classical in
/-- The Ext-Euler value between vertex simples is the Kronecker delta minus the number of
arrows from the first vertex to the second. -/
@[simp]
theorem extEuler_vertexSimpleModule_vertexSimpleModule (i j : Q)
    [Finite ((a : Q) × (i ⟶ a))] :
    extEuler k (isEulerAdmissible_vertexSimpleModule k Q i (vertexSimpleModule k Q j)
      (finiteDimensional_vertexSimpleModule_obj k Q j i)
      (fun a _ ↦ finiteDimensional_vertexSimpleModule_obj k Q j a)) =
      (if i = j then 1 else 0) - (Nat.card (i ⟶ j) : ℤ) := by
  classical
  have : Finite (i ⟶ j) := Finite.of_injective
    (fun f : i ⟶ j ↦ (⟨j, f⟩ : (a : Q) × (i ⟶ a))) (by
      intro f g h
      cases h
      rfl)
  let _ : Fintype (i ⟶ j) := Fintype.ofFinite _
  let _ : Fintype ((a : Q) × (i ⟶ a)) := Fintype.ofFinite _
  rw [extEuler_vertexSimpleModule k Q i (vertexSimpleModule k Q j)
    (finiteDimensional_vertexSimpleModule_obj k Q j i)
    (fun a _ ↦ finiteDimensional_vertexSimpleModule_obj k Q j a)]
  simp only [dimVector_eq_of_iso (vertexSimpleModuleIso k Q j), dimVector_simpleRep]
  simp only [Pi.single_apply]
  simp only [Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, Finset.sum_boole,
    sub_right_inj, Nat.cast_inj]
  let e : {x : (a : Q) × (i ⟶ a) // x.1 = j} ≃ (i ⟶ j) := {
    toFun := fun ⟨⟨a, f⟩, h⟩ ↦ by cases h; exact f
    invFun := fun f ↦ ⟨⟨j, f⟩, rfl⟩
    left_inv := by intro ⟨⟨a, f⟩, h⟩; cases h; rfl
    right_inv := by intro f; rfl
  }
  simpa only [Fintype.card_subtype, Nat.card_eq_fintype_card] using Fintype.card_congr e

end TauCeti
