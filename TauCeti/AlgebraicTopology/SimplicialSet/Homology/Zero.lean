/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

/-!
# Vertex classes and the augmentation in degree zero

Vertex classes generate zeroth simplicial homology and commute with induced maps. In particular,
the augmentation is natural. These facts let the augmentation kernels form a functor and let a
chosen vertex split the augmentation.

The construction uses Mathlib's `SSet.homology₀ε` and `SSet.homology₀Iso`.
The mathematical convention is that of Hatcher, *Algebraic Topology*, Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace TauCeti.SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] {X Y : _root_.SSet.{w}} (R : C)

/-- The class in zeroth homology of a vertex, with coefficients in `R`. -/
def ιHomology₀ (x : X _⦋0⦌) : R ⟶ X.homology R 0 :=
  (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    (X.chainComplex R).homologyπ 0

@[reassoc (attr := simp)]
lemma ιHomology₀_homology₀Iso_hom (x : X _⦋0⦌) :
    ιHomology₀ R x ≫ (X.homology₀Iso R).hom =
      Sigma.ι (fun _ : _root_.SSet.π₀ X ↦ R) (_root_.SSet.π₀.mk x) := by
  simp [ιHomology₀]

/-- Vertex classes generate zeroth homology. -/
@[ext]
lemma homology₀_hom_ext {T : C} {f g : X.homology R 0 ⟶ T}
    (h : ∀ x, ιHomology₀ R x ≫ f = ιHomology₀ R x ≫ g) : f = g := by
  apply (cancel_epi ((X.chainComplex R).homologyπ 0)).1
  apply (cancel_epi ((X.chainComplex R).cycles₀Iso.inv)).1
  apply _root_.SSet.chainComplex_hom_ext
  intro x
  have hx : X.ιChainComplex x ≫ (X.chainComplex R).cycles₀Iso.inv =
      (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex R).iCycles 0)).1
    simp
  simpa only [ιHomology₀, Category.assoc, ← hx] using h x

@[reassoc (attr := simp)]
lemma ιHomology₀_homologyMap (f : X ⟶ Y) (x : X _⦋0⦌) :
    ιHomology₀ R x ≫ _root_.SSet.homologyMap f R 0 =
      ιHomology₀ R (f.app _ x) := by
  simp only [ιHomology₀, _root_.SSet.homologyMap, Category.assoc,
    HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, _root_.SSet.ι_chainComplexMap_f]

@[reassoc (attr := simp)]
lemma ιHomology₀_homology₀ε (x : X _⦋0⦌) :
    ιHomology₀ R x ≫ X.homology₀ε R = 𝟙 R := by
  simp [ιHomology₀]

/-- The augmentation of zeroth homology commutes with maps of simplicial sets. -/
@[reassoc (attr := simp)]
lemma homologyMap_homology₀ε (f : X ⟶ Y) :
    _root_.SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  apply homology₀_hom_ext
  intro x
  simp

end TauCeti.SSet
