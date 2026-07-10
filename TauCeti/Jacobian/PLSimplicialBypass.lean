/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Simplicial Bypass for Jacobians

This file defines the Euler characteristic, genus, and homology groups for
finite simplicial complexes, acting as a combinatorial bypass for topological
properties required in the Jacobian construction.

This advances the roadmap at TauCetiRoadmap/JacobianChallenge/README.md.
-/

public section

open Set Geometry Finset CategoryTheory
open scoped BigOperators Simplicial

namespace TauCeti.Jacobian.PLSimplicialBypass

universe u

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [LinearOrder E] [DecidableEq E]

/-- Euler characteristic of a finite simplicial complex. -/
noncomputable def eulerChar (K : SimplicialComplex 𝕜 E) [Finite K.faces] : ℤ :=
  ∑ s ∈ K.faces.toFinite.toFinset, (-1)^(s.card - 1)

/-- Genus of a triangulated 2-manifold. -/
noncomputable def genusOfComplex (K : SimplicialComplex 𝕜 E) [Finite K.faces] : ℤ :=
  (2 - eulerChar K) / 2

/-- Helper definition of the simplicial set's objects. -/
@[expose]
def simplicialSetOfComplexObj (K : SimplicialComplex 𝕜 E) (n : SimplexCategoryᵒᵖ) : Type u :=
  { l : Fin (n.unop.len + 1) →o E // Finset.image l Finset.univ ∈ K.faces }

/-- Helper definition of the simplicial set's map. -/
@[expose]
def simplicialSetOfComplexMap (K : SimplicialComplex 𝕜 E) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : simplicialSetOfComplexObj K n) : simplicialSetOfComplexObj K m :=
  ⟨x.val.comp f.unop.toOrderHom, by
    refine K.isRelLowerSet_faces.mem_of_le x.property ?_ (Finset.univ_nonempty.image _)
    rw [Finset.le_iff_subset]
    change Finset.image (x.val ∘ f.unop.toOrderHom) Finset.univ ⊆ Finset.image x.val Finset.univ
    rw [← Finset.image_image]
    exact Finset.image_subset_image (Finset.subset_univ _)⟩

/-- Bridge from SimplicialComplex to SimplicialSet. -/
@[expose]
def simplicialSetOfComplex (K : SimplicialComplex 𝕜 E) : SSet.{u} where
  obj n := simplicialSetOfComplexObj K n
  map f := ↾(simplicialSetOfComplexMap K f)
  map_id n := by ext; rfl
  map_comp f g := by ext; rfl

variable {F : Type u} [AddCommGroup F] [Module 𝕜 F] [LinearOrder F] [DecidableEq F]

/-- Simplicial map between simplicial complexes. -/
structure SimplicialMap (K : SimplicialComplex 𝕜 E) (L : SimplicialComplex 𝕜 F) where
  /-- The underlying order-preserving map between the vertices. -/
  toOrderHom : E →o F
  /-- Faces are mapped to faces. -/
  map_face : ∀ s ∈ K.faces, s.image toOrderHom ∈ L.faces

/-- Induced map between the simplicial sets. -/
def simplicialSetOfComplexMapHom (K : SimplicialComplex 𝕜 E) (L : SimplicialComplex 𝕜 F)
    (f : SimplicialMap K L) : simplicialSetOfComplex K ⟶ simplicialSetOfComplex L where
  app n := ↾(fun x => ⟨f.toOrderHom.comp x.val, by
    simpa [Finset.image_image] using f.map_face (Finset.image x.val Finset.univ) x.property⟩)
  naturality n m g := by ext; rfl

attribute [local instance] Classical.propDecidable

/-- Homology group of a simplicial complex with integer coefficients. -/
noncomputable def homologyGroup (K : SimplicialComplex 𝕜 E) (n : ℕ) : AddCommGrpCat.{u} :=
  (simplicialSetOfComplex K).homology (AddCommGrpCat.of (ULift.{u} ℤ)) n

/-- Topological degree of a simplicial map. -/
noncomputable def deg (K : SimplicialComplex 𝕜 E) (L : SimplicialComplex 𝕜 F)
    (f : SimplicialMap K L) (x : homologyGroup K 2) (y : homologyGroup L 2) : ℤ :=
  let H_f :=
    SSet.homologyMap (simplicialSetOfComplexMapHom K L f) (AddCommGrpCat.of (ULift.{u} ℤ)) 2
  if h : ∃ d : ℤ, H_f x = d • y then h.choose else 0

end TauCeti.Jacobian.PLSimplicialBypass
