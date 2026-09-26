/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Mapping cones of curved duplexes

For a closed even map `f : X ⟶ Y` of curved duplexes with the same curvature, its cone has
components `X₁ ⊞ Y₀` and `X₀ ⊞ Y₁`. The differential is the block matrix with diagonal
entries `-d_X` and `d_Y` and lower-left entry `f`. Its square remains multiplication by the
curvature: the off-diagonal terms cancel because `f` commutes with the differentials.

The canonical inclusion of `Y` and projection to the parity shift of `X` give the sequence
`Y ⟶ cone(f) ⟶ X[1]` used to form cone triangles in the homotopy category.

This is the curved analogue of the ordinary mapping cone; see Frenkel, Khovanov and
Schiffmann, *Homological realization of Nakajima varieties and Weyl group actions*,
Compositio Mathematica 141 (2005), Sections 2–3.
-/

public section

universe w' v u

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w'} [Semiring R] [Linear R C] {w : R}
  {X Y : CurvedDuplex C w}

variable [HasBinaryBiproducts C]

/-- The first differential of the cone, from `X₁ ⊞ Y₀` to `X₀ ⊞ Y₁`. -/
noncomputable def coneD₀ (f : X ⟶ Y) : X.X₁ ⊞ Y.X₀ ⟶ X.X₀ ⊞ Y.X₁ :=
  biprod.desc (biprod.lift (-X.d₁) f.f₁) (biprod.lift 0 Y.d₀)

/-- The second differential of the cone, from `X₀ ⊞ Y₁` to `X₁ ⊞ Y₀`. -/
noncomputable def coneD₁ (f : X ⟶ Y) : X.X₀ ⊞ Y.X₁ ⟶ X.X₁ ⊞ Y.X₀ :=
  biprod.desc (biprod.lift (-X.d₀) f.f₀) (biprod.lift 0 Y.d₁)

/-- The mapping cone of a closed even map of curved duplexes. Both squares of its differential
are multiplication by the original curvature `w`. -/
-- The cone object is exposed because its biproduct components occur in the types of the
-- inclusion, projection, and componentwise cone-map API below.
@[expose, implicit_reducible] noncomputable def cone (f : X ⟶ Y) : CurvedDuplex C w where
  X₀ := X.X₁ ⊞ Y.X₀
  X₁ := X.X₀ ⊞ Y.X₁
  d₀ := coneD₀ f
  d₁ := coneD₁ f
  d₀_comp_d₁ := by
    ext <;> simp [coneD₀, coneD₁, Category.assoc, Preadditive.add_comp, ← f.comm₁]
  d₁_comp_d₀ := by
    ext <;> simp [coneD₀, coneD₁, Category.assoc, Preadditive.add_comp, ← f.comm₀]

@[simp] theorem cone_X₀ (f : X ⟶ Y) : (cone f).X₀ = (X.X₁ ⊞ Y.X₀) := by
  simp only [cone]

@[simp] theorem cone_X₁ (f : X ⟶ Y) : (cone f).X₁ = (X.X₀ ⊞ Y.X₁) := by
  simp only [cone]

@[simp] theorem cone_d₀ (f : X ⟶ Y) : (cone f).d₀ = coneD₀ f := by
  simp only [cone]

@[simp] theorem cone_d₁ (f : X ⟶ Y) : (cone f).d₁ = coneD₁ f := by
  simp only [cone]

/-- The canonical inclusion of the codomain into the cone. -/
noncomputable def coneInclusion (f : X ⟶ Y) : Y ⟶ cone f where
  f₀ := biprod.inr
  f₁ := biprod.inr
  comm₀ := by simp [cone, coneD₀, biprod.lift_eq]
  comm₁ := by simp [cone, coneD₁, biprod.lift_eq]

/-- The canonical projection from the cone onto the parity shift of the domain. -/
noncomputable def coneProjection (f : X ⟶ Y) : cone f ⟶ (parityShift C w).obj X where
  f₀ := biprod.fst
  f₁ := biprod.fst
  comm₀ := by simp [cone, coneD₀, biprod.desc_eq, Category.assoc]
  comm₁ := by simp [cone, coneD₁, biprod.desc_eq, Category.assoc]

@[simp] theorem coneInclusion_f₀ (f : X ⟶ Y) : (coneInclusion f).f₀ = biprod.inr := by
  simp only [coneInclusion]
@[simp] theorem coneInclusion_f₁ (f : X ⟶ Y) : (coneInclusion f).f₁ = biprod.inr := by
  simp only [coneInclusion]
@[simp] theorem coneProjection_f₀ (f : X ⟶ Y) : (coneProjection f).f₀ = biprod.fst := by
  simp only [coneProjection]
@[simp] theorem coneProjection_f₁ (f : X ⟶ Y) : (coneProjection f).f₁ = biprod.fst := by
  simp only [coneProjection]

/-- The inclusion followed by the projection vanishes. -/
@[simp]
theorem coneInclusion_comp_coneProjection (f : X ⟶ Y) :
    coneInclusion f ≫ coneProjection f = 0 := by
  ext <;> simp only [comp_f₀, comp_f₁, zero_f₀, zero_f₁,
    coneInclusion_f₀, coneInclusion_f₁, coneProjection_f₀, coneProjection_f₁] <;>
    exact biprod.inr_fst

/-- The cone of the identity is contractible. The odd contracting map sends the second
summand of each component identically into the first summand of the other component. -/
theorem nullHomotopicMap_cone_id (X : CurvedDuplex C w) :
    nullHomotopicMap (X := cone (𝟙 X)) (Y := cone (𝟙 X))
      (biprod.snd ≫ biprod.inl) (biprod.snd ≫ biprod.inl) = 𝟙 (cone (𝟙 X)) := by
  ext <;> simp [cone, coneD₀, coneD₁, biprod.lift_eq, biprod.desc_eq,
    Preadditive.add_comp, Preadditive.comp_add, Category.assoc]

/-- The cone of the identity becomes a zero object in the homotopy category. -/
theorem isZero_quotientFunctor_obj_cone_id (X : CurvedDuplex C w) :
    IsZero ((nullHomotopic C w).quotientFunctor.obj (cone (𝟙 X))) := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff]
  rw [mem_nullHomotopic_iff]
  exact ⟨_, _, nullHomotopicMap_cone_id X⟩

variable {X' Y' : CurvedDuplex C w}

/-- A commutative square of closed even maps induces a map of their cones, componentwise
given by the biproducts of its vertical maps. -/
noncomputable def coneMap (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : cone f ⟶ cone g where
  f₀ := biprod.map a.f₁ b.f₀
  f₁ := biprod.map a.f₀ b.f₁
  comm₀ := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [cone, coneD₀, biprod.map_eq, biprod.lift_eq, biprod.desc_eq,
      Category.assoc, Preadditive.add_comp, Preadditive.comp_add,
      a.comm₁, b.comm₀]
    simpa only [comp_f₁] using (congrArg Hom.f₁ h).symm
  comm₁ := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [cone, coneD₁, biprod.map_eq, biprod.lift_eq, biprod.desc_eq,
      Category.assoc, Preadditive.add_comp, Preadditive.comp_add,
      a.comm₀, b.comm₁]
    simpa only [comp_f₀] using (congrArg Hom.f₀ h).symm

/-- The even component of the map induced on cones. -/
@[simp]
theorem coneMap_f₀ (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) : (coneMap f g a b h).f₀ = biprod.map a.f₁ b.f₀ := by
  simp only [coneMap]

/-- The odd component of the map induced on cones. -/
@[simp]
theorem coneMap_f₁ (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) : (coneMap f g a b h).f₁ = biprod.map a.f₀ b.f₁ := by
  simp only [coneMap]

/-- Cone maps commute with the inclusions of their codomains. -/
theorem coneInclusion_comp_coneMap (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    coneInclusion f ≫ coneMap f g a b h = b ≫ coneInclusion g := by
  ext <;> simp only [comp_f₀, comp_f₁, coneInclusion_f₀, coneInclusion_f₁,
    coneMap_f₀, coneMap_f₁]
  · exact biprod.inr_map _ _
  · exact biprod.inr_map _ _

/-- Cone maps commute with the projections to the shifted domains. -/
theorem coneMap_comp_coneProjection (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    coneMap f g a b h ≫ coneProjection g =
      coneProjection f ≫ (parityShift C w).map a := by
  ext <;> simp only [comp_f₀, comp_f₁, coneMap_f₀, coneMap_f₁,
    coneProjection_f₀, coneProjection_f₁]
  · simpa only [cone, parityShift_map_f₀] using biprod.map_fst a.f₁ b.f₀
  · simpa only [cone, parityShift_map_f₁] using biprod.map_fst a.f₀ b.f₁

/-- The identity square induces the identity on the cone. -/
@[simp]
theorem coneMap_id (f : X ⟶ Y) :
    coneMap f f (𝟙 X) (𝟙 Y) (by simp) = 𝟙 (cone f) := by
  ext
  · apply biprod.hom_ext <;> simp [cone]
  · apply biprod.hom_ext <;> simp [cone]

/-- Composing commutative squares composes their induced cone maps. -/
theorem coneMap_comp {X'' Y'' : CurvedDuplex C w} (f : X ⟶ Y) (g : X' ⟶ Y')
    (k : X'' ⟶ Y'') (a : X ⟶ X') (b : Y ⟶ Y') (a' : X' ⟶ X'')
    (b' : Y' ⟶ Y'') (h : f ≫ b = a ≫ g) (h' : g ≫ b' = a' ≫ k) :
    coneMap f k (a ≫ a') (b ≫ b') (by
      calc
        f ≫ (b ≫ b') = (f ≫ b) ≫ b' := (Category.assoc _ _ _).symm
        _ = (a ≫ g) ≫ b' := by rw [h]
        _ = a ≫ (g ≫ b') := Category.assoc _ _ _
        _ = a ≫ (a' ≫ k) := by rw [h']
        _ = (a ≫ a') ≫ k := (Category.assoc _ _ _).symm) =
      coneMap f g a b h ≫ coneMap g k a' b' h' := by
  ext
  · simp only [comp_f₀, coneMap_f₀]
    apply biprod.hom_ext <;> simp only [cone, Category.assoc, biprod.map_fst, biprod.map_snd]
    all_goals simp only [← Category.assoc]
    all_goals first | rw [biprod.map_fst] | rw [biprod.map_snd]
    all_goals simp [Category.assoc]
  · simp only [comp_f₁, coneMap_f₁]
    apply biprod.hom_ext <;> simp only [cone, Category.assoc, biprod.map_fst, biprod.map_snd]
    all_goals simp only [← Category.assoc]
    all_goals first | rw [biprod.map_fst] | rw [biprod.map_snd]
    all_goals simp [Category.assoc]

end CurvedDuplex
end TauCeti
