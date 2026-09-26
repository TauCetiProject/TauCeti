/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import TauCeti.Algebra.Homology.Curved.Cone
public import TauCeti.Algebra.Category.FGModuleCat.Basic

/-!
# Mapping cones of finite-projective matrix factorizations

The cone of a morphism of matrix factorizations is the cone of its underlying curved duplex.
Its components are biproducts of finite projective modules, so it remains a finite-projective
matrix factorization. The usual inclusion and projection give the cone sequence inside the
matrix-factorization category, and the cone of an isomorphism is contractible.

The block-matrix cone convention follows I. Frenkel, M. Khovanov, and O. Schiffmann,
*Homological realization of Nakajima varieties and Weyl group actions*, Compositio
Mathematica 141 (2005), Sections 2–3.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S}
variable {X Y : MatrixFactorization S w}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The mapping cone of a morphism of finite-projective matrix factorizations. -/
@[expose] noncomputable def cone (f : X ⟶ Y) : MatrixFactorization S w :=
  ofCurvedDuplex (CurvedDuplex.cone f.hom)
    (FGModuleCat.projective_biprod S X.obj.X₁ Y.obj.X₀)
    (FGModuleCat.projective_biprod S X.obj.X₀ Y.obj.X₁)

@[simp] theorem cone_obj (f : X ⟶ Y) : (cone f).obj = CurvedDuplex.cone f.hom := rfl

/-- The canonical inclusion of the codomain into the cone. -/
@[expose] noncomputable def coneInclusion (f : X ⟶ Y) : Y ⟶ cone f :=
  ⟨CurvedDuplex.coneInclusion f.hom⟩

/-- The canonical projection of the cone onto the parity shift of the domain. -/
@[expose] noncomputable def coneProjection (f : X ⟶ Y) :
    cone f ⟶ (parityShift (S := S) (w := w)).obj X :=
  ⟨CurvedDuplex.coneProjection f.hom⟩

@[simp] theorem coneInclusion_hom (f : X ⟶ Y) :
    (coneInclusion f).hom = CurvedDuplex.coneInclusion f.hom := rfl

@[simp] theorem coneProjection_hom (f : X ⟶ Y) :
    (coneProjection f).hom = CurvedDuplex.coneProjection f.hom := rfl

/-- The inclusion followed by the projection is zero. -/
@[reassoc (attr := simp)] theorem coneInclusion_comp_coneProjection (f : X ⟶ Y) :
    coneInclusion f ≫ coneProjection f = 0 := by
  ext <;> simp

/-- The composite from the domain to its cone is null-homotopic. -/
theorem comp_coneInclusion_mem_nullHomotopic (f : X ⟶ Y) :
    f ≫ coneInclusion f ∈ (nullHomotopic (S := S) (w := w)).hom X (cone f) := by
  rw [mem_nullHomotopic_iff]
  exact ⟨_, _, by
    simpa using (CurvedDuplex.comp_coneInclusion f.hom).symm⟩

/-- The composite from the domain to its cone vanishes in the homotopy category. -/
@[simp] theorem quotientFunctor_map_comp_coneInclusion (f : X ⟶ Y) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor.map f ≫
      (nullHomotopic (S := S) (w := w)).quotientFunctor.map (coneInclusion f) = 0 := by
  rw [← Functor.map_comp, MorphismIdeal.quotientFunctor_map_eq_zero_iff]
  exact comp_coneInclusion_mem_nullHomotopic f

variable {X' Y' : MatrixFactorization S w}

/-- A commutative square of matrix factorizations induces a map between its cones. -/
@[expose] noncomputable def coneMap (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : cone f ⟶ cone g :=
  ⟨CurvedDuplex.coneMap f.hom g.hom a.hom b.hom (by simpa using congrArg (·.hom) h)⟩

@[simp] theorem coneMap_hom (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    (coneMap f g a b h).hom =
      CurvedDuplex.coneMap f.hom g.hom a.hom b.hom
        (by simpa using congrArg (·.hom) h) := rfl

/-- Cone maps commute with the inclusions of their codomains. -/
@[reassoc (attr := simp)] theorem coneInclusion_comp_coneMap
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    coneInclusion f ≫ coneMap f g a b h = b ≫ coneInclusion g := by
  apply ObjectProperty.hom_ext
  simpa only [ObjectProperty.FullSubcategory.comp_hom, coneInclusion_hom, coneMap_hom,
    cone_obj] using
    CurvedDuplex.coneInclusion_comp_coneMap
    f.hom g.hom a.hom b.hom (by simpa using congrArg (·.hom) h)

/-- Cone maps commute with the projections to the shifted domains. -/
@[reassoc (attr := simp)] theorem coneMap_comp_coneProjection
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    coneMap f g a b h ≫ coneProjection g =
      coneProjection f ≫ (parityShift (S := S) (w := w)).map a := by
  apply ObjectProperty.hom_ext
  simpa only [ObjectProperty.FullSubcategory.comp_hom, coneProjection_hom,
    coneMap_hom, cone_obj, parityShift_obj, parityShift_map_hom] using
    CurvedDuplex.coneMap_comp_coneProjection
    f.hom g.hom a.hom b.hom (by simpa using congrArg (·.hom) h)

/-- The cone of an isomorphism is contractible and becomes zero in the homotopy category. -/
theorem isZero_quotientFunctor_obj_cone_isIso (f : X ⟶ Y) [IsIso f] :
    IsZero ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj (cone f)) := by
  have : IsIso f.hom := (inclusion (S := S) (w := w)).map_isIso f
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff, mem_nullHomotopic_iff]
  exact ⟨_, _, by
    simpa using CurvedDuplex.nullHomotopicMap_cone_isIso f.hom⟩

end TauCeti.MatrixFactorization
