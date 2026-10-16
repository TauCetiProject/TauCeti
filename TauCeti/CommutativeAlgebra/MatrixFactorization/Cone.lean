/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic
public import TauCeti.Algebra.Homology.Curved.Cone.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Projective

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
-- The cone object is exposed because its components occur in the types of the
-- inclusion, projection, and componentwise cone-map API below.
@[expose] noncomputable def cone (f : X ⟶ Y) : MatrixFactorization S w :=
  ofCurvedDuplex (CurvedDuplex.cone f.hom)
    (FGModuleCat.projective_biprod S X.obj.X₁ Y.obj.X₀)
    (FGModuleCat.projective_biprod S X.obj.X₀ Y.obj.X₁)

theorem cone_obj (f : X ⟶ Y) : (cone f).obj = CurvedDuplex.cone f.hom := rfl

@[simp] theorem cone_obj_X₀ (f : X ⟶ Y) :
    (cone f).obj.X₀ = (X.obj.X₁ ⊞ Y.obj.X₀) := rfl

@[simp] theorem cone_obj_X₁ (f : X ⟶ Y) :
    (cone f).obj.X₁ = (X.obj.X₀ ⊞ Y.obj.X₁) := rfl

@[simp] theorem cone_obj_d₀ (f : X ⟶ Y) :
    (cone f).obj.d₀ = CurvedDuplex.coneD₀ f.hom := rfl

@[simp] theorem cone_obj_d₁ (f : X ⟶ Y) :
    (cone f).obj.d₁ = CurvedDuplex.coneD₁ f.hom := rfl

/-- The canonical inclusion of the codomain into the cone. -/
@[expose] noncomputable def coneInclusion (f : X ⟶ Y) : Y ⟶ cone f :=
  ⟨CurvedDuplex.coneInclusion f.hom⟩

/-- The canonical projection of the cone onto the parity shift of the domain. -/
@[expose] noncomputable def coneProjection (f : X ⟶ Y) :
    cone f ⟶ (parityShift (S := S) (w := w)).obj X :=
  ⟨CurvedDuplex.coneProjection f.hom⟩

theorem coneInclusion_hom (f : X ⟶ Y) :
    (coneInclusion f).hom = CurvedDuplex.coneInclusion f.hom := rfl

theorem coneProjection_hom (f : X ⟶ Y) :
    (coneProjection f).hom = CurvedDuplex.coneProjection f.hom := rfl

@[simp] theorem coneInclusion_hom_f₀ (f : X ⟶ Y) :
    (coneInclusion f).hom.f₀ = biprod.inr := by
  simpa only [coneInclusion_hom, cone_obj] using CurvedDuplex.coneInclusion_f₀ f.hom

@[simp] theorem coneInclusion_hom_f₁ (f : X ⟶ Y) :
    (coneInclusion f).hom.f₁ = biprod.inr := by
  simpa only [coneInclusion_hom, cone_obj] using CurvedDuplex.coneInclusion_f₁ f.hom

@[simp] theorem coneProjection_hom_f₀ (f : X ⟶ Y) :
    (coneProjection f).hom.f₀ = biprod.fst := by
  simpa only [coneProjection_hom, cone_obj, parityShift_obj] using
    CurvedDuplex.coneProjection_f₀ f.hom

@[simp] theorem coneProjection_hom_f₁ (f : X ⟶ Y) :
    (coneProjection f).hom.f₁ = biprod.fst := by
  simpa only [coneProjection_hom, cone_obj, parityShift_obj] using
    CurvedDuplex.coneProjection_f₁ f.hom

/-- Parity shift commutes with mapping cones, with a sign on the codomain summand. -/
noncomputable def coneParityShiftIso (f : X ⟶ Y) :
    (parityShift (S := S) (w := w)).obj (cone f) ≅
      cone ((parityShift (S := S) (w := w)).map f) :=
  ObjectProperty.isoMk (P := MatrixFactorization.isProjective S w)
    (CurvedDuplex.coneParityShiftIso f.hom)

@[simp] theorem coneParityShiftIso_hom_hom_f₀ (f : X ⟶ Y) :
    (coneParityShiftIso f).hom.hom.f₀ = biprod.map (𝟙 X.obj.X₀) (-𝟙 Y.obj.X₁) :=
  CurvedDuplex.coneParityShiftIso_hom_f₀ f.hom

@[simp] theorem coneParityShiftIso_hom_hom_f₁ (f : X ⟶ Y) :
    (coneParityShiftIso f).hom.hom.f₁ = biprod.map (𝟙 X.obj.X₁) (-𝟙 Y.obj.X₀) :=
  CurvedDuplex.coneParityShiftIso_hom_f₁ f.hom

@[simp] theorem coneParityShiftIso_inv_hom_f₀ (f : X ⟶ Y) :
    (coneParityShiftIso f).inv.hom.f₀ = biprod.map (𝟙 X.obj.X₀) (-𝟙 Y.obj.X₁) :=
  CurvedDuplex.coneParityShiftIso_inv_f₀ f.hom

@[simp] theorem coneParityShiftIso_inv_hom_f₁ (f : X ⟶ Y) :
    (coneParityShiftIso f).inv.hom.f₁ = biprod.map (𝟙 X.obj.X₁) (-𝟙 Y.obj.X₀) :=
  CurvedDuplex.coneParityShiftIso_inv_f₁ f.hom

/-- The inclusion followed by the projection is zero. -/
@[reassoc (attr := simp), simp] theorem coneInclusion_comp_coneProjection (f : X ⟶ Y) :
    coneInclusion f ≫ coneProjection f = 0 := by
  ext <;> simp [cone_obj, coneInclusion_hom, coneProjection_hom]

/-- The composite from the domain to its cone is null-homotopic. -/
theorem comp_coneInclusion_mem_nullHomotopic (f : X ⟶ Y) :
    f ≫ coneInclusion f ∈ (nullHomotopic (S := S) (w := w)).hom X (cone f) := by
  rw [mem_nullHomotopic_iff]
  exact ⟨_, _, by
    simpa [cone_obj, coneInclusion_hom] using
      (CurvedDuplex.comp_coneInclusion f.hom).symm⟩

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

theorem coneMap_hom (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    (coneMap f g a b h).hom =
      CurvedDuplex.coneMap f.hom g.hom a.hom b.hom
        (by simpa using congrArg (·.hom) h) := rfl

@[simp] theorem coneMap_hom_f₀ (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    (coneMap f g a b h).hom.f₀ = biprod.map a.hom.f₁ b.hom.f₀ := by
  simpa only [coneMap_hom, cone_obj] using
    CurvedDuplex.coneMap_f₀ f.hom g.hom a.hom b.hom (by simpa using congrArg (·.hom) h)

@[simp] theorem coneMap_hom_f₁ (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    (coneMap f g a b h).hom.f₁ = biprod.map a.hom.f₀ b.hom.f₁ := by
  simpa only [coneMap_hom, cone_obj] using
    CurvedDuplex.coneMap_f₁ f.hom g.hom a.hom b.hom (by simpa using congrArg (·.hom) h)

/-- The identity square induces the identity on the cone. -/
@[simp] theorem coneMap_id (f : X ⟶ Y) :
    coneMap f f (𝟙 X) (𝟙 Y) (by simp) = 𝟙 (cone f) := by
  apply ObjectProperty.hom_ext
  simpa only [coneMap_hom, ObjectProperty.FullSubcategory.id_hom, cone_obj] using
    CurvedDuplex.coneMap_id f.hom

/-- Composing squares composes the induced maps on cones. -/
@[simp ←] theorem coneMap_comp {X'' Y'' : MatrixFactorization S w}
    (f : X ⟶ Y) (g : X' ⟶ Y') (k : X'' ⟶ Y'')
    (a : X ⟶ X') (b : Y ⟶ Y') (a' : X' ⟶ X'') (b' : Y' ⟶ Y'')
    (h : f ≫ b = a ≫ g) (h' : g ≫ b' = a' ≫ k) :
    coneMap f k (a ≫ a') (b ≫ b') (by
      calc
        f ≫ (b ≫ b') = (f ≫ b) ≫ b' := (Category.assoc _ _ _).symm
        _ = (a ≫ g) ≫ b' := by rw [h]
        _ = a ≫ (g ≫ b') := Category.assoc _ _ _
        _ = a ≫ (a' ≫ k) := by rw [h']
        _ = (a ≫ a') ≫ k := (Category.assoc _ _ _).symm) =
      coneMap f g a b h ≫ coneMap g k a' b' h' := by
  apply ObjectProperty.hom_ext
  simpa only [coneMap_hom, ObjectProperty.FullSubcategory.comp_hom, cone_obj] using
    CurvedDuplex.coneMap_comp f.hom g.hom k.hom a.hom b.hom a'.hom b'.hom
      (by simpa using congrArg (·.hom) h)
      (by simpa using congrArg (·.hom) h')

/-- A square of isomorphisms induces an isomorphism of cones. -/
instance isIso_coneMap (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    [IsIso a] [IsIso b] : IsIso (coneMap f g a b h) := by
  apply ((MatrixFactorization.isProjective S w).isIso_hom_iff _).mp
  rw [coneMap_hom]
  exact CurvedDuplex.isIso_coneMap f.hom g.hom a.hom b.hom
    (by simpa using congrArg (·.hom) h)

/-- Cone maps commute with the inclusions of their codomains. -/
@[reassoc (attr := simp), simp] theorem coneInclusion_comp_coneMap
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    coneInclusion f ≫ coneMap f g a b h = b ≫ coneInclusion g := by
  apply ObjectProperty.hom_ext
  simpa only [ObjectProperty.FullSubcategory.comp_hom, coneInclusion_hom, coneMap_hom,
    cone_obj] using
    CurvedDuplex.coneInclusion_comp_coneMap
    f.hom g.hom a.hom b.hom (by simpa using congrArg (·.hom) h)

/-- Cone maps commute with the projections to the shifted domains. -/
@[reassoc (attr := simp), simp] theorem coneMap_comp_coneProjection
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
    simpa [cone_obj] using CurvedDuplex.nullHomotopicMap_cone_isIso f.hom⟩

end TauCeti.MatrixFactorization
