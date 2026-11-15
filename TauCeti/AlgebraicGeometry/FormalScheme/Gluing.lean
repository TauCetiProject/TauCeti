/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing formal schemes

Open gluing of locally ringed spaces preserves the property of being locally a formal
spectrum. We equip Mathlib's glued locally ringed space with this formal atlas, without
changing its structure sheaf or its morphisms. Compatible morphisms from the pieces descend
uniquely, using the same multicoequalizer as for locally ringed spaces.

Gluing ordinary schemes and then regarding the result as a formal scheme agrees with gluing
their formal schemes. No noetherian hypothesis is needed.

The construction follows Mathlib's `AlgebraicGeometry.Scheme.GlueData.gluedScheme` and reuses
`AlgebraicGeometry.LocallyRingedSpace.GlueData` and its gluing colimit.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*,
  Ch. 0, 4.1.7 and Ch. I, 10.4.2.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

/-- Locally ringed-space gluing data whose pieces admit formal atlases.
The atlas conditions are properties, so no additional choice of charts is stored. -/
structure GlueData where
  /-- The underlying gluing data, including overlap maps and their cocycle. -/
  data : LocallyRingedSpace.GlueData.{u}
  /-- Every piece is locally a formal spectrum of finite ideal type. -/
  local_spf : ∀ i (x : data.U i),
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (f : Spf A ⟶ data.U i),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base

namespace GlueData

/-- A formal gluing datum is determined by its locally ringed-space gluing datum. -/
@[ext]
theorem ext {D E : GlueData.{u}} (h : D.data = E.data) : D = E := by
  cases D
  cases E
  cases h
  rfl

variable (D : GlueData.{u})

/-- A piece with its formal atlas. The carrier is exposed so the original overlap maps
retain their types. -/
@[expose] def piece (i : D.data.J) : FormalScheme where
  toLocallyRingedSpace := D.data.U i
  local_spf := D.local_spf i

@[simp]
theorem piece_toLocallyRingedSpace (i : D.data.J) :
    (D.piece i).toLocallyRingedSpace = D.data.U i := (rfl)

/-- The glued locally ringed space is a formal scheme: compose a formal chart of a piece
with its open immersion into the gluing. The carrier is exposed to retain the supplied
locally ringed-space colimit and its maps. -/
@[expose] noncomputable def glued : FormalScheme where
  toLocallyRingedSpace := D.data.toGlueData.glued
  local_spf x := by
    obtain ⟨i, y, rfl⟩ := D.data.ι_jointly_surjective x
    obtain ⟨A, _, _, _, _, f, hf, z, hz⟩ := D.local_spf i y
    have := hf
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      f ≫ D.data.toGlueData.ι i, inferInstance, z, ?_⟩
    simp only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hz]

@[simp]
theorem glued_toLocallyRingedSpace :
    D.glued.toLocallyRingedSpace = D.data.toGlueData.glued := (rfl)

/-- The open immersion of a formal piece into the glued formal scheme. -/
noncomputable def ι (i : D.data.J) : D.piece i ⟶ D.glued :=
  InducedCategory.homMk (D.data.toGlueData.ι i)

@[simp]
theorem forget_ι (i : D.data.J) :
    forgetToLocallyRingedSpace.map (D.ι i) = D.data.toGlueData.ι i := (rfl)

/-- The canonical inclusions are open immersions on the underlying locally ringed spaces. -/
instance (i : D.data.J) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map (D.ι i)) :=
  D.data.ι_isOpenImmersion i

/-- The images of the formal pieces cover the gluing. -/
theorem ι_jointly_surjective (x : D.glued) :
    ∃ (i : D.data.J) (y : D.piece i),
      (forgetToLocallyRingedSpace.map (D.ι i)).base y = x :=
  D.data.ι_jointly_surjective x

variable {Y : FormalScheme.{u}}

/-- Descend morphisms from the pieces that agree on every supplied overlap. -/
noncomputable def desc (f : ∀ i, D.piece i ⟶ Y)
    (hf : ∀ i j, D.data.f i j ≫ (f i).hom =
      D.data.t i j ≫ D.data.f j i ≫ (f j).hom) : D.glued ⟶ Y :=
  InducedCategory.homMk <| Multicoequalizer.desc _ _ (fun i ↦ (f i).hom)
    (fun ⟨i, j⟩ ↦ (hf i j).trans (Category.assoc _ _ _).symm)

/-- The descended morphism restricts to the specified morphism on each piece. -/
@[reassoc (attr := simp)]
theorem ι_desc (f : ∀ i, D.piece i ⟶ Y)
    (hf : ∀ i j, D.data.f i j ≫ (f i).hom =
      D.data.t i j ≫ D.data.f j i ≫ (f j).hom) (i : D.data.J) :
    D.ι i ≫ D.desc f hf = f i := by
  apply InducedCategory.hom_ext
  exact Multicoequalizer.π_desc D.data.toGlueData.diagram Y.toLocallyRingedSpace _ _ i

/-- Morphisms out of the gluing are determined by their restrictions to its pieces. -/
@[ext]
theorem hom_ext {f g : D.glued ⟶ Y} (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g := by
  apply InducedCategory.hom_ext
  exact Multicoequalizer.hom_ext _ _ _ (fun i ↦ congrArg InducedCategory.Hom.hom (h i))

end GlueData
end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme.GlueData

open TauCeti TauCeti.FormalScheme

/-- Scheme gluing data acquire formal atlases from the fully faithful inclusion of schemes.
The body is exposed so its pieces retain the original index type and locally ringed spaces. -/
@[expose] noncomputable def toFormalSchemeGlueData (E : Scheme.GlueData.{u}) :
    FormalScheme.GlueData where
  data := E.toLocallyRingedSpaceGlueData
  local_spf i := (E.U i).toFormalScheme.local_spf

/-- Gluing schemes commutes with their inclusion into formal schemes. -/
noncomputable def formalGluedIso (E : Scheme.GlueData.{u}) :
    FormalScheme.ofScheme.obj E.glued ≅ E.toFormalSchemeGlueData.glued :=
  InducedCategory.isoMk E.isoLocallyRingedSpace

/-- The scheme comparison uses the original comparison of locally ringed spaces. -/
@[simp]
theorem forget_formalGluedIso_hom (E : Scheme.GlueData.{u}) :
    FormalScheme.forgetToLocallyRingedSpace.map E.formalGluedIso.hom =
      E.isoLocallyRingedSpace.hom := (rfl)

end AlgebraicGeometry.Scheme.GlueData
