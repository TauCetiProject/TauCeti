/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import TauCeti.Algebra.Category.CommAlgCat.Localization

/-!
# The spectrum of a localization as a limit of principal opens

For a submonoid `M` of a commutative ring `R` and a localization `S` of `R` at `M`, the ring `S`
is the filtered colimit of the principal localizations `R[1/∏ s]` over the finite sets `s` of
elements of `M` (`Submonoid.localizationAwayRingCoconeIsColimit`). Applying `Spec`, the scheme
`Spec S` is the cofiltered limit of the principal opens `Spec R[1/∏ s]` of `Spec R`, whose
transition maps are open immersions (`Submonoid.localizationAwaySpecConeIsLimit`). For
`M = p.primeCompl` this presents `Spec Rₚ` as the limit of the principal open neighbourhoods of
`p`, which is the starting point for spreading out from a local scheme (Stacks, Lemma 32.20.3
(0BQ5)).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Submonoid

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- The spectra of the principal localizations `R[1/∏ s]`, for finite sets `s` of elements of
`M`, with the maps induced by inverting more elements. -/
abbrev localizationAwaySpecDiagram : (Finset M)ᵒᵖ ⥤ Scheme.{u} :=
  (M.localizationAwayDiagram ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).op ⋙ Scheme.Spec

/-- The members of `Submonoid.localizationAwaySpecDiagram` are the spectra of the principal
localizations. -/
@[simp]
lemma localizationAwaySpecDiagram_obj (s : (Finset M)ᵒᵖ) :
    M.localizationAwaySpecDiagram.obj s = Spec (.of (M.localizationAwayDiagram.obj s.unop)) :=
  rfl

/-- The members of `Submonoid.localizationAwaySpecDiagram` are affine. -/
instance (s : (Finset M)ᵒᵖ) : IsAffine ((M.localizationAwaySpecDiagram).obj s) := by
  rw [localizationAwaySpecDiagram_obj]
  infer_instance

/-- The open immersion `Spec R[1/∏ s] ⟶ Spec R` of a member of
`Submonoid.localizationAwaySpecDiagram`. -/
abbrev localizationAwaySpecToSpec (s : (Finset M)ᵒᵖ) :
    (M.localizationAwaySpecDiagram).obj s ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (M.localizationAwayDiagram.obj s.unop)))

/-- The transition maps of `Submonoid.localizationAwaySpecDiagram` commute with the open
immersions into `Spec R`. -/
@[reassoc]
lemma localizationAwaySpecDiagram_map_localizationAwaySpecToSpec {s s' : (Finset M)ᵒᵖ}
    (f : s ⟶ s') :
    (M.localizationAwaySpecDiagram).map f ≫ M.localizationAwaySpecToSpec s' =
      M.localizationAwaySpecToSpec s := by
  dsimp only [localizationAwaySpecDiagram, localizationAwaySpecToSpec, Functor.comp_map,
    Functor.op_map, Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (M.localizationAwayDiagram.map f.unop).hom.commutes x

/-- The maps `Spec R[1/∏ s] ⟶ Spec R` are open immersions. -/
instance (s : (Finset M)ᵒᵖ) : IsOpenImmersion (M.localizationAwaySpecToSpec s) := by
  -- The stage is `Localization.Away (∏ x ∈ s, x)` up to the identification of its object.
  have h : CommRingCat.ofHom (algebraMap R (M.localizationAwayDiagram.obj s.unop)) =
      CommRingCat.ofHom (algebraMap R (Localization.Away (∏ x ∈ s.unop, (x : R)))) ≫
        (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).map
          (eqToHom (M.localizationAwayDiagram_obj s.unop).symm) := by
    ext x
    exact ((eqToHom (M.localizationAwayDiagram_obj s.unop).symm).hom.commutes x).symm
  rw [localizationAwaySpecToSpec, h, Spec.map_comp]
  infer_instance

/-- The transition maps of `Submonoid.localizationAwaySpecDiagram` are open immersions. -/
instance {s s' : (Finset M)ᵒᵖ} (f : s ⟶ s') :
    IsOpenImmersion ((M.localizationAwaySpecDiagram).map f) :=
  have : IsOpenImmersion ((M.localizationAwaySpecDiagram).map f ≫
      M.localizationAwaySpecToSpec s') := by
    rw [localizationAwaySpecDiagram_map_localizationAwaySpecToSpec]; infer_instance
  .of_comp _ (M.localizationAwaySpecToSpec s')

variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The cone over `Submonoid.localizationAwaySpecDiagram` with point `Spec S`, given by the maps
`Spec S ⟶ Spec R[1/∏ s]`. -/
abbrev localizationAwaySpecCone : Cone M.localizationAwaySpecDiagram :=
  Scheme.Spec.mapCone (M.localizationAwayRingCocone S).op

/-- The point of `Submonoid.localizationAwaySpecCone` is `Spec S`. -/
lemma localizationAwaySpecCone_pt : (M.localizationAwaySpecCone S).pt = Spec (.of S) :=
  rfl

/-- The legs of `Submonoid.localizationAwaySpecCone` are `Spec` of the legs of
`Submonoid.localizationAwayRingCocone`. -/
lemma localizationAwaySpecCone_π_app (s : (Finset M)ᵒᵖ) :
    (M.localizationAwaySpecCone S).π.app s =
      Spec.map ((M.localizationAwayRingCocone S).ι.app s.unop) :=
  rfl

/-- The spectrum of a localization is the cofiltered limit of the spectra of the principal
localizations, as `Spec` turns the filtered colimit `M⁻¹R = colim R[1/∏ s]` into a limit. -/
def localizationAwaySpecConeIsLimit : IsLimit (M.localizationAwaySpecCone S) :=
  isLimitOfPreserves Scheme.Spec (M.localizationAwayRingCoconeIsColimit S).op

/-- The legs of `Submonoid.localizationAwaySpecCone`, followed by the open immersions into
`Spec R`, are the map `Spec S ⟶ Spec R`. -/
@[reassoc]
lemma localizationAwaySpecCone_π_app_localizationAwaySpecToSpec (s : (Finset M)ᵒᵖ) :
    (M.localizationAwaySpecCone S).π.app s ≫ M.localizationAwaySpecToSpec s =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [localizationAwaySpecCone_π_app, localizationAwaySpecToSpec]
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext1
  exact M.localizationAwayRingCocone_ι_app_comp_algebraMap S s.unop

end Submonoid
