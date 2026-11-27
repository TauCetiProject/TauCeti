/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Modules.DepthAtPoint
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs

/-!
# Hartogs extension for coherent modules on schemes

If a coherent module on a locally Noetherian scheme has stalk depth at least two outside the
image of an open immersion, it is canonically isomorphic to the direct image of its restriction.
`Scheme.Modules.isIso_restrictAdjunction_unit_app_of_two_le_depth` and
`Scheme.Modules.restrictAdjunctionUnitIsoOfTwoLeDepth` give this result through the restriction
adjunction, providing the sheaf-level input for extension of reflexive modules.
`Scheme.Modules.presheaf_map_leTop_bijective_of_two_le_depth` gives unique extension of global
sections. On an affine chart,
`Scheme.Modules.isIso_restrict_fromSpec_presheaf_map_leTop_of_two_le_depth` gives the restriction
isomorphism using `tilde_toOpen_bijective_of_two_le_depth` and
`Scheme.Modules.stalkDepth_eq_depth_localizedModule`.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I)
-/

public section

open CategoryTheory Opposite IsLocalRing
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- In an affine chart with Noetherian coordinate ring and finite section module, the restriction
to `W` is invertible if the stalks outside `W` have depth at least two. -/
theorem isIso_restrict_fromSpec_presheaf_map_leTop_of_two_le_depth (F : X.Modules)
    [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] [Module.Finite Γ(X, V) Γ(F, V)]
    (W : (Spec Γ(X, V)).Opens) (h : ∀ p ∉ W, 2 ≤ F.stalkDepth (hV.fromSpec p)) :
    IsIso ((F.restrict hV.fromSpec).presheaf.map W.leTop.op) := by
  let M := ModuleCat.of Γ(X, V) Γ(F, V)
  have hdepth (p : PrimeSpectrum Γ(X, V)) (hp : p ∉ W) :
      2 ≤ depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) := by
    let x : V := ⟨hV.fromSpec p, hV.range_fromSpec.le ⟨p, rfl⟩⟩
    have hp' : hV.primeIdealOf x = p :=
      hV.isOpenImmersion_fromSpec.base_open.injective (hV.fromSpec_primeIdealOf x)
    rw [← hp', ← F.stalkDepth_eq_depth_localizedModule hV x]
    exact h p hp
  let N := F.restrict hV.fromSpec
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor _ _
  let eN := asIso N.fromTildeΓ
  let eM := (tilde.functor Γ(X, V)).mapIso (F.fromSpecSectionsEquiv hV).toModuleIso
  let e := (modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _).mapIso (eM ≪≫ eN)
  have : IsIso (tilde.toOpen M W) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (tilde_toOpen_bijective_of_two_le_depth M W hdepth)
  have hr : IsIso ((modulesSpecToSheaf.obj (tilde M)).presheaf.map W.leTop.op) :=
    IsIso.of_isIso_fac_left (f := tilde.toOpen M ⊤) (h := tilde.toOpen M W)
      (tilde.toOpen_res M ⊤ W W.leTop)
  -- Forgetting to modules over the base ring and restricting scalars preserve the underlying
  -- restriction function definitionally, so bijectivity gives the isomorphism over either ring.
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ((ConcreteCategory.isIso_iff_bijective ((modulesSpecToSheaf.obj N).presheaf.map W.leTop.op)).1
      ((NatIso.isIso_map_iff e _).1 hr))

/-- For a coherent module `F` on a locally Noetherian scheme, the unit `F ⟶ j_* (F|_Y)` of an open
immersion `j : Y ⟶ X` is invertible if the stalk depth is at least two off `Y` (Stacks 0E9I). -/
@[stacks 0E9I]
theorem isIso_restrictAdjunction_unit_app_of_two_le_depth (F : X.Modules)
    [IsLocallyNoetherian X] [F.IsQuasicoherent] [F.IsFiniteType]
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (h : ∀ x ∉ j.opensRange, 2 ≤ F.stalkDepth x) :
    IsIso ((restrictAdjunction j).unit.app F) := by
  refine Hom.isIso_of_isBasis _ (B := fun V : X.affineOpens ↦ V.val)
    (by simpa only [Subtype.range_coe] using X.isBasis_affineOpens) fun V ↦ ?_
  have := IsLocallyNoetherian.component_noetherian V
  have := F.finite_sections_of_isAffineOpen V.val V.property
  let f := V.property.fromSpec
  have : IsOpenImmersion f := V.property.isOpenImmersion_fromSpec
  let W := f ⁻¹ᵁ j.opensRange
  have : IsIso ((F.restrict f).presheaf.map W.leTop.op) :=
    F.isIso_restrict_fromSpec_presheaf_map_leTop_of_two_le_depth V.property W
      (fun p hp ↦ h (f p) hp)
  have hi : IsIso (F.presheaf.map (homOfLE (f.image_mono (leOfHom W.leTop))).op) := by
    rw [← isIso_comp_left_iff (F.restrictAppIso f ⊤).hom, ← F.map_restrictAppIso_hom f W.leTop.op]
    infer_instance
  have htop : f ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = V.val :=
    f.image_top_eq_opensRange.trans V.property.opensRange_fromSpec
  have hinter : f ''ᵁ W = j ''ᵁ (j ⁻¹ᵁ V.val) := by
    simp only [W, Scheme.Hom.image_preimage_eq_opensRange_inf, f, V.property.opensRange_fromSpec,
      inf_comm]
  have hj : IsIso (F.presheaf.map (homOfLE (j.image_preimage_le V.val)).op) := by
    grind only
  rw [restrictAdjunction_unit_app_app]
  exact hj

/-- The canonical Hartogs isomorphism for a coherent module across a complement of stalk depth
at least two on a locally Noetherian scheme. -/
noncomputable def restrictAdjunctionUnitIsoOfTwoLeDepth (F : X.Modules)
    [IsLocallyNoetherian X] [F.IsQuasicoherent] [F.IsFiniteType]
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (h : ∀ x ∉ j.opensRange, 2 ≤ F.stalkDepth x) :
    F ≅ (pushforward j).obj (F.restrict j) :=
  letI := F.isIso_restrictAdjunction_unit_app_of_two_le_depth j h
  asIso ((restrictAdjunction j).unit.app F)

/-- The forward map of the Hartogs isomorphism is the restriction adjunction unit. -/
@[simp]
theorem restrictAdjunctionUnitIsoOfTwoLeDepth_hom (F : X.Modules)
    [IsLocallyNoetherian X] [F.IsQuasicoherent] [F.IsFiniteType] {Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (h : ∀ x ∉ j.opensRange, 2 ≤ F.stalkDepth x) :
    (F.restrictAdjunctionUnitIsoOfTwoLeDepth j h).hom = (restrictAdjunction j).unit.app F := (rfl)

/-- **Hartogs extension for global sections.** For a coherent module on a locally Noetherian
scheme, restriction to an open is bijective if all stalks outside that open have depth at least
two. -/
theorem presheaf_map_leTop_bijective_of_two_le_depth (F : X.Modules)
    [IsLocallyNoetherian X] [F.IsQuasicoherent] [F.IsFiniteType]
    (U : X.Opens) (h : ∀ x ∉ U, 2 ≤ F.stalkDepth x) :
    Function.Bijective (F.presheaf.map U.leTop.op) := by
  have hunit := F.isIso_restrictAdjunction_unit_app_of_two_le_depth U.ι
    (fun x hx ↦ h x (by simpa only [Scheme.Opens.opensRange_ι] using hx))
  have htop : IsIso (F.presheaf.map (homOfLE (U.ι.image_preimage_le ⊤)).op) := by
    rw [← restrictAdjunction_unit_app_app U.ι F ⊤]
    exact Hom.isIso_iff_isIso_app.1 hunit ⊤
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ (⊤ : X.Opens) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_top_eq]
  have hr : IsIso (F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
    grind only
  exact (ConcreteCategory.isIso_iff_bijective _).1 hr

end AlgebraicGeometry.Scheme.Modules
