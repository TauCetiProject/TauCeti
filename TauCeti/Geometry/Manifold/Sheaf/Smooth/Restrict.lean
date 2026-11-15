/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Over

/-!
# Restricting the sheaf of smooth ring-valued functions to an open subset

Let `R` be a smooth ring, for instance `ℂ` with the model `𝓘(ℂ)`. Mathlib's
`smoothSheafRing IM I M R` is the sheaf of rings, valued in `RingCat`, of smooth functions
`M → R`. Sheaves of modules (`SheafOfModules`) are defined over sheaves valued in `RingCat`, so
this is the structure sheaf over which sheaves of modules on `M` are taken. It is the image of the
sheaf of commutative rings `smoothSheafCommRing IM I M R` under the forgetful functor
`CommRingCat ⥤ RingCat`, by definition
(`TauCeti.smoothSheafRing.sheafCompose_forget₂_smoothSheafCommRing`). For a complex manifold `M`
modelled on `𝓘(ℂ, E)` and `R = ℂ` it is the holomorphic structure sheaf, since complex-smooth
functions are holomorphic; for finite-dimensional `E`,
`TauCeti.holomorphicStructureSheaf.smoothSheafIso` compares `smoothSheafCommRing` with the sheaf of
complex analytic functions.

An open subset `U` of `M` is a manifold in its own right, with the restricted charts. This file
identifies its sheaf of smooth functions with the restriction `U.sheafRestrict` of the sheaf of
smooth functions on `M` (`TauCeti.smoothSheafRing.restrictIso`). Over an open subset `V` of `U`,
a section of the restricted sheaf is a smooth function on the image of `V` in `M`, and the
isomorphism composes it with the identification of `V` with its image. Composing with Mathlib's
`TopologicalSpace.Opens.overPullbackSheafEquivOver` gives the same identification for the
restriction to the over site of `U` (`TauCeti.smoothSheafRing.overIso`), the carrier of
`TopologicalSpace.Opens.sheafOfModulesEquivOver`. The identification is compatible with germs:
through it, the stalk of the sheaf of `U` at `x` is the stalk of the sheaf of `M` at `x`
(`TauCeti.smoothSheafRing.stalkIso`, `TauCeti.smoothSheafRing.germ_stalkIso_hom`).

No manifold axioms are needed: only the charted space structures enter.

## Main declarations

* `TauCeti.smoothSheafRing.restrictIso`: `U.sheafRestrict.obj (smoothSheafRing IM I M R)` is the
  sheaf of smooth functions on `U`.
* `TauCeti.smoothSheafRing.overIso`: the same for the restriction to the over site of `U`.
* `TauCeti.smoothSheafRing.stalkIso`: the stalks of the sheaves of `U` and of `M` at a point of `U`
  agree, compatibly with germs.

## References

* The sheaves are those of `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather Macbeth and
  Adam Topaz; the stalk comparison is `AlgebraicGeometry.PresheafedSpace.restrictStalkIso`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (R : Type u) [TopologicalSpace R] [ChartedSpace H R]

namespace TauCeti.smoothSheafRing

/-- The sheaf of smooth functions with values in a smooth ring, valued in `RingCat`, is the image
of the sheaf of smooth functions valued in `CommRingCat` under the forgetful functor. -/
theorem sheafCompose_forget₂_smoothSheafCommRing [CommRing R] [ContMDiffRing I ∞ R] :
    (sheafCompose (Opens.grothendieckTopology (TopCat.of M)) (forget₂ CommRingCat RingCat)).obj
      (smoothSheafCommRing IM I M R) = smoothSheafRing IM I M R :=
  (rfl)

variable [Ring R] [ContMDiffRing I ∞ R] {M}

/-- A point of an open subset `V` of `U`, as a point of the image of `V` in `M`. -/
private def toImage {U : Opens (TopCat.of M)} {V : Opens U} (x : V) :
    U.isOpenEmbedding.isOpenMap.functor.obj V :=
  ⟨x.1.1, x.1, x.2, rfl⟩

/-- A point of the image in `M` of an open subset `V` of `U`, as a point of `V`. -/
private def ofImage {U : Opens (TopCat.of M)} {V : Opens U}
    (y : U.isOpenEmbedding.isOpenMap.functor.obj V) : V :=
  ⟨⟨y.1, Subtype.coe_image_subset _ _ y.2⟩, by
    obtain ⟨a, ha, h⟩ := y.2
    exact (Subtype.ext h : a = ⟨y.1, Subtype.coe_image_subset _ _ y.2⟩) ▸ ha⟩

variable {IM} in
private theorem contMDiff_toImage {U : Opens (TopCat.of M)} (V : Opens U) :
    ContMDiff IM IM ∞ (toImage : V → U.isOpenEmbedding.isOpenMap.functor.obj V) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (contMDiff_subtype_val.comp contMDiff_subtype_val :
    ContMDiff IM IM ∞ fun x : V ↦ (x : U).1)

variable {IM} in
private theorem contMDiff_ofImage {U : Opens (TopCat.of M)} (V : Opens U) :
    ContMDiff IM IM ∞ (ofImage : U.isOpenEmbedding.isOpenMap.functor.obj V → V) := by
  rw [← ContMDiff.subtypeVal_comp_iff, ← ContMDiff.subtypeVal_comp_iff]
  exact contMDiff_subtype_val

/-- Smooth functions on the image in `M` of an open subset `V` of `U` are the smooth functions
on `V`. -/
private def sectionsRingEquiv {U : Opens (TopCat.of M)} (V : Opens U) :
    C^∞⟮IM, U.isOpenEmbedding.isOpenMap.functor.obj V; I, R⟯ ≃+* C^∞⟮IM, V; I, R⟯ where
  toFun f := ⟨f ∘ toImage, f.contMDiff.comp (contMDiff_toImage V)⟩
  invFun g := ⟨g ∘ ofImage, g.contMDiff.comp (contMDiff_ofImage V)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- **The sheaf of smooth functions restricts to open subsets.** The restriction to an open
subset `U` of the sheaf of smooth `R`-valued functions on `M` is the sheaf of smooth `R`-valued
functions on the manifold `U`. Over an open subset `V` of `U`, a smooth function on the image of
`V` in `M` corresponds to its composite with the identification of `V` with that image. -/
def restrictIso (U : Opens (TopCat.of M)) :
    U.sheafRestrict.obj (smoothSheafRing IM I M R) ≅ smoothSheafRing IM I U R :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun V ↦ (sectionsRingEquiv IM I R V.unop).toRingCatIso) (fun _ ↦ rfl)

-- Stored simp keys keep the carrier of `TopCat.of M` as a projection, which simp reduces in the
-- goal, so the simp lemmas below keep the section, point and open-set terms out of the index.
/-- The restriction isomorphism evaluates a section at the corresponding point of `M`. -/
@[simp]
theorem restrictIso_hom_app_apply (U : Opens (TopCat.of M)) (V : Opens U)
    (f : C^∞⟮IM, U.isOpenEmbedding.isOpenMap.functor.obj V; I, R⟯) (x : V) :
    @DFunLike.coe (no_index C^∞⟮IM, V; I, R⟯) (no_index ↥V) (fun _ ↦ R) _
        (no_index ((restrictIso IM I R U).hom.hom.app (op V) f)) x =
      f ⟨x.1.1, x.1, x.2, rfl⟩ :=
  (rfl)

/-- The inverse of the restriction isomorphism evaluates a section at the corresponding point
of `V`. -/
@[simp]
theorem restrictIso_inv_app_apply (U : Opens (TopCat.of M)) (V : Opens U)
    (g : C^∞⟮IM, V; I, R⟯) (x : V) :
    @DFunLike.coe (no_index C^∞⟮IM, U.isOpenEmbedding.isOpenMap.functor.obj V; I, R⟯)
        (no_index ↥(U.isOpenEmbedding.isOpenMap.functor.obj V)) (fun _ ↦ R) _
        (no_index ((restrictIso IM I R U).inv.hom.app (op V) g))
        (no_index ⟨x.1.1, x.1, x.2, rfl⟩) =
      g x :=
  (rfl)

/-- The restriction of the sheaf of smooth functions to the over site of an open subset `U`,
transported to a sheaf on `U`, is the sheaf of smooth functions on `U`. -/
def overIso (U : Opens (TopCat.of M)) :
    U.sheafEquivOver.functor.obj ((smoothSheafRing IM I M R).over U) ≅ smoothSheafRing IM I U R :=
  U.overPullbackSheafEquivOver.app _ ≪≫ restrictIso IM I R U

/-- Over each open subset of `U`, the comparison for the over site is the restriction
isomorphism. -/
@[simp]
theorem overIso_hom_app (U : Opens (TopCat.of M)) (V : Opens U) :
    (overIso IM I R U).hom.hom.app (no_index (op V)) = (restrictIso IM I R U).hom.hom.app (op V) :=
  (rfl)

/-- The stalk at a point `x` of an open subset `U` of the sheaf of smooth functions on `U` is the
stalk at `x` of the sheaf of smooth functions on `M`. -/
def stalkIso (U : Opens (TopCat.of M)) (x : U) :
    (smoothSheafRing IM I U R).presheaf.stalk x ≅ (smoothSheafRing IM I M R).presheaf.stalk x.1 :=
  (TopCat.Presheaf.stalkFunctor RingCat (X := TopCat.of U) x).mapIso
      ((sheafToPresheaf _ _).mapIso (restrictIso IM I R U)).symm ≪≫
    (AlgebraicGeometry.PresheafedSpace.mk (TopCat.of M)
      (smoothSheafRing IM I M R).presheaf).restrictStalkIso U.isOpenEmbedding x

/-- The stalk comparison sends the germ of a smooth function on an open subset `V` of `U` to the
germ of the corresponding smooth function on the image of `V` in `M`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem germ_stalkIso_hom (U : Opens (TopCat.of M)) (V : Opens U) (x : U) (hx : x ∈ V) :
    (smoothSheafRing IM I U R).presheaf.germ V x hx ≫ (stalkIso IM I R U x).hom =
      (restrictIso IM I R U).inv.hom.app (op V) ≫
        (smoothSheafRing IM I M R).presheaf.germ (U.isOpenEmbedding.isOpenMap.functor.obj V) x.1
          ⟨x, hx, rfl⟩ := by
  simp only [stalkIso]
  -- The presheaf of the restricted sheaf is that of `PresheafedSpace.restrict` only up to
  -- unfolding `Opens.sheafRestrict`, so the germ lemma is matched up to definitional equality.
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  congr 1
  exact AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ
    (AlgebraicGeometry.PresheafedSpace.mk (TopCat.of M) (smoothSheafRing IM I M R).presheaf)
    U.isOpenEmbedding V x hx

end TauCeti.smoothSheafRing
