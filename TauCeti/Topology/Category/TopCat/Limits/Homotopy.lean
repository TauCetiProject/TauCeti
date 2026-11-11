/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies out of colimits in `TopCat`

Let `X : J ⥤ TopCat` be a diagram of spaces with a colimit cocone `cX`, and let
`f g : cX.pt → W` be continuous maps. Homotopies `H j` between the restrictions of `f` and `g` to
the spaces `X j` which are compatible with the maps of the diagram glue to a homotopy from `f` to
`g` (`CategoryTheory.Limits.IsColimit.homotopyDesc`). Read as maps into the path space `C(I, W)`,
compatible homotopies form a cocone, and since `I` is locally compact the induced map out of the
colimit uncurries to a continuous homotopy.

For natural transformations `φ ψ : X ⟶ Z`, homotopies from `φ.app j` to `ψ.app j` compatible with
the maps of the diagrams give a homotopy between the induced maps of colimits
(`CategoryTheory.Limits.IsColimit.homotopic_map`). In particular, compatible homotopies `ψ ∘ φ ≃ id`
make the map of colimits induced by `ψ` a left homotopy inverse of the one induced by `φ`
(`CategoryTheory.Limits.IsColimit.map_comp_map_homotopic_id`).

The pushout case, with homotopies given on the two legs of a pushout square, is
`CategoryTheory.IsPushout.homotopyDesc`.
-/

public section

open CategoryTheory Limits ContinuousMap unitInterval

universe w v u

namespace CategoryTheory.Limits.IsColimit

variable {J : Type w} [Category.{v} J] {X Z : J ⥤ TopCat.{u}}

section homotopyDesc

variable {cX : Cocone X} (hcX : IsColimit cX) {W : Type u} [TopologicalSpace W]
  {f g : C(cX.pt, W)} (H : ∀ j, (f.comp (cX.ι.app j).hom).Homotopy (g.comp (cX.ι.app j).hom))
  (hH : ∀ ⦃i j : J⦄ (u : i ⟶ j) (t : I) (x : X.obj i), H j (t, X.map u x) = H i (t, x))

/-- The map `cX.pt → C(I, W)` glued from the curried homotopies `H j`. -/
private noncomputable def homotopyCurry : cX.pt ⟶ TopCat.of C(I, W) :=
  hcX.desc
    { pt := TopCat.of C(I, W)
      ι :=
        { app := fun j => TopCat.ofHom ((H j).toContinuousMap.comp prodSwap).curry
          naturality := fun i j u => by
            ext x
            refine ContinuousMap.ext fun t => ?_
            exact hH u t x } }

private theorem homotopyCurry_ι (j : J) (x : X.obj j) (t : I) :
    hcX.homotopyCurry H hH (cX.ι.app j x) t = H j (t, x) := by
  rw [homotopyCurry, ← ConcreteCategory.comp_apply, hcX.fac]
  rfl

/-- **Gluing homotopies on a colimit.** Let `cX` be a colimit cocone of a diagram `X` of spaces,
and let `f g : cX.pt → W` be continuous maps. Homotopies `H j` between the restrictions of `f` and
`g` to the spaces `X j` which are compatible with the maps of the diagram glue to a homotopy from
`f` to `g`. -/
noncomputable def homotopyDesc : f.Homotopy g where
  toContinuousMap := (hcX.homotopyCurry H hH).hom.uncurry.comp prodSwap
  map_zero_left x := by
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep X hcX x
    exact (hcX.homotopyCurry_ι H hH j y 0).trans ((H j).apply_zero y)
  map_one_left x := by
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep X hcX x
    exact (hcX.homotopyCurry_ι H hH j y 1).trans ((H j).apply_one y)

/-- On `X j`, the glued homotopy `CategoryTheory.Limits.IsColimit.homotopyDesc` is `H j`. -/
@[simp]
theorem homotopyDesc_apply_ι (j : J) (t : I) (x : X.obj j) :
    hcX.homotopyDesc H hH (t, dsimp% cX.ι.app j x) = H j (t, x) :=
  hcX.homotopyCurry_ι H hH j x t

end homotopyDesc

/-- **Gluing homotopies of maps of diagrams on a colimit.** Let `φ ψ : X ⟶ Z` be maps of diagrams
of spaces, and let `H j` be homotopies from `φ.app j` to `ψ.app j` which are compatible with the
maps of the diagrams. Then for a colimit cocone `cX` of `X` and any cocone `cZ` of `Z`, the induced
maps `cX.pt → cZ.pt` are homotopic. -/
theorem homotopic_map {cX : Cocone X} (hcX : IsColimit cX) (cZ : Cocone Z) {φ ψ : X ⟶ Z}
    (H : ∀ j, (φ.app j).hom.Homotopy (ψ.app j).hom)
    (hH : ∀ ⦃i j : J⦄ (u : i ⟶ j) (t : I) (x : X.obj i),
      H j (t, X.map u x) = Z.map u (H i (t, x))) :
    (hcX.map cZ φ).hom.Homotopic (hcX.map cZ ψ).hom := by
  have hmap (α : X ⟶ Z) (j : J) :
      (hcX.map cZ α).hom.comp (cX.ι.app j).hom = (cZ.ι.app j).hom.comp (α.app j).hom := by
    rw [← TopCat.hom_comp, hcX.ι_map, TopCat.hom_comp]
  refine ⟨hcX.homotopyDesc
    (fun j => ((Homotopy.refl (cZ.ι.app j).hom).comp (H j)).cast (hmap φ j).symm (hmap ψ j).symm)
    fun i j u t x => ?_⟩
  simp only [Homotopy.cast_apply, Homotopy.comp_apply, Homotopy.refl_apply, hH]
  exact ConcreteCategory.congr_hom (cZ.w u) (H i (t, x))

/-- **Left homotopy inverses on a colimit.** Let `φ : X ⟶ Z` and `ψ : Z ⟶ X` be maps of diagrams
of spaces, and let `H j : ψ.app j ∘ φ.app j ≃ id` be homotopies which are compatible with the maps
of `X`. Then for colimit cocones `cX` of `X` and `cZ` of `Z`, the map induced by `ψ` is a left
homotopy inverse of the map induced by `φ`. -/
theorem map_comp_map_homotopic_id {cX : Cocone X} (hcX : IsColimit cX) {cZ : Cocone Z}
    (hcZ : IsColimit cZ) {φ : X ⟶ Z} {ψ : Z ⟶ X}
    (H : ∀ j, ((ψ.app j).hom.comp (φ.app j).hom).Homotopy (ContinuousMap.id (X.obj j)))
    (hH : ∀ ⦃i j : J⦄ (u : i ⟶ j) (t : I) (x : X.obj i),
      H j (t, X.map u x) = X.map u (H i (t, x))) :
    ((hcZ.map cX ψ).hom.comp (hcX.map cZ φ).hom).Homotopic (ContinuousMap.id cX.pt) := by
  -- The components of `φ ≫ ψ` and `𝟙 X` are by definition the composites and identities that
  -- the homotopies `H j` connect.
  have h := hcX.homotopic_map cX (φ := φ ≫ ψ) (ψ := 𝟙 X) H hH
  rwa [show hcX.map cX (φ ≫ ψ) = hcX.map cZ φ ≫ hcZ.map cX ψ from hcX.hom_ext fun j => by simp,
    show hcX.map cX (𝟙 X) = 𝟙 cX.pt from hcX.hom_ext fun j => by simp] at h

end CategoryTheory.Limits.IsColimit
