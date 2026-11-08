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

Let `X Z : J ⥤ TopCat` be diagrams of spaces, and let `φ ψ : X ⟶ Z` be natural transformations.
Homotopies `H j` from `φ.app j` to `ψ.app j` which are compatible with the maps of the diagrams
glue to a homotopy between the induced maps out of a colimit of `X`
(`CategoryTheory.Limits.IsColimit.homotopic_map`). Read as maps into the path space `C(I, Z)`,
compatible homotopies form a cocone, and since `I` is locally compact the induced map out of the
colimit uncurries to a continuous homotopy. In particular, compatible homotopies `ψ ∘ φ ≃ id`
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

/-- **Gluing homotopies on a colimit.** Let `φ ψ : X ⟶ Z` be maps of diagrams of spaces, and let
`H j` be homotopies from `φ.app j` to `ψ.app j` which are compatible with the maps of the
diagrams. Then for a colimit cocone `cX` of `X` and any cocone `cZ` of `Z`, the induced maps
`cX.pt → cZ.pt` are homotopic. -/
theorem homotopic_map {cX : Cocone X} (hcX : IsColimit cX) (cZ : Cocone Z) {φ ψ : X ⟶ Z}
    (H : ∀ j, (φ.app j).hom.Homotopy (ψ.app j).hom)
    (hH : ∀ ⦃i j : J⦄ (u : i ⟶ j) (t : I) (x : X.obj i),
      H j (t, X.map u x) = Z.map u (H i (t, x))) :
    (hcX.map cZ φ).hom.Homotopic (hcX.map cZ ψ).hom := by
  -- The homotopies `H j`, read as maps into the path space `C(I, cZ.pt)`, form a cocone.
  let ι (j : J) : X.obj j ⟶ TopCat.of C(I, cZ.pt) :=
    TopCat.ofHom (((cZ.ι.app j).hom.comp (H j).toContinuousMap).comp prodSwap).curry
  have hι (j : J) (x : X.obj j) (t : I) : (ι j).hom x t = cZ.ι.app j (H j (t, x)) := rfl
  let c : Cocone X :=
    { pt := TopCat.of C(I, cZ.pt)
      ι :=
        { app := ι
          naturality := fun i j u => by
            ext x
            refine ContinuousMap.ext fun t => ?_
            exact (congrArg (cZ.ι.app j) (hH u t x)).trans
              (ConcreteCategory.congr_hom (cZ.w u) (H i (t, x))) } }
  let D := hcX.desc c
  have hD (j : J) (x : X.obj j) (t : I) : D (cX.ι.app j x) t = cZ.ι.app j (H j (t, x)) := by
    rw [← ConcreteCategory.comp_apply, hcX.fac c j]
    exact hι j x t
  have hmap (α : X ⟶ Z) (j : J) (x : X.obj j) :
      hcX.map cZ α (cX.ι.app j x) = cZ.ι.app j (α.app j x) := by
    rw [← ConcreteCategory.comp_apply, hcX.ι_map, ConcreteCategory.comp_apply]
  refine ⟨{ toContinuousMap := D.hom.uncurry.comp prodSwap
            map_zero_left := fun x => ?_
            map_one_left := fun x => ?_ }⟩ <;>
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep X hcX x <;>
  simp [hD, hmap]

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
