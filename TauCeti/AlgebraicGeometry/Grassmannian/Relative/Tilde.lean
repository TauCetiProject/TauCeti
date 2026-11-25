/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Relative.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# The relative Grassmannian of the sheaf of a module

Let `R` be a commutative ring, `M` an `R`-module and `k` a natural number. The relative
Grassmannian `G(k, M~)` of the quasi-coherent sheaf `M~` on `Spec R` is Tau Ceti's Grassmannian
scheme `G(k, M)` of the module, over `Spec R`
(`AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso`).

Over the affine open `⊤` of `Spec R` the relative Grassmannian is `G(k, Γ(M~, ⊤))` over
`Spec Γ(Spec R, ⊤)` (`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`), and
the inclusion of this part is an isomorphism because `Spec Γ(Spec R, ⊤) ⟶ Spec R` is one. The
change of base ring along `R ≅ Γ(Spec R, ⊤)` is a base change of modules
(`AlgebraicGeometry.isBaseChange_tildeToTop`), so the base change morphism
`IsBaseChange.grassmannianSchemeHom` gives `G(k, Γ(M~, ⊤)) ≅ G(k, M)`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso`: `G(k, M~) ≅ G(k, M)`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianι_grassmannianTildeIso_hom`: on the part over `⊤`
  it is the base change morphism.
* `AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso_hom_toSpec`,
  `AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso_inv_toBase`: it lies over `Spec R`.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (k : ℕ)

/-- The part of `G(k, M~)` over the affine open `⊤` of `Spec R` is all of it. -/
instance isIso_grassmannianι_tilde_top :
    IsIso (grassmannianι (tilde M) k ⟨⊤, isAffineOpen_top _⟩) := by
  have : IsIso (isAffineOpen_top (Spec R)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  exact (isPullback_grassmannianι_fromSpec (tilde M) k ⟨⊤, isAffineOpen_top _⟩).isIso_snd_of_isIso

/-- Changing the base ring along `R ≅ Γ(Spec R, ⊤)` is an isomorphism of Grassmannians. -/
instance isIso_grassmannianSchemeHom_tildeToTop :
    IsIso ((isBaseChange_tildeToTop M).grassmannianSchemeHom k) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, ⊤)))) := by
    rw [Spec_map_algebraMap_Spec_top, IsAffineOpen.fromSpec_top]
    infer_instance
  exact ((isBaseChange_tildeToTop M).isPullback_grassmannianSchemeHom k).flip.isIso_snd_of_isIso

/-- **The relative Grassmannian of `M~` is the Grassmannian of `M`.** For a module `M` over a
commutative ring `R`, the relative Grassmannian `G(k, M~)` of the quasi-coherent sheaf `M~` on
`Spec R` is isomorphic to the Grassmannian scheme `G(k, M)`, over `Spec R`
(`AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso_hom_toSpec`). -/
noncomputable def grassmannianTildeIso :
    grassmannian (tilde M) k ≅ Module.Grassmannian.scheme R M k :=
  (asIso (grassmannianι (tilde M) k ⟨⊤, isAffineOpen_top _⟩)).symm ≪≫
    asIso ((isBaseChange_tildeToTop M).grassmannianSchemeHom k)

/-- On the part over `⊤`, the isomorphism `G(k, M~) ≅ G(k, M)` is the base change morphism along
`R ≅ Γ(Spec R, ⊤)`. -/
@[reassoc (attr := simp)]
theorem grassmannianι_grassmannianTildeIso_hom :
    grassmannianι (tilde M) k ⟨⊤, isAffineOpen_top _⟩ ≫ (grassmannianTildeIso M k).hom =
      (isBaseChange_tildeToTop M).grassmannianSchemeHom k := by
  rw [grassmannianTildeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc]

/-- The isomorphism `G(k, M~) ≅ G(k, M)` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem grassmannianTildeIso_hom_toSpec :
    (grassmannianTildeIso M k).hom ≫ Module.Grassmannian.toSpec R M k =
      grassmannianToBase (tilde M) k := by
  rw [← cancel_epi (grassmannianι (tilde M) k ⟨⊤, isAffineOpen_top _⟩),
    grassmannianι_grassmannianTildeIso_hom_assoc, IsBaseChange.grassmannianSchemeHom_toSpec,
    grassmannianι_toBase, Spec_map_algebraMap_Spec_top]
  -- The two sides differ only in how the base and the open are written: the chart over
  -- `⟨⊤, _⟩ : (Spec R).affineOpens` uses its projections `.val` and `.property`, and
  -- `Module.Grassmannian.toSpec` lands in `Spec (CommRingCat.of R)`, which is `Spec R` by the
  -- structure eta of `CommRingCat`.
  rfl

/-- The inverse of `G(k, M~) ≅ G(k, M)` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem grassmannianTildeIso_inv_toBase :
    (grassmannianTildeIso M k).inv ≫ grassmannianToBase (tilde M) k =
      Module.Grassmannian.toSpec R M k := by
  rw [Iso.inv_comp_eq, grassmannianTildeIso_hom_toSpec]

end AlgebraicGeometry.Scheme.Modules
