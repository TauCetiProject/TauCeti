/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map

/-!
# Flat descent of closed subgroup schemes

Let `g : G' ⟶ G` be a morphism of group schemes lying over `f : S' ⟶ S`, compatible with
multiplication, such that the square formed by `g`, `f` and the structure morphisms is a pullback
square. The inverse image along `g` of a closed subgroup scheme `V(D)` of `G` is a closed subgroup
scheme of `G'` (`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`). Conversely, if every base
change of `f` is scheme-theoretically dominant, then `V(D)` is a subgroup scheme as soon as its
inverse image in `G'` is (`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff`). This applies to
flat surjective `f` (`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`).
No finiteness or flatness hypothesis is placed on `V(D)`, and `f` need not be quasi-compact, so
this is not an instance of effective fpqc descent.

Each of the three conditions of the closed-subgroup criterion for `V(D.comap g)`
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_le`) says that `D` vanishes on a morphism
`p ≫ φ`, where `φ` is the corresponding morphism for `V(D)` and `p` is `f` or a base change of
`f`. When `p` is scheme-theoretically dominant, `p ≫ φ` and `φ` have the same kernel
(`AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped MonObj

namespace TauCeti.GroupScheme

universe u

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {g : G'.left ⟶ G.left}

/-- **Subgroup schemes descend along universally scheme-theoretically dominant morphisms.** Let
`g : G' ⟶ G` be a morphism of group schemes lying over `f : S' ⟶ S`, all of whose base changes are
scheme-theoretically dominant, forming a pullback square with the structure morphisms and
compatible with multiplication, and let `V(D) ⊆ G` be a closed subscheme. Then `V(D)` is a subgroup
scheme of `G` exactly when its inverse image in `G'` is a subgroup scheme of `G'`. The base-change
direction (`.mpr`) is `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`, which needs no
hypothesis on `f`. -/
theorem exists_grpObj_isMonHom_comap_iff
    (hf : MorphismProperty.universally @IsSchemeTheoreticallyDominant f)
    (hg : IsPullback g G'.hom G.hom f)
    (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ μ[G].left)
    (D : G.left.IdealSheafData) :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G')) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ G.hom)),
        IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ G.hom) ⟶ G) := by
  rw [exists_grpObj_isMonHom_comap_iff_le hg.w hμ, exists_grpObj_isMonHom_iff_le]
  -- `ρ : V(D.comap g) ⟶ V(D)` is the base change of `V(D)` along `f`, and so is its fibre square
  -- over `f`, so both are scheme-theoretically dominant.
  have hD := D.isPullback_subschemeMap_comap G.hom hg
  have : IsSchemeTheoreticallyDominant f := MorphismProperty.universally_le _ _ hf
  have : IsSchemeTheoreticallyDominant
      (Scheme.IdealSheafData.subschemeMap (D.comap g) D g (D.le_map_comap g)) := hf _ _ _ hD
  have : IsSchemeTheoreticallyDominant (pullback.map _ _ _ _ _ _ f
      (D.comap_subschemeι_comp_comp hg.w) (D.comap_subschemeι_comp_comp hg.w)) :=
    hf _ _ _ (hD.flip.pullback_map hD.flip).flip
  simp only [Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant]

/-- **Subgroup schemes descend along flat surjective morphisms.** Let `g : G' ⟶ G` be a morphism
of group schemes lying over a flat surjective `f : S' ⟶ S`, forming a pullback square with the
structure morphisms and compatible with multiplication, and let `V(D) ⊆ G` be a closed subscheme.
Then `V(D)` is a subgroup scheme of `G` exactly when its inverse image in `G'` is a subgroup scheme
of `G'`. -/
theorem exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective [Flat f] [Surjective f]
    (hg : IsPullback g G'.hom G.hom f)
    (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ μ[G].left)
    (D : G.left.IdealSheafData) :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G')) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ G.hom)),
        IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ G.hom) ⟶ G) :=
  exists_grpObj_isMonHom_comap_iff
    (IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective f) hg hμ D

end TauCeti.GroupScheme
