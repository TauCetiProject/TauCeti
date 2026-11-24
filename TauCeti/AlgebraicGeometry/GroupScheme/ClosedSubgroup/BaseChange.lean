/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
public import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Monoidal.Cartesian.Over
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion

/-!
# Base change of closed subgroup schemes

Let `G` be a group scheme over `X` and `s : Y ⟶ X` a morphism of schemes. The base change of `G`
to `Y` is the group scheme `(Over.pullback s).mapGrp.obj G` over `Y`. This file shows that a closed
subgroup scheme `P` of `G` base-changes to a closed subgroup scheme of the base change of `G`: the
base change of a closed immersion of group schemes is again a closed immersion, since its
underlying morphism is the pullback of the original one along the projection
`G ×_X Y ⟶ G`.

More generally, let `g : G' ⟶ G` be a morphism of group schemes lying over `f : S' ⟶ S` and
compatible with multiplication, let `V(D)` be a closed subscheme of `G`, and let
`ρ : V(D.comap g) ⟶ V(D)` be induced by `g`. Then `V(D.comap g)` is a subgroup scheme of `G'`
exactly when `D` vanishes on three morphisms to `G`: the identity of `G` composed with `f`; the
product of the two points of `G` with values in `V(D.comap g) ×_{S'} V(D.comap g)` obtained by
composing its two projections with `ρ` and the inclusion of `V(D)` into `G`, which lie over the
same morphism to `S`; and the inverse of the point `ρ` composed with that inclusion
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_le`). In
particular the inverse image of a closed subgroup scheme is a closed subgroup scheme
(`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`); the converse holds along flat surjective
base changes (`TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.FlatDescent`).

## Main declarations

* `TauCeti.ClosedSubgroupScheme.baseChange s P`: the base change of a closed subgroup scheme `P`
  of `G` along `s`, a closed subgroup scheme of the base change of `G`.
* `TauCeti.ClosedSubgroupScheme.baseChange_mk`: the base change of the closed subgroup scheme
  represented by a closed immersion `i` is represented by the base change of `i`.
* `TauCeti.ClosedSubgroupScheme.baseChange_mono`: base change preserves inclusions of closed
  subgroup schemes.
* `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_le`: the closed-subgroup criterion for an
  inverse image `V(D.comap g)`, stated in terms of `D`.
* `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`: inverse images of closed subgroup schemes
  are closed subgroup schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.ClosedSubgroupScheme

universe u

variable {X Y : Scheme.{u}} (s : Y ⟶ X) {G K : Grp (Over X)}

/-- The base change of a closed immersion of group schemes is a closed immersion. -/
instance isClosedImmersion_pullback_mapGrp_map (i : K ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion ((Over.pullback s).mapGrp.map i).hom.hom.left :=
  MorphismProperty.of_isPullback (Over.isPullback_pullback_map_left s i.hom.hom).flip
    inferInstance

/-- The **base change of a closed subgroup scheme** `P` of `G` along `s : Y ⟶ X`: the closed
subgroup scheme of the base change `(Over.pullback s).mapGrp.obj G` represented by the base change
of the inclusion of `P`. -/
noncomputable def baseChange (P : ClosedSubgroupScheme G) :
    ClosedSubgroupScheme ((Over.pullback s).mapGrp.obj G) :=
  mk ((Over.pullback s).mapGrp.map P.val.arrow)

/-- The base change of `P` is represented by the base change of the inclusion of `P`. -/
theorem baseChange_def (P : ClosedSubgroupScheme G) :
    baseChange s P = mk ((Over.pullback s).mapGrp.map P.val.arrow) :=
  (rfl)

/-- The base change of the closed subgroup scheme represented by a closed immersion `i` is
represented by the base change of `i`. -/
@[simp]
theorem baseChange_mk (i : K ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    baseChange s (mk i) = mk ((Over.pullback s).mapGrp.map i) := by
  refine Subtype.ext ?_
  rw [coe_mk, baseChange_def, coe_mk]
  refine Subobject.mk_eq_mk_of_comm _ _ ((Over.pullback s).mapGrp.mapIso (mkIso i)) ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← (Iso.inv_comp_eq _).1 (mkIso_inv_comp_arrow i)]

/-- Base change preserves inclusions of closed subgroup schemes. -/
theorem baseChange_mono : Monotone (baseChange (G := G) s) := by
  intro P Q h
  refine Subtype.coe_le_coe.1 ?_
  rw [baseChange_def, baseChange_def, coe_mk, coe_mk]
  exact Subobject.mk_le_mk_of_comm
    ((Over.pullback s).mapGrp.map (Subobject.ofLE _ _ (Subtype.coe_le_coe.2 h)))
    (by rw [← Functor.map_comp, Subobject.ofLE_arrow])

end TauCeti.ClosedSubgroupScheme

namespace TauCeti.GroupScheme

open CategoryTheory Limits AlgebraicGeometry Scheme.IdealSheafData
open scoped MonObj

universe u

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {g : G'.left ⟶ G.left} (w : g ≫ G.hom = G'.hom ≫ f)
  (hμ : μ[G'].left ≫ g = pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left)
  (D : G.left.IdealSheafData)

include hμ

/-- **The closed-subgroup criterion for an inverse image.** Let `g : G' ⟶ G` be a morphism of
group schemes lying over `f : S' ⟶ S` and compatible with multiplication, let `V(D) ⊆ G` be a
closed subscheme, and let `ρ : V(D.comap g) ⟶ V(D)` be induced by `g`. Then `V(D.comap g)` is a
subgroup scheme of `G'` exactly when `D` vanishes on the identity of `G` composed with `f`, on the
product of the two points of `G` with values in `V(D.comap g) ×_{S'} V(D.comap g)` obtained by
composing its two projections with `ρ` and the inclusion of `V(D)` into `G`, and on the inverse of
the point `ρ` composed with that inclusion. -/
theorem exists_grpObj_isMonHom_comap_iff_le :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G')) ↔
      D ≤ (f ≫ η[G].left).ker ∧
      D ≤ (pullback.map _ _ _ _ _ _ f (D.comap_subschemeι_comp_comp w)
          (D.comap_subschemeι_comp_comp w) ≫
        pullback.map (D.subschemeι ≫ G.hom) (D.subschemeι ≫ G.hom) G.hom G.hom D.subschemeι
          D.subschemeι (𝟙 S) (by simp) (by simp) ≫ μ[G].left).ker ∧
      D ≤ (subschemeMap (D.comap g) D g (D.le_map_comap g) ≫ D.subschemeι ≫ ι[G].left).ker := by
  -- `D.comap g` lies in the kernel of `φ'` exactly when `D` lies in that of `φ' ≫ g`, and `g`
  -- carries the identity, products and inverses of points of `V(D.comap g)` to those of `V(D)`.
  rw [exists_grpObj_isMonHom_iff_le]
  simp only [← le_map_iff_comap_le, map_ker, Category.assoc,
    Over.one_left_comp_of_mul_left_comp w hμ,
    Over.inv_left_comp_of_mul_left_comp w hμ, subschemeMap_subschemeι_assoc, hμ,
    pullback.map_comp_assoc, subschemeMap_subschemeι, Category.id_comp, Category.comp_id]

/-- **Closed subgroup schemes are stable under inverse image.** Let `g : G' ⟶ G` be a morphism of
group schemes lying over `f : S' ⟶ S` and compatible with multiplication. If the closed subscheme
of `G` cut out by `D` is a subgroup scheme, then so is its inverse image in `G'`. -/
theorem exists_grpObj_isMonHom_comap
    (hD : ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ G.hom)),
      IsMonHom (Over.homMk D.subschemeι : Over.mk (D.subschemeι ≫ G.hom) ⟶ G)) :
    ∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ G'.hom)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ G'.hom) ⟶ G') := by
  obtain ⟨he, hm, hj⟩ := (exists_grpObj_isMonHom_iff_le D).mp hD
  exact (exists_grpObj_isMonHom_comap_iff_le w hμ D).mpr ⟨he.trans (Scheme.Hom.le_ker_comp _ _),
    hm.trans (Scheme.Hom.le_ker_comp _ _), hj.trans (Scheme.Hom.le_ker_comp _ _)⟩

end TauCeti.GroupScheme
