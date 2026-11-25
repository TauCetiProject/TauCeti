/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
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
`G ×_X Y ⟶ G`. The carrier of `baseChange s P` is canonically a pullback of the carrier of `P`
along `s` (`isPullback_baseChange_hom`), so finiteness, flatness, local finite presentation, and
`Scheme.Hom.finrank` are preserved (`finrank_baseChange`).

Base change of closed subgroup schemes is compatible with identity morphisms
(`Grp.pullbackIdIso`), composition (`Grp.pullbackCompIso`), and equality of base morphisms
(`Grp.pullbackCongrIso`), so the two pullbacks of `baseChange p P` to the self-fibre product
`Y ×_X Y` correspond under the canonical overlap isomorphism `Grp.pullbackOverlapIso p G`
(`mapIso_pullbackOverlapIso_baseChange`).

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
* `TauCeti.ClosedSubgroupScheme.baseChangeCarrierIso`,
  `TauCeti.ClosedSubgroupScheme.isPullback_baseChange_hom`, and
  `TauCeti.ClosedSubgroupScheme.finrank_baseChange`: carrier pullback square and preservation of
  finiteness, flatness, local finite presentation, and rank under base change.
* `TauCeti.ClosedSubgroupScheme.mapIso_pullbackIdIso_baseChange`,
  `TauCeti.ClosedSubgroupScheme.mapIso_pullbackCompIso_baseChange`,
  `TauCeti.ClosedSubgroupScheme.mapIso_pullbackCongrIso_baseChange`,
  `TauCeti.ClosedSubgroupScheme.mapIso_pullbackOverlapIso_baseChange`: `@[simp]` transport lemmas
  relating `baseChange` to the canonical pullback isomorphisms of `CategoryTheory.Grp`.
* `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_le`: the closed-subgroup criterion for an
  inverse image `V(D.comap g)`, stated in terms of `D`.
* `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`: inverse images of closed subgroup schemes
  are closed subgroup schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

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

/-- The canonical isomorphism between the group scheme underlying `baseChange s P` and the
base-changed group scheme `(Over.pullback s).mapGrp.obj (P.val : Grp (Over X))`. -/
noncomputable def baseChangeCarrierIso (P : ClosedSubgroupScheme G) :
    ((baseChange s P).val : Grp (Over Y)) ≅ (Over.pullback s).mapGrp.obj (P.val : Grp (Over X)) :=
  mkIso ((Over.pullback s).mapGrp.map P.val.arrow)

/-- The inverse of `baseChangeCarrierIso` intertwines the inclusion of `baseChange s P` with the
base-changed inclusion of `P`. -/
@[simp]
theorem baseChangeCarrierIso_inv_comp_arrow (P : ClosedSubgroupScheme G) :
    (baseChangeCarrierIso s P).inv ≫ (baseChange s P).val.arrow =
      (Over.pullback s).mapGrp.map P.val.arrow :=
  mkIso_inv_comp_arrow ((Over.pullback s).mapGrp.map P.val.arrow)

/-- The structure morphism to `Y` of `baseChange s P` factors through the second pullback
projection via `baseChangeCarrierIso s P`. -/
@[reassoc]
theorem baseChangeCarrierIso_hom_left_snd (P : ClosedSubgroupScheme G) :
    (baseChangeCarrierIso s P).hom.hom.hom.left ≫ pullback.snd (P.val : Grp (Over X)).X.hom s =
      ((baseChange s P).val : Grp (Over Y)).X.hom :=
  Over.w (baseChangeCarrierIso s P).hom.hom.hom

/-- `baseChangeCarrierIso s P` exhibits the structure morphism to `Y` of `baseChange s P` as a
pullback of the structure morphism to `X` of `P` along `s`. -/
theorem isPullback_baseChange_hom (P : ClosedSubgroupScheme G) :
    IsPullback ((baseChange s P).val : Grp (Over Y)).X.hom
      ((baseChangeCarrierIso s P).hom.hom.hom.left ≫ pullback.fst (P.val : Grp (Over X)).X.hom s)
      s (P.val : Grp (Over X)).X.hom := by
  let e : ((baseChange s P).val : Grp (Over Y)).X.left ≅ pullback (P.val : Grp (Over X)).X.hom s :=
    (Grp.forget (Over Y) ⋙ Over.forget Y).mapIso (baseChangeCarrierIso s P)
  exact (IsPullback.of_hasPullback (P.val : Grp (Over X)).X.hom s).flip.of_iso
    e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Category.comp_id, ← baseChangeCarrierIso_hom_left_snd]
      exact (e.inv_hom_id_assoc _).symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (e.inv_hom_id_assoc _).symm)
    (by simp) (by simp)

section BaseChangeProperties

variable (P : ClosedSubgroupScheme G)

/-- If a closed subgroup scheme `P` of `G` is finite over `X`, then `baseChange s P` is finite
over `Y`. -/
instance isFinite_baseChange [IsFinite (P.val : Grp (Over X)).X.hom] :
    IsFinite ((baseChange s P).val : Grp (Over Y)).X.hom :=
  MorphismProperty.of_isPullback (isPullback_baseChange_hom s P).flip ‹_›

/-- If a closed subgroup scheme `P` of `G` is flat over `X`, then `baseChange s P` is flat over
`Y`. -/
instance flat_baseChange [Flat (P.val : Grp (Over X)).X.hom] :
    Flat ((baseChange s P).val : Grp (Over Y)).X.hom :=
  MorphismProperty.of_isPullback (isPullback_baseChange_hom s P).flip ‹_›

/-- If a closed subgroup scheme `P` of `G` is locally of finite presentation over `X`, then
`baseChange s P` is locally of finite presentation over `Y`. -/
instance locallyOfFinitePresentation_baseChange
    [LocallyOfFinitePresentation (P.val : Grp (Over X)).X.hom] :
    LocallyOfFinitePresentation ((baseChange s P).val : Grp (Over Y)).X.hom :=
  MorphismProperty.of_isPullback (isPullback_baseChange_hom s P).flip ‹_›

/-- **Base-change invariance of rank for closed subgroup schemes.** If `P` is finite and flat over
`X`, the rank of `baseChange s P` over `Y` is the rank of `P` pulled back along `s`. -/
theorem finrank_baseChange [IsFinite (P.val : Grp (Over X)).X.hom]
    [Flat (P.val : Grp (Over X)).X.hom] :
    ((baseChange s P).val : Grp (Over Y)).X.hom.finrank =
      (P.val : Grp (Over X)).X.hom.finrank ∘ s := by
  funext y
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_baseChange_hom s P).flip y

end BaseChangeProperties

section Functoriality

/-- Base change along the identity morphism fixes every closed subgroup scheme under
`Grp.pullbackIdIso`. -/
@[simp]
theorem mapIso_pullbackIdIso_baseChange (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackIdIso G) (baseChange (𝟙 X) P) = P := by
  refine Subtype.ext ?_
  rw [baseChange_def, mapIso_mk, coe_mk]
  exact (Subobject.mk_eq_mk_of_comm _ _ (Grp.pullbackIdIso (P.val : Grp (Over X)))
    (Grp.pullbackIdIso_hom_naturality P.val.arrow).symm).trans (Subobject.mk_arrow P.val)

/-- Iterated base change of a closed subgroup scheme agrees with base change along the composite
morphism under `Grp.pullbackCompIso`. -/
@[simp]
theorem mapIso_pullbackCompIso_baseChange {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X)
    (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackCompIso t s G) (baseChange t (baseChange s P)) = baseChange (t ≫ s) P := by
  refine Subtype.ext ?_
  rw [baseChange_def s P, baseChange_mk, mapIso_mk, baseChange_def, coe_mk, coe_mk]
  exact Subobject.mk_eq_mk_of_comm _ _ (Grp.pullbackCompIso t s (P.val : Grp (Over X)))
    (Grp.pullbackCompIso_hom_naturality t s P.val.arrow).symm

/-- Transporting `baseChange s₁ P` along `Grp.pullbackCongrIso h G` yields `baseChange s₂ P`. -/
@[simp]
theorem mapIso_pullbackCongrIso_baseChange {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂)
    (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackCongrIso h G) (baseChange s₁ P) = baseChange s₂ P := by
  subst h
  ext1
  simp [Subobject.map_id]

/-- The two pullbacks to `Y ×_X Y` of the base change `baseChange p P` of any closed subgroup
scheme `P` of `G` agree under `Grp.pullbackOverlapIso p G`. -/
@[simp]
theorem mapIso_pullbackOverlapIso_baseChange (p : Y ⟶ X) (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackOverlapIso p G) (baseChange (pullback.fst p p) (baseChange p P)) =
      baseChange (pullback.snd p p) (baseChange p P) := by
  refine Subtype.ext ?_
  rw [baseChange_def p P, baseChange_mk, baseChange_mk, mapIso_mk, coe_mk, coe_mk]
  exact Subobject.mk_eq_mk_of_comm _ _ (Grp.pullbackOverlapIso p (P.val : Grp (Over X)))
    (Grp.pullbackOverlapIso_hom_naturality p P.val.arrow).symm

end Functoriality

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
