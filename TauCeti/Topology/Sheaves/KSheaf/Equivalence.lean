/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.KSheaf.OfPresheaf
public import TauCeti.Topology.Sheaves.KSheaf.ToPresheaf
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Topology.Sets.Compacts

/-!
# Sheaves and K-sheaves

On a locally compact Hausdorff space `X`, sheaves on the open sets of `X` and K-sheaves, presheaves
on the compact subsets of `X` satisfying Mathlib's `TopCat.KPresheaf.IsKSheaf`, are the same thing
(Pardon, Lemma A.1.8). The passage from a presheaf `P` to the K-presheaf of its germs along compact
sets is `TopCat.Presheaf.toKPresheaf`, and the passage from a K-presheaf `F` to the presheaf of
compatible families of its values on compact sets is `TopCat.KPresheaf.toPresheaf`. This file
compares the two composites with the identity.

* The *counit* `TopCat.KPresheaf.toPresheafCounit F : F.toPresheaf.toKPresheaf ⟶ F` sends the germ
  along `K` of a section over an open set `U ⊇ K` to the component of that section on `K`.
* The *unit* `TopCat.Presheaf.toKPresheafUnit P : P ⟶ P.toKPresheaf.toPresheaf` sends a section over
  `U` to the family of its germs along the compact subsets of `U`.

Both are natural, for presheaves and K-presheaves with values in any category with the relevant
limits and colimits. For values in types:

* on a locally compact Hausdorff space the counit of a K-sheaf is an isomorphism
  (`TopCat.KPresheaf.IsKSheaf.isIso_toPresheafCounit_types`). A germ along `K` is determined by
  its components on the compact neighbourhoods of `K`, and conversely every element of `F(K)` is
  the restriction of an element of `F(L)` for a compact neighbourhood `L` of `K`, by the third
  K-sheaf axiom;
* on a locally compact Hausdorff space the unit of a sheaf is an isomorphism
  (`TopCat.Presheaf.IsSheaf.isIso_toKPresheafUnit_types`). A family of germs along the compact
  subsets of `U` is represented near each point by a section over the interior of a compact
  neighbourhood, these sections glue, and the glued section has the given germs by locality of the
  K-sheaf of germs on compact sets.

Up to the comparison isomorphisms of `toKPresheaf` and `toPresheaf` with a functor `G` preserving
limits and filtered colimits, the image under `G` of the counit of `F` is the counit of `F ⋙ G`
(`TopCat.KPresheaf.map_toPresheafCounit_app`), and likewise for the unit
(`TopCat.Presheaf.map_toKPresheafUnit_app`). Applied to the forgetful functor of a concrete category
whose forgetful functor reflects isomorphisms and preserves limits and filtered colimits, such as
modules over a ring, this extends both statements to sheaves and K-sheaves with values there
(`TopCat.KPresheaf.IsKSheaf.isIso_toPresheafCounit`,
`TopCat.Presheaf.IsSheaf.isIso_toKPresheafUnit`). Together with the facts that the K-presheaf of a
sheaf is a K-sheaf (`TopCat.Presheaf.IsSheaf.isKSheaf_toKPresheaf`) and the presheaf of a K-sheaf
is a sheaf (`TopCat.KPresheaf.IsKSheaf.isSheaf_toPresheaf`), this gives the equivalence of
categories `TopCat.sheafEquivKSheaf C X : Sheaf C X ≌ KSheaf C X`. Its unit and counit are
`toKPresheafUnit` and `toPresheafCounit` themselves, which satisfy the triangle identity
`TopCat.Presheaf.toKPresheafMap_toKPresheafUnit_comp_toPresheafCounit`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.1, Definitions A.1.4 and A.1.6
  and Lemma A.1.8.
* J. Lurie, *Higher Topos Theory*, Section 7.3.4, Theorem 7.3.4.9.
-/

public section

universe w v u

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

namespace TopCat

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} [HasLimitsOfSize.{w, w} C]
  [HasColimitsOfSize.{w, w} C]

namespace KPresheaf

/-- The component on a compact set `K` of the counit `F.toPresheafCounit`. -/
private noncomputable def toPresheafCounitApp (F : KPresheaf C X) (K : Compacts X) :
    F.toPresheaf.toKPresheaf.obj (op K) ⟶ F.obj (op K) :=
  (F.toPresheaf.isColimitKGermCocone K).desc
    { pt := F.obj (op K)
      ι :=
        { app U := F.kRestrict U.unop.val K U.unop.property
          naturality _ V i := (F.toPresheaf_map_kRestrict i.unop.le.hom K
            V.unop.property).trans (Category.comp_id _).symm } }

/-- The counit of the passages between presheaves and K-presheaves: on a compact set `K`, it sends
the germ along `K` of a section of `F.toPresheaf` over an open set `U ⊇ K` to the component of that
section on `K`. -/
noncomputable def toPresheafCounit (F : KPresheaf C X) : F.toPresheaf.toKPresheaf ⟶ F where
  app K := F.toPresheafCounitApp K.unop
  naturality := by
    rintro ⟨K⟩ ⟨L⟩ f
    refine F.toPresheaf.toKPresheaf_hom_ext fun U hU ↦ ?_
    have h (M : Compacts X) (hM : (M : Set X) ⊆ U) :
        F.toPresheaf.kGerm M U hM ≫ F.toPresheafCounitApp M = F.kRestrict U M hM :=
      (F.toPresheaf.isColimitKGermCocone M).fac _ (op ⟨U, hM⟩)
    rw [Presheaf.kGerm_toKPresheaf_map_assoc, h, ← Category.assoc, h, kRestrict_map]

/-- `F.toPresheafCounit` sends the germ along `K` of a section to its component on `K`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kGerm_toPresheafCounit_app (F : KPresheaf C X) (K : Compacts X) (U : Opens X)
    (h : (K : Set X) ⊆ U) :
    F.toPresheaf.kGerm K U h ≫ F.toPresheafCounit.app (op K) = F.kRestrict U K h :=
  (F.toPresheaf.isColimitKGermCocone K).fac _ (op ⟨U, h⟩)

/-- The counit is natural in the K-presheaf. -/
@[reassoc]
theorem toPresheafCounit_naturality {F G : KPresheaf C X} (φ : F ⟶ G) :
    Presheaf.toKPresheafMap (toPresheafMap φ) ≫ G.toPresheafCounit = F.toPresheafCounit ≫ φ := by
  ext ⟨K⟩ U hU
  simp

end KPresheaf

namespace Presheaf

/-- The component on an open set `U` of the unit `P.toKPresheafUnit`. -/
private noncomputable def toKPresheafUnitApp (P : Presheaf C X) (U : Opens X) :
    P.obj (op U) ⟶ P.toKPresheaf.toPresheaf.obj (op U) :=
  (P.toKPresheaf.isLimitKRestrictCone U).lift
    { pt := P.obj (op U)
      π :=
        { app K := P.kGerm K.unop.val U K.unop.property
          naturality K _ i := (Category.id_comp _).trans
            (P.kGerm_toKPresheaf_map i.unop.le.hom.op U K.unop.property).symm } }

/-- The unit of the passages between presheaves and K-presheaves: on an open set `U`, it sends a
section of `P` over `U` to the family of its germs along the compact subsets of `U`. -/
noncomputable def toKPresheafUnit (P : Presheaf C X) : P ⟶ P.toKPresheaf.toPresheaf where
  app U := P.toKPresheafUnitApp U.unop
  naturality := by
    rintro ⟨U⟩ ⟨V⟩ i
    refine P.toKPresheaf.toPresheaf_hom_ext fun K hK ↦ ?_
    have h (W : Opens X) (hW : (K : Set X) ⊆ W) :
        P.toKPresheafUnitApp W ≫ P.toKPresheaf.kRestrict W K hW = P.kGerm K W hW :=
      (P.toKPresheaf.isLimitKRestrictCone W).fac _ (op ⟨K, hW⟩)
    rw [← Quiver.Hom.op_unop i, Category.assoc, Category.assoc, h,
      KPresheaf.toPresheaf_map_kRestrict, h]
    exact P.kGerm_res K i.unop hK

/-- `P.toKPresheafUnit` sends a section to the family of its germs. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toKPresheafUnit_app_kRestrict (P : Presheaf C X) (U : Opens X) (K : Compacts X)
    (h : (K : Set X) ⊆ U) :
    P.toKPresheafUnit.app (op U) ≫ P.toKPresheaf.kRestrict U K h = P.kGerm K U h :=
  (P.toKPresheaf.isLimitKRestrictCone U).fac _ (op ⟨K, h⟩)

/-- The unit is natural in the presheaf. -/
@[reassoc]
theorem toKPresheafUnit_naturality {P Q : Presheaf C X} (φ : P ⟶ Q) :
    φ ≫ Q.toKPresheafUnit = P.toKPresheafUnit ≫ KPresheaf.toPresheafMap (toKPresheafMap φ) := by
  ext ⟨U⟩ K hK
  simp

/-- The triangle identity: the K-presheaf of the unit of `P`, followed by the counit of
`P.toKPresheaf`, is the identity. -/
@[reassoc (attr := simp)]
theorem toKPresheafMap_toKPresheafUnit_comp_toPresheafCounit (P : Presheaf C X) :
    toKPresheafMap P.toKPresheafUnit ≫ P.toKPresheaf.toPresheafCounit = 𝟙 _ := by
  ext ⟨K⟩ U hU
  simp

end Presheaf

section Functor

variable {D : Type*} [Category* D] [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D]
  (G : C ⥤ D) [PreservesLimitsOfSize.{w, w} G] [PreservesFilteredColimitsOfSize.{w, w} G]

/-- Up to the comparison isomorphisms, the image under `G` of the counit of `F` is the counit of
`F ⋙ G`. -/
theorem KPresheaf.map_toPresheafCounit_app (F : KPresheaf C X) (K : Compacts X) :
    G.map (F.toPresheafCounit.app (op K)) =
      (F.toPresheaf.toKPresheafCompIso G).hom.app (op K) ≫
        (Presheaf.toKPresheafMap (F.toPresheafCompIso G).hom).app (op K) ≫
          (KPresheaf.toPresheafCounit (F ⋙ G)).app (op K) :=
  Presheaf.toKPresheaf_hom_ext_of_preservesColimits G F.toPresheaf fun U hU ↦ by
    rw [← G.map_comp, KPresheaf.kGerm_toPresheafCounit_app,
      Presheaf.kGerm_toKPresheafCompIso_hom_app_assoc, Presheaf.kGerm_toKPresheafMap_app_assoc,
      KPresheaf.kGerm_toPresheafCounit_app, KPresheaf.toPresheafCompIso_hom_app_kRestrict]

/-- Up to the comparison isomorphisms, the image under `G` of the unit of `P` is the unit of
`P ⋙ G`. -/
theorem Presheaf.map_toKPresheafUnit_app (P : Presheaf C X) (U : Opens X) :
    G.map (P.toKPresheafUnit.app (op U)) ≫ (P.toKPresheaf.toPresheafCompIso G).hom.app (op U) ≫
        (KPresheaf.toPresheafMap (P.toKPresheafCompIso G).hom).app (op U) =
      (Presheaf.toKPresheafUnit (P ⋙ G)).app (op U) :=
  KPresheaf.toPresheaf_hom_ext _ fun K hK ↦ by
    rw [Category.assoc, Category.assoc, KPresheaf.toPresheafMap_app_kRestrict,
      KPresheaf.toPresheafCompIso_hom_app_kRestrict_assoc, ← G.map_comp_assoc,
      toKPresheafUnit_app_kRestrict, kGerm_toKPresheafCompIso_hom_app,
      toKPresheafUnit_app_kRestrict]

end Functor

section Types

variable [T2Space X] [LocallyCompactSpace X]

namespace KPresheaf

variable {F : KPresheaf (Type w) X}

omit [LocallyCompactSpace X] in
/-- Every element of the value on `K` of a K-sheaf of types is the component on `K` of a section of
its presheaf over an open neighbourhood of `K`. -/
private theorem surjective_toPresheafCounit_app (hF : F.IsKSheaf) (K : Compacts X) :
    Function.Surjective (F.toPresheafCounit.app (op K)) := by
  intro x
  obtain ⟨⟨L⟩, z, rfl⟩ :=
    Types.jointly_surjective_of_isColimit (hF.nonempty_isColimit_coconeOfCompacts K).some x
  obtain ⟨V, hKV, hVL⟩ := Compacts.exists_open_set_nhds_of_compactsNhds L
  refine ⟨F.toPresheaf.kGerm K V hKV (toPresheafMk V
    (fun M hM ↦ F.map (opHomOfLE (show M ≤ L.val from hM.trans hVL)) z) fun M N hM _ h ↦ ?_), ?_⟩
  · exact map_opHomOfLE_comp_map_opHomOfLE_apply F _ h z
  · rw [kGerm_toPresheafCounit_app_apply, kRestrict_toPresheafMk, coconeOfCompacts_ι_app]

/-- Two germs along `K` of sections of the presheaf of a K-sheaf of types with the same component on
`K` are equal. -/
private theorem injective_toPresheafCounit_app (hF : F.IsKSheaf) (K : Compacts X) :
    Function.Injective (F.toPresheafCounit.app (op K)) := by
  intro a b hab
  obtain ⟨U, hU, s, rfl⟩ := F.toPresheaf.exists_kGerm_apply_eq a
  obtain ⟨V, hV, t, rfl⟩ := F.toPresheaf.exists_kGerm_apply_eq b
  rw [kGerm_toPresheafCounit_app_apply, kGerm_toPresheafCounit_app_apply] at hab
  -- The components of `s` and `t` on a compact neighbourhood `L ⊆ U ∩ V` of `K` restrict to the
  -- same element of `F(K)`, so they agree on a smaller compact neighbourhood `M` of `K`.
  obtain ⟨L, hL, hKL, hLUV⟩ := exists_compact_between K.isCompact (U ⊓ V).isOpen
    (subset_inter hU hV)
  set L' : Compacts X := ⟨L, hL⟩
  have hLU : (L' : Set X) ⊆ U := hLUV.trans inter_subset_left
  have hLV : (L' : Set X) ⊆ V := hLUV.trans inter_subset_right
  have hKL' : K ≤ L' := hKL.trans interior_subset
  have hL'K : L' ∈ K.compactNhds := fun x ↦ mem_interior_iff_mem_nhds.1 (hKL x.property)
  have h : F.map (opHomOfLE hKL') (F.kRestrict U L' hLU s) =
      F.map (opHomOfLE hKL') (F.kRestrict V L' hLV t) := by
    rw [kRestrict_map_apply, kRestrict_map_apply]
    exact hab
  obtain ⟨⟨M⟩, f, hst⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (hF.nonempty_isColimit_coconeOfCompacts K).some (i := op ⟨L', hL'K⟩) _ _).1 h
  have hML : (M : Set X) ⊆ L := f.unop.le
  -- The diagram of `coconeOfCompacts` sends `f` to `F.map (opHomOfLE _)` by definition, and the
  -- proofs of `M ⊆ U` and `M ⊆ V` produced by `kRestrict_map_apply` are equal by proof
  -- irrelevance, so both `replace` steps only restate `hst` in these terms.
  replace hst : F.map (opHomOfLE (show M.val ≤ L' from hML)) (F.kRestrict U L' hLU s) =
      F.map (opHomOfLE (show M.val ≤ L' from hML)) (F.kRestrict V L' hLV t) := hst
  rw [kRestrict_map_apply, kRestrict_map_apply] at hst
  replace hst : F.kRestrict U M.val (hML.trans hLU) s = F.kRestrict V M.val (hML.trans hLV) t := hst
  -- Hence `s` and `t` agree on an open neighbourhood `W ⊆ M` of `K`.
  obtain ⟨W, hKW, hWM⟩ := Compacts.exists_open_set_nhds_of_compactsNhds M
  refine (F.toPresheaf.kGerm_apply_eq_kGerm_apply_iff hU hV s t).2
    ⟨W, hKW, homOfLE (hWM.trans (hML.trans hLU)), homOfLE (hWM.trans (hML.trans hLV)),
      toPresheaf_ext fun N hN ↦ ?_⟩
  rw [toPresheaf_map_kRestrict_apply, toPresheaf_map_kRestrict_apply,
    ← F.kRestrict_map_apply U (opHomOfLE (show N ≤ M.val from hN.trans hWM)) (hML.trans hLU),
    ← F.kRestrict_map_apply V (opHomOfLE (show N ≤ M.val from hN.trans hWM)) (hML.trans hLV), hst]

/-- On a locally compact Hausdorff space, the counit `F.toPresheaf.toKPresheaf ⟶ F` of a K-sheaf of
types is an isomorphism. -/
theorem IsKSheaf.isIso_toPresheafCounit_types (hF : F.IsKSheaf) : IsIso F.toPresheafCounit := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨K⟩
  rw [isIso_iff_bijective]
  exact ⟨injective_toPresheafCounit_app hF K, surjective_toPresheafCounit_app hF K⟩

end KPresheaf

namespace Presheaf

variable {P : Presheaf (Type w) X}

omit [T2Space X] [LocallyCompactSpace X] in
/-- Two sections of a sheaf of types with the same germs along all compact sets are equal. -/
private theorem injective_toKPresheafUnit_app (hP : P.IsSheaf) (U : Opens X) :
    Function.Injective (P.toKPresheafUnit.app (op U)) := by
  intro s t hst
  -- The germs of `s` and `t` at each point `x` agree, so `s` and `t` agree near `x`.
  have h (x : U) := (P.kGerm_apply_eq_kGerm_apply_iff (K := {(x : X)}) (by simp) (by simp) s t).1 <|
    by
      have := congrArg (P.toKPresheaf.kRestrict U {(x : X)} (by simp)) hst
      rwa [toKPresheafUnit_app_kRestrict_apply, toKPresheafUnit_app_kRestrict_apply] at this
  choose W hxW iW iW' hW using h
  refine Sheaf.eq_of_locally_eq' ⟨P, hP⟩ W U iW (fun x hx ↦ ?_) s t fun x ↦ ?_
  · exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩ (by simp)⟩
  · rw [hW x, Subsingleton.elim (iW' x) (iW x)]

/-- On a locally compact space, every family of germs of a sheaf of types along the compact subsets
of an open set `U`, compatible under restriction, is the family of germs of a section over `U`. -/
private theorem surjective_toKPresheafUnit_app (hP : P.IsSheaf) (U : Opens X) :
    Function.Surjective (P.toKPresheafUnit.app (op U)) := by
  intro σ
  -- Each point `x` of `U` has a compact neighbourhood `K x ⊆ U`; the component of `σ` on `K x` is
  -- the germ of a section `s x` over an open set `V x ⊇ K x`.
  have hK (x : U) : ∃ K : Compacts X, (x : X) ∈ interior (K : Set X) ∧ (K : Set X) ⊆ U := by
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_between (isCompact_singleton (x := (x : X)))
      U.isOpen (singleton_subset_iff.2 x.property)
    exact ⟨⟨K, hK⟩, singleton_subset_iff.1 hxK, hKU⟩
  choose K hxK hKU using hK
  choose V hKV s hs using fun x ↦ P.exists_kGerm_apply_eq (P.toKPresheaf.kRestrict U (K x)
    (hKU x) σ)
  obtain ⟨W, hW⟩ : ∃ W : U → Opens X, ∀ x, (W x : Set X) = interior (K x) :=
    ⟨fun x ↦ ⟨interior (K x), isOpen_interior⟩, fun _ ↦ rfl⟩
  have hWK (x : U) : (W x : Set X) ⊆ K x := (hW x).trans_subset interior_subset
  have hcov : U ≤ iSup W := fun x hx ↦ Opens.mem_iSup.2 ⟨⟨x, hx⟩, by
    rw [← SetLike.mem_coe, hW]
    exact hxK ⟨x, hx⟩⟩
  -- The germs of `s x` and `s y` along `K x ∩ K y` agree, so `s x` and `s y` agree on
  -- `W x ∩ W y`.
  have hcompat : IsCompatible P W fun x ↦
      P.map (homOfLE (show W x ≤ V x from (hWK x).trans (hKV x))).op (s x) := by
    intro x y
    have h : P.kGerm (K x ⊓ K y) (V x) ((show ((K x ⊓ K y : Compacts X) : Set X) ⊆ K x from
          inf_le_left).trans (hKV x)) (s x) =
        P.kGerm (K x ⊓ K y) (V y) ((show ((K x ⊓ K y : Compacts X) : Set X) ⊆ K y from
          inf_le_right).trans (hKV y)) (s y) := by
      rw [← P.kGerm_toKPresheaf_map_apply (opHomOfLE (inf_le_left : K x ⊓ K y ≤ K x)) (V x)
          (hKV x), ← P.kGerm_toKPresheaf_map_apply (opHomOfLE (inf_le_right : K x ⊓ K y ≤ K y))
          (V y) (hKV y), hs x, hs y, KPresheaf.kRestrict_map_apply, KPresheaf.kRestrict_map_apply]
    dsimp only
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp, ← P.map_comp]
    exact P.map_eq_map_of_kGerm_apply_eq h (W := W x ⊓ W y)
      (fun z hz ↦ ⟨hWK x hz.1, hWK y hz.2⟩) _ _
  obtain ⟨g, hg, -⟩ := Sheaf.existsUnique_gluing' ⟨P, hP⟩ W U
    (fun x ↦ homOfLE (show W x ≤ U from (hWK x).trans (hKU x))) hcov _ hcompat
  -- The germs of the glued section `g` are the components of `σ`, by locality on compact sets.
  refine ⟨g, KPresheaf.toPresheaf_ext fun L hL ↦ ?_⟩
  rw [toKPresheafUnit_app_kRestrict_apply]
  refine hP.isKSheaf_toKPresheaf_types.eq_of_forall_map_eq_types W
    (fun z hz ↦ Opens.mem_iSup.1 (hcov (hL hz)) |>.elim fun x hx ↦ mem_iUnion.2 ⟨x, hx⟩)
    fun M hML ⟨x, hMx⟩ ↦ ?_
  rw [kGerm_toKPresheaf_map_apply, KPresheaf.kRestrict_map_apply,
    ← P.kGerm_res_apply M (homOfLE (show W x ≤ U from (hWK x).trans (hKU x))) hMx, hg x]
  dsimp only
  rw [← ConcreteCategory.comp_apply, kGerm_res,
    ← P.toKPresheaf.kRestrict_map_apply U (opHomOfLE (show M ≤ K x from hMx.trans (hWK x)))
      (hKU x),
    ← hs x, kGerm_toKPresheaf_map_apply]

/-- On a locally compact Hausdorff space, the unit `P ⟶ P.toKPresheaf.toPresheaf` of a sheaf of
types is an isomorphism. -/
theorem IsSheaf.isIso_toKPresheafUnit_types (hP : P.IsSheaf) : IsIso P.toKPresheafUnit := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨U⟩
  rw [isIso_iff_bijective]
  exact ⟨injective_toKPresheafUnit_app hP U, surjective_toKPresheafUnit_app hP U⟩

end Presheaf

end Types

section ConcreteCategory

variable [T2Space X] [LocallyCompactSpace X]

/-- On a locally compact Hausdorff space, the counit `F.toPresheaf.toKPresheaf ⟶ F` of a K-sheaf is
an isomorphism, for K-sheaves with values in a concrete category whose forgetful functor reflects
isomorphisms and preserves limits and filtered colimits, such as modules over a ring. -/
theorem KPresheaf.IsKSheaf.isIso_toPresheafCounit
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [(forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{w, w} (forget C)] [PreservesFilteredColimitsOfSize.{w, w} (forget C)]
    {F : KPresheaf C X} (hF : F.IsKSheaf) : IsIso F.toPresheafCounit := by
  have := PreservesLimitsOfSize.preservesFiniteLimits (forget C)
  have := (hF.comp (forget C)).isIso_toPresheafCounit_types
  have : IsIso (Presheaf.toKPresheafMap (F.toPresheafCompIso (forget C)).hom) :=
    inferInstanceAs (IsIso ((Presheaf.toKPresheafFunctor _ X).map _))
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨K⟩
  have : IsIso ((forget C).map (F.toPresheafCounit.app (op K))) := by
    rw [KPresheaf.map_toPresheafCounit_app]
    infer_instance
  exact isIso_of_reflects_iso _ (forget C)

/-- On a locally compact Hausdorff space, the unit `P ⟶ P.toKPresheaf.toPresheaf` of a sheaf is an
isomorphism, for sheaves with values in a concrete category whose forgetful functor reflects
isomorphisms and preserves limits and filtered colimits, such as modules over a ring. -/
theorem Presheaf.IsSheaf.isIso_toKPresheafUnit
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [(forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{w, w} (forget C)] [PreservesFilteredColimitsOfSize.{w, w} (forget C)]
    {P : Presheaf C X} (hP : P.IsSheaf) : IsIso P.toKPresheafUnit := by
  have := ((Presheaf.isSheaf_iff_isSheaf_comp' (forget C) P).1 hP).isIso_toKPresheafUnit_types
  have : IsIso (KPresheaf.toPresheafMap (P.toKPresheafCompIso (forget C)).hom) :=
    inferInstanceAs (IsIso ((KPresheaf.toPresheafFunctor _ X).map _))
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨U⟩
  have : IsIso ((forget C).map (P.toKPresheafUnit.app (op U)) ≫
      (P.toKPresheaf.toPresheafCompIso (forget C)).hom.app (op U) ≫
        (KPresheaf.toPresheafMap (P.toKPresheafCompIso (forget C)).hom).app (op U)) := by
    rw [Presheaf.map_toKPresheafUnit_app]
    infer_instance
  have := IsIso.of_isIso_comp_right ((forget C).map (P.toKPresheafUnit.app (op U)))
    ((P.toKPresheaf.toPresheafCompIso (forget C)).hom.app (op U) ≫
      (KPresheaf.toPresheafMap (P.toKPresheafCompIso (forget C)).hom).app (op U))
  exact isIso_of_reflects_iso _ (forget C)

variable (C X) in
/-- **Sheaves are K-sheaves** (Pardon, Lemma A.1.8). On a locally compact Hausdorff space, taking
germs along compact sets is an equivalence from sheaves to K-sheaves, with inverse the presheaf of
compatible families of values on compact sets. The values are in a concrete category whose
forgetful functor reflects isomorphisms and preserves limits and filtered colimits, such as types or
modules over a ring. The unit and counit are `Presheaf.toKPresheafUnit` and
`KPresheaf.toPresheafCounit`. -/
@[expose, simps! functor_obj_obj functor_map_hom inverse_obj_obj inverse_map_hom
  unitIso_hom_app_hom unitIso_inv_app_hom counitIso_hom_app_hom counitIso_inv_app_hom]
noncomputable def sheafEquivKSheaf
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [(forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{w, w} (forget C)] [PreservesFilteredColimitsOfSize.{w, w} (forget C)]
    : Sheaf C X ≌ KSheaf C X where
  functor := ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ Presheaf.toKPresheafFunctor _ X)
    fun P ↦ Presheaf.IsSheaf.isKSheaf_toKPresheaf P.property
  inverse := ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ KPresheaf.toPresheafFunctor _ X)
    fun F ↦ KPresheaf.IsKSheaf.isSheaf_toPresheaf F.property
  unitIso := NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _ (Presheaf.toKPresheafUnit P.obj)
        (Presheaf.IsSheaf.isIso_toKPresheafUnit P.property)))
    fun φ ↦ ObjectProperty.hom_ext _ (Presheaf.toKPresheafUnit_naturality φ.hom)
  counitIso := NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _ (KPresheaf.toPresheafCounit F.obj)
        (KPresheaf.IsKSheaf.isIso_toPresheafCounit F.property)))
    fun φ ↦ ObjectProperty.hom_ext _ (KPresheaf.toPresheafCounit_naturality φ.hom)
  functor_unitIso_comp P := ObjectProperty.hom_ext _
    (Presheaf.toKPresheafMap_toKPresheafUnit_comp_toPresheafCounit P.obj)

end ConcreteCategory

end TopCat

