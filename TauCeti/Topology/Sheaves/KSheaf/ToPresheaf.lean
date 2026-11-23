/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.KSheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.BaseChangeNhds
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Topology.Sets.Compacts

/-!
# The presheaf of a K-presheaf

A K-presheaf on a topological space `X` is a presheaf on the compact subsets of `X`
(`TopCat.KPresheaf`). Pardon's construction of virtual fundamental cycles passes between
K-presheaves and presheaves on the open sets in both directions; on a locally compact Hausdorff
space the two passages are inverse equivalences between K-sheaves and sheaves (Pardon,
Lemma A.1.8). The passage from presheaves to K-presheaves, by germs along compact sets, is
`TopCat.Presheaf.toKPresheaf`. This file constructs the reverse passage.

The presheaf `F.toPresheaf` of a K-presheaf `F` takes an open set `U` to the limit of the values
of `F` on the compact subsets of `U`: for a K-presheaf of types its elements are the families
`(x_K)_{K ⊆ U}` of elements `x_K ∈ F(K)` compatible under restriction. The component `x_K` of a
section over `U` is `F.kRestrict U K h x`, and `F.isLimitKRestrictCone U` is the universal property
of the limit. The construction is functorial in `F` (`TopCat.KPresheaf.toPresheafFunctor`).

The main theorem is that on a Hausdorff space the presheaf of a K-sheaf of types is a sheaf
(`TopCat.KPresheaf.IsKSheaf.isSheaf_toPresheaf_types`). The key step is a gluing statement for
compact sets: if `U` is a family of open sets covering a compact set `K`, an element of `F(K)` is
the same thing as a compatible family of elements of `F(L)` for the compact sets `L ⊆ K` contained
in a single member of `U` (`TopCat.KPresheaf.IsKSheaf.existsUnique_forall_map_eq_types`). Indeed,
`K` is covered by finitely many members of `U`, and in a Hausdorff space a compact set covered by
two open sets is the union of two compact sets, one inside each of them
(`IsCompact.binary_compact_cover`); the pullback axiom then glues by induction on the number of open
sets.

Taking presheaves commutes with every functor preserving limits
(`TopCat.KPresheaf.toPresheafCompIso`), and on a locally compact Hausdorff space a functor
preserving finite limits and filtered colimits sends K-sheaves to K-sheaves
(`TopCat.KPresheaf.IsKSheaf.comp`). Applied to the forgetful functor, these give the main theorem
for K-sheaves with values in a concrete category whose forgetful functor reflects isomorphisms and
preserves limits and filtered colimits, such as modules over a ring, on a locally compact Hausdorff
space (`TopCat.KPresheaf.IsKSheaf.isSheaf_toPresheaf`).

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.1, Definitions A.1.4 and A.1.6
  and Lemma A.1.8.
* J. Lurie, *Higher Topos Theory*, Section 7.3.4.
-/

public section

universe w v u

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

namespace TopCat.KPresheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} [HasLimitsOfSize.{w, w} C]

/-- The diagram of the values of a K-presheaf `F` on the compact subsets of an open set `U`,
indexed by these compact sets ordered by reverse inclusion. -/
abbrev compactsInsideDiagram (F : KPresheaf C X) (U : Opens X) : (↥U.compactsInside)ᵒᵖ ⥤ C :=
  (Set.mono_coe U.compactsInside).functor.op ⋙ F

/-- The presheaf of a K-presheaf `F`: its value on an open set `U` is the limit of the values of `F`
on the compact subsets of `U`, and its restriction maps forget the components on the compact sets
which do not lie in the smaller open set. -/
@[expose]
noncomputable def toPresheaf (F : KPresheaf C X) : Presheaf C X where
  obj U := limit (F.compactsInsideDiagram U.unop)
  map {U _} i := limit.pre (F.compactsInsideDiagram U.unop)
    (Opens.baseChangeCompactsInside_mono i.unop).functor.op
  map_id U := limit.hom_ext fun K ↦ (limit.pre_π (F.compactsInsideDiagram U.unop)
    (Opens.baseChangeCompactsInside_mono (𝟙 _)).functor.op K).trans (Category.id_comp _).symm
  map_comp {U _ _} f g := (limit.pre_pre (F.compactsInsideDiagram U.unop)
    (Opens.baseChangeCompactsInside_mono f.unop).functor.op
    (Opens.baseChangeCompactsInside_mono g.unop).functor.op).symm

/-- The component on a compact set `K` of a section of `F.toPresheaf` over an open set `U ⊇ K`. -/
noncomputable def kRestrict (F : KPresheaf C X) (U : Opens X) (K : Compacts X)
    (h : (K : Set X) ⊆ U) : F.toPresheaf.obj (op U) ⟶ F.obj (op K) :=
  limit.π (F.compactsInsideDiagram U) (op ⟨K, h⟩)

/-- Restricting a section of `F.toPresheaf` to a smaller open set does not change its components on
the compact subsets of the smaller open set. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toPresheaf_map_kRestrict (F : KPresheaf C X) {U V : Opens X} (i : V ⟶ U) (K : Compacts X)
    (h : (K : Set X) ⊆ V) :
    F.toPresheaf.map i.op ≫ F.kRestrict V K h = F.kRestrict U K (h.trans i.le) :=
  limit.pre_π (F.compactsInsideDiagram U) (Opens.baseChangeCompactsInside_mono i).functor.op
    (op ⟨K, h⟩)

/-- The restriction maps of `F` send the component of a section on `K` to its component on a
smaller compact set. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kRestrict_map (F : KPresheaf C X) (U : Opens X) {K L : Compacts X} (f : op K ⟶ op L)
    (h : (K : Set X) ⊆ U) :
    F.kRestrict U K h ≫ F.map f =
      F.kRestrict U L ((show (L : Set X) ⊆ K from f.unop.le).trans h) :=
  limit.w (F.compactsInsideDiagram U)
    (homOfLE (show (⟨L, (show (L : Set X) ⊆ K from f.unop.le).trans h⟩ : ↥U.compactsInside) ≤
      ⟨K, h⟩ from f.unop.le)).op

/-- The cone of components on the compact subsets of `U` over the values of `F` on these compact
sets. -/
@[expose, simps]
noncomputable def kRestrictCone (F : KPresheaf C X) (U : Opens X) :
    Cone (F.compactsInsideDiagram U) where
  pt := F.toPresheaf.obj (op U)
  π :=
    { app K := F.kRestrict U K.unop.val K.unop.property
      naturality K _ i := (Category.id_comp _).trans
        (F.kRestrict_map U i.unop.le.hom.op K.unop.property).symm }

/-- The value of `F.toPresheaf` on an open set `U` is the limit of the values of `F` on the compact
subsets of `U`, with the components as limit projections. -/
noncomputable def isLimitKRestrictCone (F : KPresheaf C X) (U : Opens X) :
    IsLimit (F.kRestrictCone U) :=
  limit.isLimit _

/-- Morphisms into a value of `F.toPresheaf` agreeing on all components are equal. -/
@[ext]
theorem toPresheaf_hom_ext (F : KPresheaf C X) {U : Opens X} {Z : C}
    {f g : Z ⟶ F.toPresheaf.obj (op U)}
    (h : ∀ (K : Compacts X) (hK : (K : Set X) ⊆ U),
      f ≫ F.kRestrict U K hK = g ≫ F.kRestrict U K hK) :
    f = g :=
  (F.isLimitKRestrictCone U).hom_ext fun K ↦ h K.unop.val K.unop.property

/-- The morphism of presheaves induced by a morphism of K-presheaves: on each open set `U` it sends
a section to the section whose components are the images of its components. -/
noncomputable def toPresheafMap {F G : KPresheaf C X} (φ : F ⟶ G) :
    F.toPresheaf ⟶ G.toPresheaf where
  app U := limMap (Functor.whiskerLeft (Set.mono_coe U.unop.compactsInside).functor.op φ)
  naturality U _ i := (limit.map_pre
    (Functor.whiskerLeft (Set.mono_coe U.unop.compactsInside).functor.op φ)
    (Opens.baseChangeCompactsInside_mono i.unop).functor.op).symm

/-- `toPresheafMap φ` sends a section to the section whose components are the images under `φ`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toPresheafMap_app_kRestrict {F G : KPresheaf C X} (φ : F ⟶ G) (U : Opens X)
    (K : Compacts X) (h : (K : Set X) ⊆ U) :
    (toPresheafMap φ).app (op U) ≫ G.kRestrict U K h = F.kRestrict U K h ≫ φ.app (op K) :=
  limMap_π _ _

variable (C X) in
/-- Taking presheaves, as a functor from K-presheaves to presheaves. -/
@[expose, simps]
noncomputable def toPresheafFunctor : KPresheaf C X ⥤ Presheaf C X where
  obj F := F.toPresheaf
  map φ := toPresheafMap φ
  map_id F := by
    ext U K hK
    -- `(𝟙 F.toPresheaf).app U` is `𝟙 _` by definition of the functor category; the category
    -- instance on `Presheaf C X` has no `simp` lemma unfolding it.
    exact (toPresheafMap_app_kRestrict (𝟙 F) U K hK).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  map_comp φ ψ := by
    ext U K hK
    simp

section Functor

variable {D : Type*} [Category* D] [HasLimitsOfSize.{w, w} D] (G : C ⥤ D)
  [PreservesLimitsOfSize.{w, w} G] (F : KPresheaf C X)

/-- Taking presheaves commutes with a functor that preserves limits. -/
noncomputable def toPresheafCompIso : F.toPresheaf ⋙ G ≅ toPresheaf (F ⋙ G) :=
  NatIso.ofComponents (fun U ↦ preservesLimitIso G (F.compactsInsideDiagram U.unop)) <| by
    rintro ⟨U⟩ ⟨V⟩ i
    refine toPresheaf_hom_ext _ fun K hK ↦ ?_
    -- The components of the comparison isomorphisms are the images under `G` of the components.
    -- The isomorphism is stated between the objects of `F.toPresheaf ⋙ G` and `(F ⋙ G).toPresheaf`,
    -- as in the goal, so that `rw` can match it.
    have h (W : Opens X) (hW : (K : Set X) ⊆ W) :
        Iso.hom (X := (F.toPresheaf ⋙ G).obj (op W)) (Y := (toPresheaf (F ⋙ G)).obj (op W))
          (preservesLimitIso G (F.compactsInsideDiagram W)) ≫ kRestrict (F ⋙ G) W K hW =
          G.map (F.kRestrict W K hW) :=
      preservesLimitIso_hom_π G (F.compactsInsideDiagram W) (op ⟨K, hW⟩)
    rw [← Quiver.Hom.op_unop i, Category.assoc, Category.assoc, h V hK, toPresheaf_map_kRestrict,
      h U, Functor.comp_map, ← G.map_comp, toPresheaf_map_kRestrict]

/-- `F.toPresheafCompIso G` sends the image under `G` of a section of `F.toPresheaf` to the section
of `(F ⋙ G).toPresheaf` whose components are the images under `G` of its components. -/
@[reassoc (attr := simp)]
theorem toPresheafCompIso_hom_app_kRestrict (U : Opens X) (K : Compacts X)
    (h : (K : Set X) ⊆ U) :
    (F.toPresheafCompIso G).hom.app (op U) ≫ kRestrict (F ⋙ G) U K h = G.map (F.kRestrict U K h) :=
  preservesLimitIso_hom_π G (F.compactsInsideDiagram U) (op ⟨K, h⟩)

/-- `(F.toPresheafCompIso G).inv` sends a section of `(F ⋙ G).toPresheaf` to the image under `G` of
the section of `F.toPresheaf` with the corresponding components. -/
@[reassoc (attr := simp)]
theorem toPresheafCompIso_inv_app_kRestrict (U : Opens X) (K : Compacts X)
    (h : (K : Set X) ⊆ U) :
    (F.toPresheafCompIso G).inv.app (op U) ≫ G.map (F.kRestrict U K h) = kRestrict (F ⋙ G) U K h :=
  preservesLimitIso_inv_π G (F.compactsInsideDiagram U) (op ⟨K, h⟩)

omit [HasLimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} D] [PreservesLimitsOfSize.{w, w} G] in
/-- On a locally compact Hausdorff space, a functor preserving finite limits and filtered colimits
sends K-sheaves to K-sheaves. -/
theorem IsKSheaf.comp [T2Space X] [LocallyCompactSpace X] {F : KPresheaf C X} (hF : F.IsKSheaf)
    [PreservesFiniteLimits G] [PreservesFilteredColimitsOfSize.{w, w} G] :
    KPresheaf.IsKSheaf (F ⋙ G) where
  nonempty_isTerminal := ⟨IsTerminal.isTerminalObj G _ hF.nonempty_isTerminal.some⟩
  isPullback sq := (hF.isPullback sq).map G
  nonempty_isColimit_coconeOfCompacts K :=
    ⟨isColimitOfPreserves G (hF.nonempty_isColimit_coconeOfCompacts K).some⟩

end Functor

omit [HasLimitsOfSize.{w, w} C] in
/-- Restriction along `L ≤ K` followed by restriction along `M ≤ L` is restriction along `M ≤ K`. -/
@[reassoc, elementwise]
theorem map_opHomOfLE_comp_map_opHomOfLE (F : KPresheaf C X) {K L M : Compacts X} (h : L ≤ K)
    (h' : M ≤ L) : F.map (opHomOfLE h) ≫ F.map (opHomOfLE h') = F.map (opHomOfLE (h'.trans h)) := by
  rw [← F.map_comp, Subsingleton.elim (opHomOfLE h ≫ opHomOfLE h') _]

omit [HasLimitsOfSize.{w, w} C] in
/-- Restriction along `K ≤ K` is the identity. -/
@[elementwise]
theorem map_opHomOfLE_refl (F : KPresheaf C X) (K : Compacts X) :
    F.map (opHomOfLE (le_refl K)) = 𝟙 _ := by
  rw [Subsingleton.elim (opHomOfLE (le_refl K)) (𝟙 (op K)), F.map_id]

section Types

variable {F : KPresheaf (Type w) X}

/-- Two sections of the presheaf of a K-presheaf of types are equal when all their components
are. -/
theorem toPresheaf_ext {U : Opens X} {s t : F.toPresheaf.obj (op U)}
    (h : ∀ (K : Compacts X) (hK : (K : Set X) ⊆ U), F.kRestrict U K hK s = F.kRestrict U K hK t) :
    s = t :=
  Types.limit_ext _ s t fun K ↦ h K.unop.val K.unop.property

/-- A section of the presheaf of a K-presheaf of types over `U`, from a family of elements of the
values of `F` on the compact subsets of `U` which is compatible under restriction. -/
noncomputable def toPresheafMk (U : Opens X)
    (x : ∀ (K : Compacts X), (K : Set X) ⊆ U → F.obj (op K))
    (hx : ∀ (K L : Compacts X) (hK : (K : Set X) ⊆ U) (hL : (L : Set X) ⊆ U) (h : L ≤ K),
      F.map (opHomOfLE h) (x K hK) = x L hL) :
    F.toPresheaf.obj (op U) :=
  Types.Limit.mk _ (fun K ↦ x K.unop.val K.unop.property) fun K L i ↦
    hx K.unop.val L.unop.val _ _ i.unop.le

/-- The components of `toPresheafMk U x hx` are the elements `x K`. -/
@[simp]
theorem kRestrict_toPresheafMk (U : Opens X)
    (x : ∀ (K : Compacts X), (K : Set X) ⊆ U → F.obj (op K))
    (hx : ∀ (K L : Compacts X) (hK : (K : Set X) ⊆ U) (hL : (L : Set X) ⊆ U) (h : L ≤ K),
      F.map (opHomOfLE h) (x K hK) = x L hL)
    (K : Compacts X) (hK : (K : Set X) ⊆ U) :
    F.kRestrict U K hK (toPresheafMk U x hx) = x K hK :=
  Types.Limit.π_mk _ _ _ _

variable [T2Space X]

variable {ι : Type*} (U : ι → Opens X)

/-- Uniqueness in the gluing statement for compact sets: two elements of the value of a K-sheaf of
types on a compact set `K` covered by finitely many members of a family `U` of open sets agree if
they agree on every compact subset of `K` lying in a single member of `U`. -/
private theorem IsKSheaf.eq_of_forall_map_eq_of_finset (hF : F.IsKSheaf) (t : Finset ι) :
    ∀ (K : Compacts X), (K : Set X) ⊆ ⋃ i ∈ t, (U i : Set X) → ∀ x y : F.obj (op K),
      (∀ (L : Compacts X) (h : L ≤ K), (∃ i, (L : Set X) ⊆ U i) →
        F.map (opHomOfLE h) x = F.map (opHomOfLE h) y) → x = y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro K hK x y _
    obtain rfl : K = ⊥ := Compacts.ext (by simpa using hK)
    have := Types.isTerminalEquivUnique _ hF.nonempty_isTerminal.some
    exact Subsingleton.elim x y
  | insert a t _ ih =>
    intro K hK x y h
    rw [Finset.set_biUnion_insert] at hK
    obtain ⟨K₁, K₂, hK₁, hK₂, rfl⟩ := Compacts.exists_sup_eq_of_subset_union (U a).isOpen
      (isOpen_biUnion fun i _ ↦ (U i).isOpen) hK
    refine Types.ext_of_isPullback (hF.isPullback ⟨rfl, rfl⟩) (h K₁ le_sup_left ⟨a, hK₁⟩)
      (ih K₂ hK₂ _ _ fun L hL hLU ↦ ?_)
    rw [map_opHomOfLE_comp_map_opHomOfLE_apply, map_opHomOfLE_comp_map_opHomOfLE_apply]
    exact h L _ hLU

/-- Existence in the gluing statement for compact sets: on a compact set covered by finitely many
members of a family `U` of open sets, a compatible family of elements of the values of a K-sheaf of
types on the compact sets lying in a single member of `U` comes from an element. -/
private theorem IsKSheaf.exists_forall_map_eq_of_finset (hF : F.IsKSheaf)
    (x : ∀ (L : Compacts X), (∃ i, (L : Set X) ⊆ U i) → F.obj (op L))
    (hx : ∀ (L M : Compacts X) (hL : ∃ i, (L : Set X) ⊆ U i) (hM : ∃ i, (M : Set X) ⊆ U i)
      (h : M ≤ L), F.map (opHomOfLE h) (x L hL) = x M hM) (t : Finset ι) :
    ∀ (K : Compacts X), (K : Set X) ⊆ ⋃ i ∈ t, (U i : Set X) → ∃ y : F.obj (op K),
      ∀ (L : Compacts X) (h : L ≤ K) (hL : ∃ i, (L : Set X) ⊆ U i),
        F.map (opHomOfLE h) y = x L hL := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro K hK
    obtain rfl : K = ⊥ := Compacts.ext (by simpa using hK)
    have := Types.isTerminalEquivUnique _ hF.nonempty_isTerminal.some
    refine ⟨default, fun L h hL ↦ ?_⟩
    obtain rfl : L = ⊥ := le_bot_iff.1 h
    exact Subsingleton.elim _ _
  | insert a t _ ih =>
    intro K hK
    rw [Finset.set_biUnion_insert] at hK
    obtain ⟨K₁, K₂, hK₁, hK₂, rfl⟩ := Compacts.exists_sup_eq_of_subset_union (U a).isOpen
      (isOpen_biUnion fun i _ ↦ (U i).isOpen) hK
    obtain ⟨y₂, hy₂⟩ := ih K₂ hK₂
    have hK₁₂ : ∃ i, ((K₁ ⊓ K₂ : Compacts X) : Set X) ⊆ U i :=
      ⟨a, (show ((K₁ ⊓ K₂ : Compacts X) : Set X) ⊆ K₁ from inf_le_left).trans hK₁⟩
    obtain ⟨y, hy₁, hy₂'⟩ := Types.exists_of_isPullback (hF.isPullback (K₁ := K₁ ⊓ K₂) ⟨rfl, rfl⟩)
      (x K₁ ⟨a, hK₁⟩) y₂ ((hx _ _ _ hK₁₂ _).trans (hy₂ _ _ hK₁₂).symm)
    refine ⟨y, fun L h hL ↦ ?_⟩
    -- `L` is the union of `L ⊓ K₁` and `L ⊓ K₂`, on which `y` restricts to the values of `x`.
    have hLK : L = L ⊓ K₁ ⊔ L ⊓ K₂ := by rw [← inf_sup_left, inf_eq_left.2 h]
    obtain ⟨i, hi⟩ := hL
    have h₁ : ∃ i, ((L ⊓ K₁ : Compacts X) : Set X) ⊆ U i :=
      ⟨i, (show ((L ⊓ K₁ : Compacts X) : Set X) ⊆ L from inf_le_left).trans hi⟩
    have h₂ : ∃ i, ((L ⊓ K₂ : Compacts X) : Set X) ⊆ U i :=
      ⟨i, (show ((L ⊓ K₂ : Compacts X) : Set X) ⊆ L from inf_le_left).trans hi⟩
    refine Types.ext_of_isPullback
      (hF.isPullback (K₂ := L ⊓ K₁) (K₃ := L ⊓ K₂) ⟨hLK.symm, rfl⟩) ?_ ?_
    · rw [map_opHomOfLE_comp_map_opHomOfLE_apply, hx _ _ _ h₁,
        ← map_opHomOfLE_comp_map_opHomOfLE_apply F (le_sup_left : K₁ ≤ K₁ ⊔ K₂) inf_le_right, hy₁,
        hx _ _ _ h₁]
    · rw [map_opHomOfLE_comp_map_opHomOfLE_apply, hx _ _ _ h₂,
        ← map_opHomOfLE_comp_map_opHomOfLE_apply F (le_sup_right : K₂ ≤ K₁ ⊔ K₂) inf_le_right, hy₂',
        hy₂ _ _ h₂]

/-- **Locality on compact sets.** Let `F` be a K-sheaf of types on a Hausdorff space and let `K` be
a compact set covered by a family `U` of open sets. Two elements of `F(K)` are equal if their
restrictions to every compact subset of `K` lying in a single member of `U` are. -/
theorem IsKSheaf.eq_of_forall_map_eq_types (hF : F.IsKSheaf) {K : Compacts X}
    (hK : (K : Set X) ⊆ ⋃ i, (U i : Set X)) {y y' : F.obj (op K)}
    (h : ∀ (L : Compacts X) (hLK : L ≤ K), (∃ i, (L : Set X) ⊆ U i) →
      F.map (opHomOfLE hLK) y = F.map (opHomOfLE hLK) y') :
    y = y' := by
  obtain ⟨t, ht⟩ := K.isCompact.elim_finite_subcover (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) hK
  exact hF.eq_of_forall_map_eq_of_finset U t K ht y y' h

/-- **Gluing on compact sets.** Let `F` be a K-sheaf of types on a Hausdorff space, let `U` be a
family of open sets and let `K` be a compact set covered by `U`. A family of elements of the values
of `F` on the compact sets lying in a single member of `U`, compatible under restriction, is the
family of restrictions of a unique element of `F(K)`. -/
theorem IsKSheaf.existsUnique_forall_map_eq_types (hF : F.IsKSheaf)
    (x : ∀ (L : Compacts X), (∃ i, (L : Set X) ⊆ U i) → F.obj (op L))
    (hx : ∀ (L M : Compacts X) (hL : ∃ i, (L : Set X) ⊆ U i) (hM : ∃ i, (M : Set X) ⊆ U i)
      (h : M ≤ L), F.map (opHomOfLE h) (x L hL) = x M hM)
    {K : Compacts X} (hK : (K : Set X) ⊆ ⋃ i, (U i : Set X)) :
    ∃! y : F.obj (op K), ∀ (L : Compacts X) (h : L ≤ K) (hL : ∃ i, (L : Set X) ⊆ U i),
      F.map (opHomOfLE h) y = x L hL := by
  obtain ⟨t, ht⟩ := K.isCompact.elim_finite_subcover (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) hK
  obtain ⟨y, hy⟩ := hF.exists_forall_map_eq_of_finset U x hx t K ht
  exact ⟨y, hy, fun y' hy' ↦ hF.eq_of_forall_map_eq_types U hK fun L h hL ↦
    (hy' L h hL).trans (hy L h hL).symm⟩

/-- On a Hausdorff space, the presheaf of a K-sheaf of types is a sheaf. -/
theorem IsKSheaf.isSheaf_toPresheaf_types (hF : F.IsKSheaf) : F.toPresheaf.IsSheaf := by
  refine (Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).2 fun ι U sf hsf ↦ ?_
  -- The component of `sf i` on a compact set `L ⊆ U i` does not depend on `i`.
  have key (L : Compacts X) (i j : ι) (hi : (L : Set X) ⊆ U i) (hj : (L : Set X) ⊆ U j) :
      F.kRestrict (U i) L hi (sf i) = F.kRestrict (U j) L hj (sf j) := by
    simpa using congrArg (F.kRestrict (U i ⊓ U j) L (subset_inter hi hj)) (hsf i j)
  let x (L : Compacts X) (hL : ∃ i, (L : Set X) ⊆ U i) : F.obj (op L) :=
    F.kRestrict (U hL.choose) L hL.choose_spec (sf hL.choose)
  have hx (L : Compacts X) (hL) (i : ι) (hi : (L : Set X) ⊆ U i) :
      x L hL = F.kRestrict (U i) L hi (sf i) := key _ _ _ _ _
  have hxc (L M : Compacts X) (hL hM) (h : M ≤ L) : F.map (opHomOfLE h) (x L hL) = x M hM := by
    obtain ⟨i, hi⟩ := hL
    rw [hx L _ i hi, hx M _ i ((show (M : Set X) ⊆ L from h).trans hi), kRestrict_map_apply]
  have hcov (K : Compacts X) (hK : (K : Set X) ⊆ (iSup U : Opens X)) :
      (K : Set X) ⊆ ⋃ i, (U i : Set X) := by
    rwa [← Opens.coe_iSup]
  choose y hy hyu using fun (K : Compacts X) (hK : (K : Set X) ⊆ (iSup U : Opens X)) ↦
    hF.existsUnique_forall_map_eq_types U x hxc (hcov K hK)
  have hyc (K L : Compacts X) (hK hL) (h : L ≤ K) : F.map (opHomOfLE h) (y K hK) = y L hL :=
    hyu L hL _ fun M hM hMU ↦ by
      rw [map_opHomOfLE_comp_map_opHomOfLE_apply]
      exact hy K hK M _ hMU
  refine ⟨toPresheafMk (iSup U) y hyc, fun i ↦ toPresheaf_ext fun K hK ↦ ?_, fun s hs ↦ ?_⟩
  · rw [toPresheaf_map_kRestrict_apply, kRestrict_toPresheafMk, ← hx K ⟨i, hK⟩ i hK,
      ← hy K (hK.trans (show ((U i : Opens X) : Set X) ⊆ (iSup U : Opens X) from le_iSup U i))
        K le_rfl ⟨i, hK⟩, map_opHomOfLE_refl_apply]
  · refine toPresheaf_ext fun K hK ↦ ?_
    rw [kRestrict_toPresheafMk]
    refine hyu K hK _ fun L h ⟨i, hi⟩ ↦ ?_
    rw [kRestrict_map_apply, hx L _ i hi, ← hs i, toPresheaf_map_kRestrict_apply]

end Types

/-- On a locally compact Hausdorff space, the presheaf of a K-sheaf is a sheaf, for K-sheaves with
values in a concrete category whose forgetful functor reflects isomorphisms and preserves limits
and filtered colimits, such as modules over a ring. -/
theorem IsKSheaf.isSheaf_toPresheaf [T2Space X] [LocallyCompactSpace X]
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [(forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{w, w} (forget C)] [PreservesFilteredColimitsOfSize.{w, w} (forget C)]
    {F : KPresheaf C X} (hF : F.IsKSheaf) : F.toPresheaf.IsSheaf := by
  have := PreservesLimitsOfSize.preservesFiniteLimits (forget C)
  exact (Presheaf.isSheaf_iff_isSheaf_comp' (forget C) F.toPresheaf).2 <| Presheaf.isSheaf_of_iso
    (F.toPresheafCompIso (forget C)).symm ((hF.comp (forget C)).isSheaf_toPresheaf_types)

end TopCat.KPresheaf
