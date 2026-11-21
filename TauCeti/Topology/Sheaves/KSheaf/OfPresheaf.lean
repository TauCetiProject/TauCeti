/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.KSheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.BaseChangeNhds
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.Topology.Sets.Compacts

/-!
# The K-presheaf of a presheaf

A K-presheaf on a topological space `X` is a presheaf on the compact subsets of `X`
(`TopCat.KPresheaf`). It is a K-sheaf (`TopCat.KPresheaf.IsKSheaf`) when its value on `∅` is
terminal, its value on `K₂ ∪ K₃` is the pullback of its values on `K₂` and `K₃` over `K₂ ∩ K₃`,
and its value on each compact set `K` is the colimit of its values on the compact neighbourhoods of
`K`. Pardon's construction of virtual fundamental cycles works with K-sheaves and complexes of
K-presheaves, and on a locally compact Hausdorff space K-sheaves are another description of sheaves
(Pardon, Lemma A.1.8).

This file constructs the passage from presheaves on the open sets to K-presheaves. The K-presheaf
`P.toKPresheaf` of a presheaf `P` takes a compact set `K` to the colimit of the values of `P` on
the open neighbourhoods of `K`: its elements are the germs along `K` of sections of `P` defined
near `K`, and its restriction maps restrict germs. The germ along `K` of the sections over an open
`U ⊇ K` is `P.kGerm K U h`, and `P.isColimitKGermCocone K` is the universal property of the
colimit. The construction is functorial in `P` (`TopCat.Presheaf.toKPresheafFunctor`) and
commutes with every functor preserving filtered colimits (`TopCat.Presheaf.toKPresheafCompIso`).

The main theorem is that on a locally compact Hausdorff space the K-presheaf of a sheaf is a
K-sheaf (`TopCat.Presheaf.IsSheaf.isKSheaf_toKPresheaf`), for sheaves of types and more generally
for sheaves with values in a concrete category whose forgetful functor reflects isomorphisms and
preserves limits and filtered colimits, such as modules over a ring.

* The open set `∅` is the smallest open neighbourhood of `∅`, so the value on `∅` is the value of
  the sheaf on `∅`, which is terminal (`TopCat.Presheaf.isTerminalToKPresheafObjBot`).
* Two germs along `K₂ ∪ K₃` agreeing along `K₂` and along `K₃` agree on a neighbourhood of
  `K₂ ∪ K₃`, by locality. Germs along `K₂` and `K₃` agreeing on an open `W ⊇ K₂ ∩ K₃` are
  represented on opens `U₂ ⊇ K₂` and `U₃ ⊇ K₃` with `U₂ ∩ U₃ ⊆ W`, because `K₂ \ W` and `K₃ \ W`
  are disjoint compact sets, which disjoint open sets separate in a Hausdorff space; the sheaf glues
  these representatives (`TopCat.Presheaf.IsSheaf.isPullback_toKPresheaf_map_types`).
* Every open neighbourhood of a compact set `K` in a locally compact Hausdorff space contains a
  compact neighbourhood of `K`, so germs along `K` are restrictions of germs along compact
  neighbourhoods of `K`, and so are the identifications between them
  (`TopCat.Presheaf.isColimitToKPresheafCoconeOfCompacts`). This holds for every presheaf of
  types.

The first two axioms only use that `X` is Hausdorff. Local compactness is needed for the last one:
a point without compact neighbourhoods has an empty diagram of compact neighbourhoods.

The converse construction, from K-presheaves to presheaves through limits over the compact subsets
of an open set, and the equivalence between sheaves and K-sheaves are not treated here.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.1, Definitions A.1.4 and A.1.6
  and Lemma A.1.8.
* J. Lurie, *Higher Topos Theory*, Section 7.3.4.
-/

public section

universe w v u

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}} [HasColimitsOfSize.{w, w} C]

/-- The diagram of the values of a presheaf `P` on the open neighbourhoods of a compact set `K`,
indexed by these neighbourhoods ordered by reverse inclusion. -/
abbrev openNhdsDiagram (P : Presheaf C X) (K : Compacts X) : (↥K.openNhds)ᵒᵖ ⥤ C :=
  (Set.mono_coe K.openNhds).functor.op ⋙ P

/-- The K-presheaf of a presheaf `P`: its value on a compact set `K` is the colimit of the values
of `P` on the open neighbourhoods of `K`, the germs along `K` of sections of `P`, and its
restriction maps restrict germs to smaller compact sets. -/
@[expose]
noncomputable def toKPresheaf (P : Presheaf C X) : KPresheaf C X where
  obj K := colimit (P.openNhdsDiagram K.unop)
  map {_ L} f :=
    colimit.pre (P.openNhdsDiagram L.unop) (Compacts.baseChangeOpenNhds_mono f.unop).functor.op
  map_id K := colimit.hom_ext fun U ↦ (colimit.ι_pre (P.openNhdsDiagram K.unop)
    (Compacts.baseChangeOpenNhds_mono (𝟙 _)).functor.op U).trans (Category.comp_id _).symm
  map_comp {_ _ M} f g := (colimit.pre_pre (P.openNhdsDiagram M.unop)
    (Compacts.baseChangeOpenNhds_mono g.unop).functor.op
    (Compacts.baseChangeOpenNhds_mono f.unop).functor.op).symm

/-- The germ along a compact set `K` of a section of `P` over an open neighbourhood `U` of `K`. -/
noncomputable def kGerm (P : Presheaf C X) (K : Compacts X) (U : Opens X) (h : (K : Set X) ⊆ U) :
    P.obj (op U) ⟶ P.toKPresheaf.obj (op K) :=
  colimit.ι (P.openNhdsDiagram K) (op ⟨U, h⟩)

/-- Restricting a section to a smaller open neighbourhood does not change its germ. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kGerm_res (P : Presheaf C X) (K : Compacts X) {U V : Opens X} (i : U ⟶ V)
    (hU : (K : Set X) ⊆ U) :
    P.map i.op ≫ P.kGerm K U hU = P.kGerm K V (hU.trans i.le) :=
  colimit.w (P.openNhdsDiagram K) (homOfLE (show (⟨U, hU⟩ : ↥K.openNhds) ≤ ⟨V, hU.trans i.le⟩
    from i.le)).op

/-- The restriction maps of `P.toKPresheaf` send the germ of a section along `K` to its germ along
a smaller compact set. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kGerm_toKPresheaf_map (P : Presheaf C X) {K L : Compacts X} (f : op K ⟶ op L)
    (U : Opens X) (h : (K : Set X) ⊆ U) :
    P.kGerm K U h ≫ P.toKPresheaf.map f =
      P.kGerm L U ((show (L : Set X) ⊆ K from f.unop.le).trans h) :=
  colimit.ι_pre (P.openNhdsDiagram L) (Compacts.baseChangeOpenNhds_mono f.unop).functor.op
    (op ⟨U, h⟩)

/-- The cocone of germs along `K` over the values of `P` on the open neighbourhoods of `K`. -/
@[expose, simps]
noncomputable def kGermCocone (P : Presheaf C X) (K : Compacts X) :
    Cocone (P.openNhdsDiagram K) where
  pt := P.toKPresheaf.obj (op K)
  ι :=
    { app U := P.kGerm K U.unop.val U.unop.property
      naturality _ V i := (P.kGerm_res K i.unop.le.hom V.unop.property).trans
          (Category.comp_id _).symm }

/-- The value of `P.toKPresheaf` on a compact set `K` is the colimit of the values of `P` on the
open neighbourhoods of `K`, with the germs as colimit insertions. -/
noncomputable def isColimitKGermCocone (P : Presheaf C X) (K : Compacts X) :
    IsColimit (P.kGermCocone K) :=
  colimit.isColimit _

/-- Morphisms out of a value of `P.toKPresheaf` agreeing on all germs are equal. -/
@[ext]
theorem toKPresheaf_hom_ext (P : Presheaf C X) {K : Compacts X} {Z : C}
    {f g : P.toKPresheaf.obj (op K) ⟶ Z}
    (h : ∀ (U : Opens X) (hU : (K : Set X) ⊆ U), P.kGerm K U hU ≫ f = P.kGerm K U hU ≫ g) :
    f = g :=
  (P.isColimitKGermCocone K).hom_ext fun U ↦
    h U.unop.val U.unop.property

/-- The morphism of K-presheaves induced by a morphism of presheaves: on each compact set `K` it
sends the germ along `K` of a section to the germ of its image. -/
noncomputable def toKPresheafMap {P Q : Presheaf C X} (φ : P ⟶ Q) :
    P.toKPresheaf ⟶ Q.toKPresheaf where
  app K := colimMap (Functor.whiskerLeft (Set.mono_coe K.unop.openNhds).functor.op φ)
  naturality _ L f := colimit.pre_map
    (Functor.whiskerLeft (Set.mono_coe L.unop.openNhds).functor.op φ)
    (Compacts.baseChangeOpenNhds_mono f.unop).functor.op

/-- `toKPresheafMap φ` sends the germ of a section to the germ of its image under `φ`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem kGerm_toKPresheafMap_app {P Q : Presheaf C X} (φ : P ⟶ Q) (K : Compacts X) (U : Opens X)
    (h : (K : Set X) ⊆ U) :
    P.kGerm K U h ≫ (toKPresheafMap φ).app (op K) = φ.app (op U) ≫ Q.kGerm K U h :=
  ι_colimMap _ _

variable (C X) in
/-- Taking K-presheaves, as a functor from presheaves to K-presheaves. -/
@[expose, simps]
noncomputable def toKPresheafFunctor : Presheaf C X ⥤ KPresheaf C X where
  obj P := P.toKPresheaf
  map φ := toKPresheafMap φ
  map_id P := by
    ext ⟨K⟩ U hU
    -- `(𝟙 P).app (op U)` is `𝟙 (P.obj (op U))` by definition of the functor category; the
    -- category instance on `Presheaf C X` has no `simp` lemma unfolding it.
    exact (P.kGerm_toKPresheafMap_app (𝟙 P) K U hU).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  map_comp φ ψ := by
    ext ⟨K⟩ U hU
    simp

/-- The value on `∅` of the K-presheaf of a sheaf is terminal. -/
noncomputable def isTerminalToKPresheafObjBot {P : Presheaf C X} (hP : P.IsSheaf) :
    IsTerminal (P.toKPresheaf.obj (op ⊥)) :=
  (Sheaf.isTerminalOfEmpty ⟨P, hP⟩).ofIso <| ((P.isColimitKGermCocone ⊥).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal Compacts.isInitialBotOpensOpenNhdsBot.op _)).symm

section Types

variable (P : Presheaf (Type w) X)

/-- Every element of the value on `K` of the K-presheaf of a presheaf of types is the germ of a
section over an open neighbourhood of `K`. -/
theorem exists_kGerm_apply_eq {K : Compacts X} (x : P.toKPresheaf.obj (op K)) :
    ∃ (U : Opens X) (hU : (K : Set X) ⊆ U) (s : P.obj (op U)), P.kGerm K U hU s = x := by
  obtain ⟨⟨U⟩, s, rfl⟩ := Types.jointly_surjective_of_isColimit (P.isColimitKGermCocone K) x
  exact ⟨U.val, U.property, s, rfl⟩

/-- Two sections of a presheaf of types have the same germ along `K` exactly when they agree on an
open neighbourhood of `K`. -/
theorem kGerm_apply_eq_kGerm_apply_iff {K : Compacts X} {U V : Opens X} (hU : (K : Set X) ⊆ U)
    (hV : (K : Set X) ⊆ V) (s : P.obj (op U)) (t : P.obj (op V)) :
    P.kGerm K U hU s = P.kGerm K V hV t ↔
      ∃ (W : Opens X) (_ : (K : Set X) ⊆ W) (iU : W ⟶ U) (iV : W ⟶ V),
        P.map iU.op s = P.map iV.op t := by
  refine (Types.FilteredColimit.isColimit_eq_iff _ (P.isColimitKGermCocone K)
    (i := op ⟨U, hU⟩) (j := op ⟨V, hV⟩)).trans ⟨?_, ?_⟩
  · rintro ⟨⟨W⟩, iU, iV, h⟩
    exact ⟨W.val, W.property, homOfLE iU.unop.le, homOfLE iV.unop.le, h⟩
  · rintro ⟨W, hW, iU, iV, h⟩
    exact ⟨op ⟨W, hW⟩, (homOfLE iU.le).op, (homOfLE iV.le).op, h⟩

/-- On a locally compact Hausdorff space, the value on a compact set `K` of the K-presheaf of a
presheaf of types is the colimit of its values on the compact neighbourhoods of `K`. -/
noncomputable def isColimitToKPresheafCoconeOfCompacts [T2Space X] [LocallyCompactSpace X]
    (K : Compacts X) : IsColimit (P.toKPresheaf.coconeOfCompacts K) := by
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) fun L x y hxy ↦ ?_
  · obtain ⟨U, hKU, s, rfl⟩ := P.exists_kGerm_apply_eq x
    obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between K.isCompact U.isOpen hKU
    refine ⟨op (Compacts.compactNhdsOfSubsetInterior ⟨L, hL⟩ hKL), P.kGerm ⟨L, hL⟩ U hLU s, ?_⟩
    exact (P.kGerm_toKPresheaf_map_apply
      (opHomOfLE (show K ≤ ⟨L, hL⟩ from hKL.trans interior_subset)) U hLU s).symm
  · obtain ⟨U, hLU, s, rfl⟩ := P.exists_kGerm_apply_eq x
    obtain ⟨V, hLV, t, rfl⟩ := P.exists_kGerm_apply_eq y
    simp only [KPresheaf.coconeOfCompacts_ι_app, kGerm_toKPresheaf_map_apply] at hxy
    obtain ⟨W, hKW, iU, iV, hst⟩ := (P.kGerm_apply_eq_kGerm_apply_iff _ _ _ _).1 hxy
    obtain ⟨V', hKV', hV'L⟩ := Compacts.exists_open_set_nhds_of_compactsNhds L.unop
    obtain ⟨L', hL', hKL', hL'W⟩ := exists_compact_between K.isCompact (W ⊓ V').isOpen
      (subset_inter hKW hKV')
    have hL'L : (L' : Set X) ⊆ L.unop.val := fun x hx ↦ hV'L (hL'W hx).2
    refine ⟨op (Compacts.compactNhdsOfSubsetInterior ⟨L', hL'⟩ hKL'),
      (homOfLE (show _ ≤ L.unop from hL'L)).op, ?_⟩
    have hL'W' : (L' : Set X) ⊆ W := fun x hx ↦ (hL'W hx).1
    let f : op L.unop.val ⟶ op ⟨L', hL'⟩ := (homOfLE (show _ ≤ L.unop.val from hL'L)).op
    calc _ = P.kGerm ⟨L', hL'⟩ U (hL'L.trans hLU) s := P.kGerm_toKPresheaf_map_apply f U hLU s
      _ = P.kGerm ⟨L', hL'⟩ W hL'W' (P.map iU.op s) := (P.kGerm_res_apply _ iU hL'W' s).symm
      _ = P.kGerm ⟨L', hL'⟩ W hL'W' (P.map iV.op t) := by rw [hst]
      _ = P.kGerm ⟨L', hL'⟩ V (hL'L.trans hLV) t := P.kGerm_res_apply _ iV hL'W' t
      _ = _ := (P.kGerm_toKPresheaf_map_apply f V hLV t).symm

/-- Locality for germs of a sheaf of types: two germs along `K₄ = K₂ ∪ K₃` agreeing along `K₂`
and along `K₃` are equal. -/
private theorem eq_of_toKPresheaf_map_eq [T2Space X] {P : Presheaf (Type w) X} (hP : P.IsSheaf)
    {K₁ K₂ K₃ K₄ : Compacts X} (sq : Lattice.BicartSq K₁ K₂ K₃ K₄)
    {x y : P.toKPresheaf.obj (op K₄)}
    (h₂ : P.toKPresheaf.map (opHomOfLE sq.le₂₄) x = P.toKPresheaf.map (opHomOfLE sq.le₂₄) y)
    (h₃ : P.toKPresheaf.map (opHomOfLE sq.le₃₄) x = P.toKPresheaf.map (opHomOfLE sq.le₃₄) y) :
    x = y := by
  -- Represent `x` and `y` by sections `s` and `t`, which agree on opens `W₂ ⊇ K₂`, `W₃ ⊇ K₃`.
  obtain ⟨U, hU, s, rfl⟩ := P.exists_kGerm_apply_eq x
  obtain ⟨V, hV, t, rfl⟩ := P.exists_kGerm_apply_eq y
  rw [kGerm_toKPresheaf_map_apply, kGerm_toKPresheaf_map_apply,
    kGerm_apply_eq_kGerm_apply_iff] at h₂ h₃
  obtain ⟨W₂, hW₂, iU₂, iV₂, e₂⟩ := h₂
  obtain ⟨W₃, hW₃, iU₃, iV₃, e₃⟩ := h₃
  have hW : (K₄ : Set X) ⊆ W₂ ⊔ W₃ := sq.sup_eq ▸ Compacts.coe_sup_subset_coe_sup hW₂ hW₃
  let iU : W₂ ⊔ W₃ ⟶ U := homOfLE (sup_le iU₂.le iU₃.le)
  let iV : W₂ ⊔ W₃ ⟶ V := homOfLE (sup_le iV₂.le iV₃.le)
  -- By locality `s` and `t` agree on `W₂ ⊔ W₃`, an open neighbourhood of `K₄`.
  have e : P.map iU.op s = P.map iV.op t := by
    refine (Sheaf.eq_of_locally_eq₂ ⟨P, hP⟩ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl
      _ _ ?_ ?_)
    · simp only [← Functor.map_comp_apply, ← op_comp]
      exact e₂
    · simp only [← Functor.map_comp_apply, ← op_comp]
      exact e₃
  rw [← P.kGerm_res_apply K₄ iU hW, ← P.kGerm_res_apply K₄ iV hW, e]

/-- Gluing for germs of a sheaf of types on a Hausdorff space: germs along `K₂` and `K₃` agreeing
along `K₁ = K₂ ∩ K₃` are the restrictions of a germ along `K₄ = K₂ ∪ K₃`. -/
private theorem exists_toKPresheaf_map_eq [T2Space X] {P : Presheaf (Type w) X}
    (hP : P.IsSheaf) {K₁ K₂ K₃ K₄ : Compacts X} (sq : Lattice.BicartSq K₁ K₂ K₃ K₄)
    {x₂ : P.toKPresheaf.obj (op K₂)} {x₃ : P.toKPresheaf.obj (op K₃)}
    (h : P.toKPresheaf.map (opHomOfLE sq.le₁₂) x₂ = P.toKPresheaf.map (opHomOfLE sq.le₁₃) x₃) :
    ∃ x, P.toKPresheaf.map (opHomOfLE sq.le₂₄) x = x₂ ∧
      P.toKPresheaf.map (opHomOfLE sq.le₃₄) x = x₃ := by
  -- Represent `x₂` and `x₃` by sections `s₂` and `s₃`, which agree on an open `W ⊇ K₁`.
  obtain ⟨U₂, hU₂, s₂, rfl⟩ := P.exists_kGerm_apply_eq x₂
  obtain ⟨U₃, hU₃, s₃, rfl⟩ := P.exists_kGerm_apply_eq x₃
  rw [kGerm_toKPresheaf_map_apply, kGerm_toKPresheaf_map_apply,
    kGerm_apply_eq_kGerm_apply_iff] at h
  obtain ⟨W, hW, i₂, i₃, e⟩ := h
  -- Separate the disjoint compact sets `K₂ \ W` and `K₃ \ W`, and shrink `U₂` and `U₃` to opens
  -- `U₂' ⊇ K₂` and `U₃' ⊇ K₃` meeting inside `W`.
  obtain ⟨V₂, V₃, hV₂, hV₃, hKV₂, hKV₃, hV⟩ := SeparatedNhds.of_isCompact_isCompact
    (K₂.isCompact.diff W.isOpen) (K₃.isCompact.diff W.isOpen) <| by
      rw [Set.disjoint_left]
      rintro x ⟨hx₂, hxW⟩ ⟨hx₃, -⟩
      exact hxW (hW (by rw [← sq.inf_eq, Compacts.coe_inf]; exact ⟨hx₂, hx₃⟩))
  let U₂' : Opens X := U₂ ⊓ (⟨V₂, hV₂⟩ ⊔ W)
  let U₃' : Opens X := U₃ ⊓ (⟨V₃, hV₃⟩ ⊔ W)
  have hK₂ : (K₂ : Set X) ⊆ U₂' := fun x hx ↦
    ⟨hU₂ hx, (em (x ∈ W)).elim Or.inr fun hxW ↦ Or.inl (hKV₂ ⟨hx, hxW⟩)⟩
  have hK₃ : (K₃ : Set X) ⊆ U₃' := fun x hx ↦
    ⟨hU₃ hx, (em (x ∈ W)).elim Or.inr fun hxW ↦ Or.inl (hKV₃ ⟨hx, hxW⟩)⟩
  have hW' : U₂' ⊓ U₃' ≤ W := by
    rintro x ⟨⟨-, hx₂ | hx₂⟩, -, hx₃ | hx₃⟩
    exacts [(Set.disjoint_left.1 hV hx₂ hx₃).elim, hx₃, hx₂, hx₃]
  -- The restrictions of `s₂` and `s₃` agree on `U₂' ⊓ U₃' ⊆ W`, so they glue to `s`.
  have key (j₂ : U₂' ⊓ U₃' ⟶ U₂) (j₃ : U₂' ⊓ U₃' ⟶ U₃) : P.map j₂.op s₂ = P.map j₃.op s₃ := by
    rw [Subsingleton.elim j₂ (homOfLE hW' ≫ i₂), Subsingleton.elim j₃ (homOfLE hW' ≫ i₃)]
    simp only [op_comp, Functor.map_comp_apply, e]
  obtain ⟨s, hs₂, hs₃⟩ : ∃ s : P.obj (op (U₂' ⊔ U₃')),
      P.map (homOfLE le_sup_left : U₂' ⟶ _).op s = P.map (homOfLE inf_le_left : U₂' ⟶ U₂).op s₂ ∧
        P.map (homOfLE le_sup_right : U₃' ⟶ _).op s =
          P.map (homOfLE inf_le_left : U₃' ⟶ U₃).op s₃ :=
    Types.exists_of_isPullback (IsPullback.of_isLimit
      (Sheaf.isLimitPullbackCone ⟨P, hP⟩ U₂' U₃')) _ _ <| by
        simpa only [← Functor.map_comp_apply, ← op_comp] using key _ _
  have hK₄ : (K₄ : Set X) ⊆ U₂' ⊔ U₃' := sq.sup_eq ▸ Compacts.coe_sup_subset_coe_sup hK₂ hK₃
  refine ⟨P.kGerm K₄ _ hK₄ s, ?_, ?_⟩
  · rw [kGerm_toKPresheaf_map_apply, ← P.kGerm_res_apply K₂ (homOfLE le_sup_left) hK₂, hs₂,
      P.kGerm_res_apply]
  · rw [kGerm_toKPresheaf_map_apply, ← P.kGerm_res_apply K₃ (homOfLE le_sup_right) hK₃, hs₃,
      P.kGerm_res_apply]

/-- On a Hausdorff space, the K-presheaf of a sheaf of types turns the union of two compact sets
into the pullback of its values on them over their intersection. -/
theorem IsSheaf.isPullback_toKPresheaf_map_types [T2Space X] {P : Presheaf (Type w) X}
    (hP : P.IsSheaf) {K₁ K₂ K₃ K₄ : Compacts X} (sq : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    IsPullback (P.toKPresheaf.map (opHomOfLE sq.le₂₄)) (P.toKPresheaf.map (opHomOfLE sq.le₃₄))
      (P.toKPresheaf.map (opHomOfLE sq.le₁₂)) (P.toKPresheaf.map (opHomOfLE sq.le₁₃)) := by
  rw [Types.isPullback_iff]
  exact ⟨by rw [← Functor.map_comp, ← Functor.map_comp]; congr 1,
    fun _ _ ⟨h₂, h₃⟩ ↦ eq_of_toKPresheaf_map_eq hP sq h₂ h₃,
    fun _ _ h ↦ exists_toKPresheaf_map_eq hP sq h⟩

/-- On a locally compact Hausdorff space, the K-presheaf of a sheaf of types is a K-sheaf. -/
theorem IsSheaf.isKSheaf_toKPresheaf_types [T2Space X] [LocallyCompactSpace X]
    {P : Presheaf (Type w) X} (hP : P.IsSheaf) : P.toKPresheaf.IsKSheaf where
  nonempty_isTerminal := ⟨isTerminalToKPresheafObjBot hP⟩
  isPullback := hP.isPullback_toKPresheaf_map_types
  nonempty_isColimit_coconeOfCompacts K := ⟨P.isColimitToKPresheafCoconeOfCompacts K⟩

end Types

section Functor

variable {D : Type*} [Category* D] [HasColimitsOfSize.{w, w} D] (G : C ⥤ D)
  [PreservesFilteredColimitsOfSize.{w, w} G] (P : Presheaf C X)

omit [HasColimitsOfSize.{w, w} D] in
/-- For a functor `G` preserving filtered colimits, morphisms out of the image under `G` of a value
of `P.toKPresheaf` agreeing on the images of all germs are equal. -/
theorem toKPresheaf_hom_ext_of_preservesColimits {K : Compacts X} {Z : D}
    {f g : G.obj (P.toKPresheaf.obj (op K)) ⟶ Z}
    (h : ∀ (U : Opens X) (hU : (K : Set X) ⊆ U),
      G.map (P.kGerm K U hU) ≫ f = G.map (P.kGerm K U hU) ≫ g) :
    f = g :=
  (isColimitOfPreserves G (P.isColimitKGermCocone K)).hom_ext fun U ↦
    h U.unop.val U.unop.property

/-- Taking K-presheaves commutes with a functor that preserves filtered colimits. -/
noncomputable def toKPresheafCompIso : P.toKPresheaf ⋙ G ≅ toKPresheaf (P ⋙ G) :=
  NatIso.ofComponents (fun K ↦ preservesColimitIso G (P.openNhdsDiagram K.unop)) fun {K L} f ↦
    P.toKPresheaf_hom_ext_of_preservesColimits G fun U hU ↦ by
      -- Both composites send the image under `G` of a germ of `P` along `K` to the germ of
      -- `P ⋙ G` along `L`.
      rw [Functor.comp_map, ← G.map_comp_assoc, kGerm_toKPresheaf_map]
      calc _ = kGerm (P ⋙ G) L.unop U _ := ι_preservesColimitIso_hom G _ _
        _ = kGerm (P ⋙ G) K.unop U hU ≫ (toKPresheaf (P ⋙ G)).map f :=
          (kGerm_toKPresheaf_map _ f U hU).symm
        _ = _ := (ι_preservesColimitIso_hom_assoc G (P.openNhdsDiagram K.unop) _ _).symm

theorem toKPresheafCompIso_hom_app (K : Compacts X) :
    (P.toKPresheafCompIso G).hom.app (op K) = (preservesColimitIso G (P.openNhdsDiagram K)).hom :=
  (rfl)

theorem toKPresheafCompIso_inv_app (K : Compacts X) :
    (P.toKPresheafCompIso G).inv.app (op K) = (preservesColimitIso G (P.openNhdsDiagram K)).inv :=
  (rfl)

/-- `P.toKPresheafCompIso G` sends the image under `G` of a germ of `P` to the germ of `P ⋙ G`. -/
@[reassoc (attr := simp)]
theorem kGerm_toKPresheafCompIso_hom_app (K : Compacts X) (U : Opens X) (h : (K : Set X) ⊆ U) :
    G.map (P.kGerm K U h) ≫ (P.toKPresheafCompIso G).hom.app (op K) = kGerm (P ⋙ G) K U h :=
  ι_preservesColimitIso_hom G (P.openNhdsDiagram K) _

/-- `(P.toKPresheafCompIso G).inv` sends a germ of `P ⋙ G` to the image under `G` of the germ
of `P`. -/
@[reassoc (attr := simp)]
theorem kGerm_toKPresheafCompIso_inv_app (K : Compacts X) (U : Opens X) (h : (K : Set X) ⊆ U) :
    kGerm (P ⋙ G) K U h ≫ (P.toKPresheafCompIso G).inv.app (op K) = G.map (P.kGerm K U h) :=
  ι_preservesColimitIso_inv G (P.openNhdsDiagram K) _

end Functor

/-- On a locally compact Hausdorff space, the K-presheaf of a sheaf is a K-sheaf, for sheaves with
values in a concrete category whose forgetful functor reflects isomorphisms and preserves limits
and filtered colimits, such as modules over a ring. -/
theorem IsSheaf.isKSheaf_toKPresheaf [T2Space X] [LocallyCompactSpace X]
    {FC : C → C → Type*} {CC : C → Type w} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [HasLimitsOfSize.{w, w} C] [(forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{w, w} (forget C)] [PreservesFilteredColimitsOfSize.{w, w} (forget C)]
    {P : Presheaf C X} (hP : P.IsSheaf) : P.toKPresheaf.IsKSheaf := by
  have h : KPresheaf.IsKSheaf (P.toKPresheaf ⋙ forget C) :=
    (KPresheaf.isKSheaf _ X).prop_of_iso (P.toKPresheafCompIso (forget C)).symm
      ((isSheaf_iff_isSheaf_comp' (forget C) P).1 hP).isKSheaf_toKPresheaf_types
  refine ⟨⟨isTerminalToKPresheafObjBot hP⟩, fun sq ↦ ?_, fun K ↦ ?_⟩
  · have : ReflectsLimitsOfShape WalkingCospan (forget C) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact IsPullback.of_map (forget C) (by rw [← Functor.map_comp, ← Functor.map_comp]; congr 1)
      (h.isPullback sq)
  · have : Nonempty K.compactNhds := by
      obtain ⟨L, hL, hKL⟩ := exists_compact_superset K.isCompact
      exact ⟨Compacts.compactNhdsOfSubsetInterior ⟨L, hL⟩ hKL⟩
    have : ReflectsColimitsOfShape (↥K.compactNhds)ᵒᵖ (forget C) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact ⟨isColimitOfReflects (forget C) (h.nonempty_isColimit_coconeOfCompacts K).some⟩

end TopCat.Presheaf
