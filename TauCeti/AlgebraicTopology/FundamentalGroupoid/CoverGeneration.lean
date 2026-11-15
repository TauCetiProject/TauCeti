/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.Topology.Homotopy.Path

/-!
# Covers generate the fundamental groupoid

Let `U : ι → Set X` be a family of subsets whose interiors cover `X`, that is, every point has
some `U i` as a neighbourhood (for instance an open cover). This file proves the generation half
of the groupoid Seifert--van Kampen theorem: every morphism of the fundamental groupoid of `X` is
a composite of morphisms coming from the fundamental groupoids of the sets `U i`.

The proof subdivides a path by the Lebesgue number lemma on the unit interval so that each piece
lies in a single `U i` (`Path.exists_monotone_range_subpath_subset`), and then uses Mathlib's
homotopy between a path and the concatenation of its consecutive subpaths.

Generation also pushes paths off simply connected sets. Suppose the cover consists of a set `V`
together with simply connected sets `W i`, each meeting `V` in a path-connected set, and that
distinct `W i` overlap only inside `V`. Conjugating by paths inside the `W i` to points of `V`
turns every morphism between points of `V` into the class of a path in `V`. This is how a loop in
a space with 2-cells attached is pushed off one point of each open cell.

## Main results

* `TauCeti.FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top`: the images of the inclusion functors
  `FundamentalGroupoid (U i) ⥤ FundamentalGroupoid X` generate the whole fundamental groupoid as
  a subgroupoid.
* `TauCeti.FundamentalGroupoid.functor_ext`: two functors out of `FundamentalGroupoid X` which
  agree after precomposition with every inclusion functor are equal. This is the uniqueness part
  of the universal property of the fundamental groupoid as a colimit over the cover.
* `Path.exists_range_subset_homotopic`: if `X` is covered by `V` and simply connected sets `W i`,
  each meeting `V` in a path-connected set and overlapping one another only inside `V`, then
  every path between points of `V` is homotopic to a path in `V`.

## References

* R. Brown, *Topology and Groupoids*, Section 6.7.
* A. Hatcher, *Algebraic Topology*, Section 1.2, proof of Theorem 1.20.
* T. Zhu, [mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603), whose
  fundamental-groupoid cosheaf interface guides the colimit formulation.
-/

public section

open CategoryTheory Set Topology
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X}

namespace TauCeti

namespace FundamentalGroupoid

open _root_.FundamentalGroupoid

/-- A path class whose representative has range in `U i` lies in the image of the inclusion
functor of `U i`. -/
private theorem mk_mem_iSup_im {x y : X} (γ : Path x y) {i : ι} (hγ : range γ ⊆ U i) :
    (Path.Homotopic.Quotient.mk γ : mk x ⟶ mk y) ∈
      (⨆ j, Subgroupoid.im (map (ContinuousMap.subtypeVal (U j)))
        (ContinuousMap.fundamentalGroupoid_map_obj_injective
          (ContinuousMap.subtypeVal (U j)) Subtype.val_injective)).arrows (mk x) (mk y) := by
  refine (Subgroupoid.le_iff _ _).1 (le_iSup (fun j ↦ Subgroupoid.im
    (map (ContinuousMap.subtypeVal (U j)))
      (ContinuousMap.fundamentalGroupoid_map_obj_injective
        (ContinuousMap.subtypeVal (U j)) Subtype.val_injective)) i) ?_
  have hmem : ∀ t, γ t ∈ U i := fun t ↦ hγ ⟨t, rfl⟩
  have hx : x ∈ U i := γ.source ▸ hmem 0
  have hy : y ∈ U i := γ.target ▸ hmem 1
  have h := Subgroupoid.Map.Arrows.im (φ := map (ContinuousMap.subtypeVal (U i)))
    (hφ := ContinuousMap.fundamentalGroupoid_map_obj_injective
      (ContinuousMap.subtypeVal (U i)) Subtype.val_injective) (S := ⊤)
    (Path.Homotopic.Quotient.mk (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hmem)) trivial
  rw [map_map, ← Path.Homotopic.Quotient.mk_map] at h
  have hp : (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hmem).map
      (ContinuousMap.subtypeVal (U i)).continuous = γ :=
    Path.map_codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) γ hmem
  rw [hp] at h
  -- Membership in `Subgroupoid.im` is by definition membership in `Subgroupoid.Map.Arrows`, and
  -- `(map f).obj (mk a)` is by definition `mk (f a)`.
  exact h

/-- A concatenation of paths, each with range in some `U i`, lies in the subgroupoid generated
by the images of the inclusion functors. -/
private theorem mk_concat_mem_iSup_im (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (hF : ∀ k, ∃ i, range (F k) ⊆ U i) :
    (Path.Homotopic.Quotient.mk (Path.concat p F) : mk (p 0) ⟶ mk (p (Fin.last n))) ∈
      (⨆ j, Subgroupoid.im (map (ContinuousMap.subtypeVal (U j)))
        (ContinuousMap.fundamentalGroupoid_map_obj_injective
          (ContinuousMap.subtypeVal (U j)) Subtype.val_injective)).arrows
        (mk (p 0)) (mk (p (Fin.last n))) := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := hU (p 0)
    rw [Path.concat_zero]
    exact mk_mem_iSup_im _ (by simpa using mem_of_mem_nhds hi)
  | succ n ih =>
    obtain ⟨i, hi⟩ := hF (Fin.last n)
    rw [Path.concat_succ]
    exact Subgroupoid.mul _ (ih (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc) fun k ↦ hF k.castSucc)
      (mk_mem_iSup_im _ hi)

/-- **Generation half of the groupoid van Kampen theorem.** If every point of `X` has some `U i`
as a neighbourhood, then the images of the inclusion functors
`FundamentalGroupoid (U i) ⥤ FundamentalGroupoid X` generate the fundamental groupoid of `X`:
every morphism is a composite of morphisms coming from the sets `U i`. -/
theorem iSup_im_map_subtypeVal_eq_top (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) :
    ⨆ i, Subgroupoid.im (map (ContinuousMap.subtypeVal (U i)))
      (ContinuousMap.fundamentalGroupoid_map_obj_injective
        (ContinuousMap.subtypeVal (U i)) Subtype.val_injective) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨⟨x⟩, ⟨y⟩, f⟩ -
  induction f using Path.Homotopic.Quotient.ind with | mk γ =>
  obtain ⟨n, t, ht0, htn, -, ht⟩ := γ.exists_monotone_range_subpath_subset fun s ↦ by
    obtain ⟨i, hi⟩ := hU (γ s)
    exact ⟨i, γ.continuous.continuousAt.preimage_mem_nhds hi⟩
  have hsub := mk_concat_mem_iSup_im hU (γ ∘ t) (fun k ↦ γ.subpath (t k.castSucc) (t k.succ)) ht
  rw [Path.Homotopic.Quotient.eq.2 (Path.Homotopic.concat_subpath γ t)] at hsub
  have hγ : ∀ (a b : I) (ha : a = 0) (hb : b = 1),
      γ = (γ.subpath a b).cast (by simp [ha]) (by simp [hb]) := by
    rintro _ _ rfl rfl
    rw [Path.subpath_zero_one]
    rfl
  rw [hγ _ _ ht0 htn, Path.Homotopic.Quotient.mk_cast]
  exact (Path.Homotopic.Quotient.cast_mem_arrows_iff _ _ _).2 hsub

/-- Two functors out of the fundamental groupoid of `X` are equal as soon as they agree after
precomposition with the inclusion functor of every `U i`, provided every point of `X` has some
`U i` as a neighbourhood. -/
theorem functor_ext (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) {D : Type*} [Category D]
    {F G : _root_.FundamentalGroupoid X ⥤ D}
    (h : ∀ i, map (ContinuousMap.subtypeVal (U i)) ⋙ F =
      map (ContinuousMap.subtypeVal (U i)) ⋙ G) :
    F = G := by
  have hobj : ∀ c, F.obj c = G.obj c := by
    rintro ⟨x⟩
    obtain ⟨i, hi⟩ := hU x
    have hx := CategoryTheory.Functor.congr_obj (h i) (mk ⟨x, mem_of_mem_nhds hi⟩)
    -- `(map f ⋙ F).obj (mk a)` is by definition `F.obj (mk (f a))`, since `map f` sends `mk a` to
    -- `mk (f a)`; here `f` is `Subtype.val`, so `f ⟨x, _⟩` is `x`.
    change F.obj (mk x) = G.obj (mk x) at hx
    exact hx
  -- The morphisms on which `F` and `G` agree form a subgroupoid.
  let S : Subgroupoid (_root_.FundamentalGroupoid X) :=
    { arrows := fun c d ↦ {f | F.map f = eqToHom (hobj c) ≫ G.map f ≫ eqToHom (hobj d).symm}
      inv := fun {c d f} hf ↦ by
        simp only [mem_ofPred_eq, Groupoid.inv_eq_inv, Functor.map_inv] at hf ⊢
        simp [hf]
      mul := fun {c d e f} hf {g} hg ↦ by
        simp only [mem_ofPred_eq, Functor.map_comp] at hf hg ⊢
        simp [hf, hg] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← iSup_im_map_subtypeVal_eq_top hU]
    refine iSup_le fun i ↦ ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨a, b, g⟩ -
    -- Membership in `Subgroupoid.comap φ S` is by definition membership of `φ.map g` in `S`, and
    -- `(φ ⋙ F).map g` is by definition `F.map (φ.map g)`.
    exact CategoryTheory.Functor.congr_hom (h i) g
  refine CategoryTheory.Functor.ext hobj fun c d f ↦ ?_
  have hf : f ∈ S.arrows c d := by
    rw [hS]
    trivial
  exact hf

/-! ### Pushing paths off simply connected sets -/

section PushOff

variable {V : Set X} {W : ι → Set X}

/-- The morphism `f` of the fundamental groupoid is the class of a path with range in `V`. -/
private def IsArrowIn (V : Set X) {c d : _root_.FundamentalGroupoid X} (f : c ⟶ d) : Prop :=
  ∃ p : Path c.as d.as, range p ⊆ V ∧ f = Path.Homotopic.Quotient.mk p

private theorem IsArrowIn.source_mem {c d : _root_.FundamentalGroupoid X} {f : c ⟶ d}
    (hf : IsArrowIn V f) : c.as ∈ V := by
  obtain ⟨p, hp, -⟩ := hf
  exact hp ⟨0, p.source⟩

private theorem IsArrowIn.target_mem {c d : _root_.FundamentalGroupoid X} {f : c ⟶ d}
    (hf : IsArrowIn V f) : d.as ∈ V := by
  obtain ⟨p, hp, -⟩ := hf
  exact hp ⟨1, p.target⟩

private theorem isArrowIn_id {c : _root_.FundamentalGroupoid X} (hc : c.as ∈ V) :
    IsArrowIn V (𝟙 c) :=
  ⟨Path.refl c.as, by rw [Path.refl_range]; exact singleton_subset_iff.2 hc, id_eq_path_refl c⟩

private theorem IsArrowIn.comp {c d e : _root_.FundamentalGroupoid X} {f : c ⟶ d} {g : d ⟶ e}
    (hf : IsArrowIn V f) (hg : IsArrowIn V g) : IsArrowIn V (f ≫ g) := by
  obtain ⟨p, hp, rfl⟩ := hf
  obtain ⟨q, hq, rfl⟩ := hg
  exact ⟨p.trans q, by rw [Path.trans_range]; exact union_subset hp hq,
    (Path.Homotopic.Quotient.mk_trans p q).symm⟩

private theorem IsArrowIn.inv {c d : _root_.FundamentalGroupoid X} {f : c ⟶ d}
    (hf : IsArrowIn V f) : IsArrowIn V (inv f) := by
  obtain ⟨p, hp, rfl⟩ := hf
  refine ⟨p.symm, by rwa [Path.symm_range], ?_⟩
  rw [← Groupoid.inv_eq_inv, Path.Homotopic.Quotient.mk_symm]
  -- The inverse in the fundamental groupoid is by definition induced by `Path.symm`.
  rfl

/-- Inside a simply connected `W i`, a morphism between two points of `W i ∩ V` is the class of a
path in `V`: it is the class of any path joining them inside the path-connected `W i ∩ V`. -/
private theorem IsArrowIn.of_isSimplyConnected {i : ι} (hW : IsSimplyConnected (W i))
    (hWV : IsPathConnected (W i ∩ V)) {c d : _root_.FundamentalGroupoid X} {f : c ⟶ d}
    (hf : IsArrowIn (W i) f) (hc : c.as ∈ V) (hd : d.as ∈ V) : IsArrowIn V f := by
  have hc' := hf.source_mem
  have hd' := hf.target_mem
  obtain ⟨p, hp, rfl⟩ := hf
  have hq := hWV.joinedIn c.as ⟨hc', hc⟩ d.as ⟨hd', hd⟩
  obtain ⟨K, -⟩ := Path.exists_homotopy_forall_mem_of_isSimplyConnected hW
    (fun t ↦ hp ⟨t, rfl⟩) fun t ↦ (hq.somePath_mem t).1
  exact ⟨hq.somePath, range_subset_iff.2 fun t ↦ (hq.somePath_mem t).2,
    Quotient.sound ⟨K⟩⟩

/-- A morphism `e : c ⟶ u` is admissible when it ends in `V` and is the class of a path in `V` or
in a single `W i`. -/
private def IsAdmissible (V : Set X) (W : ι → Set X) {c u : _root_.FundamentalGroupoid X}
    (e : c ⟶ u) : Prop :=
  u.as ∈ V ∧ (IsArrowIn V e ∨ ∃ i, IsArrowIn (W i) e)

variable (hW : ∀ i, IsSimplyConnected (W i)) (hWV : ∀ i, IsPathConnected (W i ∩ V))
  (hdisj : Pairwise fun i j ↦ W i ∩ W j ⊆ V)
include hW hWV

private theorem IsAdmissible.isArrowIn {c u : _root_.FundamentalGroupoid X} {e : c ⟶ u}
    (he : IsAdmissible V W e) (hc : c.as ∈ V) : IsArrowIn V e := by
  obtain ⟨hu, he | ⟨i, he⟩⟩ := he
  · exact he
  · exact he.of_isSimplyConnected (hW i) (hWV i) hc hu

include hdisj in
/-- Two admissible morphisms out of the same point differ by the class of a path in `V`. -/
private theorem IsAdmissible.inv_comp {c u u' : _root_.FundamentalGroupoid X} {e : c ⟶ u}
    {e' : c ⟶ u'} (he : IsAdmissible V W e) (he' : IsAdmissible V W e') :
    IsArrowIn V (inv e ≫ e') := by
  by_cases hc : c.as ∈ V
  · exact ((he.isArrowIn hW hWV hc).inv).comp (he'.isArrowIn hW hWV hc)
  obtain ⟨hu, he | ⟨i, he⟩⟩ := he
  · exact absurd he.source_mem hc
  obtain ⟨hu', he' | ⟨j, he'⟩⟩ := he'
  · exact absurd he'.source_mem hc
  obtain rfl : i = j := by
    by_contra hij
    exact hc (hdisj hij ⟨he.source_mem, he'.source_mem⟩)
  exact (he.inv.comp he').of_isSimplyConnected (hW i) (hWV i) hu hu'

/-- Every point has an admissible morphism out of it: the identity at a point of `V`, and the
class of a path inside some `W i` to a point of `W i ∩ V` otherwise. -/
private theorem _root_.FundamentalGroupoid.exists_isAdmissible
    (hcover : ∀ y, V ∈ 𝓝 y ∨ ∃ i, W i ∈ 𝓝 y)
    (c : _root_.FundamentalGroupoid X) :
    ∃ (u : _root_.FundamentalGroupoid X) (e : c ⟶ u), IsAdmissible V W e := by
  by_cases hc : c.as ∈ V
  · exact ⟨c, 𝟙 c, hc, .inl (isArrowIn_id hc)⟩
  obtain hV | ⟨i, hi⟩ := hcover c.as
  · exact absurd (mem_of_mem_nhds hV) hc
  obtain ⟨y, hy⟩ := (hWV i).nonempty
  have hp := (hW i).isPathConnected.joinedIn c.as (mem_of_mem_nhds hi) y hy.1
  exact ⟨mk y, Path.Homotopic.Quotient.mk hp.somePath, hy.2, .inr
    ⟨i, hp.somePath, range_subset_iff.2 hp.somePath_mem, rfl⟩⟩

/-- Conjugating the class of a path in `V` by admissible morphisms gives the class of a path in
`V`. -/
private theorem IsArrowIn.conj_of_isAdmissible {c d u v : _root_.FundamentalGroupoid X}
    {f : c ⟶ d} (hf : IsArrowIn V f) {e : c ⟶ u} {e' : d ⟶ v} (he : IsAdmissible V W e)
    (he' : IsAdmissible V W e') : IsArrowIn V (CategoryTheory.inv e ≫ f ≫ e') :=
  (he.isArrowIn hW hWV hf.source_mem).inv.comp
    (hf.comp (he'.isArrowIn hW hWV hf.target_mem))

include hdisj in
/-- Conjugating the class of a path in a single `W i` by admissible morphisms gives the class of
a path in `V`. Route the path through a point `y` of `W i ∩ V` by paths inside `W i`: the middle
loop at `y` lies in the simply connected `W i`, and the outer pieces compare admissible
morphisms. -/
private theorem IsArrowIn.conj_of_isAdmissible_of_isArrowIn {i : ι}
    {c d u v : _root_.FundamentalGroupoid X} {f : c ⟶ d} (hf : IsArrowIn (W i) f) {e : c ⟶ u}
    {e' : d ⟶ v} (he : IsAdmissible V W e) (he' : IsAdmissible V W e') :
    IsArrowIn V (CategoryTheory.inv e ≫ f ≫ e') := by
  obtain ⟨y, hy⟩ := (hWV i).nonempty
  have hpc := (hW i).isPathConnected.joinedIn c.as hf.source_mem y hy.1
  have hpd := (hW i).isPathConnected.joinedIn d.as hf.target_mem y hy.1
  let εc : c ⟶ mk y := Path.Homotopic.Quotient.mk hpc.somePath
  let εd : d ⟶ mk y := Path.Homotopic.Quotient.mk hpd.somePath
  have hεc : IsArrowIn (W i) εc := ⟨_, range_subset_iff.2 hpc.somePath_mem, rfl⟩
  have hεd : IsArrowIn (W i) εd := ⟨_, range_subset_iff.2 hpd.somePath_mem, rfl⟩
  have hmid := (hεc.inv.comp (hf.comp hεd)).of_isSimplyConnected (hW i) (hWV i) hy.2 hy.2
  have h := ((he.inv_comp hW hWV hdisj ⟨hy.2, .inr ⟨i, hεc⟩⟩).comp hmid).comp
    (IsAdmissible.inv_comp hW hWV hdisj ⟨hy.2, .inr ⟨i, hεd⟩⟩ he')
  simpa using h

end PushOff

/-- **Paths can be pushed off simply connected sets.** Suppose that every point of `X` has as a
neighbourhood either `V` or one of the sets `W i`, that every `W i` is simply connected and meets
`V` in a path-connected set, and that distinct `W i` overlap only inside `V`. Then every path
between two points of `V` is homotopic to a path with range in `V`.

The typical application is to a space with open 2-cells attached: `V` is the complement of a
point in each open cell, and `W i` is the `i`-th open cell. -/
theorem _root_.Path.exists_range_subset_homotopic {V : Set X} {W : ι → Set X}
    (hcover : ∀ y, V ∈ 𝓝 y ∨ ∃ i, W i ∈ 𝓝 y) (hW : ∀ i, IsSimplyConnected (W i))
    (hWV : ∀ i, IsPathConnected (W i ∩ V)) (hdisj : Pairwise fun i j ↦ W i ∩ W j ⊆ V)
    {a b : X} (ha : a ∈ V) (hb : b ∈ V) (γ : Path a b) :
    ∃ δ : Path a b, range δ ⊆ V ∧ γ.Homotopic δ := by
  -- The morphisms `f : c ⟶ d` whose conjugates by admissible morphisms are classes of paths
  -- in `V`.
  let S : Subgroupoid (_root_.FundamentalGroupoid X) :=
    { arrows := fun c d ↦ {f | ∀ (u v : _root_.FundamentalGroupoid X) (e : c ⟶ u) (e' : d ⟶ v),
        IsAdmissible V W e → IsAdmissible V W e' → IsArrowIn V (inv e ≫ f ≫ e')}
      inv := fun {c d f} hf u v e e' he he' ↦ by
        have h := (hf v u e' e he' he).inv
        rw [← Groupoid.inv_eq_inv]
        simpa using h
      mul := fun {c d e f} hf {g} hg u v ec eb hc hb ↦ by
        obtain ⟨w, ed, hd⟩ := exists_isAdmissible hW hWV hcover d
        have h := (hf u w ec ed hc hd).comp (hg w v ed eb hd hb)
        simpa using h }
  -- The cover of `X` by `V` and the sets `W i`, indexed by `Option ι`.
  let U : Option ι → Set X := fun o ↦ o.elim V W
  have hU : ∀ y, ∃ o, U o ∈ 𝓝 y := fun y ↦ by
    obtain hV | ⟨i, hi⟩ := hcover y
    exacts [⟨none, hV⟩, ⟨some i, hi⟩]
  -- Every morphism coming from a single member of the cover lies in `S`, so `S` is everything.
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← iSup_im_map_subtypeVal_eq_top hU]
    refine iSup_le fun o ↦ ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨⟨c⟩, ⟨d⟩, g⟩ -
    induction g using Path.Homotopic.Quotient.ind with | mk δ =>
    have hδ : IsArrowIn (U o) (Path.Homotopic.Quotient.mk (δ.map continuous_subtype_val) :
        mk c.1 ⟶ mk d.1) := ⟨_, by rintro _ ⟨t, rfl⟩; exact (δ t).2, rfl⟩
    intro u v e e' he he'
    cases o with
    | none => exact IsArrowIn.conj_of_isAdmissible hW hWV hδ he he'
    | some i => exact IsArrowIn.conj_of_isAdmissible_of_isArrowIn hW hWV hdisj hδ he he'
  have hγ : (Path.Homotopic.Quotient.mk γ : mk a ⟶ mk b) ∈ S.arrows (mk a) (mk b) := by
    rw [hS]
    trivial
  obtain ⟨δ, hδ, h⟩ := hγ (mk a) (mk b) (𝟙 _) (𝟙 _) ⟨ha, .inl (isArrowIn_id ha)⟩
    ⟨hb, .inl (isArrowIn_id hb)⟩
  refine ⟨δ, hδ, Path.Homotopic.Quotient.exact ?_⟩
  simpa using h

end FundamentalGroupoid

end TauCeti
