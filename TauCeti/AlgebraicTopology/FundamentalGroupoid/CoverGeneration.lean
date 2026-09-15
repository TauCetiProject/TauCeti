/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
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

## Main results

* `TauCeti.FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top`: the images of the inclusion functors
  `FundamentalGroupoid (U i) ⥤ FundamentalGroupoid X` generate the whole fundamental groupoid as
  a subgroupoid.
* `TauCeti.FundamentalGroupoid.functor_ext`: two functors out of `FundamentalGroupoid X` which
  agree after precomposition with every inclusion functor are equal. This is the uniqueness part
  of the universal property of the fundamental groupoid as a colimit over the cover.

## References

* R. Brown, *Topology and Groupoids*, Section 6.7.
* A. Hatcher, *Algebraic Topology*, Section 1.2, proof of Theorem 1.20.
* T. Zhu, [mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603)
  (Seifert--van Kampen for the fundamental groupoid functor). Its groupoid formulation informed
  the direction of this construction; no code from it was copied.
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
        (fundamentalGroupoid_map_obj_injective (ContinuousMap.subtypeVal (U j))
          Subtype.val_injective)).arrows (mk x) (mk y) := by
  refine (Subgroupoid.le_iff _ _).1 (le_iSup (fun j ↦ Subgroupoid.im
    (map (ContinuousMap.subtypeVal (U j)))
      (fundamentalGroupoid_map_obj_injective (ContinuousMap.subtypeVal (U j))
        Subtype.val_injective)) i) ?_
  have hmem : ∀ t, γ t ∈ U i := fun t ↦ hγ ⟨t, rfl⟩
  have hx : x ∈ U i := γ.source ▸ hmem 0
  have hy : y ∈ U i := γ.target ▸ hmem 1
  have h := Subgroupoid.Map.Arrows.im (φ := map (ContinuousMap.subtypeVal (U i)))
    (hφ := fundamentalGroupoid_map_obj_injective (ContinuousMap.subtypeVal (U i))
      Subtype.val_injective) (S := ⊤)
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
        (fundamentalGroupoid_map_obj_injective (ContinuousMap.subtypeVal (U j))
          Subtype.val_injective)).arrows (mk (p 0)) (mk (p (Fin.last n))) := by
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
      (fundamentalGroupoid_map_obj_injective (ContinuousMap.subtypeVal (U i))
        Subtype.val_injective) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨⟨x⟩, ⟨y⟩, f⟩ -
  induction f using Path.Homotopic.Quotient.ind with | mk γ =>
  obtain ⟨n, t, ht0, htn, -, ht⟩ := γ.exists_monotone_range_subpath_subset fun s ↦ hU (γ s)
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
    exact CategoryTheory.Functor.congr_obj (h i) (mk ⟨x, mem_of_mem_nhds hi⟩)
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

end FundamentalGroupoid

end TauCeti
