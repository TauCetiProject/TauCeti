/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Module.Basic

/-!
# Chain maps out of the normalized chains of standard simplices

The normalized chain complex `N_*(Δ[n])` of the standard `n`-simplex is free on its nondegenerate
simplices, which are the nonempty subsets `J ⊆ {0, …, n}`: the generator `e_J` sits in homological
degree `#J - 1`, and `∂ e_J = ∑_{j ∈ J} (-1) ^ #{s ∈ J | s < j} e_{J \ {j}}`. For a cochain
complex `K` of modules, a chain map from `N_*(Δ[n])` to the good truncation `τ_{≥ 0} K` therefore
amounts to elements `g J` of `K` in cohomological degree `1 - #J`, one for each nonempty `J`, with

`d (g J) = ∑_{j ∈ J} (-1) ^ #{s ∈ J | s < j} • g (J \ {j})`,

where the term for the empty set is zero; for a singleton `J` this says that `g J` is a cycle of
degree zero, as the truncation requires. A monotone map `α : [m] → [n]` acts on such families by
`(α^* g) J = g (α J)` when `α` is injective on `J`, and `0` otherwise, which is how it acts on
normalized chains. This gives a simplicial set `K.simplexChainMaps`: the normalized-chain
description of the simplicial set that the Dold–Kan correspondence attaches to `τ_{≥ 0} K`. The
right mapping spaces of a differential graded nerve are computed by it
(`TauCeti.dgNerve.rightMappingSpaceIso`).

We record a family `g` as a function of all finite sets `J` and all degrees `d`, required to
vanish unless `J` is nonempty and `d + #J = 1`. This avoids degree casts: the value at `J` in the
wrong degree is zero rather than undefined.

## Main definitions

* `CochainComplex.SimplexChainMap K n`: the chain maps from `N_*(Δ[n])` to `τ_{≥ 0} K`, by their
  values on the nondegenerate simplices.
* `CochainComplex.SimplexChainMap.map`: their pullback along a monotone map.
* `CochainComplex.simplexChainMaps K`: the simplicial set they form.

## References

* J. Lurie, *Higher Algebra*, Section 1.2.3 and Remark 1.3.1.12.
* P. Goerss and J. Jardine, *Simplicial homotopy theory*, Section III.2.
-/

public section

open CategoryTheory Finset Simplicial

universe v u

namespace CochainComplex

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℤ)

/-- A chain map from the normalized chains of the standard `n`-simplex to the good truncation
`τ_{≥ 0}` of a cochain complex `K` of modules, given by its values on the nondegenerate simplices:
for each nonempty set `J` of vertices, an element `val J (1 - #J)` of `K` whose differential is
the alternating sum of the values on the faces of `J`. The values in all other degrees, and on the
empty set, vanish. -/
@[ext]
structure SimplexChainMap (n : ℕ) : Type v where
  /-- The value on the simplex with vertex set `J`, in cohomological degree `d`. -/
  val : Finset (Fin (n + 1)) → ∀ d : ℤ, K.X d
  /-- The value on `J` vanishes outside cohomological degree `1 - #J`. -/
  val_eq_zero_of_ne (J : Finset (Fin (n + 1))) (d : ℤ) (h : d + #J ≠ 1) : val J d = 0
  /-- The value on the empty set vanishes. -/
  val_empty : val ∅ 1 = 0
  /-- The differential of the value on `J` is the alternating sum of the values on its faces. -/
  d_val (J : Finset (Fin (n + 1))) (d : ℤ) :
    (K.d d (d + 1)).hom (val J d) =
      ∑ j ∈ J, (#{s ∈ J | s < j} : ℤ).negOnePow • val (J.erase j) (d + 1)

namespace SimplexChainMap

variable {K} {m n : ℕ}

/-- The value of a simplex chain map on the empty set vanishes in every degree. -/
@[simp]
theorem val_empty' (g : K.SimplexChainMap n) (d : ℤ) : g.val ∅ d = 0 := by
  by_cases hd : d = 1
  · subst hd
    exact g.val_empty
  · exact g.val_eq_zero_of_ne _ _ (by simpa using hd)

/-- The value on a single vertex is a cycle. -/
theorem d_val_singleton (g : K.SimplexChainMap n) (j : Fin (n + 1)) (d : ℤ) :
    (K.d d (d + 1)).hom (g.val {j} d) = 0 := by
  simp [g.d_val]

/-- If a monotone map is not injective on `J`, the alternating sum over the faces of `J` of the
values of the pullback vanishes: the two faces omitting two consecutive vertices of `J` with the
same image cancel, and every other face is still not mapped injectively. -/
private theorem sum_faces_eq_zero_of_not_injOn (g : K.SimplexChainMap n)
    (α : Fin (m + 1) →o Fin (n + 1)) {J : Finset (Fin (m + 1))} (hJ : #(J.image α) ≠ #J)
    (d : ℤ) :
    ∑ j ∈ J, (#{s ∈ J | s < j} : ℤ).negOnePow •
      (if #((J.erase j).image α) = #(J.erase j) then g.val ((J.erase j).image α) d else 0) =
      0 := by
  -- Two vertices `a < b` of `J` with the same image and no vertex of `J` between them.
  obtain ⟨x, hx, y, hy, hxy, hαxy⟩ : ∃ x ∈ J, ∃ y ∈ J, x < y ∧ α x = α y := by
    have hJ' : ¬ Set.InjOn α J := fun h ↦ hJ (card_image_iff.2 h)
    simp only [Set.InjOn, mem_coe, not_forall] at hJ'
    obtain ⟨x, hx, y, hy, hαxy, hne⟩ := hJ'
    rcases Ne.lt_or_gt hne with h | h
    · exact ⟨x, hx, y, hy, h, hαxy⟩
    · exact ⟨y, hy, x, hx, h, hαxy.symm⟩
  have hne : {s ∈ J | x < s}.Nonempty := ⟨y, mem_filter.2 ⟨hy, hxy⟩⟩
  set b := {s ∈ J | x < s}.min' hne
  have hb : b ∈ J ∧ x < b := mem_filter.1 (min'_mem _ hne)
  have hby : b ≤ y := min'_le _ _ (mem_filter.2 ⟨hy, hxy⟩)
  have hαb : α x = α b :=
    le_antisymm (α.monotone hb.2.le) (hαxy ▸ α.monotone hby)
  have hbetween : ∀ s ∈ J, x < s → b ≤ s := fun s hs hxs ↦ min'_le _ _ (mem_filter.2 ⟨hs, hxs⟩)
  -- Faces containing both `x` and `b` are not mapped injectively.
  have hnot : ∀ T ⊆ J, x ∈ T → b ∈ T → #(T.image α) ≠ #T := by
    intro T _ hxT hbT h
    rw [card_image_iff] at h
    exact hb.2.ne (h hxT hbT hαb)
  rw [sum_eq_add_of_mem x b hx hb.1 hb.2.ne fun c hc hcxb ↦ by
    rw [ite_eq_right (hnot _ (erase_subset _ _) (mem_erase.2 ⟨hcxb.1.symm, hx⟩)
      (mem_erase.2 ⟨hcxb.2.symm, hb.1⟩)), smul_zero]]
  have himage : (J.erase x).image α = (J.erase b).image α := by
    ext z
    simp only [mem_image, mem_erase]
    constructor
    · rintro ⟨w, ⟨hwx, hw⟩, rfl⟩
      by_cases hwb : w = b
      · exact ⟨x, ⟨hb.2.ne, hx⟩, hwb ▸ hαb⟩
      · exact ⟨w, ⟨hwb, hw⟩, rfl⟩
    · rintro ⟨w, ⟨hwb, hw⟩, rfl⟩
      by_cases hwx : w = x
      · exact ⟨b, ⟨hb.2.ne', hb.1⟩, hwx ▸ hαb.symm⟩
      · exact ⟨w, ⟨hwx, hw⟩, rfl⟩
  have hcard : #(J.erase x) = #(J.erase b) := by
    rw [card_erase_of_mem hx, card_erase_of_mem hb.1]
  have hsign : #{s ∈ J | s < b} = #{s ∈ J | s < x} + 1 := by
    have : {s ∈ J | s < b} = insert x {s ∈ J | s < x} := by
      ext s
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hs, hsb⟩
        rcases lt_trichotomy s x with h | h | h
        · exact Or.inr ⟨hs, h⟩
        · exact Or.inl h
        · exact absurd (hbetween s hs h) (not_le.2 hsb)
      · rintro (rfl | ⟨hs, hsx⟩)
        · exact ⟨hx, hb.2⟩
        · exact ⟨hs, hsx.trans hb.2⟩
    rw [this, card_insert_of_notMem (by simp)]
  rw [himage, hcard, hsign, Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.neg_smul,
    add_neg_cancel]

/-- The pullback of a simplex chain map along a monotone map `α`: its value on `J` is the value
on the image of `J` when `α` is injective on `J`, and zero otherwise. -/
noncomputable def map (g : K.SimplexChainMap n) (α : Fin (m + 1) →o Fin (n + 1)) :
    K.SimplexChainMap m where
  val J d := if #(J.image α) = #J then g.val (J.image α) d else 0
  val_eq_zero_of_ne J d h := by
    split_ifs with hα
    · exact g.val_eq_zero_of_ne _ _ (by rwa [hα])
    · rfl
  val_empty := by simp
  d_val J d := by
    by_cases hα : #(J.image α) = #J
    · have hinj : Set.InjOn α J := card_image_iff.1 hα
      have hsub : ∀ j ∈ J, #((J.erase j).image α) = #(J.erase j) := fun j _ ↦
        card_image_iff.2 (hinj.mono (coe_subset.2 (erase_subset _ _)))
      rw [ite_eq_left hα, g.d_val, sum_image fun a ha b hb h ↦ hinj ha hb h]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [ite_eq_left (hsub j hj)]
      have himage : (J.erase j).image α = (J.image α).erase (α j) := by
        ext z
        simp only [mem_image, mem_erase]
        constructor
        · rintro ⟨w, ⟨hwj, hw⟩, rfl⟩
          exact ⟨fun h ↦ hwj (hinj hw hj h), w, hw, rfl⟩
        · rintro ⟨hz, w, hw, rfl⟩
          exact ⟨w, ⟨fun h ↦ hz (h ▸ rfl), hw⟩, rfl⟩
      have hcount : #{s ∈ J.image α | s < α j} = #{s ∈ J | s < j} := by
        rw [filter_image, card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _)))]
        congr 1
        refine filter_congr fun s hs ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · exact lt_of_le_of_ne (α.monotone.reflect_lt h |>.le) fun hsj ↦ h.ne (hsj ▸ rfl)
        · exact lt_of_le_of_ne (α.monotone h.le) fun h' ↦ h.ne (hinj hs hj h')
      rw [himage, hcount]
    · rw [ite_eq_right hα, map_zero, sum_faces_eq_zero_of_not_injOn g α hα]

/-- The value of a pullback on `J`. -/
theorem map_val (g : K.SimplexChainMap n) (α : Fin (m + 1) →o Fin (n + 1))
    (J : Finset (Fin (m + 1))) (d : ℤ) :
    (g.map α).val J d = if #(J.image α) = #J then g.val (J.image α) d else 0 :=
  (rfl)

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem map_id (g : K.SimplexChainMap n) : g.map OrderHom.id = g := by
  ext J d
  simp [map_val]

/-- Pulling back along `α` and then along `β` is pulling back along `α ∘ β`. -/
@[simp]
theorem map_map {k : ℕ} (g : K.SimplexChainMap n) (α : Fin (m + 1) →o Fin (n + 1))
    (β : Fin (k + 1) →o Fin (m + 1)) : (g.map α).map β = g.map (α.comp β) := by
  ext J d
  simp only [map_val, OrderHom.comp_coe, ← image_image]
  have h₁ := card_image_le (s := J) (f := β)
  have h₂ := card_image_le (s := J.image β) (f := α)
  by_cases hβ : #(J.image β) = #J
  · by_cases hα : #((J.image β).image α) = #(J.image β)
    · rw [ite_eq_left hβ, ite_eq_left hα, ite_eq_left (hα.trans hβ)]
    · rw [ite_eq_left hβ, ite_eq_right hα, ite_eq_right (by omega)]
  · rw [ite_eq_right hβ, ite_eq_right (by omega)]

end SimplexChainMap

/-- The simplicial set of chain maps from the normalized chains of the standard simplices to the
good truncation `τ_{≥ 0} K`: its `n`-simplices are `K.SimplexChainMap n`, and a monotone map acts
by `CochainComplex.SimplexChainMap.map`. -/
-- Exposed so that the `n`-simplices are definitionally `K.SimplexChainMap n` downstream, where
-- right mapping spaces are identified with this simplicial set simplex by simplex.
@[expose] noncomputable def simplexChainMaps : SSet.{v} where
  obj Δ := K.SimplexChainMap Δ.unop.len
  map f := ↾fun g ↦ g.map f.unop.toOrderHom
  map_id Δ := by
    ext g : 3
    exact g.map_id
  map_comp f g := by
    ext x : 3
    exact (x.map_map _ _).symm

/-- A simplicial operator acts on `K.simplexChainMaps` by `CochainComplex.SimplexChainMap.map`. -/
@[simp]
theorem simplexChainMaps_map_apply {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (g : K.simplexChainMaps.obj Δ) :
    K.simplexChainMaps.map f g = SimplexChainMap.map g f.unop.toOrderHom :=
  (rfl)

end CochainComplex
