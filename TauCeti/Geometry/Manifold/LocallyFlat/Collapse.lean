/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Analysis.InnerProductSpace.Sphere.Latitude
public import TauCeti.Geometry.Manifold.LocallyFlat.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The sides of a bicollared sphere and Brown's collapsing map

Let `b : N × ℝ → M` be a bicollar of `f : N → M` (`TauCeti.IsBicollar`), and suppose the
complement of the image of `f` is the union of two disjoint open sets `A` and `B`, both nonempty,
in a preconnected space `M`. If `N` is preconnected, the two sides `b (N × (0, ∞))` and
`b (N × (-∞, 0))` of the bicollar cannot lie in the same one of `A` and `B`
(`TauCeti.IsBicollar.mapsTo_or_mapsTo`): otherwise the image of `b` together with that set and the
other set would disconnect `M`.

For an embedded sphere `f : Sᵐ⁻¹ → Sᵐ`, `m ≥ 2`, the Jordan–Brouwer separation theorem
(`TauCeti.natCard_zerothHomotopy_sphere_compl_range_eq_two`) says the complement of the image
has exactly two path components. If `f` is bicollared, the two sides of the bicollar are
connected and lie one in each of them (`TauCeti.IsBicollar.exists_pathComponents_sphere`, in
`TauCeti.Geometry.Manifold.LocallyFlat.Sphere`). For `m = 1` the sides are not connected, and
the two components need not be told apart by the sides: both halves of one side may lie in the
same component.

Given such a decomposition, M. Brown's proof of the generalized Schoenflies theorem collapses the
two outer regions to points. Follow the bicollar by a map `g : N × [-1, 1] → Y` sending the two
ends `N × {1}` and `N × {-1}` to points `ypos` and `yneg`. The *collapsing map*
`TauCeti.bicollarCollapse b A g ypos yneg : M → Y` is `g (x, t)` at `b (x, t)` for
`t ∈ [-1, 1]`, is `ypos` on the rest of `A`, and is `yneg` on the rest of `B`. It is continuous
when `N` is compact and `M` is Hausdorff (`TauCeti.IsBicollar.continuous_bicollarCollapse`). When
`g` collapses only its two ends and is injective elsewhere, the preimage of `ypos` is the outer
piece `A \ b (N × (-∞, 1))`, the preimage of `yneg` is `B \ b (N × (-1, ∞))`, and every other
point has at most one preimage.

For spheres, `g` is the latitude map (`TauCeti.sphereLatitude`) onto `Sᵐ` with poles `±p`. This
gives a continuous surjection `Sᵐ → Sᵐ` whose only point preimages with more than one point are
the two outer pieces (`TauCeti.IsBicollar.exists_collapse_sphere`). Brown shows that the point
preimages of such a map are cellular, and collapsing a cellular set does not change the
homeomorphism type; this identifies the closure of each complementary component with a disc.

## Main definitions

* `TauCeti.bicollarCollapse`: the map collapsing the two outer regions of a bicollared
  separating map to points.

## Main results

* `TauCeti.IsBicollar.continuous_bicollarCollapse`: the collapsing map is continuous.
* `TauCeti.IsBicollar.preimage_bicollarCollapse_left` and
  `TauCeti.IsBicollar.preimage_bicollarCollapse_right`: the two collapsed point preimages.
* `TauCeti.IsBicollar.subsingleton_preimage_bicollarCollapse`: every other point preimage has at
  most one point.
* `TauCeti.IsBicollar.exists_collapse_sphere`: Brown's collapsing map of a bicollared
  codimension-one sphere onto the sphere.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
-/

public section

noncomputable section

open Function Metric Module Set Topology

namespace TauCeti

section Collapse

variable {N M Y : Type*} {b : N × ℝ → M} {A B : Set M}

open Classical in
/-- **Brown's collapsing map.** Given a map `b : N × ℝ → M`, a set `A ⊆ M`, a map
`g : N × [-1, 1] → Y` and two points `ypos`, `yneg` of `Y`, the map `M → Y` which is
`g (x, t)` at `b (x, t)` with `t` clamped to `[-1, 1]`, which is `ypos` at the other points of `A`,
and `yneg` at the remaining points. When `b` is a bicollar whose positive side lies in `A` and
negative side in the complementary region `B`, and `g` sends the two ends of `N × [-1, 1]` to `ypos`
and `yneg`, it collapses the outer pieces of `A` and `B` to `ypos` and `yneg`
(`TauCeti.IsBicollar.preimage_bicollarCollapse_left`). -/
def bicollarCollapse (b : N × ℝ → M) (A : Set M) (g : N × Icc (-1 : ℝ) 1 → Y) (ypos yneg : Y) :
    M → Y :=
  fun m ↦ if hm : m ∈ range b then
      g ((Classical.choose hm).1, projIcc (-1) 1 (by norm_num) (Classical.choose hm).2)
    else if m ∈ A then ypos else yneg

section Values

variable (g : N × Icc (-1 : ℝ) 1 → Y) (ypos yneg : Y)

/-- Off the image of `b`, the collapsing map is `ypos` on `A`. -/
@[simp]
theorem bicollarCollapse_of_notMem_range_of_mem {m : M} (hm : m ∉ range b) (hmA : m ∈ A) :
    bicollarCollapse b A g ypos yneg m = ypos := by
  classical
  rw [bicollarCollapse, dite_eq_right_of_eq_false (eq_false hm),
    ite_eq_left_of_eq_true _ _ (eq_true hmA)]

/-- Off the image of `b`, the collapsing map is `yneg` outside `A`. -/
@[simp]
theorem bicollarCollapse_of_notMem_range_of_notMem {m : M} (hm : m ∉ range b) (hmA : m ∉ A) :
    bicollarCollapse b A g ypos yneg m = yneg := by
  classical
  rw [bicollarCollapse, dite_eq_right_of_eq_false (eq_false hm),
    ite_eq_right_of_eq_false _ _ (eq_false hmA)]

/-- On the image of an injective `b`, such as a bicollar, the collapsing map is `g` with the
depth clamped to `[-1, 1]`. -/
@[simp]
theorem bicollarCollapse_apply (hb : Injective b) (x : N) (t : ℝ) :
    bicollarCollapse b A g ypos yneg (b (x, t)) = g (x, projIcc (-1) 1 (by norm_num) t) := by
  have key : ∀ hm : b (x, t) ∈ range b, Classical.choose hm = (x, t) :=
    fun hm ↦ hb (Classical.choose_spec hm)
  rw [bicollarCollapse, dite_eq_left_of_eq_true (eq_true (mem_range_self _)), key]

end Values

variable [TopologicalSpace N] [TopologicalSpace M] {f : N → M} (g : N × Icc (-1 : ℝ) 1 → Y)
  (ypos yneg : Y)

namespace IsBicollar

omit [TopologicalSpace N] [TopologicalSpace M] in
/-- The image of `f` is disjoint from a complementary region. -/
private theorem disjoint_range_left (hcompl : (range f)ᶜ = A ∪ B) : Disjoint (range f) A :=
  disjoint_left.2 fun m hmf hmA ↦ (by rw [hcompl]; exact Or.inl hmA : m ∈ (range f)ᶜ) hmf

/-- A point of `A` on the bicollar has positive depth. -/
private theorem pos_of_apply_mem_left (h : IsBicollar f b) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hneg : MapsTo b (univ ×ˢ Iio 0) B) {x : N} {t : ℝ}
    (hxt : b (x, t) ∈ A) : 0 < t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exact (disjoint_left.1 hAB hxt (hneg ⟨mem_univ x, mem_Iio.2 ht⟩)).elim
  · rw [h.apply_zero] at hxt
    exact (disjoint_left.1 (disjoint_range_left hcompl) (mem_range_self x) hxt).elim
  · exact ht

/-- A point of `B` on the bicollar has negative depth. -/
private theorem neg_of_apply_mem_right (h : IsBicollar f b) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hpos : MapsTo b (univ ×ˢ Ioi 0) A) {x : N} {t : ℝ}
    (hxt : b (x, t) ∈ B) : t < 0 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exact ht
  · rw [h.apply_zero] at hxt
    exact (disjoint_left.1 (disjoint_range_left (hcompl.trans (union_comm _ _)))
      (mem_range_self x) hxt).elim
  · exact (disjoint_left.1 hAB (hpos ⟨mem_univ x, mem_Ioi.2 ht⟩) hxt).elim

/-- The collapsing map is `ypos` on the outer piece `A \ b (N × (-∞, 1))`. -/
theorem bicollarCollapse_of_mem_left (h : IsBicollar f b)
    (hgpos : ∀ x, g (x, ⟨1, by norm_num⟩) = ypos) {m : M}
    (hm : m ∈ A \ b '' (univ ×ˢ Iio 1)) : bicollarCollapse b A g ypos yneg m = ypos := by
  by_cases hmb : m ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hmb
    have ht : 1 ≤ t := not_lt.1 fun ht ↦ hm.2 ⟨(x, t), ⟨mem_univ x, ht⟩, rfl⟩
    rw [bicollarCollapse_apply _ _ _ h.isOpenEmbedding.injective, projIcc_of_right_le _ ht, hgpos]
  · exact bicollarCollapse_of_notMem_range_of_mem g ypos yneg hmb hm.1

/-- The collapsing map is `yneg` on the outer piece `B \ b (N × (-1, ∞))`. -/
theorem bicollarCollapse_of_mem_right (h : IsBicollar f b) (hAB : Disjoint A B)
    (hgneg : ∀ x, g (x, ⟨-1, by norm_num⟩) = yneg) {m : M}
    (hm : m ∈ B \ b '' (univ ×ˢ Ioi (-1))) : bicollarCollapse b A g ypos yneg m = yneg := by
  by_cases hmb : m ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hmb
    have ht : t ≤ -1 := not_lt.1 fun ht ↦ hm.2 ⟨(x, t), ⟨mem_univ x, ht⟩, rfl⟩
    rw [bicollarCollapse_apply _ _ _ h.isOpenEmbedding.injective, projIcc_of_le_left _ ht, hgneg]
  · exact bicollarCollapse_of_notMem_range_of_notMem g ypos yneg hmb
      fun hmA ↦ disjoint_left.1 hAB hmA hm.1

/-- **The collapsing map is continuous**, when `N` is compact, `M` is Hausdorff and `g` is
continuous: on the open image of the bicollar it is `g` read through the bicollar, and near a
point of `A` or `B` off the bicollar it is constant. -/
theorem continuous_bicollarCollapse [TopologicalSpace Y] [CompactSpace N] [T2Space M]
    (h : IsBicollar f b)
    (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hcompl : (range f)ᶜ = A ∪ B)
    (hpos : MapsTo b (univ ×ˢ Ioi 0) A) (hneg : MapsTo b (univ ×ˢ Iio 0) B)
    (hg : Continuous g) (hgpos : ∀ x, g (x, ⟨1, by norm_num⟩) = ypos)
    (hgneg : ∀ x, g (x, ⟨-1, by norm_num⟩) = yneg) :
    Continuous (bicollarCollapse b A g ypos yneg) := by
  refine continuous_iff_continuousAt.2 fun m ↦ ?_
  by_cases hmb : m ∈ range b
  · obtain ⟨z, rfl⟩ := hmb
    rw [← h.isOpenEmbedding.continuousAt_iff]
    have hcomp : bicollarCollapse b A g ypos yneg ∘ b =
        fun z : N × ℝ ↦ g (z.1, projIcc (-1) 1 (by norm_num) z.2) :=
      funext fun z ↦ bicollarCollapse_apply g ypos yneg h.isOpenEmbedding.injective z.1 z.2
    rw [hcomp]
    exact (hg.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))).continuousAt
  -- Off the bicollar, `m` lies in `A` or `B` but outside the compact set `b (N × [-1, 1])`.
  have hK : IsClosed (b '' (univ ×ˢ Icc (-1) 1)) :=
    (isCompact_univ.prod isCompact_Icc).image h.isOpenEmbedding.continuous |>.isClosed
  have hmK : m ∉ b '' (univ ×ˢ Icc (-1) 1) := fun hm ↦ hmb (image_subset_range _ _ hm)
  have hmAB : m ∈ A ∪ B := by
    rw [← hcompl]
    exact fun hmf ↦ hmb (h.range_subset_range hmf)
  rcases hmAB with hmA | hmB
  · refine (continuousAt_const : ContinuousAt (fun _ : M ↦ ypos) m).congr
      (Filter.mem_of_superset ((hA.inter hK.isOpen_compl).mem_nhds ⟨hmA, hmK⟩) fun m' hm' ↦ ?_)
    refine (h.bicollarCollapse_of_mem_left g ypos yneg hgpos ⟨hm'.1, ?_⟩).symm
    rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    have := h.pos_of_apply_mem_left hAB hcompl hneg hm'.1
    exact hm'.2 ⟨(x, t), ⟨mem_univ x, by linarith, (mem_Iio.1 ht).le⟩, rfl⟩
  · refine (continuousAt_const : ContinuousAt (fun _ : M ↦ yneg) m).congr
      (Filter.mem_of_superset ((hB.inter hK.isOpen_compl).mem_nhds ⟨hmB, hmK⟩) fun m' hm' ↦ ?_)
    refine (h.bicollarCollapse_of_mem_right g ypos yneg hAB hgneg ⟨hm'.1, ?_⟩).symm
    rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    have := h.neg_of_apply_mem_right hAB hcompl hpos hm'.1
    exact hm'.2 ⟨(x, t), ⟨mem_univ x, (mem_Ioi.1 ht).le, by linarith⟩, rfl⟩

/-- Every point of `M` lies in one of the two outer pieces or on the open part
`b (N × (-1, 1))` of the bicollar. -/
theorem diff_union_diff_union_image_Ioo_eq_univ (h : IsBicollar f b) (hcompl : (range f)ᶜ = A ∪ B)
    (hpos : MapsTo b (univ ×ˢ Ioi 0) A) (hneg : MapsTo b (univ ×ˢ Iio 0) B) :
    (A \ b '' (univ ×ˢ Iio 1)) ∪ (B \ b '' (univ ×ˢ Ioi (-1))) ∪ b '' (univ ×ˢ Ioo (-1) 1) =
      univ := by
  refine eq_univ_of_forall fun m ↦ ?_
  by_cases hmb : m ∈ range b
  · obtain ⟨⟨x, t⟩, rfl⟩ := hmb
    -- A point `b (x, t')` of a slab `N × s` has `t' = t`.
    have hslab : ∀ {s : Set ℝ}, b (x, t) ∈ b '' (univ ×ˢ s) → t ∈ s := by
      rintro s ⟨⟨x', t'⟩, ⟨-, ht'⟩, he⟩
      obtain ⟨-, rfl⟩ := Prod.ext_iff.1 (h.isOpenEmbedding.injective he)
      exact ht'
    rcases lt_or_ge t 1 with ht1 | ht1
    · rcases lt_or_ge (-1) t with ht2 | ht2
      · exact Or.inr ⟨(x, t), ⟨mem_univ x, ht2, ht1⟩, rfl⟩
      · exact Or.inl (Or.inr ⟨hneg ⟨mem_univ x, mem_Iio.2 (by linarith)⟩,
          fun hm ↦ (not_lt.2 ht2) (hslab hm)⟩)
    · exact Or.inl (Or.inl ⟨hpos ⟨mem_univ x, mem_Ioi.2 (by linarith)⟩,
        fun hm ↦ (not_lt.2 ht1) (hslab hm)⟩)
  · have hmAB : m ∈ A ∪ B := by
      rw [← hcompl]
      exact fun hmf ↦ hmb (h.range_subset_range hmf)
    rcases hmAB with hmA | hmB
    · exact Or.inl (Or.inl ⟨hmA, fun hm ↦ hmb (image_subset_range _ _ hm)⟩)
    · exact Or.inl (Or.inr ⟨hmB, fun hm ↦ hmb (image_subset_range _ _ hm)⟩)

/-- **The positive outer piece is a point preimage.** If `g` takes the value `ypos` exactly on the
end `N × {1}` and the value `yneg` on the end `N × {-1}`, with `ypos ≠ yneg`, the preimage of
`ypos` under the collapsing map is `A \ b (N × (-∞, 1))`. -/
theorem preimage_bicollarCollapse_left (h : IsBicollar f b) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hpos : MapsTo b (univ ×ˢ Ioi 0) A)
    (hneg : MapsTo b (univ ×ˢ Iio 0) B)
    (hgpos : ∀ z, g z = ypos ↔ (z.2 : ℝ) = 1) (hgneg : ∀ x, g (x, ⟨-1, by norm_num⟩) = yneg)
    (hy : ypos ≠ yneg) :
    bicollarCollapse b A g ypos yneg ⁻¹' {ypos} = A \ b '' (univ ×ˢ Iio 1) := by
  refine Subset.antisymm (fun m hm ↦ ?_) fun m hm ↦
    h.bicollarCollapse_of_mem_left g ypos yneg (fun x ↦ (hgpos _).2 rfl) hm
  have hcov := h.diff_union_diff_union_image_Ioo_eq_univ hcompl hpos hneg
  rcases (hcov ▸ mem_univ m : m ∈ _) with (hm' | hm') | ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
  · exact hm'
  · exact (hy ((h.bicollarCollapse_of_mem_right g ypos yneg hAB hgneg hm').symm.trans
      hm).symm).elim
  · have hgt := (hgpos _).1
      ((bicollarCollapse_apply g ypos yneg h.isOpenEmbedding.injective x t).symm.trans hm)
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at hgt
    exact (ht.2.ne hgt).elim

/-- **The negative outer piece is a point preimage.** If `g` takes the value `ypos` on the end
`N × {1}` and the value `yneg` exactly on the end `N × {-1}`, with `ypos ≠ yneg`, the preimage of
`yneg` under the collapsing map is `B \ b (N × (-1, ∞))`. -/
theorem preimage_bicollarCollapse_right (h : IsBicollar f b) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hpos : MapsTo b (univ ×ˢ Ioi 0) A)
    (hneg : MapsTo b (univ ×ˢ Iio 0) B)
    (hgpos : ∀ x, g (x, ⟨1, by norm_num⟩) = ypos) (hgneg : ∀ z, g z = yneg ↔ (z.2 : ℝ) = -1)
    (hy : ypos ≠ yneg) :
    bicollarCollapse b A g ypos yneg ⁻¹' {yneg} = B \ b '' (univ ×ˢ Ioi (-1)) := by
  refine Subset.antisymm (fun m hm ↦ ?_) fun m hm ↦
    h.bicollarCollapse_of_mem_right g ypos yneg hAB (fun x ↦ (hgneg _).2 rfl) hm
  have hcov := h.diff_union_diff_union_image_Ioo_eq_univ hcompl hpos hneg
  rcases (hcov ▸ mem_univ m : m ∈ _) with (hm' | hm') | ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
  · exact (hy ((h.bicollarCollapse_of_mem_left g ypos yneg hgpos hm').symm.trans hm)).elim
  · exact hm'
  · have hgt := (hgneg _).1
      ((bicollarCollapse_apply g ypos yneg h.isOpenEmbedding.injective x t).symm.trans hm)
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at hgt
    exact (ht.1.ne' hgt).elim

/-- On the open part `b (N × (-1, 1))` of the bicollar the collapsing map is injective, provided
`g` is injective on `N × (-1, 1)`. -/
theorem injOn_bicollarCollapse (h : IsBicollar f b)
    (hg : InjOn g {z | (z.2 : ℝ) ∈ Ioo (-1 : ℝ) 1}) :
    InjOn (bicollarCollapse b A g ypos yneg) (b '' (univ ×ˢ Ioo (-1) 1)) := by
  rintro _ ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩ _ ⟨⟨x', t'⟩, ⟨-, ht'⟩, rfl⟩ he
  rw [bicollarCollapse_apply _ _ _ h.isOpenEmbedding.injective,
    bicollarCollapse_apply _ _ _ h.isOpenEmbedding.injective,
    projIcc_of_mem _ (Ioo_subset_Icc_self ht), projIcc_of_mem _ (Ioo_subset_Icc_self ht')] at he
  have := hg ht ht' he
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
  rw [this.1, this.2]

/-- The collapsing map is onto when `g` is. -/
theorem surjective_bicollarCollapse (h : IsBicollar f b) (hg : Surjective g) :
    Surjective (bicollarCollapse b A g ypos yneg) := by
  intro y
  obtain ⟨⟨x, t⟩, rfl⟩ := hg y
  exact ⟨b (x, t), by rw [bicollarCollapse_apply _ _ _ h.isOpenEmbedding.injective, projIcc_val]⟩

/-- **Every other point preimage of the collapsing map has at most one point.** If `g` takes the
value `ypos` on the end `N × {1}`, the value `yneg` on the end `N × {-1}`, and is injective on
`N × (-1, 1)`, then every point other than `ypos` and `yneg` has at most one preimage, for any
set `A`. -/
theorem subsingleton_preimage_bicollarCollapse (h : IsBicollar f b)
    (hgpos : ∀ x, g (x, ⟨1, by norm_num⟩) = ypos) (hgneg : ∀ x, g (x, ⟨-1, by norm_num⟩) = yneg)
    (hg : InjOn g {z | (z.2 : ℝ) ∈ Ioo (-1 : ℝ) 1}) {y : Y} (hypos : y ≠ ypos) (hyneg : y ≠ yneg) :
    (bicollarCollapse b A g ypos yneg ⁻¹' {y}).Subsingleton := by
  -- Off the open part of the bicollar the collapsing map only takes the values `ypos` and `yneg`.
  have hS : ∀ m, bicollarCollapse b A g ypos yneg m = y → m ∈ b '' (univ ×ˢ Ioo (-1) 1) := by
    intro m hm
    by_cases hmb : m ∈ range b
    · obtain ⟨⟨x, t⟩, rfl⟩ := hmb
      rw [bicollarCollapse_apply _ _ _ h.isOpenEmbedding.injective] at hm
      refine ⟨(x, t), ⟨mem_univ x, ?_, ?_⟩, rfl⟩
      · refine lt_of_not_ge fun ht ↦ hyneg ?_
        rw [← hm, projIcc_of_le_left _ ht, hgneg]
      · refine lt_of_not_ge fun ht ↦ hypos ?_
        rw [← hm, projIcc_of_right_le _ ht, hgpos]
    · by_cases hmA : m ∈ A
      · exact (hypos (hm.symm.trans (bicollarCollapse_of_notMem_range_of_mem g ypos yneg hmb
          hmA))).elim
      · exact (hyneg (hm.symm.trans (bicollarCollapse_of_notMem_range_of_notMem g ypos yneg hmb
          hmA))).elim
  intro m hm m' hm'
  exact h.injOn_bicollarCollapse g ypos yneg hg (hS m hm) (hS m' hm') (hm.trans hm'.symm)

end IsBicollar

end Collapse

section CollapseSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : sphere (0 : E) 1 → sphere (0 : F) 1} {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}
  {A B : Set (sphere (0 : F) 1)}

/-- **Brown's collapsing map of a bicollared sphere.** Let `b` be a bicollar of an embedding `f`
of the unit sphere of `E`, `dim E ≥ 1`, into the unit sphere of `F`, `dim F = dim E + 1`, and let
the complement of the image of `f` be the union of disjoint open sets `A` and `B` containing the
positive and the negative side of the bicollar. Then there are a point `p` of the unit sphere of
`F` and a continuous surjection `c` of that sphere onto itself, such that the preimage of `p` is
the outer piece `A \ b (Sᵐ⁻¹ × (-∞, 1))`, the preimage of `-p` is the outer piece
`B \ b (Sᵐ⁻¹ × (-1, ∞))`, and every other point has exactly one preimage. -/
theorem IsBicollar.exists_collapse_sphere (h : IsBicollar f b) (hE : 0 < finrank ℝ E)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B)
    (hcompl : (range f)ᶜ = A ∪ B) (hpos : MapsTo b (univ ×ˢ Ioi 0) A)
    (hneg : MapsTo b (univ ×ˢ Iio 0) B) :
    ∃ (c : C(sphere (0 : F) 1, sphere (0 : F) 1)) (p : sphere (0 : F) 1), Surjective c ∧
      c ⁻¹' {p} = A \ b '' (univ ×ˢ Iio 1) ∧ c ⁻¹' {-p} = B \ b '' (univ ×ˢ Ioi (-1)) ∧
      ∀ y, y ≠ p → y ≠ -p → (c ⁻¹' {y}).Subsingleton := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- A pole `p` and the identification of the sphere of `E` with the equator `(ℝ ∙ p)ᗮ`.
  obtain ⟨p, hp⟩ := (NormedSpace.sphere_nonempty (x := (0 : F)) (r := 1)).2 zero_le_one
  let P : sphere (0 : F) 1 := ⟨p, hp⟩
  have hp0 : p ≠ 0 := ne_zero_of_mem_unit_sphere P
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  have hfin : finrank ℝ E = finrank ℝ (ℝ ∙ p)ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton hp0).symm
  have : Nontrivial (ℝ ∙ p)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  let e := sphereHomeomorphOfFinrankEq hfin
  let g : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 → sphere (0 : F) 1 :=
    fun z ↦ sphereLatitude P (e z.1, z.2)
  have hg : Continuous g := (sphereLatitude P).continuous.comp
    ((e.continuous.comp continuous_fst).prodMk continuous_snd)
  have hgpos : ∀ z, g z = P ↔ (z.2 : ℝ) = 1 := fun z ↦ sphereLatitude_apply_eq_iff_eq_one P
  have hgneg : ∀ z, g z = -P ↔ (z.2 : ℝ) = -1 := fun z ↦ sphereLatitude_apply_eq_neg_iff P
  have hg1 : ∀ x, g (x, ⟨1, by norm_num⟩) = P := fun x ↦ (hgpos _).2 rfl
  have hgm1 : ∀ x, g (x, ⟨-1, by norm_num⟩) = -P := fun x ↦ (hgneg _).2 rfl
  have hginj : InjOn g {z | (z.2 : ℝ) ∈ Ioo (-1 : ℝ) 1} := by
    intro z hz z' hz' he
    have := injOn_sphereLatitude P (x₁ := (e z.1, z.2)) hz (x₂ := (e z'.1, z'.2)) hz' he
    simp only [Prod.mk.injEq] at this
    exact Prod.ext (e.injective this.1) this.2
  have hgs : Surjective g := by
    intro y
    obtain ⟨⟨x, t⟩, hxt⟩ := sphereLatitude_surjective P y
    exact ⟨(e.symm x, t), by simp [g, hxt]⟩
  have hy : P ≠ -P := by
    intro hP
    have : p = -p := congrArg (fun q : sphere (0 : F) 1 ↦ (q : F)) hP
    have h2 : (2 : ℝ) • p = 0 := by
      rw [two_smul]
      nth_rw 1 [this]
      exact neg_add_cancel p
    exact hp0 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)
  refine ⟨⟨bicollarCollapse b A g P (-P), h.continuous_bicollarCollapse g P (-P) hA hB hAB
    hcompl hpos hneg hg hg1 hgm1⟩, P,
    h.surjective_bicollarCollapse g P (-P) hgs,
    h.preimage_bicollarCollapse_left g P (-P) hAB hcompl hpos hneg hgpos hgm1 hy,
    h.preimage_bicollarCollapse_right g P (-P) hAB hcompl hpos hneg hg1 hgneg hy,
    fun y hypos hyneg ↦ h.subsingleton_preimage_bicollarCollapse g P (-P) hg1 hgm1 hginj hypos
      hyneg⟩

end CollapseSphere

end TauCeti
