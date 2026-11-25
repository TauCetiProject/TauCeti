/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Topology.Connected.Basic

/-!
# The two sides of a normal collar

Let `c : M × ℝ → N` be a `C^n` partial diffeomorphism with source `M × (-ε, ε)` whose zero slice is
a map `f : M → N`, `c (x, 0) = f x`. This is the shape of the smooth normal collar
`c_ν (x, t) = exp_{f x} (t ν x)` of a two-sided compact hypersurface
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalCollar`). Write `U = c (M × (-ε, ε))`
for its image, `t : U → (-ε, ε)` for the **collar coordinate**, the second component of the
inverse of `c`, and

`U₊ = c (M × (0, ε))`, `U₋ = c (M × (-ε, 0))`

for the **two sides** of the collar. This file proves:

* `TauCeti.NormalCollar.target_eq_union`: `U = U₋ ∪ f M ∪ U₊`, and the three pieces are pairwise
  disjoint (`disjoint_sideNeg_sidePos`, `disjoint_range_sidePos`, `disjoint_range_sideNeg`);
* `TauCeti.NormalCollar.isOpen_sidePos`, `isOpen_sideNeg`: the two sides are open;
* `TauCeti.NormalCollar.isPreconnected_sidePos`, `isPreconnected_sideNeg`: they are preconnected
  when `M` is;
* `TauCeti.NormalCollar.contMDiffOn_coordinate`: the collar coordinate is `C^n` on `U`;
* `TauCeti.NormalCollar.mem_sidePos_iff`, `mem_sideNeg_iff`, `mem_range_iff`: a point of `U` lies
  on the positive side, on the negative side or on `f M` according as its collar coordinate is
  positive, negative or zero.

Here `U₊` and `U₋` are written as the images `c '' (univ ×ˢ Ioo 0 ε)` and
`c '' (univ ×ˢ Ioo (-ε) 0)`.
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.NormalCollar

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}
  {c : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (M × ℝ) N n} {ε : ℝ} {f : M → N}

/-- The source of a collar consists of the points with depth in `(-ε, ε)`. -/
private theorem mem_source_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) {p : M × ℝ} :
    p ∈ c.source ↔ p.2 ∈ Ioo (-ε) ε := by
  simp [hc]

/-- A collar is injective on its source. -/
private theorem injOn_source : InjOn c c.source := c.toPartialEquiv.injOn

/-- The zero slice of a collar is the image of `M × {0}`. -/
theorem range_eq_image (hc0 : ∀ x, c (x, 0) = f x) : range f = c '' (univ ×ˢ {0}) := by
  ext y
  simp [← hc0]

/-- The image of a collar is the union of its negative side, the zero slice and its positive
side. -/
theorem target_eq_union (hc : c.source = univ ×ˢ Ioo (-ε) ε) (hε : 0 < ε)
    (hc0 : ∀ x, c (x, 0) = f x) :
    c.target = c '' (univ ×ˢ Ioo (-ε) 0) ∪ range f ∪ c '' (univ ×ˢ Ioo 0 ε) := by
  have himage : c '' c.source = c.target := c.toOpenPartialHomeomorph.image_source_eq_target
  ext y
  rw [← himage]
  constructor
  · rintro ⟨⟨x, t⟩, hp, rfl⟩
    have ht := (mem_source_iff hc).1 hp
    rcases lt_trichotomy t 0 with h | rfl | h
    · exact Or.inl (Or.inl ⟨(x, t), ⟨mem_univ _, ht.1, h⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, (hc0 x).symm⟩)
    · exact Or.inr ⟨(x, t), ⟨mem_univ _, h, ht.2⟩, rfl⟩
  · rintro ((⟨p, ⟨-, hp⟩, rfl⟩ | ⟨x, rfl⟩) | ⟨p, ⟨-, hp⟩, rfl⟩)
    · exact ⟨p, (mem_source_iff hc).2 ⟨hp.1, hp.2.trans hε⟩, rfl⟩
    · exact ⟨(x, 0), (mem_source_iff hc).2 ⟨neg_lt_zero.mpr hε, hε⟩, hc0 x⟩
    · exact ⟨p, (mem_source_iff hc).2 ⟨(neg_lt_zero.mpr hε).trans hp.1, hp.2⟩, rfl⟩

/-- The positive side of a collar lies in its source. -/
private theorem prod_Ioo_pos_subset_source (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    univ ×ˢ Ioo 0 ε ⊆ c.source := fun p hp ↦
  (mem_source_iff hc).2 ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩

/-- The negative side of a collar lies in its source. -/
private theorem prod_Ioo_neg_subset_source (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    univ ×ˢ Ioo (-ε) 0 ⊆ c.source := fun p hp ↦
  (mem_source_iff hc).2 ⟨hp.2.1, by linarith [hp.2.1, hp.2.2]⟩

/-- The positive side `c (M × (0, ε))` of a collar is open. -/
theorem isOpen_sidePos (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    IsOpen (c '' (univ ×ˢ Ioo 0 ε)) :=
  c.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
    (prod_Ioo_pos_subset_source hc)

/-- The negative side `c (M × (-ε, 0))` of a collar is open. -/
theorem isOpen_sideNeg (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    IsOpen (c '' (univ ×ˢ Ioo (-ε) 0)) :=
  c.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
    (prod_Ioo_neg_subset_source hc)

/-- The images under a collar of two subsets of its source with disjoint sets of depths are
disjoint. -/
private theorem disjoint_image_prod (hc : c.source = univ ×ˢ Ioo (-ε) ε) {s t : Set ℝ}
    (hs : s ⊆ Ioo (-ε) ε) (ht : t ⊆ Ioo (-ε) ε) (hst : Disjoint s t) :
    Disjoint (c '' (univ ×ˢ s)) (c '' (univ ×ˢ t)) := by
  rw [disjoint_iff_forall_ne]
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ h
  have hpq := injOn_source ((mem_source_iff hc).2 (hs hp.2)) ((mem_source_iff hc).2 (ht hq.2)) h
  exact disjoint_left.1 hst hp.2 (hpq ▸ hq.2)

/-- The two sides of a collar are disjoint. -/
theorem disjoint_sideNeg_sidePos (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    Disjoint (c '' (univ ×ˢ Ioo (-ε) 0)) (c '' (univ ×ˢ Ioo 0 ε)) :=
  disjoint_image_prod hc (fun t ht ↦ ⟨ht.1, by linarith [ht.1, ht.2]⟩)
    (fun t ht ↦ ⟨by linarith [ht.1, ht.2], ht.2⟩)
    (disjoint_left.2 fun t h₁ h₂ ↦ by linarith [h₁.2, h₂.1])

/-- The zero slice of a collar is disjoint from its positive side. -/
theorem disjoint_range_sidePos (hc : c.source = univ ×ˢ Ioo (-ε) ε) (hε : 0 < ε)
    (hc0 : ∀ x, c (x, 0) = f x) : Disjoint (range f) (c '' (univ ×ˢ Ioo 0 ε)) := by
  rw [range_eq_image hc0]
  exact disjoint_image_prod hc (singleton_subset_iff.2 ⟨neg_lt_zero.mpr hε, hε⟩)
    (fun t ht ↦ ⟨by linarith [ht.1, ht.2], ht.2⟩)
    (disjoint_singleton_left.2 fun h ↦ lt_irrefl _ h.1)

/-- The zero slice of a collar is disjoint from its negative side. -/
theorem disjoint_range_sideNeg (hc : c.source = univ ×ˢ Ioo (-ε) ε) (hε : 0 < ε)
    (hc0 : ∀ x, c (x, 0) = f x) : Disjoint (range f) (c '' (univ ×ˢ Ioo (-ε) 0)) := by
  rw [range_eq_image hc0]
  exact disjoint_image_prod hc (singleton_subset_iff.2 ⟨neg_lt_zero.mpr hε, hε⟩)
    (fun t ht ↦ ⟨ht.1, by linarith [ht.1, ht.2]⟩)
    (disjoint_singleton_left.2 fun h ↦ lt_irrefl _ h.2)

/-- The positive side of a collar of a preconnected manifold is preconnected. -/
theorem isPreconnected_sidePos [PreconnectedSpace M] (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    IsPreconnected (c '' (univ ×ˢ Ioo 0 ε)) :=
  (isPreconnected_univ.prod isPreconnected_Ioo).image _
    (c.contMDiffOn.continuousOn.mono (prod_Ioo_pos_subset_source hc))

/-- The negative side of a collar of a preconnected manifold is preconnected. -/
theorem isPreconnected_sideNeg [PreconnectedSpace M] (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    IsPreconnected (c '' (univ ×ˢ Ioo (-ε) 0)) :=
  (isPreconnected_univ.prod isPreconnected_Ioo).image _
    (c.contMDiffOn.continuousOn.mono (prod_Ioo_neg_subset_source hc))

/-- **The collar coordinate is smooth**: the second component `t` of the inverse of a `C^n`
collar is `C^n` on the image of the collar. -/
theorem contMDiffOn_coordinate :
    ContMDiffOn J 𝓘(ℝ) n (fun y ↦ (c.symm y).2) c.target :=
  contMDiff_snd.comp_contMDiffOn c.symm.contMDiffOn

/-- The collar coordinate of a point `c (x, t)` of the source is `t`. -/
theorem coordinate_apply {p : M × ℝ} (hp : p ∈ c.source) : (c.symm (c p)).2 = p.2 :=
  congrArg Prod.snd (c.toPartialEquiv.left_inv hp)

/-- A point of the image of a collar with collar coordinate `t` is the image of a point of the
source at depth `t`. -/
private theorem exists_eq_of_mem_target {y : N} (hy : y ∈ c.target) :
    c.symm y ∈ c.source ∧ c (c.symm y) = y :=
  ⟨c.toPartialEquiv.map_target hy, c.toPartialEquiv.right_inv hy⟩

/-- A point lies on the positive side of a collar exactly when it lies in the image and its
collar coordinate is positive. -/
theorem mem_sidePos_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) {y : N} :
    y ∈ c '' (univ ×ˢ Ioo 0 ε) ↔ y ∈ c.target ∧ 0 < (c.symm y).2 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hps := prod_Ioo_pos_subset_source hc hp
    exact ⟨c.toPartialEquiv.map_source hps, (coordinate_apply hps).symm ▸ hp.2.1⟩
  · rintro ⟨hy, hpos⟩
    obtain ⟨hs, heq⟩ := exists_eq_of_mem_target hy
    exact ⟨c.symm y, ⟨mem_univ _, hpos, ((mem_source_iff hc).1 hs).2⟩, heq⟩

/-- A point lies on the negative side of a collar exactly when it lies in the image and its
collar coordinate is negative. -/
theorem mem_sideNeg_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) {y : N} :
    y ∈ c '' (univ ×ˢ Ioo (-ε) 0) ↔ y ∈ c.target ∧ (c.symm y).2 < 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hps := prod_Ioo_neg_subset_source hc hp
    exact ⟨c.toPartialEquiv.map_source hps, (coordinate_apply hps).symm ▸ hp.2.2⟩
  · rintro ⟨hy, hneg⟩
    obtain ⟨hs, heq⟩ := exists_eq_of_mem_target hy
    exact ⟨c.symm y, ⟨mem_univ _, ((mem_source_iff hc).1 hs).1, hneg⟩, heq⟩

/-- A point of the image of a collar lies on its zero slice exactly when its collar coordinate
vanishes. -/
theorem mem_range_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) (hε : 0 < ε)
    (hc0 : ∀ x, c (x, 0) = f x) {y : N} (hy : y ∈ c.target) :
    y ∈ range f ↔ (c.symm y).2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [← hc0, coordinate_apply ((mem_source_iff hc).2 ⟨neg_lt_zero.mpr hε, hε⟩)]
  · intro h0
    obtain ⟨-, heq⟩ := exists_eq_of_mem_target hy
    refine ⟨(c.symm y).1, ?_⟩
    calc f (c.symm y).1 = c ((c.symm y).1, 0) := (hc0 _).symm
      _ = c (c.symm y) := by rw [← h0]
      _ = y := heq

end TauCeti.NormalCollar
