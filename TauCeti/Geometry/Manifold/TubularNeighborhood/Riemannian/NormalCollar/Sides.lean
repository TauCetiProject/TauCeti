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

Let `c : M × ℝ → N` be an open partial homeomorphism with source `M × (-ε, ε)` whose zero slice
is a map `f : M → N`, `c (x, 0) = f x`. This is the shape of the smooth normal collar
`c_ν (x, t) = exp_{f x} (t ν x)` of a two-sided compact hypersurface
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalCollar`). Write `U = c (M × (-ε, ε))`
for its image, `t : U → (-ε, ε)` for the **collar coordinate** `TauCeti.NormalCollar.coordinate`,
the second component of the inverse of `c`, and

`U₊ = c (M × (0, ε))`, `U₋ = c (M × (-ε, 0))`

for the **two sides** `TauCeti.NormalCollar.sidePos` and `TauCeti.NormalCollar.sideNeg` of the
collar. This file proves:

* `TauCeti.NormalCollar.target_eq_union`: `U = U₋ ∪ f M ∪ U₊`, and the three pieces are pairwise
  disjoint (`disjoint_sideNeg_sidePos`, `disjoint_range_sidePos`, `disjoint_range_sideNeg`);
* `TauCeti.NormalCollar.isOpen_sidePos`, `isOpen_sideNeg`: the two sides are open;
* `TauCeti.NormalCollar.isPreconnected_sidePos`, `isPreconnected_sideNeg`: they are preconnected
  when `M` is;
* `TauCeti.NormalCollar.coordinate_mem_Ioo`: the collar coordinate takes values in `(-ε, ε)` on
  `U`;
* `TauCeti.NormalCollar.mem_sidePos_iff`, `mem_sideNeg_iff`, `mem_range_iff`: a point of `U` lies
  on the positive side, on the negative side or on `f M` according as its collar coordinate is
  positive, negative or zero;
* `TauCeti.NormalCollar.contMDiffOn_coordinate`: when `c` is a `C^n` partial diffeomorphism, the
  collar coordinate is `C^n` on `U`.
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.NormalCollar

section Topological

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {c : OpenPartialHomeomorph (M × ℝ) N} {ε : ℝ} {f : M → N}

variable (c ε) in
/-- The positive side `c (M × (0, ε))` of a collar `c : M × ℝ → N`. -/
def sidePos : Set N := c '' (univ ×ˢ Ioo 0 ε)

variable (c ε) in
/-- The negative side `c (M × (-ε, 0))` of a collar `c : M × ℝ → N`. -/
def sideNeg : Set N := c '' (univ ×ˢ Ioo (-ε) 0)

variable (c) in
/-- The collar coordinate of a collar `c : M × ℝ → N`: the second component of its inverse. -/
def coordinate (y : N) : ℝ := (c.symm y).2

/-- The positive side of a collar is the image of `M × (0, ε)`. -/
theorem sidePos_def : sidePos c ε = c '' (univ ×ˢ Ioo 0 ε) := by
  rw [sidePos]

/-- The negative side of a collar is the image of `M × (-ε, 0)`. -/
theorem sideNeg_def : sideNeg c ε = c '' (univ ×ˢ Ioo (-ε) 0) := by
  rw [sideNeg]

/-- The collar coordinate is the second component of the inverse of the collar. -/
theorem coordinate_def (y : N) : coordinate c y = (c.symm y).2 := by
  rw [coordinate]

/-- The source of a collar consists of the points with depth in `(-ε, ε)`. -/
private theorem mem_source_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) {p : M × ℝ} :
    p ∈ c.source ↔ p.2 ∈ Ioo (-ε) ε := by
  simp [hc]

/-- The collar coordinate of a point `c (x, t)` of the source is `t`. -/
@[simp]
theorem coordinate_apply {p : M × ℝ} (hp : p ∈ c.source) : coordinate c (c p) = p.2 :=
  congrArg Prod.snd (c.left_inv hp)

/-- The collar coordinate takes values in `(-ε, ε)` on the image of a collar. -/
theorem coordinate_mem_Ioo (hc : c.source = univ ×ˢ Ioo (-ε) ε) {y : N} (hy : y ∈ c.target) :
    coordinate c y ∈ Ioo (-ε) ε :=
  (mem_source_iff hc).1 (c.map_target hy)

/-- The zero slice of a collar is the image of `M × {0}`. -/
theorem range_eq_image (hc0 : ∀ x, c (x, 0) = f x) : range f = c '' (univ ×ˢ {0}) := by
  ext y
  simp [← hc0]

/-- The positive side of a collar lies in its source. -/
private theorem prod_Ioo_pos_subset_source (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    univ ×ˢ Ioo 0 ε ⊆ c.source := fun p hp ↦
  (mem_source_iff hc).2 ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩

/-- The negative side of a collar lies in its source. -/
private theorem prod_Ioo_neg_subset_source (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    univ ×ˢ Ioo (-ε) 0 ⊆ c.source := fun p hp ↦
  (mem_source_iff hc).2 ⟨hp.2.1, by linarith [hp.2.1, hp.2.2]⟩

/-- A point lies on the positive side of a collar exactly when it lies in the image and its
collar coordinate is positive. -/
theorem mem_sidePos_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) {y : N} :
    y ∈ sidePos c ε ↔ y ∈ c.target ∧ 0 < coordinate c y := by
  rw [sidePos, c.image_eq_target_inter_inv_preimage (prod_Ioo_pos_subset_source hc)]
  exact and_congr_right fun hy ↦
    ⟨fun h ↦ h.2.1, fun h ↦ ⟨mem_univ _, h, (coordinate_mem_Ioo hc hy).2⟩⟩

/-- A point lies on the negative side of a collar exactly when it lies in the image and its
collar coordinate is negative. -/
theorem mem_sideNeg_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) {y : N} :
    y ∈ sideNeg c ε ↔ y ∈ c.target ∧ coordinate c y < 0 := by
  rw [sideNeg, c.image_eq_target_inter_inv_preimage (prod_Ioo_neg_subset_source hc)]
  exact and_congr_right fun hy ↦
    ⟨fun h ↦ h.2.2, fun h ↦ ⟨mem_univ _, (coordinate_mem_Ioo hc hy).1, h⟩⟩

/-- A point of the image of a collar lies on its zero slice exactly when its collar coordinate
vanishes. -/
theorem mem_range_iff (hc : c.source = univ ×ˢ Ioo (-ε) ε) (hc0 : ∀ x, c (x, 0) = f x) {y : N}
    (hy : y ∈ c.target) : y ∈ range f ↔ coordinate c y = 0 := by
  have hε : 0 < ε := by linarith [(coordinate_mem_Ioo hc hy).1, (coordinate_mem_Ioo hc hy).2]
  constructor
  · rintro ⟨x, rfl⟩
    rw [← hc0, coordinate_apply ((mem_source_iff hc).2 ⟨neg_lt_zero.mpr hε, hε⟩)]
  · intro h0
    refine ⟨(c.symm y).1, ?_⟩
    calc f (c.symm y).1 = c ((c.symm y).1, coordinate c y) := by rw [h0, hc0]
      _ = y := c.right_inv hy

/-- The image of a collar is the union of its negative side, the zero slice and its positive
side. -/
theorem target_eq_union (hc : c.source = univ ×ˢ Ioo (-ε) ε) (hε : 0 < ε)
    (hc0 : ∀ x, c (x, 0) = f x) : c.target = sideNeg c ε ∪ range f ∪ sidePos c ε := by
  ext y
  constructor
  · intro hy
    rcases lt_trichotomy (coordinate c y) 0 with h | h | h
    · exact Or.inl (Or.inl ((mem_sideNeg_iff hc).2 ⟨hy, h⟩))
    · exact Or.inl (Or.inr ((mem_range_iff hc hc0 hy).2 h))
    · exact Or.inr ((mem_sidePos_iff hc).2 ⟨hy, h⟩)
  · rintro ((h | ⟨x, rfl⟩) | h)
    · exact ((mem_sideNeg_iff hc).1 h).1
    · rw [← hc0]
      exact c.map_source ((mem_source_iff hc).2 ⟨neg_lt_zero.mpr hε, hε⟩)
    · exact ((mem_sidePos_iff hc).1 h).1

/-- The positive side `c (M × (0, ε))` of a collar is open. -/
theorem isOpen_sidePos (hc : c.source = univ ×ˢ Ioo (-ε) ε) : IsOpen (sidePos c ε) :=
  c.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) (prod_Ioo_pos_subset_source hc)

/-- The negative side `c (M × (-ε, 0))` of a collar is open. -/
theorem isOpen_sideNeg (hc : c.source = univ ×ˢ Ioo (-ε) ε) : IsOpen (sideNeg c ε) :=
  c.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) (prod_Ioo_neg_subset_source hc)

/-- The two sides of a collar are disjoint. -/
theorem disjoint_sideNeg_sidePos (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    Disjoint (sideNeg c ε) (sidePos c ε) :=
  Disjoint.image (disjoint_prod.2 (Or.inr (disjoint_left.2 fun _ h₁ h₂ ↦ lt_asymm h₁.2 h₂.1)))
    c.injOn (prod_Ioo_neg_subset_source hc) (prod_Ioo_pos_subset_source hc)

/-- The zero slice of a collar is disjoint from its positive side. -/
theorem disjoint_range_sidePos (hc : c.source = univ ×ˢ Ioo (-ε) ε)
    (hc0 : ∀ x, c (x, 0) = f x) : Disjoint (range f) (sidePos c ε) :=
  disjoint_left.2 fun _ hf hpos ↦ by
    obtain ⟨hy, h⟩ := (mem_sidePos_iff hc).1 hpos
    exact h.ne' ((mem_range_iff hc hc0 hy).1 hf)

/-- The zero slice of a collar is disjoint from its negative side. -/
theorem disjoint_range_sideNeg (hc : c.source = univ ×ˢ Ioo (-ε) ε)
    (hc0 : ∀ x, c (x, 0) = f x) : Disjoint (range f) (sideNeg c ε) :=
  disjoint_left.2 fun _ hf hneg ↦ by
    obtain ⟨hy, h⟩ := (mem_sideNeg_iff hc).1 hneg
    exact h.ne ((mem_range_iff hc hc0 hy).1 hf)

/-- The positive side of a collar of a preconnected space is preconnected. -/
theorem isPreconnected_sidePos [PreconnectedSpace M] (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    IsPreconnected (sidePos c ε) :=
  (isPreconnected_univ.prod isPreconnected_Ioo).image _
    (c.continuousOn.mono (prod_Ioo_pos_subset_source hc))

/-- The negative side of a collar of a preconnected space is preconnected. -/
theorem isPreconnected_sideNeg [PreconnectedSpace M] (hc : c.source = univ ×ˢ Ioo (-ε) ε) :
    IsPreconnected (sideNeg c ε) :=
  (isPreconnected_univ.prod isPreconnected_Ioo).image _
    (c.continuousOn.mono (prod_Ioo_neg_subset_source hc))

end Topological

section Smooth

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

/-- **The collar coordinate is smooth**: the collar coordinate of a `C^n` partial
diffeomorphism `c : M × ℝ → N` is `C^n` on the image of `c`. -/
theorem contMDiffOn_coordinate {c : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (M × ℝ) N n} :
    ContMDiffOn J 𝓘(ℝ) n (coordinate c.toOpenPartialHomeomorph) c.target :=
  contMDiff_snd.comp_contMDiffOn c.symm.contMDiffOn

end Smooth

end TauCeti.NormalCollar
