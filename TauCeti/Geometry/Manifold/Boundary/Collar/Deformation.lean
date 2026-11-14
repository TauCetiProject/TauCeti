/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import Mathlib.Topology.Homotopy.Basic

/-!
# The collar of a given depth and its deformation onto the boundary

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar`). For `t : ℝ`, the part
`TauCeti.collarPart c t = c(N × [0, t))` of depth less than `t` is open, contains the boundary
`f(N)` when `0 < t`, and increases with `t`. Every point outside `f(N)` lies outside the collar of
some positive depth.

The collar coordinates `TauCeti.IsCollar.collarCoord` of a point `x` of `c(N × [0, t))` are the
unique `p` with `c p = x`. Scaling the depth coordinate from `1` down to `0` deforms
`c(N × [0, t))` onto `f(N)` relative to `f(N)` (`TauCeti.IsCollar.collarDeformation`). This is the
deformation used by Hatcher to show that the collar has no homology relative to the boundary.

## Main definitions

* `TauCeti.collarPart`: the part `c(N × [0, t))` of a collar of depth less than `t`.
* `TauCeti.IsCollar.collarCoord`: the collar coordinates of a point of the collar.
* `TauCeti.IsCollar.collarRetraction`: the retraction of the collar onto the boundary.
* `TauCeti.IsCollar.collarDeformation`: the deformation of the collar onto the boundary, relative
  to the boundary.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, proof of
  Theorem 3.43.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {f : N → M}
  {c : N × Ico (0 : ℝ) 1 → M}

/-- The part `c(N × [0, t))` of the collar `c` of depth less than `t`. -/
def collarPart (c : N × Ico (0 : ℝ) 1 → M) (t : ℝ) : Set M :=
  c '' {p | (p.2 : ℝ) < t}

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- A point lies in the collar of depth less than `t` exactly when it is `c p` for collar
coordinates `p` of depth less than `t`. -/
lemma mem_collarPart_iff {x : M} {t : ℝ} :
    x ∈ collarPart c t ↔ ∃ p : N × Ico (0 : ℝ) 1, (p.2 : ℝ) < t ∧ c p = x :=
  Iff.rfl

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- For an injective collar `c` (such as one with `TauCeti.IsCollar f c`), the point `c p` lies in
the collar of depth less than `t` exactly when `p` has depth less than `t`. -/
@[simp]
lemma apply_mem_collarPart_iff (hc : Function.Injective c) {p : N × Ico (0 : ℝ) 1} {t : ℝ} :
    c p ∈ collarPart c t ↔ (p.2 : ℝ) < t :=
  ⟨fun ⟨_, hq, hqp⟩ ↦ hc hqp ▸ hq, fun h ↦ ⟨p, h, rfl⟩⟩

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- The collar of depth less than `t` increases with `t`. -/
lemma collarPart_mono {s t : ℝ} (h : s ≤ t) : collarPart c s ⊆ collarPart c t :=
  image_mono fun _ hp ↦ lt_of_lt_of_le hp h

namespace IsCollar

variable (hc : IsCollar f c)
include hc

/-- The collar of depth less than `t` is open. -/
lemma isOpen_collarPart (t : ℝ) : IsOpen (collarPart c t) :=
  hc.isOpenEmbedding.isOpenMap _ (isOpen_lt (by fun_prop) continuous_const)

/-- The collar of positive depth contains the boundary. -/
lemma range_subset_collarPart {t : ℝ} (ht : 0 < t) : range f ⊆ collarPart c t := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(y, ⟨0, by norm_num⟩), ht, hc.apply_zero y⟩

/-- Every point outside the boundary lies outside the collar of some positive depth. -/
lemma exists_notMem_collarPart {x : M} (hx : x ∉ range f) : ∃ t, 0 < t ∧ x ∉ collarPart c t := by
  by_cases hxc : x ∈ range c
  · obtain ⟨q, rfl⟩ := hxc
    -- The depth of `x = c q` is positive, since the zero slice of the collar is the boundary.
    have hq : 0 < (q.2 : ℝ) := by
      refine lt_of_le_of_ne q.2.2.1 fun h ↦ hx ?_
      have h₀ : q = (q.1, ⟨0, by norm_num⟩) := Prod.ext rfl (Subtype.ext h.symm)
      rw [h₀, hc.apply_zero]
      exact mem_range_self _
    exact ⟨q.2, hq, (lt_irrefl (q.2 : ℝ)) ∘
      (apply_mem_collarPart_iff hc.isOpenEmbedding.injective).1⟩
  · exact ⟨1, one_pos, fun ⟨p, _, hp⟩ ↦ hxc ⟨p, hp⟩⟩

/-- The collar coordinates of a point of the collar of depth less than `t`. -/
def collarCoord (t : ℝ) : C(collarPart c t, N × Ico (0 : ℝ) 1) :=
  ⟨fun x ↦ hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm
      ⟨x, image_subset_range _ _ x.2⟩,
    hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)⟩

/-- The collar sends the collar coordinates of a point back to the point. -/
lemma apply_collarCoord {t : ℝ} (x : collarPart c t) : c (hc.collarCoord t x) = x :=
  congrArg Subtype.val (hc.isOpenEmbedding.isEmbedding.toHomeomorph.apply_symm_apply
    ⟨x, image_subset_range _ _ x.2⟩)

/-- The collar coordinates of `c p` are `p`. -/
lemma collarCoord_apply {t : ℝ} (x : collarPart c t) (p : N × Ico (0 : ℝ) 1) (hp : c p = x) :
    hc.collarCoord t x = p :=
  hc.isOpenEmbedding.injective ((hc.apply_collarCoord x).trans hp.symm)

/-- A point of the collar of depth less than `t` has depth less than `t`. -/
lemma collarCoord_lt {t : ℝ} (x : collarPart c t) : ((hc.collarCoord t x).2 : ℝ) < t := by
  obtain ⟨p, hp, hpx⟩ := x.2
  rw [hc.collarCoord_apply x p hpx]
  exact hp

/-- The retraction of the collar onto the boundary, sending `c (y, s)` to `f y`. -/
def collarRetraction (t : ℝ) : C(collarPart c t, range f) :=
  ⟨fun x ↦ ⟨f (hc.collarCoord t x).1, mem_range_self _⟩,
    (hc.continuous.comp (map_continuous (hc.collarCoord t)).fst).subtype_mk _⟩

/-- The retraction sends `c (y, s)` to `f y`. -/
@[simp]
lemma coe_collarRetraction {t : ℝ} (x : collarPart c t) :
    (hc.collarRetraction t x : M) = f (hc.collarCoord t x).1 := by
  rfl

/-- The point at the same base as `x` and at depth `τ` times the depth of `x`. -/
private def collarScale {t : ℝ} (τ : I) (x : collarPart c t) : M :=
  c ((hc.collarCoord t x).1, ⟨τ * (hc.collarCoord t x).2,
    mul_nonneg τ.2.1 (hc.collarCoord t x).2.2.1,
    (mul_le_of_le_one_left (hc.collarCoord t x).2.2.1 τ.2.2).trans_lt
      (hc.collarCoord t x).2.2.2⟩)

private lemma collarScale_mem {t : ℝ} (τ : I) (x : collarPart c t) :
    hc.collarScale τ x ∈ collarPart c t :=
  ⟨_, (mul_le_of_le_one_left (hc.collarCoord t x).2.2.1 τ.2.2).trans_lt (hc.collarCoord_lt x),
    rfl⟩

private lemma continuous_collarScale {t : ℝ} :
    Continuous fun q : I × collarPart c t ↦ hc.collarScale q.1 q.2 := by
  have h : Continuous fun q : I × collarPart c t ↦ hc.collarCoord t q.2 :=
    (map_continuous _).comp continuous_snd
  exact hc.isOpenEmbedding.continuous.comp (h.fst.prodMk (((continuous_subtype_val.comp
    continuous_fst).mul (continuous_subtype_val.comp h.snd)).subtype_mk _))

/-- **The collar deforms onto the boundary.** For `0 < t`, scaling the depth coordinate deforms
the collar `c(N × [0, t))` of depth less than `t` onto the boundary `f(N)`, relative to `f(N)`. -/
def collarDeformation {t : ℝ} (ht : 0 < t) :
    ((ContinuousMap.inclusion (hc.range_subset_collarPart ht)).comp
      (hc.collarRetraction t)).HomotopyRel (ContinuousMap.id (collarPart c t))
      {x | (x : M) ∈ range f} where
  toFun q := ⟨hc.collarScale q.1 q.2, hc.collarScale_mem q.1 q.2⟩
  continuous_toFun := hc.continuous_collarScale.subtype_mk _
  map_zero_left x := by
    refine Subtype.ext (Eq.trans ?_ (hc.apply_zero _))
    exact congrArg c (Prod.ext rfl (Subtype.ext (zero_mul _)))
  map_one_left x := by
    refine Subtype.ext (Eq.trans ?_ (hc.apply_collarCoord x))
    exact congrArg c (Prod.ext rfl (Subtype.ext (one_mul _)))
  prop' τ x hx := by
    -- The boundary consists of the points of depth `0`, which the deformation fixes.
    obtain ⟨y, hy⟩ := hx
    have h₀ : ((hc.collarCoord t x).2 : ℝ) = 0 := by
      rw [hc.collarCoord_apply x _ ((hc.apply_zero y).trans hy)]
    refine Subtype.ext (Eq.trans ?_ (hc.apply_zero _))
    exact congrArg c (Prod.ext rfl (Subtype.ext ((congrArg ((τ : ℝ) * ·) h₀).trans (mul_zero _))))

/-- The deformation of the collar keeps the base coordinate. -/
@[simp]
lemma collarCoord_collarDeformation_fst {t : ℝ} (ht : 0 < t) (τ : I) (x : collarPart c t) :
    (hc.collarCoord t (hc.collarDeformation ht (τ, x))).1 = (hc.collarCoord t x).1 := by
  rw [hc.collarCoord_apply _ _ rfl]

/-- The deformation of the collar at time `τ` scales the depth coordinate by `τ`. -/
@[simp]
lemma coe_collarCoord_collarDeformation_snd {t : ℝ} (ht : 0 < t) (τ : I) (x : collarPart c t) :
    ((hc.collarCoord t (hc.collarDeformation ht (τ, x))).2 : ℝ) =
      τ * (hc.collarCoord t x).2 := by
  rw [hc.collarCoord_apply _ _ rfl]

end IsCollar

end TauCeti
