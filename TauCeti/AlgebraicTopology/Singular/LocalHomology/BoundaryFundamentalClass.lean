/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The boundary of the relative fundamental class

Let `X` be a compact Hausdorff space and `ι : M → X` an open embedding of an oriented topological
`n`-manifold `M`, whose complement `∂X = X ∖ ι(M)` is the image of a collared map `f : N → X`, as
for a compact manifold with boundary or with corners. The connecting morphism
`∂ : Hₙ(X, ∂X; ℤ) ⟶ Hₙ₋₁(∂X; ℤ)` of the pair `(X, ∂X)` sends the relative fundamental class
`[X, ∂X]` (`TauCeti.HomologicalOrientation.fundamentalClassRel`) to a fundamental class of the
boundary: at every point `a` of `∂X` the image of `∂[X, ∂X]` in the local homology
`Hₙ₋₁(∂X, ∂X ∖ {a}; ℤ)` generates it
(`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`).
This is the homological input of fundamental chains relative to the boundary: a relative cycle
representing `[X, ∂X]` has as boundary a cycle representing a fundamental class of `∂X`.

No manifold structure on `∂X` is assumed: the local homology of `∂X` at `a` is computed from that
of `M` at an interior point, through the collar. In the collar coordinates `c : N × [0, 1) → X`,
let `a = c (y, 0)`, let `p = c (y, 1/2)` and let `L = c ({y} × [0, 1/2])` be the segment joining
them. The identity of `X` is a map of triples `(X, ∂X, ∂X ∖ {a}) ⟶ (X, X ∖ {p}, X ∖ L)`, and the
connecting morphisms of the two triples commute with it:

* `Hₙ(X, ∂X) ⟶ Hₙ(X, X ∖ {p})` sends `[X, ∂X]` to the local orientation at `p`, a generator;
* the connecting morphism `Hₙ(X, X ∖ {p}) ⟶ Hₙ₋₁(X ∖ {p}, X ∖ L)` is an isomorphism, because
  pushing the collar coordinate up past `1/2` deforms `X` into `X ∖ L`, so `H_*(X, X ∖ L) = 0`;
* `Hₙ₋₁(∂X, ∂X ∖ {a}) ⟶ Hₙ₋₁(X ∖ {p}, X ∖ L)` is an isomorphism. It factors through the tube
  `T = c ((N × [0, 1/2)) ∪ ((N ∖ {y}) × [0, 1)))` and its slit part `S = c ((N ∖ {y}) × [0, 1))`:
  scaling the collar coordinate to `0` deforms `(T, S)` onto `(∂X, ∂X ∖ {a})`, and since
  `T ∪ (X ∖ L) = X ∖ {p}` and `T ∩ (X ∖ L) = S` are open, `(T, S) ⟶ (X ∖ {p}, X ∖ L)` is an
  excision.

The connecting morphism of the triple `(X, ∂X, ∂X ∖ {a})` is that of the pair `(X, ∂X)` followed by
the map to the local homology of `∂X` at `a`, so the image of `∂[X, ∂X]` there is a generator.

## Main results

* `TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`: the
  connecting morphism of `(X, ∂X)` sends the relative fundamental class to a fundamental class of
  `∂X`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the
  fundamental class of a compact manifold with boundary and Lefschetz duality.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A, where the boundary of a fundamental chain relative to the
  boundary is the signed sum of the fundamental chains of the faces.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Module

namespace TauCeti

namespace HomologicalOrientation

/-! ### Collar coordinates near a boundary point -/

section Collar

variable {X : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

/-- The collar parameter `1 / 2`. -/
private def half : Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The segment `c ({y} × [0, 1/2])` of the collar, from the boundary point `c (y, 0)` to the
interior point `c (y, 1/2)`. -/
private def segment (c : N × Ico (0 : ℝ) 1 → X) (y : N) : Set X :=
  c '' ({y} ×ˢ (Subtype.val ⁻¹' Icc 0 (1 / 2)))

/-- The tube `c ((N × [0, 1/2)) ∪ ((N ∖ {y}) × [0, 1)))`: the collar with the part of the fibre
over `y` from `1/2` on removed. -/
private def tube (c : N × Ico (0 : ℝ) 1 → X) (y : N) : Set X :=
  c '' {q | q.1 ≠ y ∨ (q.2 : ℝ) < 1 / 2}

/-- The slit collar `c ((N ∖ {y}) × [0, 1))`: the collar with the whole fibre over `y` removed. -/
private def slit (c : N × Ico (0 : ℝ) 1 → X) (y : N) : Set X :=
  c '' {q | q.1 ≠ y}

/-- Scaling the collar parameter by `τ ∈ [0, 1]`. -/
private def scale (τ : unitInterval) (t : Ico (0 : ℝ) 1) : Ico (0 : ℝ) 1 :=
  ⟨τ * t, mul_nonneg τ.2.1 t.2.1, (mul_le_of_le_one_left t.2.1 τ.2.2).trans_lt t.2.2⟩

private lemma continuous_scale :
    Continuous fun q : unitInterval × Ico (0 : ℝ) 1 ↦ scale q.1 q.2 :=
  ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- Raising the collar parameter to at least `3τ/4`, for `τ ∈ [0, 1]`. -/
private def raise (τ : unitInterval) (t : Ico (0 : ℝ) 1) : Ico (0 : ℝ) 1 :=
  ⟨max t (τ * (3 / 4)), le_max_of_le_left t.2.1,
    max_lt t.2.2 ((mul_le_of_le_one_left (by norm_num) τ.2.2).trans_lt (by norm_num))⟩

private lemma continuous_raise :
    Continuous fun q : unitInterval × Ico (0 : ℝ) 1 ↦ raise q.1 q.2 :=
  ((continuous_subtype_val.comp continuous_snd).max
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk _

omit [TopologicalSpace X] [TopologicalSpace N] in
private lemma slit_subset_tube (y : N) : slit c y ⊆ tube c y :=
  image_mono fun _ hq ↦ Or.inl hq

variable (hc : IsCollar f c) (y : N)
include hc

private lemma mem_segment_iff (q : N × Ico (0 : ℝ) 1) :
    c q ∈ segment c y ↔ q.1 = y ∧ (q.2 : ℝ) ≤ 1 / 2 := by
  rw [segment, hc.isOpenEmbedding.injective.mem_set_image]
  exact and_congr Iff.rfl ⟨fun h ↦ h.2, fun h ↦ ⟨q.2.2.1, h⟩⟩

private lemma mem_tube_iff (q : N × Ico (0 : ℝ) 1) :
    c q ∈ tube c y ↔ q.1 ≠ y ∨ (q.2 : ℝ) < 1 / 2 :=
  hc.isOpenEmbedding.injective.mem_set_image

private lemma mem_slit_iff (q : N × Ico (0 : ℝ) 1) : c q ∈ slit c y ↔ q.1 ≠ y :=
  hc.isOpenEmbedding.injective.mem_set_image

private lemma isClosed_segment [T2Space X] : IsClosed (segment c y) := by
  refine (IsCompact.image ?_ hc.isOpenEmbedding.continuous).isClosed
  refine isCompact_singleton.prod (IsEmbedding.subtypeVal.isCompact_iff.2 ?_)
  rw [Subtype.image_preimage_coe, inter_eq_right.2 (Icc_subset_Ico_right (by norm_num))]
  exact isCompact_Icc

private lemma isOpen_tube [T2Space X] : IsOpen (tube c y) := by
  have := hc.isEmbedding.t2Space
  refine hc.isOpenEmbedding.isOpenMap _ ?_
  exact (isOpen_compl_singleton.preimage continuous_fst).union
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)

private lemma slit_subset_compl_segment : slit c y ⊆ (segment c y)ᶜ := by
  rintro _ ⟨q, hq, rfl⟩ h
  exact hq ((mem_segment_iff hc y q).1 h).1

private lemma range_subset_tube : range f ⊆ tube c y := by
  rintro _ ⟨z, rfl⟩
  rw [← hc.apply_zero, mem_tube_iff hc]
  exact Or.inr (by norm_num)

private lemma diff_subset_slit : range f \ {f y} ⊆ slit c y := by
  rintro _ ⟨⟨z, rfl⟩, hz⟩
  rw [← hc.apply_zero, mem_slit_iff hc]
  exact fun h ↦ hz (h ▸ rfl)

private lemma diff_subset_compl_segment : range f \ {f y} ⊆ (segment c y)ᶜ :=
  (diff_subset_slit hc y).trans (slit_subset_compl_segment hc y)

private lemma tube_subset_compl_singleton {p : X} (hp : c (y, half) = p) : tube c y ⊆ {p}ᶜ := by
  rintro _ ⟨q, hq, rfl⟩ h
  obtain rfl := hc.isOpenEmbedding.injective (h.trans hp.symm)
  rcases hq with h | h
  · exact h rfl
  · exact lt_irrefl (1 / 2 : ℝ) h

private lemma compl_segment_subset_compl_singleton {p : X} (hp : c (y, half) = p) :
    (segment c y)ᶜ ⊆ {p}ᶜ := by
  refine compl_subset_compl.2 (singleton_subset_iff.2 ?_)
  rw [← hp, mem_segment_iff hc]
  exact ⟨rfl, le_of_eq rfl⟩

private lemma range_subset_compl_singleton {p : X} (hp : c (y, half) = p) : range f ⊆ {p}ᶜ :=
  (range_subset_tube hc y).trans (tube_subset_compl_singleton hc y hp)

/-- Off the point `p`, every point lies in the tube or off the segment. -/
private lemma tube_union_compl_segment {p : X} (hp : c (y, half) = p) {x : X} (hx : x ≠ p) :
    x ∈ tube c y ∨ x ∉ segment c y := by
  by_cases h : x ∈ segment c y
  · obtain ⟨q, hq, rfl⟩ := h
    refine Or.inl ((mem_tube_iff hc y q).2 (Or.inr (lt_of_le_of_ne hq.2.2 fun h ↦ hx ?_)))
    rw [← hp]
    exact congrArg c (Prod.ext hq.1 (Subtype.ext h))
  · exact Or.inr h

/-- A point of the tube off the segment lies in the slit collar. -/
private lemma mem_slit_of_mem_tube {x : X} (hx : x ∈ tube c y) (hx' : x ∉ segment c y) :
    x ∈ slit c y := by
  obtain ⟨q, hq, rfl⟩ := hx
  rw [mem_slit_iff hc]
  intro hne
  exact hx' ((mem_segment_iff hc y q).2 ⟨hne, (hq.resolve_left (not_not_intro hne)).le⟩)

/-! ### Collar coordinates on the tube -/

omit [TopologicalSpace X] [TopologicalSpace N] hc in
private lemma tube_subset_collarPart : tube c y ⊆ collarPart c 1 := by
  rintro _ ⟨q, -, rfl⟩
  exact mem_collarPart_iff.2 ⟨q, q.2.2.2, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace N] hc in
private lemma segment_subset_collarPart : segment c y ⊆ collarPart c 1 := by
  rintro _ ⟨q, -, rfl⟩
  exact mem_collarPart_iff.2 ⟨q, q.2.2.2, rfl⟩

/-- The collar coordinates of a point of the tube. -/
private def tubeCoord : C(tube c y, N × Ico (0 : ℝ) 1) :=
  (hc.collarCoord 1).comp (ContinuousMap.inclusion (tube_subset_collarPart y))

private lemma apply_tubeCoord (b : tube c y) : c (tubeCoord hc y b) = b :=
  hc.apply_collarCoord _

private lemma tubeCoord_mem (b : tube c y) :
    (tubeCoord hc y b).1 ≠ y ∨ ((tubeCoord hc y b).2 : ℝ) < 1 / 2 := by
  have hb := b.2
  rwa [← apply_tubeCoord hc y b, mem_tube_iff hc] at hb

/-- The retraction of the tube onto the boundary `f(N)`, by the first collar coordinate. -/
private def tubeRetraction : C(tube c y, range f) :=
  (hc.collarRetraction 1).comp (ContinuousMap.inclusion (tube_subset_collarPart y))

private lemma scale_mem_tube (τ : unitInterval) (b : tube c y) :
    c ((tubeCoord hc y b).1, scale τ (tubeCoord hc y b).2) ∈ tube c y := by
  rw [mem_tube_iff hc]
  refine (tubeCoord_mem hc y b).imp id fun h ↦ ?_
  exact (mul_le_of_le_one_left (tubeCoord hc y b).2.2.1 τ.2.2).trans_lt h

private lemma continuous_scale_tube :
    Continuous fun q : unitInterval × tube c y ↦
      c ((tubeCoord hc y q.2).1, scale q.1 (tubeCoord hc y q.2).2) :=
  hc.isOpenEmbedding.continuous.comp
    ((continuous_fst.comp ((tubeCoord hc y).continuous.comp continuous_snd)).prodMk
      (continuous_scale.comp (continuous_fst.prodMk
        (continuous_snd.comp ((tubeCoord hc y).continuous.comp continuous_snd)))))

/-- Scaling the collar parameter to `0` deforms the tube onto the boundary `f(N)`. -/
private def tubeHomotopy :
    ((ContinuousMap.inclusion (range_subset_tube hc y)).comp (tubeRetraction hc y)).Homotopy
      (ContinuousMap.id (tube c y)) where
  toFun q := ⟨c ((tubeCoord hc y q.2).1, scale q.1 (tubeCoord hc y q.2).2),
    scale_mem_tube hc y q.1 q.2⟩
  continuous_toFun := (continuous_scale_tube hc y).subtype_mk _
  map_zero_left b := Subtype.ext <|
    (congrArg (fun t ↦ c ((tubeCoord hc y b).1, t)) (Subtype.ext (zero_mul _))).trans
      ((hc.apply_zero _).trans (hc.coe_collarRetraction _).symm)
  map_one_left b := Subtype.ext <|
    (congrArg (fun t ↦ c ((tubeCoord hc y b).1, t)) (Subtype.ext (one_mul _))).trans
      (apply_tubeCoord hc y b)

omit [TopologicalSpace X] [TopologicalSpace N] hc y in
private lemma raise_zero (t : Ico (0 : ℝ) 1) : raise 0 t = t :=
  Subtype.ext (max_eq_left (by simpa using t.2.1))

/-- Raising the collar parameter to at least `3/4`, on the collar. -/
private def raiseMap : C(collarPart c 1, collarPart c 1) :=
  ⟨fun u ↦ ⟨c ((hc.collarCoord 1 u).1, raise 1 (hc.collarCoord 1 u).2),
    mem_collarPart_iff.2 ⟨_, (raise _ _).2.2, rfl⟩⟩,
    (hc.isOpenEmbedding.continuous.comp
      ((continuous_fst.comp (hc.collarCoord 1).continuous).prodMk
        (continuous_raise.comp (continuous_const.prodMk
          (continuous_snd.comp (hc.collarCoord 1).continuous))))).subtype_mk _⟩

omit y in
private lemma coe_raiseMap (u : collarPart c 1) :
    (raiseMap hc u : X) = c ((hc.collarCoord 1 u).1, raise 1 (hc.collarCoord 1 u).2) :=
  rfl

/-- Raising the collar parameter past `1/2` moves the collar off the segment. -/
private def raiseHomotopy : (ContinuousMap.id (collarPart c 1)).Homotopy (raiseMap hc) where
  toFun q := ⟨c ((hc.collarCoord 1 q.2).1, raise q.1 (hc.collarCoord 1 q.2).2),
    mem_collarPart_iff.2 ⟨_, (raise _ _).2.2, rfl⟩⟩
  continuous_toFun := (hc.isOpenEmbedding.continuous.comp
    ((continuous_fst.comp ((hc.collarCoord 1).continuous.comp continuous_snd)).prodMk
      (continuous_raise.comp (continuous_fst.prodMk
        (continuous_snd.comp ((hc.collarCoord 1).continuous.comp continuous_snd)))))).subtype_mk _
  map_zero_left u := by
    refine Subtype.ext ?_
    rw [ContinuousMap.id_apply, ← hc.apply_collarCoord u]
    exact congrArg (fun t ↦ c ((hc.collarCoord 1 u).1, t)) (raise_zero _)
  map_one_left _ := rfl

private lemma raise_mem_compl_segment {τ : unitInterval} {q : N × Ico (0 : ℝ) 1}
    (hq : c q ∉ segment c y) : c (q.1, raise τ q.2) ∉ segment c y := by
  rw [mem_segment_iff hc] at hq ⊢
  exact fun h ↦ hq ⟨h.1, (le_max_left _ _).trans h.2⟩

end Collar

/-! ### Homology of the collar pairs -/

section Homology

variable {X : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c) (y : N)
  {C : Type*} [Category C] [HasCoproducts.{0} C] [Abelian C] (R : C)
include hc

/-- **The deformation of the tube onto the boundary.** For `A = f(N)`, the inclusion of pairs
`(A, A ∖ {b}) ⟶ (T, S)`, `b = f y`, into the tube and its slit part induces isomorphisms on relative
homology: scaling the collar parameter to `0` is a homotopy inverse. -/
private lemma isIso_singularHomologyMap_tube {A : Set X} (hA : A = range f) {b : X}
    (hb : f y = b) (hAT : A ⊆ tube c y) (hAS : A \ {b} ⊆ slit c y) (k : ℕ) :
    IsIso ((TopPair.ofInclusion (X := TopCat.of X) (sdiff_subset : A \ {b} ⊆ A)).singularHomologyMap
      (TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of X) sdiff_subset
        (slit_subset_tube y) (ContinuousMap.inclusion hAT)
        fun _ hx ↦ mem_of_subset_of_mem hAS hx) R k) := by
  subst hA hb
  refine TopPair.isIso_singularHomologyMap _ (TopPair.ofInclusionMap (X := TopCat.of X)
    (Y := TopCat.of X) (slit_subset_tube y) sdiff_subset (tubeRetraction hc y)
    fun b hb ↦ ⟨(tubeRetraction hc y b).2, fun h ↦ ?_⟩) ?_ ?_ R k
  · -- A point of the slit collar retracts to a boundary point other than `f y`.
    rw [← apply_tubeCoord hc y b, mem_slit_iff hc] at hb
    exact hb (hc.injective ((hc.coe_collarRetraction _).symm.trans h))
  · -- The sets live in `Set X` while the pairs are formed in `TopCat.of X`, so the composite
    -- matches `TopPair.ofInclusionMap_comp` only up to unfolding `TopCat.of`.
    erw [← TopPair.ofInclusionMap_comp, ← TopPair.ofInclusionMap_id]
    have hid : (tubeRetraction hc y).comp (ContinuousMap.inclusion (range_subset_tube hc y)) =
        ContinuousMap.id _ := by
      ext ⟨_, z, rfl⟩
      refine (hc.coe_collarRetraction _).trans ?_
      rw [hc.collarCoord_apply ((ContinuousMap.inclusion (tube_subset_collarPart y))
        ((ContinuousMap.inclusion (range_subset_tube hc y)) ⟨f z, mem_range_self z⟩))
        (z, ⟨0, by norm_num⟩) (hc.apply_zero z)]
      rfl
    simp only [hid]
    exact TopPair.Homotopy.refl _
  · erw [← TopPair.ofInclusionMap_comp, ← TopPair.ofInclusionMap_id]
    refine TopPair.ofInclusionHomotopy (tubeHomotopy hc y) fun τ b hb ↦ ?_
    rw [← apply_tubeCoord hc y b, mem_slit_iff hc] at hb
    exact (mem_slit_iff hc y _).2 hb

/-- **The complement of the segment carries the homology of `X`.** Raising the collar parameter
past `1/2` deforms the collar off the segment `L`, so `H_*(X, X ∖ L) = 0`; by excision this is
computed in the image of the collar. -/
private lemma isZero_singularHomology_compl_segment [T2Space X] (k : ℕ) :
    IsZero ((TopPair.ofSubset ((segment c y)ᶜ : Set (TopCat.of X))).singularHomology R k) := by
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R (X := TopCat.of X)
    (hc.isOpen_collarPart 1) (isClosed_segment hc y) (segment_subset_collarPart y) k
  refine IsZero.of_iso ?_ (asIso (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := TopCat.of X) (collarPart c 1) (segment c y)ᶜ) R k)).symm
  have hmem (τ : unitInterval) (u : collarPart c 1) (hu : (u : X) ∉ segment c y) :
      c ((hc.collarCoord 1 u).1, raise τ (hc.collarCoord 1 u).2) ∉ segment c y :=
    raise_mem_compl_segment hc y (q := hc.collarCoord 1 u)
      ((hc.apply_collarCoord u).symm ▸ hu)
  have hone (u : collarPart c 1) : (raiseMap hc u : X) ∉ segment c y := by
    rw [coe_raiseMap, mem_segment_iff hc]
    exact fun h ↦ absurd h.2 (not_le.2 ((by norm_num : (1 / 2 : ℝ) < 1 * (3 / 4)).trans_le
      (le_max_right _ _)))
  have H := TopPair.ofSubsetHomotopy (X := TopCat.of (collarPart c 1))
    (Y := TopCat.of (collarPart c 1)) (B := Subtype.val ⁻¹' (segment c y)ᶜ)
    (B' := Subtype.val ⁻¹' (segment c y)ᶜ)
    (g₀ := 𝟙 _) (g₁ := TopCat.ofHom (raiseMap hc)) (raiseHomotopy hc) fun τ u hu ↦ hmem τ u hu
  -- The identity of `TopCat.of (collarPart c 1)` appears as `𝟙` of the coerced subspace
  -- `↧(collarPart c 1)`, so `TopPair.ofSubsetMap_id` matches only up to unfolding.
  erw [TopPair.ofSubsetMap_id] at H
  let g : TopCat.of (collarPart c 1) ⟶
      TopCat.of (Subtype.val ⁻¹' (segment c y)ᶜ : Set (collarPart c 1)) :=
    TopCat.ofHom ⟨fun u ↦ ⟨raiseMap hc u, hone u⟩, (raiseMap hc).continuous.subtype_mk _⟩
  have hg : g ≫ (TopPair.ofSubset (X := TopCat.of (collarPart c 1))
      (Subtype.val ⁻¹' (segment c y)ᶜ)).map = TopCat.ofHom (raiseMap hc) := by
    ext
    rfl
  exact TopPair.isZero_singularHomology_of_homotopy H g
    (hg.trans (TopPair.ofSubsetMap_fst _ _).symm) R k

/-- **Excision onto the tube.** The tube `T` and the complement of the segment `L` are open, with
union `X ∖ {p}` and intersection the slit collar `S`, so the inclusion of pairs
`(T, S) ⟶ (X ∖ {p}, X ∖ L)` induces isomorphisms on relative homology. -/
private lemma isIso_singularHomologyMap_compl_segment [T2Space X] {p : X} (hp : c (y, half) = p)
    (k : ℕ) :
    IsIso ((TopPair.ofInclusion (X := TopCat.of X) (slit_subset_tube y)).singularHomologyMap
      (TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of X) (slit_subset_tube y)
        (compl_segment_subset_compl_singleton hc y hp)
        (ContinuousMap.inclusion (tube_subset_compl_singleton hc y hp))
        fun _ hx ↦ mem_of_subset_of_mem (slit_subset_compl_segment hc y) hx) R k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R _ ?_ ?_
    (fun b : Bool ↦ bif b then Subtype.val ⁻¹' tube c y else Subtype.val ⁻¹' (segment c y)ᶜ)
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · rw [TopPair.ofInclusionMap_fst]
    exact IsEmbedding.inclusion (tube_subset_compl_singleton hc y hp)
  · rintro b ⟨s, hs⟩
    rw [TopPair.ofInclusionMap_fst] at hs
    refine ⟨⟨b.1, mem_slit_of_mem_tube hc y b.2 fun h ↦ s.2 ?_⟩, rfl⟩
    have hsb : s.1 = b.1 := congrArg Subtype.val hs
    rwa [hsb]
  · cases b
    · exact (isClosed_segment hc y).isOpen_compl.preimage continuous_subtype_val
    · exact (isOpen_tube hc y).preimage continuous_subtype_val
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    rcases tube_union_compl_segment hc y hp x.2 with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rw [TopPair.ofInclusionMap_fst]
    cases b
    · exact Or.inl fun x hx ↦ ⟨⟨x.1, hx⟩, rfl⟩
    · exact Or.inr fun x hx ↦ ⟨⟨x.1, hx⟩, rfl⟩

/-- The map `Hₖ(A, A ∖ {b}) ⟶ Hₖ(X ∖ {p}, X ∖ L)` induced by the identity is an isomorphism, for
`A = f(N)` and `b = f y`: it is the deformation onto the tube followed by excision. -/
private lemma isIso_singularHomologyMap_compl_singleton [T2Space X] {A : Set X}
    (hA : A = range f) {b : X} (hb : f y = b) {p : X} (hp : c (y, half) = p) (hAp : A ⊆ {p}ᶜ)
    (hBL : A \ {b} ⊆ (segment c y)ᶜ) (k : ℕ) :
    IsIso ((TopPair.ofInclusion (X := TopCat.of X) (sdiff_subset : A \ {b} ⊆ A)).singularHomologyMap
      (TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of X) sdiff_subset
        (compl_segment_subset_compl_singleton hc y hp) (ContinuousMap.inclusion hAp)
        fun _ hx ↦ mem_of_subset_of_mem hBL hx) R k) := by
  have hAT : A ⊆ tube c y := hA ▸ range_subset_tube hc y
  have hAS : A \ {b} ⊆ slit c y := hA ▸ hb ▸ diff_subset_slit hc y
  have hcomp : TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of X) sdiff_subset
      (compl_segment_subset_compl_singleton hc y hp) (ContinuousMap.inclusion hAp)
        (fun _ hx ↦ mem_of_subset_of_mem hBL hx) =
      TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of X) sdiff_subset
          (slit_subset_tube y) (ContinuousMap.inclusion hAT)
          (fun _ hx ↦ mem_of_subset_of_mem hAS hx) ≫
        TopPair.ofInclusionMap (X := TopCat.of X) (Y := TopCat.of X) (slit_subset_tube y)
          (compl_segment_subset_compl_singleton hc y hp)
          (ContinuousMap.inclusion (tube_subset_compl_singleton hc y hp))
          (fun _ hx ↦ mem_of_subset_of_mem (slit_subset_compl_segment hc y) hx) := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.ofInclusionMap_fst, TopPair.ofInclusionMap_fst,
      TopPair.ofInclusionMap_fst]
    rfl
  rw [hcomp]
  -- As above, `TopPair.singularHomologyMap_comp` matches only up to unfolding `TopCat.of`.
  erw [TopPair.singularHomologyMap_comp]
  exact IsIso.comp_isIso' (isIso_singularHomologyMap_tube hc y R hA hb hAT hAS k)
    (isIso_singularHomologyMap_compl_segment hc y R hp k)

/-- The connecting morphism `Hₙ(X, X ∖ {p}) ⟶ Hₘ(X ∖ {p}, X ∖ L)` of the triple
`(X, X ∖ {p}, X ∖ L)` is an isomorphism, since `H_*(X, X ∖ L) = 0`. -/
private lemma isIso_singularHomologyδ_compl_segment [T2Space X] {p : X} (hp : c (y, half) = p)
    {n m : ℕ} (hm : m + 1 = n) :
    IsIso ((TopTriple.ofSubset (X := TopCat.of X)
      (compl_segment_subset_compl_singleton hc y hp)).singularHomologyδ R n m hm) := by
  have hpair : TopTriple.totalPair.obj (TopTriple.ofSubset (X := TopCat.of X)
      (compl_segment_subset_compl_singleton hc y hp)) =
      TopPair.ofSubset ((segment c y)ᶜ : Set (TopCat.of X)) := rfl
  refine TopTriple.isIso_singularHomologyδ_of_isZero _ R n m ?_ ?_ hm
  · rw [hpair]
    exact isZero_singularHomology_compl_segment hc y R n
  · rw [hpair]
    exact isZero_singularHomology_compl_segment hc y R m

end Homology

/-! ### The local homology of the boundary -/

/-- At a point `a` of a subspace `A ⊆ X`, a class of `Hₘ(A; ℤ)` generates the local homology of `A`
at `a` exactly when its image in `Hₘ(A, A ∖ {a}; ℤ)`, for the subsets `A ∖ {a} ⊆ A` of `X`,
generates it: the two pairs are the same subspaces of `A`. -/
private lemma span_singularHomologyToLocalHomology_iff {X : Type} [TopologicalSpace X] {A : Set X}
    (a : A) (m : ℕ)
    (μ : ((TopCat.toSSet.obj (TopCat.of A)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) m :
      ModuleCat.{0} ℤ)) :
    Submodule.span ℤ {singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) a m μ} = ⊤ ↔
      Submodule.span ℤ (singleton ((TopPair.ofInclusion (X := TopCat.of X)
        (sdiff_subset : A \ {(a : X)} ⊆ A)).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) m
          μ)) = ⊤ := by
  -- The identity of `A`, as a map of pairs from `(A, A ∖ {a})` read in `A` to the same pair of
  -- subsets of `X`, is an isomorphism.
  let ψ : TopPair.ofSubset ({a}ᶜ : Set (TopCat.of A)) ⟶
      TopPair.ofInclusion (X := TopCat.of X) (sdiff_subset : A \ {(a : X)} ⊆ A) :=
    TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun z ↦ ⟨z.1.1, z.1.2, fun h ↦ z.2 (Subtype.ext h)⟩,
      by fun_prop⟩) (by ext; rfl)
  have : IsIso ψ := by
    have : IsIso (TopPair.Hom.fst ψ) := inferInstanceAs (IsIso (𝟙 _))
    exact TopPair.isIso_of_isIso_fst_of_surjective_snd ψ fun w ↦
      ⟨⟨⟨w.1, w.2.1⟩, fun h ↦ w.2.2 (congrArg Subtype.val h)⟩, rfl⟩
  have : IsIso (TopPair.singularHomologyMap ψ (ModuleCat.of ℤ (ULift.{0} ℤ)) m) :=
    ⟨⟨TopPair.singularHomologyMap (inv ψ) (ModuleCat.of ℤ (ULift.{0} ℤ)) m,
      by rw [← TopPair.singularHomologyMap_comp, IsIso.hom_inv_id, TopPair.singularHomologyMap_id],
      by rw [← TopPair.singularHomologyMap_comp, IsIso.inv_hom_id, TopPair.singularHomologyMap_id]⟩⟩
  have hnat := TopPair.singularHomologyπ_naturality ψ (ModuleCat.of ℤ (ULift.{0} ℤ)) m
  rw [show SSet.homologyMap (TopCat.toSSet.map (TopPair.Hom.fst ψ))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) m = 𝟙 _ from
    (congrArg (SSet.homologyMap · _ m) (TopCat.toSSet.map_id _)).trans
      (SSet.homologyMap_id _ _ m)] at hnat
  have hres : (TopPair.ofSubset ((univ : Set (TopCat.of A)))ᶜ).singularHomologyπ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) m ≫ localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (subset_univ {a}) m =
      (TopPair.ofSubset ({a}ᶜ : Set (TopCat.of A))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) m := by
    rw [localHomologyRestriction_def]
    exact TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id _ _ m
  rw [← (asIso (TopPair.singularHomologyMap ψ (ModuleCat.of ℤ (ULift.{0} ℤ)) m)).toLinearEquiv
    |>.span_singleton_apply_eq_top_iff]
  refine Eq.congr_left (congrArg (fun v ↦ Submodule.span ℤ {v}) ?_)
  exact (congrArg _ ((singularHomologyToLocalHomology_apply _ _ _).trans
    (ConcreteCategory.congr_hom hres _))).trans (ConcreteCategory.congr_hom hnat μ).symm

/-! ### The boundary of the relative fundamental class -/

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  {ι : M → X} {f : N → X} [T2Space X] [CompactSpace X] [T2Space M] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

omit [TopologicalSpace M] [T2Space X] [CompactSpace X] [T2Space M] in
include hιf in
/-- The point `c (y, 1/2)` of the collar lies in the interior `ι(M)`. -/
private lemma exists_apply_half_eq {c : N × Ico (0 : ℝ) 1 → X} (hc : IsCollar f c) (y : N) :
    ∃ x, c (y, half) = ι x := by
  obtain ⟨x, hx⟩ : c (y, half) ∈ range ι := by
    rw [hιf]
    rintro ⟨z, hz⟩
    have h := congrArg (fun q : N × Ico (0 : ℝ) 1 ↦ (q.2 : ℝ))
      (hc.isOpenEmbedding.injective ((hc.apply_zero z).trans hz))
    norm_num [half] at h
  exact ⟨x, hx.symm⟩

/-- The relative fundamental class restricts to a generator of the local homology at every
interior point. -/
private lemma span_localHomologyRestriction_fundamentalClassRel (x : M) {S : Set (TopCat.of X)}
    (hS : (range ι)ᶜ ⊆ S) (hSx : S = {ι x}ᶜ) :
    Submodule.span ℤ (singleton (TopPair.singularHomologyMap
      (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hS)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n (o.fundamentalClassRel hn hι hιf hf))) = ⊤ := by
  subst hSx
  have h := o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf x
  rw [localHomologyRestriction_def] at h
  rw [h, ← Iso.toLinearEquiv_apply, LinearEquiv.span_singleton_apply_eq_top_iff,
    Submodule.span_singleton_eq_top_iff]
  exact fun v ↦ ((isLocalOrientation_iff _ _ _).1 (o x).2 v).imp fun c hc ↦
    (int_smul_eq_zsmul _ c _).trans hc

/-- **The boundary of the relative fundamental class is a fundamental class of the boundary.**
Let `ι : M → X` be an open embedding of an oriented `n`-manifold into a compact Hausdorff space,
whose complement `∂X = X ∖ ι(M)` is the image of a collared map. The connecting morphism
`Hₙ(X, ∂X; ℤ) ⟶ Hₙ₋₁(∂X; ℤ)` of the pair `(X, ∂X)` sends the relative fundamental class
`[X, ∂X]` to a class whose image in the local homology `Hₙ₋₁(∂X, ∂X ∖ {a}; ℤ)` generates it, at
every point `a` of `∂X`. -/
theorem isFundamentalClass_singularHomologyδ_fundamentalClassRel {m : ℕ} (hm : m + 1 = n) :
    IsFundamentalClass ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf)) := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  refine (isFundamentalClass_iff _).2 fun a ↦ ?_
  have hA : (range ι)ᶜ = range f := by rw [hιf, compl_compl]
  obtain ⟨y, hy⟩ : (a : X) ∈ range f := hA ▸ a.2
  -- The interior point `p = c (y, 1/2)` of the collar over the boundary point `a = f y`.
  obtain ⟨x, hp⟩ := exists_apply_half_eq hιf hc y
  -- The map of triples `(X, ∂X, ∂X ∖ {a}) ⟶ (X, X ∖ {p}, X ∖ L)` induced by the identity.
  have hAB : ((range ι)ᶜ \ {(a : X)} : Set (TopCat.of X)) ⊆ (range ι)ᶜ := sdiff_subset
  have hT : ((segment c y)ᶜ : Set (TopCat.of X)) ⊆ {ι x}ᶜ :=
    compl_segment_subset_compl_singleton hc y hp
  have hAp : ((range ι)ᶜ : Set (TopCat.of X)) ⊆ {ι x}ᶜ :=
    hA ▸ range_subset_compl_singleton hc y hp
  have hBp : ((range ι)ᶜ \ {(a : X)} : Set (TopCat.of X)) ⊆ (segment c y)ᶜ :=
    fun z hz ↦ diff_subset_compl_segment hc y ⟨hA ▸ hz.1, fun h ↦ hz.2 (h.trans hy)⟩
  let φ := TopTriple.ofSubsetMap (𝟙 (TopCat.of X)) hAB hT hAp hBp
  have key := TopTriple.singularHomologyδ_naturality φ (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm
  rw [show TopTriple.outerPair.map φ = TopPair.ofSubsetMap (𝟙 _) hAp from
    TopTriple.outerPair_map_ofSubsetMap _ _ _ _ _] at key
  replace key := ConcreteCategory.congr_hom key (o.fundamentalClassRel hn hι hιf hf)
  have : IsIso (TopPair.singularHomologyMap (TopTriple.innerPair.map φ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) m) := by
    rw [show TopTriple.innerPair.map φ = _ from TopTriple.innerPair_map_ofSubsetMap _ _ _ _ _]
    exact isIso_singularHomologyMap_compl_singleton hc y _ hA hy hp hAp hBp m
  have := isIso_singularHomologyδ_compl_segment hc y (ModuleCat.of ℤ (ULift.{0} ℤ)) hp hm
  -- By naturality of the connecting morphisms, the connecting morphism of `(X, ∂X, ∂X ∖ {a})`
  -- sends `[X, ∂X]` to a generator, as the local orientation at `p` is one.
  have h₁ : Submodule.span ℤ (singleton ((TopTriple.ofSubset hAB).singularHomologyδ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf))) = ⊤ := by
    refine ((asIso (TopPair.singularHomologyMap (TopTriple.innerPair.map φ)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) m)).toLinearEquiv.span_singleton_apply_eq_top_iff).1 ?_
    refine (congrArg (fun v ↦ Submodule.span ℤ {v}) key).trans ?_
    exact ((asIso ((TopTriple.ofSubset hT).singularHomologyδ (ModuleCat.of ℤ (ULift.{0} ℤ)) n m
      hm)).toLinearEquiv.span_singleton_apply_eq_top_iff).2
      (span_localHomologyRestriction_fundamentalClassRel o hn hι hιf hf x hAp rfl)
  -- That connecting morphism is the one of the pair `(X, ∂X)` followed by the map to
  -- `Hₘ(∂X, ∂X ∖ {a})`.
  have hδπ : (TopTriple.ofSubset hAB).singularHomologyδ (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm
      (o.fundamentalClassRel hn hι hιf hf) =
      (TopTriple.innerPair.obj (TopTriple.ofSubset hAB)).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) m
        ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf)) :=
    ConcreteCategory.congr_hom (TopTriple.singularHomologyδ_eq_comp_singularHomologyπ
      (TopTriple.ofSubset hAB) (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm) _
  rw [hδπ] at h₁
  exact (span_singularHomologyToLocalHomology_iff a m _).2 h₁

end HomologicalOrientation

end TauCeti
