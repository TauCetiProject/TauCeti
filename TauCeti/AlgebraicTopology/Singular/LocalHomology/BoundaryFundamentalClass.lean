/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
import TauCeti.Algebra.Group.ZMultiples
import TauCeti.AlgebraicTopology.Singular.Excision
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The boundary of the relative fundamental class

Let `X` be a compact Hausdorff space, `ι : M → X` an open embedding of an oriented topological
`n`-manifold `M` without boundary, and suppose that the complement `∂X = X ∖ ι(M)` is the image of
a collared map `f : N → X`, as for a compact manifold with boundary (or with corners) whose
interior is `M`. The relative fundamental class `[X, ∂X] ∈ Hₙ(X, ∂X; ℤ)`
(`TauCeti.HomologicalOrientation.fundamentalClassRel`) has an image `∂[X, ∂X]` under the
connecting morphism `Hₙ(X, ∂X) ⟶ Hₙ₋₁(∂X)` of the pair. This file proves that `∂[X, ∂X]` is a
fundamental class of `∂X` (`TauCeti.IsFundamentalClass`): at every point `b` of the boundary its
image in the local homology `Hₙ₋₁(∂X, ∂X ∖ {b}; ℤ)` generates that group
(`TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`).
No orientation, chart or manifold structure on `N` is assumed: the collar alone identifies the
local homology of the boundary with the local homology of the interior one dimension up. The
boundary orientation of `∂X` is the one this class determines.

This is the homological fact behind the representing chain systems of Barraud and Cornea. A
fundamental chain of `X` relative to its boundary has as boundary a fundamental cycle of `∂X`;
when `∂X` is glued from products of lower-dimensional compactified trajectory spaces, the signed
sum of the products of their fundamental chains is such a cycle, which is the gluing condition of
`TauCeti.TwistingChainSystem.exists_isRepresenting`.

## Proof

Fix `b = f y` and let `c : N × [0, 1) → X` be the collar. Put `p = c (y, 1/2)`, an interior point,
and let `T = c({y} × [0, 1/2])` be the segment of the collar joining `b` to `p`.

* Pushing the depth coordinate of the collar towards `1` deforms the collar into the complement
  of `T` while keeping that complement inside itself, so `Hₖ(X, X ∖ T) = 0` in every degree,
  after excising the outside of the collar.
* So in the long exact sequence of the triple `(X, X ∖ {p}, X ∖ T)` the connecting morphism
  `Hₙ(X, X ∖ {p}) ⟶ Hₙ₋₁(X ∖ {p}, X ∖ T)` is an isomorphism. It sends the local orientation at
  `p`, the image of `[X, ∂X]`, to a generator.
* The inclusion `(∂X, ∂X ∖ {b}) ⟶ (X ∖ {p}, X ∖ T)` induces isomorphisms. It factors through the
  pair `(Y, Y ∖ T)`, where `Y` is the collar with the ray `c({y} × [1/2, 1))` removed. Scaling the
  depth coordinate to `0` deforms `(Y, Y ∖ T)` onto `(∂X, ∂X ∖ {b})`, and `(Y, Y ∖ T)` includes
  into `(X ∖ {p}, X ∖ T)` by excision, since `Y` and `X ∖ T` are open and cover `X ∖ {p}`.
* By naturality of the connecting morphisms, the image of `∂[X, ∂X]` in
  `Hₙ₋₁(∂X, ∂X ∖ {b})` is carried by this isomorphism to the generator above.

## Main results

* `TauCeti.HomologicalOrientation.isFundamentalClass_singularHomologyδ_fundamentalClassRel`:
  the connecting morphism of the pair `(X, ∂X)` sends the relative fundamental class to a
  fundamental class of the boundary.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the
  fundamental class of a compact manifold with boundary and its boundary (proof of
  Theorem 3.43).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Appendix A.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Module unitInterval

namespace TauCeti

namespace HomologicalOrientation

variable {X : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

/-! ### The segment of the collar over a boundary point -/

section Segment

/-- The depth `1 / 2` in the collar. -/
private def half : Ico (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

variable (c) in
/-- The segment `c({y} × [0, 1/2])` of the collar over `y`. -/
private def collarSegment (y : N) : Set X := c '' ({y} ×ˢ {s : Ico (0 : ℝ) 1 | (s : ℝ) ≤ 1 / 2})

variable (c) in
/-- The collar with the ray `c({y} × [1/2, 1))` over `y` removed. -/
private def collarSlit (y : N) : Set X := c '' ({y} ×ˢ {s : Ico (0 : ℝ) 1 | 1 / 2 ≤ (s : ℝ)})ᶜ

variable (hc : IsCollar f c) (y : N)
include hc

private lemma apply_mem_collarSegment_iff {z : N} {s : Ico (0 : ℝ) 1} :
    c (z, s) ∈ collarSegment c y ↔ z = y ∧ (s : ℝ) ≤ 1 / 2 := by
  rw [collarSegment, hc.isOpenEmbedding.injective.mem_set_image, prodMk_mem_set_prod_eq,
    mem_singleton_iff, mem_ofPred_eq]

private lemma apply_mem_collarSlit_iff {z : N} {s : Ico (0 : ℝ) 1} :
    c (z, s) ∈ collarSlit c y ↔ ¬(z = y ∧ 1 / 2 ≤ (s : ℝ)) := by
  rw [collarSlit, hc.isOpenEmbedding.injective.mem_set_image, mem_compl_iff,
    prodMk_mem_set_prod_eq, mem_singleton_iff, mem_ofPred_eq]

private lemma collarSegment_subset : collarSegment c y ⊆ collarPart c 1 :=
  image_subset_iff.2 fun q _ ↦ (apply_mem_collarPart_iff hc.isOpenEmbedding.injective).2 q.2.2.2

private lemma collarSlit_subset : collarSlit c y ⊆ collarPart c 1 :=
  image_subset_iff.2 fun q _ ↦ (apply_mem_collarPart_iff hc.isOpenEmbedding.injective).2 q.2.2.2

private lemma isClosed_collarSegment [T2Space X] : IsClosed (collarSegment c y) := by
  have hK : IsCompact {s : Ico (0 : ℝ) 1 | (s : ℝ) ≤ 1 / 2} := by
    rw [Subtype.isCompact_iff]
    convert isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2) using 1
    ext r
    grind [Subtype.exists]
  exact ((isCompact_singleton.prod hK).image hc.isOpenEmbedding.continuous).isClosed

private lemma isOpen_collarSlit [T2Space X] : IsOpen (collarSlit c y) := by
  refine hc.isOpenEmbedding.isOpenMap _ (isOpen_compl_iff.2 ?_)
  refine IsClosed.prod ?_ (isClosed_le continuous_const continuous_subtype_val)
  -- `{y}` is the preimage of the point `f y` of the Hausdorff space `X` under `f = c (·, 0)`.
  have hf : f = fun z ↦ c (z, ⟨0, by norm_num⟩) := funext fun z ↦ (hc.apply_zero z).symm
  have hy : ({y} : Set N) = f ⁻¹' {f y} := by
    ext z
    simp only [mem_singleton_iff, mem_preimage, hf]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ congrArg Prod.fst (hc.isOpenEmbedding.injective h)⟩
  rw [hy, hf]
  exact isClosed_singleton.preimage
    (hc.isOpenEmbedding.continuous.comp (continuous_id.prodMk continuous_const))

private lemma apply_half_mem_collarSegment : c (y, half) ∈ collarSegment c y :=
  (apply_mem_collarSegment_iff hc y).2 ⟨rfl, le_rfl⟩

private lemma apply_zero_mem_collarSegment_iff {z : N} :
    f z ∈ collarSegment c y ↔ z = y := by
  rw [← hc.apply_zero, apply_mem_collarSegment_iff hc]
  exact ⟨And.left, fun h ↦ ⟨h, by norm_num⟩⟩

private lemma apply_half_notMem_range : c (y, half) ∉ range f := by
  rintro ⟨z, hz⟩
  rw [← hc.apply_zero] at hz
  have h := congrArg (fun q : N × Ico (0 : ℝ) 1 ↦ (q.2 : ℝ)) (hc.isOpenEmbedding.injective hz)
  norm_num [half] at h

private lemma apply_half_notMem_collarSlit : c (y, half) ∉ collarSlit c y := by
  rw [apply_mem_collarSlit_iff hc, not_not]
  exact ⟨rfl, le_rfl⟩

private lemma range_subset_collarSlit : range f ⊆ collarSlit c y := by
  rintro _ ⟨z, rfl⟩
  rw [← hc.apply_zero, apply_mem_collarSlit_iff hc]
  exact fun h ↦ absurd h.2 (by norm_num)

/-- Away from `p = c (y, 1/2)`, every point lies in the slit collar or outside the segment. -/
private lemma compl_singleton_subset_collarSlit_union :
    ({c (y, half)} : Set X)ᶜ ⊆ collarSlit c y ∪ (collarSegment c y)ᶜ := by
  intro x hx
  by_contra h
  rw [mem_union, not_or, mem_compl_iff, not_not] at h
  obtain ⟨hxS, ⟨q, hq, rfl⟩⟩ := h
  rw [apply_mem_collarSlit_iff hc, not_not] at hxS
  refine hx (mem_singleton_iff.2 (congrArg c (Prod.ext hxS.1 ?_)))
  exact Subtype.ext (le_antisymm hq.2 hxS.2)

/-- In the slit collar, a point outside the segment does not lie over `y`. -/
private lemma collarCoord_fst_ne_of_mem_collarSlit {x : collarPart c 1}
    (hx : (x : X) ∈ collarSlit c y) (hT : (x : X) ∉ collarSegment c y) :
    (hc.collarCoord 1 x).1 ≠ y := by
  intro h
  rw [← hc.apply_collarCoord x] at hx hT
  rw [apply_mem_collarSlit_iff hc] at hx
  rw [apply_mem_collarSegment_iff hc] at hT
  exact hT ⟨h, le_of_not_ge fun h' ↦ hx ⟨h, h'⟩⟩

/-- The deformation of the collar onto the boundary keeps the slit collar inside itself. -/
private lemma collarDeformation_mem_collarSlit (τ : I) (x : collarPart c 1)
    (hx : (x : X) ∈ collarSlit c y) :
    (hc.collarDeformation one_pos (τ, x) : X) ∈ collarSlit c y := by
  rw [← hc.apply_collarCoord (hc.collarDeformation one_pos (τ, x)), apply_mem_collarSlit_iff hc,
    hc.collarCoord_collarDeformation_fst, hc.coe_collarCoord_collarDeformation_snd]
  rw [← hc.apply_collarCoord x, apply_mem_collarSlit_iff hc] at hx
  exact fun h ↦ hx ⟨h.1, h.2.trans (mul_le_of_le_one_left (hc.collarCoord 1 x).2.2.1 τ.2.2)⟩

/-- The deformation of the collar onto the boundary keeps the slit collar off the segment. -/
private lemma collarDeformation_notMem_collarSegment (τ : I) (x : collarPart c 1)
    (hx : (x : X) ∈ collarSlit c y) (hT : (x : X) ∉ collarSegment c y) :
    (hc.collarDeformation one_pos (τ, x) : X) ∉ collarSegment c y := by
  rw [← hc.apply_collarCoord (hc.collarDeformation one_pos (τ, x)),
    apply_mem_collarSegment_iff hc, hc.collarCoord_collarDeformation_fst]
  exact fun h ↦ collarCoord_fst_ne_of_mem_collarSlit hc y hx hT h.1

end Segment

/-! ### The segment has no local homology -/

section Push

variable (hc : IsCollar f c)

/-- The depth `t + τ (3/4) (1 - t)` lies in `[0, 1)` for `t ∈ [0, 1)` and `τ ∈ [0, 1]`. -/
private def pushDepth (τ : I) (t : Ico (0 : ℝ) 1) : Ico (0 : ℝ) 1 :=
  ⟨t + τ * (3 / 4) * (1 - t), by
    have := t.2.1; have := t.2.2; have := τ.2.1
    positivity, by
    have := t.2.1; have := t.2.2; have := τ.2.1; have := τ.2.2
    nlinarith⟩

private lemma coe_pushDepth (τ : I) (t : Ico (0 : ℝ) 1) :
    (pushDepth τ t : ℝ) = t + τ * (3 / 4) * (1 - t) :=
  (rfl)

private lemma le_pushDepth (τ : I) (t : Ico (0 : ℝ) 1) : (t : ℝ) ≤ pushDepth τ t := by
  have := t.2.2; have := τ.2.1
  rw [coe_pushDepth]
  nlinarith

private lemma half_lt_pushDepth_one (t : Ico (0 : ℝ) 1) : 1 / 2 < (pushDepth 1 t : ℝ) := by
  have := t.2.1
  rw [coe_pushDepth, Set.Icc.coe_one]
  nlinarith

private lemma pushDepth_zero (t : Ico (0 : ℝ) 1) : pushDepth 0 t = t :=
  Subtype.ext (by simp [pushDepth])

/-- Pushing the depth coordinate of the collar towards `1`, as a homotopy of self-maps of the
collar. -/
private def collarPush : C(I × collarPart c 1, collarPart c 1) where
  toFun q := ⟨c ((hc.collarCoord 1 q.2).1, pushDepth q.1 (hc.collarCoord 1 q.2).2),
    (apply_mem_collarPart_iff hc.isOpenEmbedding.injective).2 (pushDepth _ _).2.2⟩
  continuous_toFun := by
    have h : Continuous fun q : I × collarPart c 1 ↦ hc.collarCoord 1 q.2 :=
      (map_continuous _).comp continuous_snd
    refine (hc.isOpenEmbedding.continuous.comp (h.fst.prodMk ?_)).subtype_mk _
    refine Continuous.subtype_mk ?_ _
    have hd : Continuous fun q : I × collarPart c 1 ↦ ((hc.collarCoord 1 q.2).2 : ℝ) :=
      continuous_subtype_val.comp h.snd
    exact hd.add (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_const.sub hd))

private lemma coe_collarPush (q : I × collarPart c 1) :
    (collarPush hc q : X) = c ((hc.collarCoord 1 q.2).1, pushDepth q.1 (hc.collarCoord 1 q.2).2) :=
  (rfl)

/-- The push of the collar keeps the complement of the segment inside itself. -/
private lemma collarPush_notMem_collarSegment (y : N) (τ : I) (x : collarPart c 1)
    (hx : (x : X) ∉ collarSegment c y) : (collarPush hc (τ, x) : X) ∉ collarSegment c y := by
  rw [← hc.apply_collarCoord x, apply_mem_collarSegment_iff hc] at hx
  rw [coe_collarPush, apply_mem_collarSegment_iff hc]
  exact fun h ↦ hx ⟨h.1, (le_pushDepth τ _).trans h.2⟩

/-- At the end of the push the collar lies outside the segment. -/
private lemma collarPush_one_notMem_collarSegment (y : N) (x : collarPart c 1) :
    (collarPush hc (1, x) : X) ∉ collarSegment c y := by
  rw [coe_collarPush, apply_mem_collarSegment_iff hc]
  exact fun h ↦ absurd h.2 (not_le.2 (half_lt_pushDepth_one _))

include hc in
/-- **The segment of the collar has no local homology**: `Hₖ(X, X ∖ T) = 0` for the segment
`T = c({y} × [0, 1/2])`, in every degree. -/
private lemma isZero_localHomology_collarSegment [T2Space X] (y : N) (k : ℕ) :
    IsZero (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (collarSegment c y) k) := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset R
    (X := TopCat.of X) (hc.isOpen_collarPart 1) (isClosed_collarSegment hc y)
    (collarSegment_subset hc y) k
  refine IsZero.of_iso ?_ (asIso (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := TopCat.of X) (collarPart c 1) (collarSegment c y)ᶜ) R k)).symm
  -- In the collar, the push deforms the identity of the pair into its subspace.
  let ρ : C(collarPart c 1, collarPart c 1) := (collarPush hc).comp (.prodMk (.const _ 1) (.id _))
  let F : (ContinuousMap.id (collarPart c 1)).Homotopy ρ :=
    { toContinuousMap := collarPush hc
      map_zero_left x := Subtype.ext <| by
        rw [ContinuousMap.toFun_eq_coe, coe_collarPush, pushDepth_zero, Prod.mk.eta]
        exact hc.apply_collarCoord x
      map_one_left _ := rfl }
  have hρ : MapsTo (TopCat.ofHom ρ) (Subtype.val ⁻¹' (collarSegment c y)ᶜ)
      (Subtype.val ⁻¹' (collarSegment c y)ᶜ) :=
    fun x _ ↦ collarPush_one_notMem_collarSegment hc y x
  refine TopPair.isZero_singularHomology_of_homotopy
    (f := TopPair.ofSubsetMap (TopCat.ofHom ρ) hρ) ?_
    (TopCat.ofHom ⟨fun x ↦ ⟨ρ x, collarPush_one_notMem_collarSegment hc y x⟩, by fun_prop⟩)
    (by ext x; exact (TopPair.ofSubsetMap_fst_apply _ hρ x).symm) R k
  rw [← TopPair.ofSubsetMap_id (X := TopCat.of (collarPart c 1))
    (B := Subtype.val ⁻¹' (collarSegment c y)ᶜ) fun _ hx ↦ hx]
  exact TopPair.ofSubsetHomotopy (g₀ := 𝟙 (TopCat.of (collarPart c 1))) (g₁ := TopCat.ofHom ρ) F
    fun τ x hx ↦ collarPush_notMem_collarSegment hc y τ x hx

end Push

/-! ### The slit collar -/

section Slit

variable (hc : IsCollar f c) (y : N)

variable (c) in
/-- The pair `(Y, Y ∖ T)` of the slit collar `Y` and the segment `T` over `y`. -/
private abbrev slitPair : TopPair :=
  TopPair.ofInclusion (X := TopCat.of X)
    (inter_subset_left : collarSlit c y ∩ (collarSegment c y)ᶜ ⊆ collarSlit c y)

/-- The triple `(X, X ∖ {p}, X ∖ T)` of the segment `T` over `y`, with `p = c (y, 1/2)`. -/
private abbrev segmentTriple : TopTriple :=
  TopTriple.ofSubset (X := TopCat.of X)
    (compl_subset_compl.2 (singleton_subset_iff.2 (apply_half_mem_collarSegment hc y)))

include hc in
private lemma collarSlit_subset_compl_singleton_half :
    collarSlit c y ⊆ ({c (y, half)} : Set X)ᶜ :=
  fun _ hx h ↦ apply_half_notMem_collarSlit hc y (h ▸ hx)

/-- The inclusion `(Y, Y ∖ T) ⟶ (X ∖ {p}, X ∖ T)`. -/
private def slitToSegment : slitPair c y ⟶ TopTriple.innerPair.obj (segmentTriple hc y) :=
  TopPair.ofHom
    (TopCat.ofHom (ContinuousMap.inclusion (collarSlit_subset_compl_singleton_half hc y)))
    (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) (by ext; rfl)

/-- **Excision onto the slit collar.** The slit collar `Y` and the complement `X ∖ T` of the
segment are open and cover `X ∖ {p}`, so `(Y, Y ∖ T) ⟶ (X ∖ {p}, X ∖ T)` induces isomorphisms on
relative homology. -/
private lemma isIso_singularHomologyMap_slitToSegment [T2Space X] (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (slitToSegment hc y)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover _ (slitToSegment hc y)
    (IsEmbedding.inclusion (collarSlit_subset_compl_singleton_half hc y)) ?_
    (fun i : Bool ↦ bif i then Subtype.val ⁻¹' collarSlit c y
      else Subtype.val ⁻¹' (collarSegment c y)ᶜ) ?_ ?_ ?_ k
  · rintro x ⟨w, hw⟩
    exact ⟨⟨x.1, x.2, congrArg Subtype.val hw ▸ w.2⟩, rfl⟩
  · rintro (_ | _)
    · exact (isClosed_collarSegment hc y).isOpen_compl.preimage continuous_subtype_val
    · exact (isOpen_collarSlit hc y).preimage continuous_subtype_val
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    rcases compl_singleton_subset_collarSlit_union hc y x.2 with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rintro (_ | _)
    · exact Or.inl fun x hx ↦ ⟨⟨x.1, hx⟩, rfl⟩
    · exact Or.inr fun x hx ↦ ⟨⟨x.1, hx⟩, rfl⟩

/-- The retraction `c (z, t) ↦ f z` of the slit collar onto the boundary. -/
private def slitRetraction : C(collarSlit c y, range f) :=
  (hc.collarRetraction 1).comp (ContinuousMap.inclusion (collarSlit_subset hc y))

/-- The retraction fixes the boundary. -/
private lemma slitRetraction_apply (x : range f) :
    slitRetraction hc y ⟨x, range_subset_collarSlit hc y x.2⟩ = x := by
  obtain ⟨_, z, rfl⟩ := x
  refine Subtype.ext ?_
  rw [slitRetraction, ContinuousMap.comp_apply, hc.coe_collarRetraction,
    hc.collarCoord_apply _ (z, ⟨0, by norm_num⟩) (hc.apply_zero z)]

/-- The retraction of the slit collar onto the boundary, as a map into the slit collar. -/
private def slitRetractionSelf : C(collarSlit c y, collarSlit c y) :=
  ⟨fun x ↦ ⟨slitRetraction hc y x, range_subset_collarSlit hc y (slitRetraction hc y x).2⟩,
    by fun_prop⟩

/-- **The slit collar deforms onto the boundary**, by scaling the depth coordinate. -/
private def slitDeformation : (slitRetractionSelf hc y).Homotopy (ContinuousMap.id _) where
  toFun q := ⟨hc.collarDeformation one_pos (q.1, ⟨q.2, collarSlit_subset hc y q.2.2⟩),
    collarDeformation_mem_collarSlit hc y q.1 _ q.2.2⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((hc.collarDeformation one_pos).continuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))).subtype_mk _
  -- Both endpoint identities hold by unfolding: `slitRetractionSelf` is `slitRetraction`, the
  -- composite of `collarRetraction 1` with the inclusion of the slit collar, and the endpoints of
  -- `collarDeformation` are that retraction and the identity, read in the ambient space `X`.
  map_zero_left x := Subtype.ext (congrArg Subtype.val
    ((hc.collarDeformation one_pos).apply_zero ⟨x, collarSlit_subset hc y x.2⟩) :)
  map_one_left x := Subtype.ext (congrArg Subtype.val
    ((hc.collarDeformation one_pos).apply_one ⟨x, collarSlit_subset hc y x.2⟩) :)

/-- The deformation of the slit collar keeps the complement of the segment inside itself. -/
private lemma slitDeformation_mem (τ : I) (x : collarSlit c y)
    (hx : (x : X) ∈ collarSlit c y ∩ (collarSegment c y)ᶜ) :
    (slitDeformation hc y (τ, x) : X) ∈ collarSlit c y ∩ (collarSegment c y)ᶜ :=
  ⟨collarDeformation_mem_collarSlit hc y τ _ hx.1,
    collarDeformation_notMem_collarSegment hc y τ ⟨x, collarSlit_subset hc y x.2⟩ hx.1 hx.2⟩

end Slit

/-! ### The boundary pair and the pair of the segment -/

section BoundaryToSlit

variable (hc : IsCollar f c) (y : N) (b : range f) (hb : (b : X) = f y)
include hc hb

private lemma notMem_collarSegment (x : ({b}ᶜ : Set (range f))) :
    (x : X) ∉ collarSegment c y := by
  obtain ⟨⟨_, z, rfl⟩, hx⟩ := x
  rw [apply_zero_mem_collarSegment_iff hc]
  rintro rfl
  exact hx (Subtype.ext hb.symm)

/-- Off the segment, the retraction of the slit collar avoids `b`. -/
private lemma slitRetraction_ne (x : collarSlit c y) (hx : (x : X) ∉ collarSegment c y) :
    slitRetraction hc y x ≠ b := by
  intro h
  have h' : f (hc.collarCoord 1 ⟨x, collarSlit_subset hc y x.2⟩).1 = f y := by
    rw [← hb, ← h]
    exact (hc.coe_collarRetraction _).symm
  refine collarCoord_fst_ne_of_mem_collarSlit hc y (x := ⟨x, collarSlit_subset hc y x.2⟩) x.2
    hx ?_
  rw [← hc.apply_zero, ← hc.apply_zero] at h'
  exact congrArg Prod.fst (hc.isOpenEmbedding.injective h')

variable (c) in
/-- The inclusion `(∂X, ∂X ∖ {b}) ⟶ (Y, Y ∖ T)` of the boundary pair into the slit collar. -/
private def boundaryToSlit :
    TopPair.ofSubset ({b}ᶜ : Set (TopCat.of (range f))) ⟶ slitPair c y :=
  TopPair.ofHom (TopCat.ofHom ⟨fun x ↦ ⟨x, range_subset_collarSlit hc y x.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨x, range_subset_collarSlit hc y x.1.2,
      notMem_collarSegment hc y b hb x⟩, by fun_prop⟩)
    (by ext; rfl)

/-- The retraction `(Y, Y ∖ T) ⟶ (∂X, ∂X ∖ {b})` of the slit collar onto the boundary pair. -/
private def slitToBoundary :
    slitPair c y ⟶ TopPair.ofSubset ({b}ᶜ : Set (TopCat.of (range f))) :=
  TopPair.ofHom (TopCat.ofHom (slitRetraction hc y))
    (TopCat.ofHom ⟨fun x ↦ ⟨slitRetraction hc y ⟨x, inter_subset_left x.2⟩,
      slitRetraction_ne hc y b hb _ x.2.2⟩, by fun_prop⟩)
    (by ext; rfl)

/-- **The slit collar deforms onto the boundary pair**, so `(∂X, ∂X ∖ {b}) ⟶ (Y, Y ∖ T)` induces
isomorphisms on relative homology. -/
private lemma isIso_singularHomologyMap_boundaryToSlit (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (boundaryToSlit c hc y b hb)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k) := by
  refine TopPair.isIso_singularHomologyMap _ (slitToBoundary hc y b hb) ?_ ?_ _ k
  · have h : boundaryToSlit c hc y b hb ≫ slitToBoundary hc y b hb = 𝟙 _ := by
      ext x : 2
      · exact Subtype.ext (slitRetraction_apply hc y x.1)
      · exact slitRetraction_apply hc y x
    rw [h]
    exact .refl _
  · have h : slitToBoundary hc y b hb ≫ boundaryToSlit c hc y b hb =
        TopPair.ofInclusionMap _ _ (slitRetractionSelf hc y) fun x hx ↦
          (slitDeformation hc y).apply_zero x ▸ slitDeformation_mem hc y 0 x hx := by
      ext x : 2
      · refine Subtype.ext (Eq.trans ?_
          (TopPair.ofInclusionMap_snd_apply (hst := inter_subset_left)
            (hst' := inter_subset_left) _ _ x).symm)
        -- Both sides are `slitRetraction hc y ⟨x, _⟩` once the `TopPair.ofHom` components of the
        -- composite unfold.
        rfl
      · exact (TopPair.ofInclusionMap_fst_apply (hst := inter_subset_left)
          (hst' := inter_subset_left) _ _ x).symm
    rw [h, ← TopPair.ofInclusionMap_id]
    exact TopPair.ofInclusionHomotopy (slitDeformation hc y) (slitDeformation_mem hc y)

end BoundaryToSlit

section Boundary

variable (hc : IsCollar f c) {S : Set X} (hS : S = range f) (y : N) (b : S)
  (hb : (b : X) = f y)
include hc hS hb

private lemma mem_compl_singleton_half (x : S) : (x : X) ∈ ({c (y, half)} : Set X)ᶜ := by
  subst hS
  obtain ⟨_, z, rfl⟩ := x
  exact fun h ↦ apply_half_notMem_range hc y (h ▸ mem_range_self z)

variable (c) in
/-- The inclusion `(∂X, ∂X ∖ {b}) ⟶ (X ∖ {p}, X ∖ T)` of the boundary pair at `b = f y` into the
pair of the segment `T` over `y`, with `p = c (y, 1/2)`. -/
private def boundaryPairMap :
    TopPair.ofSubset ({b}ᶜ : Set (TopCat.of S)) ⟶ TopTriple.innerPair.obj (segmentTriple hc y) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x ↦ ⟨x, mem_compl_singleton_half hc hS y b hb x⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨x, by subst hS; exact notMem_collarSegment hc y b hb x⟩, by fun_prop⟩)
    (by ext; rfl)

/-- **The boundary pair at `b` computes the homology of the pair of the segment.** The inclusion
`(∂X, ∂X ∖ {b}) ⟶ (X ∖ {p}, X ∖ T)` induces isomorphisms on relative homology: it factors
through the slit collar `(Y, Y ∖ T)`, which deforms onto the boundary pair and includes into
`(X ∖ {p}, X ∖ T)` by excision. -/
private lemma isIso_singularHomologyMap_boundaryPairMap [T2Space X] (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (boundaryPairMap c hc hS y b hb)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) k) := by
  subst hS
  have hG : boundaryPairMap c hc rfl y b hb =
      boundaryToSlit c hc y b hb ≫ slitToSegment hc y := by
    ext : 2 <;> rfl
  have := isIso_singularHomologyMap_boundaryToSlit hc y b hb k
  have := isIso_singularHomologyMap_slitToSegment hc y k
  rw [hG, TopPair.singularHomologyMap_comp]
  infer_instance

end Boundary

/-! ### The boundary of the relative fundamental class -/

section Naturality

variable (hc : IsCollar f c) {A : Set X} (hA : Aᶜ = range f) (y : N) (b : (Aᶜ : Set X))
  (hb : (b : X) = f y)

/-- **The connecting morphism at a boundary point.** For a class `μ` of `Hₙ(X, ∂X)`, with
`∂X = X ∖ A`, the image of `∂μ` in `Hₙ₋₁(∂X, ∂X ∖ {b})` is carried by the inclusion of the
boundary pair to the image under the connecting morphism of the triple `(X, X ∖ {p}, X ∖ T)` of
the restriction of `μ` to the local homology at `p`. -/
private lemma singularHomologyMap_boundaryPairMap_singularHomologyToLocalHomology
    (hp : c (y, half) ∈ A) {n m : ℕ} (hm : m + 1 = n)
    (μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) A n) :
    TopPair.singularHomologyMap (boundaryPairMap c hc hA y b hb) (ModuleCat.of ℤ (ULift.{0} ℤ)) m
        (singularHomologyToLocalHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) b m
          ((TopPair.ofSubset (Aᶜ : Set (TopCat.of X))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm μ)) =
      (segmentTriple hc y).singularHomologyδ (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm
        (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hp) n
          μ) := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let δμ := (TopPair.ofSubset (Aᶜ : Set (TopCat.of X))).singularHomologyδ R n m hm μ
  let F := TopPair.ofSubsetMap (𝟙 (TopCat.of X))
    (compl_subset_compl.2 (singleton_subset_iff.2 hp) : MapsTo (𝟙 (TopCat.of X)) _ _)
  have hGF : TopPair.Hom.fst (boundaryPairMap c hc hA y b hb) = TopPair.Hom.snd F := by
    ext x
    exact Subtype.ext ((TopPair.ofSubsetMap_snd_apply (X := TopCat.of X)
      (Y := TopCat.of X) (B := (Aᶜ : Set (TopCat.of X)))
      (B' := ({c (y, half)}ᶜ : Set (TopCat.of X))) (𝟙 (TopCat.of X)) _ x).symm)
  -- The local image of `∂μ` at `b` is its image in `Hₙ₋₁(∂X, ∂X ∖ {b})`.
  have h₁ : singularHomologyToLocalHomology R b m δμ =
      (TopPair.ofSubset ({b}ᶜ : Set (TopCat.of (Aᶜ : Set X)))).singularHomologyπ R m δμ := by
    have e := ConcreteCategory.congr_hom
      (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id
        (X := TopCat.of (Aᶜ : Set X)) (S := ({b}ᶜ : Set _)) (S' := (univᶜ : Set _)) R
        (fun _ hx ↦ absurd (mem_univ _) hx) m) δμ
    refine (singularHomologyToLocalHomology_apply R b δμ).trans ?_
    rw [localHomologyRestriction_def]
    exact e
  -- Naturality of the connecting morphisms of the pair `(X, ∂X)` and of the triple.
  have e₁ := ConcreteCategory.congr_hom
    (TopPair.singularHomologyπ_naturality (boundaryPairMap c hc hA y b hb) R m) δμ
  have e₂ := ConcreteCategory.congr_hom (TopPair.singularHomologyδ_naturality R F n m hm) μ
  have e₃ := ConcreteCategory.congr_hom
    (TopTriple.singularHomologyδ_eq_comp_singularHomologyπ (segmentTriple hc y) R n m hm)
    (TopPair.singularHomologyMap F R n μ)
  rw [hGF] at e₁
  refine (congrArg _ h₁).trans ?_
  rw [localHomologyRestriction_def]
  exact e₁.symm.trans ((congrArg (ConcreteCategory.hom
    ((TopTriple.innerPair.obj (segmentTriple hc y)).singularHomologyπ R m)) e₂).trans e₃.symm)

end Naturality

variable [T2Space X] [CompactSpace X] {M : Type} [TopologicalSpace M] [T2Space M] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ}
  (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) {ι : M → X} (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary of the relative fundamental class is a fundamental class of the boundary.** Let
`ι : M → X` be an open embedding of an oriented `n`-manifold `M` into a compact Hausdorff space
`X` whose complement `∂X = X ∖ ι(M)` is the image of a collared map `f : N → X`. The connecting
morphism `Hₙ(X, ∂X; ℤ) ⟶ Hₙ₋₁(∂X; ℤ)` of the pair `(X, ∂X)` sends the relative fundamental class
`[X, ∂X]` to a fundamental class of `∂X`: at every point `b` of `∂X` its image generates the local
homology `Hₙ₋₁(∂X, ∂X ∖ {b}; ℤ)`. -/
theorem isFundamentalClass_singularHomologyδ_fundamentalClassRel {m : ℕ} (hm : m + 1 = n) :
    IsFundamentalClass (M := ((range ι)ᶜ : Set X)) (R := ℤ)
      (N := ModuleCat.of ℤ (ULift.{0} ℤ))
      ((TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n m hm (o.fundamentalClassRel hn hι hιf hf)) := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  have hS : (range ι)ᶜ = range f := by rw [hιf, compl_compl]
  refine (isFundamentalClass_iff_forall_isLocalOrientation _).2 fun b ↦ ?_
  obtain ⟨y, hy⟩ : (b : X) ∈ range f := hS ▸ b.2
  -- The interior point `p = c (y, 1/2)`; the triple `(X, X ∖ {p}, X ∖ T)` has an isomorphism as
  -- connecting morphism, since `(X, X ∖ T)` has no homology.
  have hp : c (y, half) ∈ range ι := by
    rw [hιf]
    exact apply_half_notMem_range hc y
  have hz (k : ℕ) : IsZero ((TopTriple.totalPair.obj (segmentTriple hc y)).singularHomology R k) :=
    isZero_localHomology_collarSegment hc y k
  have := TopTriple.isIso_singularHomologyδ_of_isZero _ R n m (hz n) (hz m) hm
  have := isIso_singularHomologyMap_boundaryPairMap hc hS y b hy.symm m
  have key := singularHomologyMap_boundaryPairMap_singularHomologyToLocalHomology hc hS y b
    hy.symm hp hm (o.fundamentalClassRel hn hι hιf hf)
  -- The image of `[X, ∂X]` at `p` generates, hence so do its images under the two isomorphisms.
  have h := zmultiples_apply_eq_top_of_surjective
    (ConcreteCategory.bijective_of_isIso ((segmentTriple hc y).singularHomologyδ R n m hm)).2
    ((isLocalOrientation_iff_zmultiples_eq_top _ _ _).1
      (o.isLocalOrientation_localHomologyRestriction_fundamentalClassRel hn hι hιf hf hp))
  rw [← key] at h
  have h' := zmultiples_apply_eq_top_of_surjective (ConcreteCategory.bijective_of_isIso
    (inv (TopPair.singularHomologyMap (boundaryPairMap c hc hS y b hy.symm) R m))).2 h
  rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply] at h'
  exact (isLocalOrientation_iff_zmultiples_eq_top _ _ _).2 h'

end HomologicalOrientation

end TauCeti
