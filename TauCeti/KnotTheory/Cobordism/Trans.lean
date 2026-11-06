/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Cobordism.Basic
public import TauCeti.Geometry.Manifold.Instances.Quotient

import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum
import TauCeti.Geometry.Manifold.Orientation.Glue
import TauCeti.Geometry.Manifold.Orientation.OpenSubset
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension

/-!
# Composing knot cobordisms

Knot cobordisms compose: a cobordism `S₁` from `K₀` to `K₁` followed by a cobordism `S₂` from `K₁`
to `K₂` is a cobordism from `K₀` to `K₂`, obtained by stacking the surface of `S₂` on top of that
of `S₁` in `Sⁿ × [0, 1]`. This is the composition operation that a category whose morphisms are
knot cobordisms would use, and with the genus it is the step behind the triangle inequality for the
cobordism distance.

Knot cobordisms are recorded in collared form (`TauCeti.KnotCobordism`): a boundaryless surface,
smoothly embedded in `Sⁿ × ℝ`, which is the cylinder over the initial knot at heights at most `ε`
and the cylinder over the final knot at heights at least `1 - ε`. The composite
`TauCeti.KnotCobordism.trans` halves the heights of `S₁`, so that its part over `Sⁿ × [0, 1]` goes
to the heights `[0, 1 / 2]`, and moves the heights `t` of `S₂` to `(t + 1) / 2`, so that its part
over `Sⁿ × [0, 1]` goes to `[1 / 2, 1]`; the cylinder ends go along. In a band of heights around
`1 / 2` both rescaled surfaces are the same cylinder over `K₁`. The surface of the composite is
glued from the part of `S₁` below the top of that band and the part of `S₂` above its bottom,
identifying the points with the same image in `Sⁿ × ℝ`:

* its charts are pushed forward from the two parts along the quotient map, which has smooth local
  deck transformations because a smooth map into the image of a smooth embedding factors smoothly
  through it (`Manifold.IsImmersionAt.exists_contMDiffAt_comp_eventuallyEq`);
* its embedding into `Sⁿ × ℝ` is a topological embedding by construction, and an immersion because
  on each part it is a rescaled embedding of `S₁` or `S₂` read through a local diffeomorphism;
* it is connected, being the union of the two halves with their heights pushed towards `1 / 2`,
  two connected sets meeting along `K₁ × {1 / 2}`;
* it is orientable: the overlap of the two parts is a connected annulus, so orientations of `S₁`
  and `S₂` can be chosen to agree on it, and they are then glued to an orientation of the
  composite (`TauCeti.Manifold.Orientation.glue`).

The embedded surface of the composite is described by `TauCeti.KnotCobordism.range_toFun_trans`:
at heights at most `1 / 2` it is the part of `S₁` at heights at most `1`, with halved heights
(`TauCeti.KnotCobordism.range_toFun_trans_inter_snd_le`), and at heights at least `1 / 2` the part
of `S₂` at heights at least `0`, with heights moved to `(t + 1) / 2`
(`TauCeti.KnotCobordism.range_toFun_trans_inter_le_snd`). Classically the genus of the composite
is the sum of the genera; that computation, which gives the triangle inequality for the cobordism
distance, is not done here.

## Main definitions

* `TauCeti.KnotCobordism.trans`: the composite of two knot cobordisms.

## Main results

* `TauCeti.KnotCobordism.range_toFun_trans`: the embedded surface of the composite.
* `TauCeti.KnotCobordism.range_toFun_trans_inter_snd_le`,
  `TauCeti.KnotCobordism.range_toFun_trans_inter_le_snd`: the lower and upper halves of the
  embedded surface of the composite.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  knot cobordism.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 15, for gluing orientations along a connected overlap.
-/

public section

noncomputable section

open Function Filter Manifold Metric Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace KnotCobordism

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {K₀ K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  (S₁ : KnotCobordism K₀ K₁) (S₂ : KnotCobordism K₁ K₂)

/-! ### The two halves of the composite -/

/-- The width of the collar at the top of `S₁` used for the composite, at most `1 / 2`. -/
private def topWidth : ℝ :=
  min S₁.exists_pos_range_inter_le_snd.choose (1 / 2)

/-- The width of the collar at the bottom of `S₂` used for the composite, at most `1 / 2`. -/
private def botWidth : ℝ :=
  min S₂.exists_pos_range_inter_snd_le.choose (1 / 2)

private theorem topWidth_pos : 0 < topWidth S₁ :=
  lt_min S₁.exists_pos_range_inter_le_snd.choose_spec.1 one_half_pos

private theorem botWidth_pos : 0 < botWidth S₂ :=
  lt_min S₂.exists_pos_range_inter_snd_le.choose_spec.1 one_half_pos

private theorem topWidth_le : topWidth S₁ ≤ 1 / 2 := min_le_right _ _

private theorem botWidth_le : botWidth S₂ ≤ 1 / 2 := min_le_right _ _

/-- Above height `1 - topWidth S₁`, the surface of `S₁` is the cylinder over `K₁`. -/
private theorem mem_range_iff_of_topWidth_le {p : sphere (0 : E) 1 × ℝ}
    (hp : 1 - topWidth S₁ ≤ p.2) : p ∈ range S₁.toFun ↔ p.1 ∈ range K₁ := by
  have h := Set.ext_iff.1 S₁.exists_pos_range_inter_le_snd.choose_spec.2 p
  have hw : topWidth S₁ ≤ S₁.exists_pos_range_inter_le_snd.choose := min_le_left _ _
  have hp' : 1 - S₁.exists_pos_range_inter_le_snd.choose ≤ p.2 := by linarith
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ici] at h
  exact ⟨fun hr ↦ (h.1 ⟨hr, hp'⟩).1, fun hK ↦ (h.2 ⟨hK, hp'⟩).1⟩

/-- Below height `botWidth S₂`, the surface of `S₂` is the cylinder over `K₁`. -/
private theorem mem_range_iff_of_le_botWidth {p : sphere (0 : E) 1 × ℝ}
    (hp : p.2 ≤ botWidth S₂) : p ∈ range S₂.toFun ↔ p.1 ∈ range K₁ := by
  have h := Set.ext_iff.1 S₂.exists_pos_range_inter_snd_le.choose_spec.2 p
  have hp' : p.2 ≤ S₂.exists_pos_range_inter_snd_le.choose :=
    hp.trans (min_le_left _ _)
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Iic] at h
  exact ⟨fun hr ↦ (h.1 ⟨hr, hp'⟩).1, fun hK ↦ (h.2 ⟨hK, hp'⟩).1⟩

/-- The lower half of the composite: the surface of `S₁` with its heights halved. -/
private def lower (x : S₁.carrier) : sphere (0 : E) 1 × ℝ :=
  ((S₁.toFun x).1, (S₁.toFun x).2 / 2)

/-- The upper half of the composite: the surface of `S₂` with its heights `t` moved to
`(t + 1) / 2`. -/
private def upper (y : S₂.carrier) : sphere (0 : E) 1 × ℝ :=
  ((S₂.toFun y).1, ((S₂.toFun y).2 + 1) / 2)

private theorem lower_snd (x : S₁.carrier) : (lower S₁ x).2 = (S₁.toFun x).2 / 2 :=
  (rfl)

private theorem upper_snd (y : S₂.carrier) : (upper S₂ y).2 = ((S₂.toFun y).2 + 1) / 2 :=
  (rfl)

private theorem isSmoothEmbedding_lower :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (lower S₁) := by
  convert isSmoothEmbedding_diffeomorph_comp S₁.isSmoothEmbedding
    ((Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞).prodCongr
      (Diffeomorph.smulAdd ∞ (1 / 2 : ℝ) (0 : ℝ) (by norm_num))) using 1
  ext x <;> simp [lower, Diffeomorph.coe_prodCongr, Diffeomorph.smulAdd_apply, div_eq_inv_mul]

private theorem isSmoothEmbedding_upper :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (upper S₂) := by
  convert isSmoothEmbedding_diffeomorph_comp S₂.isSmoothEmbedding
    ((Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞).prodCongr
      (Diffeomorph.smulAdd ∞ (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num))) using 1
  ext y <;> simp [upper, Diffeomorph.coe_prodCongr, Diffeomorph.smulAdd_apply]; ring

private theorem mem_range_lower_iff {p : sphere (0 : E) 1 × ℝ} :
    p ∈ range (lower S₁) ↔ (p.1, 2 * p.2) ∈ range S₁.toFun := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, Prod.ext rfl (by simp only [lower]; ring)⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, Prod.ext (by simp [lower, hx]) ?_⟩
    simp only [lower, hx]
    ring

private theorem mem_range_upper_iff {p : sphere (0 : E) 1 × ℝ} :
    p ∈ range (upper S₂) ↔ (p.1, 2 * p.2 - 1) ∈ range S₂.toFun := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, Prod.ext rfl (by simp only [upper]; ring)⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Prod.ext (by simp [upper, hy]) ?_⟩
    simp only [upper, hy]
    ring

/-- Above height `(1 - topWidth S₁) / 2`, the lower half is the cylinder over `K₁`. -/
private theorem mem_range_lower_iff_of_le {p : sphere (0 : E) 1 × ℝ}
    (hp : (1 - topWidth S₁) / 2 ≤ p.2) : p ∈ range (lower S₁) ↔ p.1 ∈ range K₁ := by
  rw [mem_range_lower_iff]
  exact mem_range_iff_of_topWidth_le S₁ (by dsimp only; linarith)

/-- Below height `(1 + botWidth S₂) / 2`, the upper half is the cylinder over `K₁`. -/
private theorem mem_range_upper_iff_of_le {p : sphere (0 : E) 1 × ℝ}
    (hp : p.2 ≤ (1 + botWidth S₂) / 2) : p ∈ range (upper S₂) ↔ p.1 ∈ range K₁ := by
  rw [mem_range_upper_iff]
  exact mem_range_iff_of_le_botWidth S₂ (by dsimp only; linarith)

/-- In the band of heights between `(1 - topWidth S₁) / 2` and `(1 + botWidth S₂) / 2` the two
halves are the same cylinder over `K₁`. -/
private theorem mem_range_lower_iff_mem_range_upper {p : sphere (0 : E) 1 × ℝ}
    (h₁ : (1 - topWidth S₁) / 2 ≤ p.2) (h₂ : p.2 ≤ (1 + botWidth S₂) / 2) :
    p ∈ range (lower S₁) ↔ p ∈ range (upper S₂) :=
  (mem_range_lower_iff_of_le S₁ h₁).trans (mem_range_upper_iff_of_le S₂ h₂).symm

/-- The part of `S₁` used for the composite: the points below height `1 + botWidth S₂`, which
lie below height `(1 + botWidth S₂) / 2` in the lower half. -/
private def lowerPiece : TopologicalSpace.Opens S₁.carrier :=
  ⟨{x | (S₁.toFun x).2 < 1 + botWidth S₂},
    isOpen_lt (continuous_snd.comp S₁.isSmoothEmbedding.isEmbedding.continuous) continuous_const⟩

/-- The part of `S₂` used for the composite: the points above height `-topWidth S₁`, which lie
above height `(1 - topWidth S₁) / 2` in the upper half. -/
private def upperPiece : TopologicalSpace.Opens S₂.carrier :=
  ⟨{y | -topWidth S₁ < (S₂.toFun y).2},
    isOpen_lt continuous_const (continuous_snd.comp S₂.isSmoothEmbedding.isEmbedding.continuous)⟩

private theorem mem_lowerPiece {x : S₁.carrier} :
    x ∈ lowerPiece S₁ S₂ ↔ (S₁.toFun x).2 < 1 + botWidth S₂ :=
  Iff.rfl

private theorem mem_upperPiece {y : S₂.carrier} :
    y ∈ upperPiece S₁ S₂ ↔ -topWidth S₁ < (S₂.toFun y).2 :=
  Iff.rfl

private theorem mem_lowerPiece_iff {x : S₁.carrier} :
    x ∈ lowerPiece S₁ S₂ ↔ (lower S₁ x).2 < (1 + botWidth S₂) / 2 := by
  rw [mem_lowerPiece, lower_snd]
  constructor <;> intro h <;> linarith

private theorem mem_upperPiece_iff {y : S₂.carrier} :
    y ∈ upperPiece S₁ S₂ ↔ (1 - topWidth S₁) / 2 < (upper S₂ y).2 := by
  rw [mem_upperPiece, upper_snd]
  constructor <;> intro h <;> linarith

/-- The disjoint union of the two parts of `S₁` and `S₂` used for the composite. -/
private abbrev Pieces : Type :=
  lowerPiece S₁ S₂ ⊕ upperPiece S₁ S₂

/-- The embedding of each part into `Sⁿ × ℝ`, through the lower and upper halves. -/
private def piecesMap : Pieces S₁ S₂ → sphere (0 : E) 1 × ℝ :=
  Sum.elim (fun x ↦ lower S₁ x) (fun y ↦ upper S₂ y)

@[simp]
private theorem piecesMap_inl (x : lowerPiece S₁ S₂) : piecesMap S₁ S₂ (.inl x) = lower S₁ x :=
  (rfl)

@[simp]
private theorem piecesMap_inr (y : upperPiece S₁ S₂) : piecesMap S₁ S₂ (.inr y) = upper S₂ y :=
  (rfl)

/-! ### The surface of the composite -/

/-- The surface of the composite: the two parts glued along the points with the same image in
`Sⁿ × ℝ`. -/
private def Stack : Type :=
  Quotient (Setoid.ker (piecesMap S₁ S₂))

/-- The embedding of the surface of the composite into `Sⁿ × ℝ`. -/
private def stackMap : Stack S₁ S₂ → sphere (0 : E) 1 × ℝ :=
  Setoid.kerLift (piecesMap S₁ S₂)

/-- The surface of the composite carries the topology of its image in `Sⁿ × ℝ`. -/
private instance : TopologicalSpace (Stack S₁ S₂) :=
  .induced (stackMap S₁ S₂) inferInstance

/-- The quotient map from the two parts to the surface of the composite. -/
private def proj : Pieces S₁ S₂ → Stack S₁ S₂ :=
  Quotient.mk _

private theorem stackMap_proj (z : Pieces S₁ S₂) :
    stackMap S₁ S₂ (proj S₁ S₂ z) = piecesMap S₁ S₂ z :=
  (rfl)

private theorem proj_eq_proj_iff {z w : Pieces S₁ S₂} :
    proj S₁ S₂ z = proj S₁ S₂ w ↔ piecesMap S₁ S₂ z = piecesMap S₁ S₂ w :=
  Quotient.eq

private theorem proj_surjective : Surjective (proj S₁ S₂) :=
  Quotient.mk_surjective

private theorem isEmbedding_stackMap : IsEmbedding (stackMap S₁ S₂) :=
  ⟨⟨rfl⟩, Setoid.kerLift_injective _⟩

private theorem range_stackMap : range (stackMap S₁ S₂) = range (piecesMap S₁ S₂) := by
  rw [← (proj_surjective S₁ S₂).range_comp]
  exact congrArg range (funext (stackMap_proj S₁ S₂))

private theorem continuous_proj : Continuous (proj S₁ S₂) :=
  continuous_induced_rng.2 <| continuous_sum_dom.2
    ⟨(isSmoothEmbedding_lower S₁).isEmbedding.continuous.comp continuous_subtype_val,
      (isSmoothEmbedding_upper S₂).isEmbedding.continuous.comp continuous_subtype_val⟩

/-- The range of the lower part in the composite: the points below height
`(1 + botWidth S₂) / 2`. -/
private theorem range_proj_inl :
    range (proj S₁ S₂ ∘ Sum.inl) = {t | (stackMap S₁ S₂ t).2 < (1 + botWidth S₂) / 2} := by
  ext t
  obtain ⟨z, rfl⟩ := proj_surjective S₁ S₂ t
  simp only [mem_range, comp_apply, mem_ofPred_eq, stackMap_proj]
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨x, hx⟩
    rw [← stackMap_proj, ← hx, stackMap_proj]
    exact (mem_lowerPiece_iff S₁ S₂).1 x.2
  rcases z with x | y
  · exact ⟨x, rfl⟩
  · -- A point of the upper part below that height lies on the cylinder over `K₁`.
    have hy := (mem_upperPiece_iff S₁ S₂).1 y.2
    obtain ⟨x, hx⟩ := (mem_range_lower_iff_mem_range_upper S₁ S₂ hy.le hz.le).2
      (mem_range_self (y : S₂.carrier))
    refine ⟨⟨x, (mem_lowerPiece_iff S₁ S₂).2 ?_⟩, (proj_eq_proj_iff S₁ S₂).2 hx⟩
    rw [hx]
    exact hz

/-- The range of the upper part in the composite: the points above height
`(1 - topWidth S₁) / 2`. -/
private theorem range_proj_inr :
    range (proj S₁ S₂ ∘ Sum.inr) = {t | (1 - topWidth S₁) / 2 < (stackMap S₁ S₂ t).2} := by
  ext t
  obtain ⟨z, rfl⟩ := proj_surjective S₁ S₂ t
  simp only [mem_range, comp_apply, mem_ofPred_eq, stackMap_proj]
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨y, hy⟩
    rw [← stackMap_proj, ← hy, stackMap_proj]
    exact (mem_upperPiece_iff S₁ S₂).1 y.2
  rcases z with x | y
  · -- A point of the lower part above that height lies on the cylinder over `K₁`.
    have hx := (mem_lowerPiece_iff S₁ S₂).1 x.2
    obtain ⟨y, hy⟩ := (mem_range_lower_iff_mem_range_upper S₁ S₂ hz.le hx.le).1
      (mem_range_self (x : S₁.carrier))
    refine ⟨⟨y, (mem_upperPiece_iff S₁ S₂).2 ?_⟩, (proj_eq_proj_iff S₁ S₂).2 hy⟩
    rw [hy]
    exact hz
  · exact ⟨y, rfl⟩

private theorem isOpenEmbedding_proj_inl : IsOpenEmbedding (proj S₁ S₂ ∘ Sum.inl) := by
  have he : IsEmbedding (stackMap S₁ S₂ ∘ (proj S₁ S₂ ∘ Sum.inl)) :=
    (isSmoothEmbedding_lower S₁).isEmbedding.comp IsEmbedding.subtypeVal
  refine ⟨⟨(isEmbedding_stackMap S₁ S₂).isInducing.of_comp_iff.1 he.isInducing,
    fun x x' h ↦ he.injective (congrArg (stackMap S₁ S₂) h)⟩, ?_⟩
  rw [range_proj_inl]
  exact isOpen_lt (continuous_snd.comp (isEmbedding_stackMap S₁ S₂).continuous) continuous_const

private theorem isOpenEmbedding_proj_inr : IsOpenEmbedding (proj S₁ S₂ ∘ Sum.inr) := by
  have he : IsEmbedding (stackMap S₁ S₂ ∘ (proj S₁ S₂ ∘ Sum.inr)) :=
    (isSmoothEmbedding_upper S₂).isEmbedding.comp IsEmbedding.subtypeVal
  refine ⟨⟨(isEmbedding_stackMap S₁ S₂).isInducing.of_comp_iff.1 he.isInducing,
    fun y y' h ↦ he.injective (congrArg (stackMap S₁ S₂) h)⟩, ?_⟩
  rw [range_proj_inr]
  exact isOpen_lt continuous_const (continuous_snd.comp (isEmbedding_stackMap S₁ S₂).continuous)

/-- The quotient map is a local homeomorphism: it is an open embedding on each part. -/
private theorem isLocalHomeomorph_proj : IsLocalHomeomorph (proj S₁ S₂) := by
  refine isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 fun z _ ↦ ?_
  rcases z with x | y
  · exact (isOpenEmbedding_proj_inl S₁ S₂).isLocalHomeomorph.isLocalHomeomorphOn.of_comp_right
      IsOpenEmbedding.inl.isLocalHomeomorph.isLocalHomeomorphOn _ ⟨x, mem_univ x, rfl⟩
  · exact (isOpenEmbedding_proj_inr S₁ S₂).isLocalHomeomorph.isLocalHomeomorphOn.of_comp_right
      IsOpenEmbedding.inr.isLocalHomeomorph.isLocalHomeomorphOn _ ⟨y, mem_univ y, rfl⟩

private theorem isImmersionAt_lower_val (x : lowerPiece S₁ S₂) :
    IsImmersionAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (lower S₁ ∘ ((↑) : lowerPiece S₁ S₂ → S₁.carrier)) x :=
  isImmersionAt_comp_isLocalDiffeomorphAt (isLocalDiffeomorph_subtype_val x)
    ((isSmoothEmbedding_lower S₁).isImmersion.isImmersionAt _)

private theorem isImmersionAt_upper_val (y : upperPiece S₁ S₂) :
    IsImmersionAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (upper S₂ ∘ ((↑) : upperPiece S₁ S₂ → S₂.carrier)) y :=
  isImmersionAt_comp_isLocalDiffeomorphAt (isLocalDiffeomorph_subtype_val y)
    ((isSmoothEmbedding_upper S₂).isImmersion.isImmersionAt _)

private theorem contMDiff_piecesMap :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (piecesMap S₁ S₂) :=
  ((isSmoothEmbedding_lower S₁).isImmersion.contMDiff.comp contMDiff_subtype_val).sumElim
    ((isSmoothEmbedding_upper S₂).isImmersion.contMDiff.comp contMDiff_subtype_val)

/-- Let `ι : W → Pieces S₁ S₂` include a part `W`, so that `ι` followed by the quotient map is an
open embedding, and let `ι` followed by the embedding into `Sⁿ × ℝ` be an immersion at `w`. Then a
point `z` of the parts with the same image in the composite as `ι w` is sent to `w` by a map to
`W`, smooth at `z`, under which the composite agrees with the quotient map near `z`. -/
private theorem exists_deck {W : Type}
    [TopologicalSpace W] [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) W]
    {ι : W → Pieces S₁ S₂} (hι : IsOpenEmbedding (proj S₁ S₂ ∘ ι)) {w : W}
    (hw : IsImmersionAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (piecesMap S₁ S₂ ∘ ι) w)
    {z : Pieces S₁ S₂} (h : proj S₁ S₂ z = proj S₁ S₂ (ι w)) :
    ∃ τ : Pieces S₁ S₂ → W, ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ τ z ∧ τ z = w ∧
      proj S₁ S₂ ∘ ι ∘ τ =ᶠ[𝓝 z] proj S₁ S₂ := by
  -- Near `z` the quotient map stays in the open range of the part `W`.
  have hrange : ∀ᶠ z' in 𝓝 z, piecesMap S₁ S₂ z' ∈ range (piecesMap S₁ S₂ ∘ ι) := by
    filter_upwards [(continuous_proj S₁ S₂).continuousAt.preimage_mem_nhds
      (hι.isOpen_range.mem_nhds ⟨w, h.symm⟩)] with z' ⟨w', hw'⟩
    exact ⟨w', congrArg (stackMap S₁ S₂) hw'⟩
  obtain ⟨τ, hτ, hτw, hτeq⟩ := hw.exists_contMDiffAt_comp_eventuallyEq
    ((isEmbedding_stackMap S₁ S₂).comp hι.isEmbedding) ((contMDiff_piecesMap S₁ S₂) z)
    ((proj_eq_proj_iff S₁ S₂).1 h) hrange
  exact ⟨τ, hτ, hτw, hτeq.mono fun _ hq ↦ (proj_eq_proj_iff S₁ S₂).2 hq⟩

/-- The quotient map has smooth local deck transformations: two points of the parts with the same
image in the composite are related by a map smooth at the first, commuting with the quotient
map near it. -/
private theorem proj_deck (z w : Pieces S₁ S₂) (h : proj S₁ S₂ z = proj S₁ S₂ w) :
    ∃ φ : Pieces S₁ S₂ → Pieces S₁ S₂,
      ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ φ z ∧ φ z = w ∧
        proj S₁ S₂ ∘ φ =ᶠ[𝓝 z] proj S₁ S₂ := by
  rcases w with x | y
  · obtain ⟨τ, hτ, rfl, hτeq⟩ :=
      exists_deck S₁ S₂ (isOpenEmbedding_proj_inl S₁ S₂) (isImmersionAt_lower_val S₁ S₂ x) h
    exact ⟨Sum.inl ∘ τ, ContMDiff.inl.contMDiffAt.comp z hτ, rfl, hτeq⟩
  · obtain ⟨τ, hτ, rfl, hτeq⟩ :=
      exists_deck S₁ S₂ (isOpenEmbedding_proj_inr S₁ S₂) (isImmersionAt_upper_val S₁ S₂ y) h
    exact ⟨Sum.inr ∘ τ, ContMDiff.inr.contMDiffAt.comp z hτ, rfl, hτeq⟩

/-- The charts of the surface of the composite, pushed forward from the two parts. -/
private instance : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) (Stack S₁ S₂) :=
  (isLocalHomeomorph_proj S₁ S₂).chartedSpaceOfRightInverse
    (rightInverse_surjInv (proj_surjective S₁ S₂))

private instance : IsManifold ((𝓡 1).prod 𝓘(ℝ)) ∞ (Stack S₁ S₂) :=
  (isLocalHomeomorph_proj S₁ S₂).isManifold_chartedSpaceOfRightInverse _ (proj_deck S₁ S₂)

private theorem isLocalDiffeomorph_proj :
    IsLocalDiffeomorph ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ (proj S₁ S₂) :=
  (isLocalHomeomorph_proj S₁ S₂).isLocalDiffeomorph_chartedSpaceOfRightInverse _ (proj_deck S₁ S₂)

private theorem isLocalDiffeomorph_proj_inl :
    IsLocalDiffeomorph ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ (proj S₁ S₂ ∘ Sum.inl) :=
  fun x ↦ (isLocalDiffeomorph_sumInl x).comp (hg := isLocalDiffeomorph_proj S₁ S₂ _)

private theorem isLocalDiffeomorph_proj_inr :
    IsLocalDiffeomorph ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ (proj S₁ S₂ ∘ Sum.inr) :=
  fun y ↦ (isLocalDiffeomorph_sumInr y).comp (hg := isLocalDiffeomorph_proj S₁ S₂ _)

/-- The surface of the composite is smoothly embedded in `Sⁿ × ℝ`: on each part its embedding is
a half of the composite, read through a local diffeomorphism. -/
private theorem isSmoothEmbedding_stackMap :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (stackMap S₁ S₂) := by
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun t ↦ ?_, isEmbedding_stackMap S₁ S₂⟩
  obtain ⟨z, rfl⟩ := proj_surjective S₁ S₂ t
  rcases z with x | y
  · exact (isImmersionAt_comp_isLocalDiffeomorphAt_iff (f := stackMap S₁ S₂)
      (g := proj S₁ S₂ ∘ Sum.inl) (isLocalDiffeomorph_proj_inl S₁ S₂ x)).1
      (isImmersionAt_lower_val S₁ S₂ x)
  · exact (isImmersionAt_comp_isLocalDiffeomorphAt_iff (f := stackMap S₁ S₂)
      (g := proj S₁ S₂ ∘ Sum.inr) (isLocalDiffeomorph_proj_inr S₁ S₂ y)).1
      (isImmersionAt_upper_val S₁ S₂ y)

/-- The image of the composite: the lower half below height `(1 + botWidth S₂) / 2` and the upper
half above height `(1 - topWidth S₁) / 2`. -/
private theorem mem_range_stackMap_iff {p : sphere (0 : E) 1 × ℝ} :
    p ∈ range (stackMap S₁ S₂) ↔ (p ∈ range (lower S₁) ∧ p.2 < (1 + botWidth S₂) / 2) ∨
      (p ∈ range (upper S₂) ∧ (1 - topWidth S₁) / 2 < p.2) := by
  rw [range_stackMap]
  constructor
  · rintro ⟨x | y, rfl⟩
    · exact .inl ⟨mem_range_self _, (mem_lowerPiece_iff S₁ S₂).1 x.2⟩
    · exact .inr ⟨mem_range_self _, (mem_upperPiece_iff S₁ S₂).1 y.2⟩
  · rintro (⟨⟨x, rfl⟩, hx⟩ | ⟨⟨y, rfl⟩, hy⟩)
    · exact ⟨.inl ⟨x, (mem_lowerPiece_iff S₁ S₂).2 hx⟩, rfl⟩
    · exact ⟨.inr ⟨y, (mem_upperPiece_iff S₁ S₂).2 hy⟩, rfl⟩

private theorem quarter_le_sub : 1 / 4 ≤ (1 - topWidth S₁) / 2 := by
  linarith [topWidth_le S₁]

private theorem sub_lt_half : (1 - topWidth S₁) / 2 < 1 / 2 := by
  linarith [topWidth_pos S₁]

private theorem half_lt_add : 1 / 2 < (1 + botWidth S₂) / 2 := by
  linarith [botWidth_pos S₂]

private theorem add_le_three_quarters : (1 + botWidth S₂) / 2 ≤ 3 / 4 := by
  linarith [botWidth_le S₂]

/-- At heights at most `1 / 2`, the image of the composite is the lower half. -/
private theorem mem_range_lower_of_mem_range_stackMap {p : sphere (0 : E) 1 × ℝ}
    (hp : p ∈ range (stackMap S₁ S₂)) (hle : p.2 ≤ 1 / 2) : p ∈ range (lower S₁) := by
  rcases (mem_range_stackMap_iff S₁ S₂).1 hp with ⟨hl, -⟩ | ⟨hu, hp'⟩
  · exact hl
  · exact (mem_range_lower_iff_mem_range_upper S₁ S₂ hp'.le
      (hle.trans (half_lt_add S₂).le)).2 hu

/-- At heights at least `1 / 2`, the image of the composite is the upper half. -/
private theorem mem_range_upper_of_mem_range_stackMap {p : sphere (0 : E) 1 × ℝ}
    (hp : p ∈ range (stackMap S₁ S₂)) (hle : 1 / 2 ≤ p.2) : p ∈ range (upper S₂) := by
  rcases (mem_range_stackMap_iff S₁ S₂).1 hp with ⟨hl, hp'⟩ | ⟨hu, -⟩
  · exact (mem_range_lower_iff_mem_range_upper S₁ S₂ ((sub_lt_half S₁).le.trans hle)
      hp'.le).1 hl
  · exact hu

/-- The image of the composite is connected: it is the union of the lower half with its heights
capped at `1 / 2` and the upper half with its heights raised to at least `1 / 2`, two connected
sets meeting along the circle `K₁` at height `1 / 2`. -/
private theorem isPreconnected_range_stackMap : IsPreconnected (range (stackMap S₁ S₂)) := by
  let P : sphere (0 : E) 1 × ℝ → sphere (0 : E) 1 × ℝ := fun p ↦ (p.1, min p.2 (1 / 2))
  let Q : sphere (0 : E) 1 × ℝ → sphere (0 : E) 1 × ℝ := fun p ↦ (p.1, max p.2 (1 / 2))
  have hP : Continuous P := by fun_prop
  have hQ : Continuous Q := by fun_prop
  have hA : IsPreconnected (range (P ∘ lower S₁)) :=
    isPreconnected_range (hP.comp (isSmoothEmbedding_lower S₁).isEmbedding.continuous)
  have hB : IsPreconnected (range (Q ∘ upper S₂)) :=
    isPreconnected_range (hQ.comp (isSmoothEmbedding_upper S₂).isEmbedding.continuous)
  have h₁ := sub_lt_half S₁
  have h₂ := half_lt_add S₂
  have hPfix (p : sphere (0 : E) 1 × ℝ) (hp : p.2 ≤ 1 / 2) : P p = p :=
    Prod.ext rfl (min_eq_left hp)
  have hQfix (p : sphere (0 : E) 1 × ℝ) (hp : 1 / 2 ≤ p.2) : Q p = p :=
    Prod.ext rfl (max_eq_left hp)
  -- On the circle `K₁` at height `1 / 2` both halves are the cylinder over `K₁`.
  have hp₀A : (K₁ 1, (1 / 2 : ℝ)) ∈ range (P ∘ lower S₁) := by
    obtain ⟨x, hx⟩ := (mem_range_lower_iff_of_le S₁ (p := (K₁ 1, 1 / 2)) h₁.le).2
      (mem_range_self (f := ⇑K₁) 1)
    exact ⟨x, by rw [comp_apply, hx, hPfix _ le_rfl]⟩
  have hp₀B : (K₁ 1, (1 / 2 : ℝ)) ∈ range (Q ∘ upper S₂) := by
    obtain ⟨y, hy⟩ := (mem_range_upper_iff_of_le S₂ (p := (K₁ 1, 1 / 2)) h₂.le).2
      (mem_range_self (f := ⇑K₁) 1)
    exact ⟨y, by rw [comp_apply, hy, hQfix _ le_rfl]⟩
  convert hA.union _ hp₀A hp₀B hB using 1
  ext p
  rw [mem_range_stackMap_iff, mem_union]
  constructor
  · rintro (⟨⟨x, rfl⟩, hx⟩ | ⟨⟨y, rfl⟩, hy⟩)
    · rcases le_or_gt (lower S₁ x).2 (1 / 2) with hle | hlt
      · exact .inl ⟨x, hPfix _ hle⟩
      · obtain ⟨y, hy⟩ := (mem_range_lower_iff_mem_range_upper S₁ S₂ (h₁.trans hlt).le hx.le).1
          (mem_range_self x)
        exact .inr ⟨y, by rw [comp_apply, hy, hQfix _ hlt.le]⟩
    · rcases le_or_gt (1 / 2) (upper S₂ y).2 with hle | hlt
      · exact .inr ⟨y, hQfix _ hle⟩
      · obtain ⟨x, hx⟩ := (mem_range_lower_iff_mem_range_upper S₁ S₂ hy.le (hlt.trans h₂).le).2
          (mem_range_self y)
        exact .inl ⟨x, by rw [comp_apply, hx, hPfix _ hlt.le]⟩
  · rintro (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · rcases le_or_gt (lower S₁ x).2 (1 / 2) with hle | hlt
      · rw [comp_apply, hPfix _ hle]
        exact .inl ⟨mem_range_self x, hle.trans_lt h₂⟩
      · have hK := (mem_range_lower_iff_of_le S₁ (h₁.trans hlt).le).1 (mem_range_self x)
        have hPx : P (lower S₁ x) = ((lower S₁ x).1, 1 / 2) := Prod.ext rfl (min_eq_right hlt.le)
        rw [comp_apply, hPx]
        exact .inl ⟨(mem_range_lower_iff_of_le S₁ h₁.le).2 hK, h₂⟩
    · rcases le_or_gt (1 / 2) (upper S₂ y).2 with hle | hlt
      · rw [comp_apply, hQfix _ hle]
        exact .inr ⟨mem_range_self y, h₁.trans_le hle⟩
      · have hK := (mem_range_upper_iff_of_le S₂ (hlt.trans h₂).le).1 (mem_range_self y)
        have hQy : Q (upper S₂ y) = ((upper S₂ y).1, 1 / 2) := Prod.ext rfl (max_eq_right hlt.le)
        rw [comp_apply, hQy]
        exact .inr ⟨(mem_range_upper_iff_of_le S₂ h₂.le).2 hK, h₁⟩

private instance : ConnectedSpace (Stack S₁ S₂) := by
  have hne : (range (stackMap S₁ S₂)).Nonempty :=
    ⟨(K₁ 1, 1 / 2), (mem_range_stackMap_iff S₁ S₂).2 (.inl ⟨(mem_range_lower_iff_of_le S₁
      (p := (K₁ 1, 1 / 2)) (sub_lt_half S₁).le).2 (mem_range_self (f := ⇑K₁) 1),
      half_lt_add S₂⟩)⟩
  obtain ⟨_, t, -⟩ := hne
  refine connectedSpace_iff_univ.2 ⟨⟨t, mem_univ t⟩, ?_⟩
  refine (isEmbedding_stackMap S₁ S₂).isInducing.isPreconnected_image.1 ?_
  rw [image_univ]
  exact isPreconnected_range_stackMap S₁ S₂

/-- The part of the composite over the slab `Sⁿ × [0, 1]` is compact: it is the union of the
parts of the two halves over the slabs `Sⁿ × [0, 1 / 2]` and `Sⁿ × [1 / 2, 1]`, which are the
images of the compact parts of `S₁` and `S₂` over `Sⁿ × [0, 1]`. -/
private theorem isCompact_preimage_Icc_stackMap :
    IsCompact {t : Stack S₁ S₂ | (stackMap S₁ S₂ t).2 ∈ Icc (0 : ℝ) 1} := by
  have hL : IsCompact (lower S₁ '' {x | (S₁.toFun x).2 ∈ Icc (0 : ℝ) 1}) :=
    S₁.isCompact_preimage_Icc.image (isSmoothEmbedding_lower S₁).isEmbedding.continuous
  have hU : IsCompact (upper S₂ '' {y | (S₂.toFun y).2 ∈ Icc (0 : ℝ) 1}) :=
    S₂.isCompact_preimage_Icc.image (isSmoothEmbedding_upper S₂).isEmbedding.continuous
  have h₁ := sub_lt_half S₁
  have h₂ := half_lt_add S₂
  have hsub : lower S₁ '' {x | (S₁.toFun x).2 ∈ Icc (0 : ℝ) 1} ∪
      upper S₂ '' {y | (S₂.toFun y).2 ∈ Icc (0 : ℝ) 1} ⊆ range (stackMap S₁ S₂) := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact (mem_range_stackMap_iff S₁ S₂).2
        (.inl ⟨mem_range_self x, by rw [lower_snd]; linarith [hx.2]⟩)
    · exact (mem_range_stackMap_iff S₁ S₂).2
        (.inr ⟨mem_range_self y, by rw [upper_snd]; linarith [hy.1]⟩)
  convert (isEmbedding_stackMap S₁ S₂).isInducing.isCompact_preimage' (hL.union hU) hsub using 1
  ext t
  have ht := mem_range_self (f := stackMap S₁ S₂) t
  simp only [mem_ofPred_eq, mem_preimage, mem_union, mem_image, mem_Icc]
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_or_gt (stackMap S₁ S₂ t).2 (1 / 2) with hle | hlt
    · obtain ⟨x, hx⟩ := mem_range_lower_of_mem_range_stackMap S₁ S₂ ht hle
      have hx2 := lower_snd S₁ x
      rw [hx] at hx2
      exact .inl ⟨x, ⟨by linarith, by linarith⟩, hx⟩
    · obtain ⟨y, hy⟩ := mem_range_upper_of_mem_range_stackMap S₁ S₂ ht hlt.le
      have hy2 := upper_snd S₂ y
      rw [hy] at hy2
      exact .inr ⟨y, ⟨by linarith, by linarith⟩, hy⟩
  · rintro (⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩)
    · have hx2 := lower_snd S₁ x
      rw [hxt] at hx2
      constructor <;> linarith [hx.1, hx.2]
    · have hy2 := upper_snd S₂ y
      rw [hyt] at hy2
      constructor <;> linarith [hy.1, hy.2]

/-- Near height `0` the composite is the cylinder over `K₀`, as `S₁` is. -/
private theorem exists_pos_range_stackMap_inter_snd_le :
    ∃ ε > 0, range (stackMap S₁ S₂) ∩ {p | p.2 ≤ ε} = range K₀ ×ˢ Iic ε := by
  obtain ⟨ε₀, hε₀, h₀⟩ := S₁.exists_pos_range_inter_snd_le
  refine ⟨min (ε₀ / 2) (1 / 8), lt_min (half_pos hε₀) (by norm_num), Set.ext fun p ↦ ?_⟩
  have hq := quarter_le_sub S₁
  have h₂ := half_lt_add S₂
  have hm₁ := min_le_left (ε₀ / 2) (1 / 8)
  have hm₂ := min_le_right (ε₀ / 2) (1 / 8)
  have key := Set.ext_iff.1 h₀ (p.1, 2 * p.2)
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Iic] at key ⊢
  constructor
  · rintro ⟨hp, hle⟩
    rcases (mem_range_stackMap_iff S₁ S₂).1 hp with ⟨hl, -⟩ | ⟨-, hu⟩
    · exact ⟨(key.1 ⟨(mem_range_lower_iff S₁).1 hl, by linarith⟩).1, hle⟩
    · linarith
  · rintro ⟨hK, hle⟩
    refine ⟨(mem_range_stackMap_iff S₁ S₂).2
      (.inl ⟨(mem_range_lower_iff S₁).2 (key.2 ⟨hK, by linarith⟩).1, by linarith⟩), hle⟩

/-- Near height `1` the composite is the cylinder over `K₂`, as `S₂` is. -/
private theorem exists_pos_range_stackMap_inter_le_snd :
    ∃ ε > 0, range (stackMap S₁ S₂) ∩ {p | 1 - ε ≤ p.2} = range K₂ ×ˢ Ici (1 - ε) := by
  obtain ⟨ε₃, hε₃, h₃⟩ := S₂.exists_pos_range_inter_le_snd
  refine ⟨min (ε₃ / 2) (1 / 8), lt_min (half_pos hε₃) (by norm_num), Set.ext fun p ↦ ?_⟩
  have hq := add_le_three_quarters S₂
  have h₁ := sub_lt_half S₁
  have hm₁ := min_le_left (ε₃ / 2) (1 / 8)
  have hm₂ := min_le_right (ε₃ / 2) (1 / 8)
  have key := Set.ext_iff.1 h₃ (p.1, 2 * p.2 - 1)
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ici] at key ⊢
  constructor
  · rintro ⟨hp, hle⟩
    rcases (mem_range_stackMap_iff S₁ S₂).1 hp with ⟨-, hl⟩ | ⟨hu, -⟩
    · linarith
    · exact ⟨(key.1 ⟨(mem_range_upper_iff S₂).1 hu, by linarith⟩).1, hle⟩
  · rintro ⟨hK, hle⟩
    refine ⟨(mem_range_stackMap_iff S₁ S₂).2
      (.inr ⟨(mem_range_upper_iff S₂).2 (key.2 ⟨hK, by linarith⟩).1, by linarith⟩), hle⟩

/-! ### Orientability of the composite -/

/-- The overlap of the two parts, read in the lower part: the points above height
`(1 - topWidth S₁) / 2` in the lower half, where it is the cylinder over `K₁`. -/
private def overlap : TopologicalSpace.Opens (lowerPiece S₁ S₂) :=
  ⟨{q | (1 - topWidth S₁) / 2 < (lower S₁ q).2}, isOpen_lt continuous_const (continuous_snd.comp
    ((isSmoothEmbedding_lower S₁).isEmbedding.continuous.comp continuous_subtype_val))⟩

private theorem exists_upper_eq_lower (w : overlap S₁ S₂) :
    ∃ y : upperPiece S₁ S₂, upper S₂ y = lower S₁ (w : lowerPiece S₁ S₂) := by
  obtain ⟨y, hy⟩ := (mem_range_lower_iff_mem_range_upper S₁ S₂ w.2.le
    ((mem_lowerPiece_iff S₁ S₂).1 (w : lowerPiece S₁ S₂).2).le).1 (mem_range_self _)
  exact ⟨⟨y, (mem_upperPiece_iff S₁ S₂).2 (hy ▸ w.2)⟩, hy⟩

/-- The transition from the overlap, in the lower part, to the upper part: the point of the upper
part with the same image. -/
private def transition (w : overlap S₁ S₂) : upperPiece S₁ S₂ :=
  (exists_upper_eq_lower S₁ S₂ w).choose

private theorem upper_transition (w : overlap S₁ S₂) :
    upper S₂ (transition S₁ S₂ w) = lower S₁ (w : lowerPiece S₁ S₂) :=
  (exists_upper_eq_lower S₁ S₂ w).choose_spec

private theorem upper_injective : Injective fun y : upperPiece S₁ S₂ ↦ upper S₂ y :=
  fun _ _ h ↦ Subtype.ext ((isSmoothEmbedding_upper S₂).isEmbedding.injective h)

/-- On the overlap, the transition followed by the upper part is the inclusion followed by the
lower part. -/
private theorem proj_inr_comp_transition :
    (proj S₁ S₂ ∘ Sum.inr) ∘ transition S₁ S₂ = (proj S₁ S₂ ∘ Sum.inl) ∘ Subtype.val :=
  funext fun w ↦ (proj_eq_proj_iff S₁ S₂).2 (upper_transition S₁ S₂ w)

private theorem contMDiff_transition :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ (transition S₁ S₂) := by
  intro w
  have hT := congrFun (proj_inr_comp_transition S₁ S₂)
  obtain ⟨τ, hτ, -, hτeq⟩ := exists_deck S₁ S₂ (isOpenEmbedding_proj_inr S₁ S₂)
    (isImmersionAt_upper_val S₁ S₂ (transition S₁ S₂ w)) (hT w).symm
  have hinl : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞
      (Sum.inl ∘ Subtype.val : overlap S₁ S₂ → Pieces S₁ S₂) :=
    ContMDiff.inl.comp contMDiff_subtype_val
  refine (hτ.comp w (hinl w)).congr_of_eventuallyEq ?_
  filter_upwards [hinl.continuous.continuousAt.preimage_mem_nhds hτeq] with w' hw'
  exact (isOpenEmbedding_proj_inr S₁ S₂).injective ((hT w').trans hw'.symm)

private theorem isInvertible_mfderiv_transition (w : overlap S₁ S₂) :
    (mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) (transition S₁ S₂) w).IsInvertible := by
  -- `proj ∘ inr ∘ transition = proj ∘ inl ∘ val` is a local diffeomorphism, and cancelling the
  -- local diffeomorphism `proj ∘ inr` makes `transition` one.
  have hcomp : IsLocalDiffeomorphAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞
      ((proj S₁ S₂ ∘ Sum.inr) ∘ transition S₁ S₂) w := by
    rw [proj_inr_comp_transition]
    exact (isLocalDiffeomorph_subtype_val w).comp
      (hg := isLocalDiffeomorph_proj_inl S₁ S₂ (w : lowerPiece S₁ S₂))
  exact (hcomp.of_comp_left (isLocalDiffeomorph_proj_inr S₁ S₂ (transition S₁ S₂ w))
    (contMDiff_transition S₁ S₂).continuous.continuousAt).isInvertible_mfderiv (NeZero.ne ∞)

/-- The index type of orientations of surfaces modelled on `ℝ¹ × ℝ`. -/
private abbrev OrientationIndex : Type :=
  Fin (finrank ℝ (EuclideanSpace ℝ (Fin 1) × ℝ))

private theorem mem_overlap_iff {q : lowerPiece S₁ S₂} :
    q ∈ overlap S₁ S₂ ↔ (1 - topWidth S₁) / 2 < (lower S₁ q).2 :=
  Iff.rfl

/-- The overlap is connected: its image is the cylinder over `K₁` over an open interval of
heights. -/
private instance : PreconnectedSpace (overlap S₁ S₂) := by
  let g : overlap S₁ S₂ → sphere (0 : E) 1 × ℝ :=
    fun w ↦ lower S₁ ((w : lowerPiece S₁ S₂) : S₁.carrier)
  have hg : IsEmbedding g := ((isSmoothEmbedding_lower S₁).isEmbedding.comp
    IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal
  have hrange : range g = range K₁ ×ˢ Ioo ((1 - topWidth S₁) / 2) ((1 + botWidth S₂) / 2) := by
    ext p
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(mem_range_lower_iff_of_le S₁ ((mem_overlap_iff S₁ S₂).1 w.2).le).1
        (mem_range_self _), (mem_overlap_iff S₁ S₂).1 w.2,
        (mem_lowerPiece_iff S₁ S₂).1 (w : lowerPiece S₁ S₂).2⟩
    · rintro ⟨hK, h₁, h₂⟩
      obtain ⟨x, hx⟩ := (mem_range_lower_iff_of_le S₁ h₁.le).2 hK
      exact ⟨⟨⟨x, (mem_lowerPiece_iff S₁ S₂).2 (hx ▸ h₂)⟩, (mem_overlap_iff S₁ S₂).2 (hx ▸ h₁)⟩,
        hx⟩
  refine ⟨hg.isInducing.isPreconnected_image.1 ?_⟩
  rw [image_univ, hrange]
  exact (isPreconnected_range K₁.isEmbedding.continuous).prod isPreconnected_Ioo

open Manifold.Orientation

/-- The transition from the overlap to the upper part preserves orientation from `o₁` to `o₂`. -/
private def TransitionPreserves
    (o₁ : Manifold.Orientation ((𝓡 1).prod 𝓘(ℝ)) (lowerPiece S₁ S₂) OrientationIndex)
    (o₂ : Manifold.Orientation ((𝓡 1).prod 𝓘(ℝ)) (upperPiece S₁ S₂) OrientationIndex) : Prop :=
  ∀ w : overlap S₁ S₂,
    IsOrientationPreservingAt (o₁.restrict (overlap S₁ S₂)) o₂ (transition S₁ S₂) w

/-- Orientations of `S₁` and `S₂`, restricted to the two parts, can be chosen so that the transition
preserves orientation on the overlap: the overlap is connected, so the restricted orientation of
`S₁` there is either the pullback of that of `S₂` or its opposite. -/
private theorem exists_transitionPreserves : ∃ o₁ o₂, TransitionPreserves S₁ S₂ o₁ o₂ := by
  obtain ⟨o₁⟩ := S₁.orientable.nonempty_orientation
  obtain ⟨o₂⟩ := S₂.orientable.nonempty_orientation
  have hT := (contMDiff_transition S₁ S₂).of_le (m := 1)
    (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne ∞))
  rcases ((o₁.restrict (lowerPiece S₁ S₂)).restrict (overlap S₁ S₂)).eq_or_eq_neg
    ((o₂.restrict (upperPiece S₁ S₂)).pullback hT (isInvertible_mfderiv_transition S₁ S₂)
      o₂.card_eq) with h | h
  · refine ⟨o₁.restrict (lowerPiece S₁ S₂), o₂.restrict (upperPiece S₁ S₂), fun w ↦ ?_⟩
    rw [h]
    exact isOrientationPreservingAt_pullback _ _ _ _ w
  · refine ⟨o₁.restrict (lowerPiece S₁ S₂), -o₂.restrict (upperPiece S₁ S₂), fun w ↦ ?_⟩
    rw [h, ← pullback_neg]
    exact isOrientationPreservingAt_pullback _ _ _ _ w

/-- The surface of the composite is orientable: the orientations of the two parts, chosen to agree
on the overlap, glue to an orientation of the composite. -/
private instance : Orientable ((𝓡 1).prod 𝓘(ℝ)) (Stack S₁ S₂) := by
  obtain ⟨o₁, o₂, ho⟩ := exists_transitionPreserves S₁ S₂
  have hcover : range (proj S₁ S₂ ∘ Sum.inl) ∪ range (proj S₁ S₂ ∘ Sum.inr) = univ := by
    refine eq_univ_of_forall fun t ↦ ?_
    obtain ⟨x | y, rfl⟩ := proj_surjective S₁ S₂ t
    exacts [.inl ⟨x, rfl⟩, .inr ⟨y, rfl⟩]
  refine ⟨⟨glue (o₁ := o₁) (o₂ := o₂) (isLocalDiffeomorph_proj_inl S₁ S₂)
    (isLocalDiffeomorph_proj_inr S₁ S₂) (isOpenEmbedding_proj_inl S₁ S₂).injective
    (isOpenEmbedding_proj_inr S₁ S₂).injective hcover fun x y hxy ↦ ?_⟩⟩
  -- The point `x` lies in the overlap, and `y` is its transition.
  have hw : lower S₁ x = upper S₂ y := by
    simpa only [piecesMap_inl, piecesMap_inr] using (proj_eq_proj_iff S₁ S₂).1 hxy
  have hx : x ∈ overlap S₁ S₂ := by
    rw [mem_overlap_iff, hw]
    exact (mem_upperPiece_iff S₁ S₂).1 y.2
  obtain rfl : transition S₁ S₂ ⟨x, hx⟩ = y :=
    upper_injective S₁ S₂ ((upper_transition S₁ S₂ ⟨x, hx⟩).trans hw)
  -- Both are read off the overlap, by the inclusion into the lower part and by the transition.
  exact (map_orientationAt_eq_of_comp_eventuallyEq (isLocalDiffeomorph_proj_inl S₁ S₂)
    (isLocalDiffeomorph_proj_inr S₁ S₂) (isOrientationPreservingAt_restrict o₁ _ ⟨x, hx⟩)
    (ho ⟨x, hx⟩) ((isLocalDiffeomorph_subtype_val _).mdifferentiableAt (NeZero.ne ∞))
    ((contMDiff_transition S₁ S₂ _).mdifferentiableAt (NeZero.ne ∞))
    (.of_eq (proj_inr_comp_transition S₁ S₂).symm) :)

/-! ### The composite -/

/-- **Composing knot cobordisms.** A knot cobordism `S₁` from `K₀` to `K₁` followed by a knot
cobordism `S₂` from `K₁` to `K₂` is a knot cobordism from `K₀` to `K₂`: the surface of `S₁` with
its heights halved, so that its part over `Sⁿ × [0, 1]` goes to the heights `[0, 1 / 2]`, stacked
on the surface of `S₂` with its heights `t` moved to `(t + 1) / 2`, so that its part over
`Sⁿ × [0, 1]` goes to `[1 / 2, 1]`; the cylinder ends go along. Near the level `1 / 2` both are the
cylinder over `K₁`, so the two surfaces are glued along a neighbourhood of the circle
`K₁ × {1 / 2}`. -/
def trans : KnotCobordism K₀ K₂ where
  carrier := Stack S₁ S₂
  toFun := stackMap S₁ S₂
  isSmoothEmbedding := isSmoothEmbedding_stackMap S₁ S₂
  isCompact_preimage_Icc := isCompact_preimage_Icc_stackMap S₁ S₂
  exists_pos_range_inter_snd_le := exists_pos_range_stackMap_inter_snd_le S₁ S₂
  exists_pos_range_inter_le_snd := exists_pos_range_stackMap_inter_le_snd S₁ S₂

/-- **The lower half of the composite.** At heights at most `1 / 2`, the composite is the part of
the surface of `S₁` at heights at most `1`, with its heights halved. -/
theorem range_toFun_trans_inter_snd_le :
    range (S₁.trans S₂).toFun ∩ {p | p.2 ≤ 1 / 2} =
      (fun p ↦ (p.1, p.2 / 2)) '' (range S₁.toFun ∩ {p | p.2 ≤ 1}) := by
  have h₂ := half_lt_add S₂
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hp, hle⟩
    obtain ⟨x, rfl⟩ := mem_range_lower_of_mem_range_stackMap S₁ S₂ hp hle
    exact ⟨S₁.toFun x, ⟨mem_range_self x, by linarith [lower_snd S₁ x]⟩, rfl⟩
  · rintro ⟨_, ⟨⟨x, rfl⟩, hx⟩, rfl⟩
    refine ⟨(mem_range_stackMap_iff S₁ S₂).2 (.inl ⟨mem_range_self x, ?_⟩), ?_⟩ <;>
      linarith [lower_snd S₁ x]

/-- **The upper half of the composite.** At heights at least `1 / 2`, the composite is the part of
the surface of `S₂` at heights at least `0`, with its heights `t` moved to `(t + 1) / 2`. -/
theorem range_toFun_trans_inter_le_snd :
    range (S₁.trans S₂).toFun ∩ {p | 1 / 2 ≤ p.2} =
      (fun p ↦ (p.1, (p.2 + 1) / 2)) '' (range S₂.toFun ∩ {p | 0 ≤ p.2}) := by
  have h₁ := sub_lt_half S₁
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hp, hle⟩
    obtain ⟨y, rfl⟩ := mem_range_upper_of_mem_range_stackMap S₁ S₂ hp hle
    exact ⟨S₂.toFun y, ⟨mem_range_self y, by linarith [upper_snd S₂ y]⟩, rfl⟩
  · rintro ⟨_, ⟨⟨y, rfl⟩, hy⟩, rfl⟩
    refine ⟨(mem_range_stackMap_iff S₁ S₂).2 (.inr ⟨mem_range_self y, ?_⟩), ?_⟩ <;>
      linarith [upper_snd S₂ y]

/-- **The surface of the composite** is the part of `S₁` at heights at most `1`, with its heights
halved, together with the part of `S₂` at heights at least `0`, with its heights `t` moved to
`(t + 1) / 2`. -/
@[simp]
theorem range_toFun_trans :
    range (S₁.trans S₂).toFun =
      (fun p ↦ (p.1, p.2 / 2)) '' (range S₁.toFun ∩ {p | p.2 ≤ 1}) ∪
        (fun p ↦ (p.1, (p.2 + 1) / 2)) '' (range S₂.toFun ∩ {p | 0 ≤ p.2}) := by
  have h : {p : sphere (0 : E) 1 × ℝ | p.2 ≤ 1 / 2} ∪ {p | 1 / 2 ≤ p.2} = univ :=
    eq_univ_of_forall fun p ↦ le_total p.2 (1 / 2)
  rw [← range_toFun_trans_inter_snd_le, ← range_toFun_trans_inter_le_snd,
    ← inter_union_distrib_left, h, inter_univ]

end KnotCobordism

end TauCeti
