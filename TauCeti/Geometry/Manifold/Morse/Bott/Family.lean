/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Topology.ConnectedComponents
import TauCeti.Geometry.Manifold.Morse.Bott.Lemma
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
import TauCeti.Topology.Connected.Basic

/-!
# Morse–Bott functions

A function `f` on a manifold `M` is **Morse–Bott** when its critical set is a disjoint union of
nondegenerate critical submanifolds. Different components of the critical set may have different
dimensions, so the critical set is presented by a family of smooth embeddings `i a : S a → M`,
each modelled on its own space. The family **exhibits `f` as a Morse–Bott function**
(`TauCeti.IsMorseBottFamily`) when

* `f` is smooth, as for Morse functions (`TauCeti.IsMorse`);
* each `i a` is a nondegenerate critical submanifold of `f`
  (`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`): along its image the kernel of
  the critical Hessian is exactly the tangent space of the image;
* each piece `S a` is a nonempty manifold without boundary, as in Bott's definition; a critical
  half-line, say, is not a Morse–Bott critical submanifold;
* the images `range (i a)` are exactly the connected components of the critical set, each
  occurring for exactly one index;
* the family of images is locally finite.

The index set is what the Morse–Bott inequalities sum over: each critical component contributes
the Poincaré polynomial of its piece, with coefficients twisted by the orientation of its negative
normal bundle, multiplied by `t` to the power of its index.

So the pieces are pairwise disjoint and cover the critical set
(`TauCeti.IsMorseBottFamily.pairwise_disjoint_range`, `TauCeti.IsMorseBottFamily.iUnion_range`),
each critical point lies on exactly one of them
(`TauCeti.IsMorseBottFamily.existsUnique_mem_range`), only finitely many of them meet a compact set
(by `LocallyFinite.finite_nonempty_inter_compact`), and on a compact manifold there are finitely
many (`TauCeti.IsMorseBottFamily.finite`). Each piece is closed
(`TauCeti.IsMorseBottFamily.isClosed_range`). The function takes a single value on each piece
(`TauCeti.IsMorseBottFamily.subsingleton_image_range`), so on a compact manifold it has finitely
many critical values (`TauCeti.IsMorseBottFamily.finite_image_criticalPoints`). The same family
exhibits `-f` as a Morse–Bott function (`TauCeti.IsMorseBottFamily.neg`). The conditions only
involve the underlying maps of the embeddings, so a family with the same maps and possibly another
order of smoothness is again Morse–Bott (`TauCeti.IsMorseBottFamily.congr`).

Conversely, the last two conditions follow from the first three once the pieces are known to
partition the critical set. A Morse–Bott critical submanifold is isolated in the critical set, so
if `f` is smooth and the images of `C²` nondegenerate critical submanifolds with nonempty
preconnected sources are pairwise disjoint and cover the critical set, each image is closed, hence
a connected component of the critical set, and the family is locally finite
(`TauCeti.IsMorseBottFamily.of_pairwise_disjoint`). This is how a Morse–Bott family is built from
a description of the critical set as a disjoint union of nondegenerate critical submanifolds.

Morse functions are the zero-dimensional case. On a boundaryless finite-dimensional manifold, a
critical point is nondegenerate exactly when the piece through it is modelled on a trivial space
(`TauCeti.IsMorseBottFamily.isManifoldNondegenerateCriticalPoint_iff`); so a function with a
Morse–Bott family of zero-dimensional pieces is Morse
(`TauCeti.IsMorseBottFamily.isMorse_of_subsingleton`), and conversely the critical points of a
Morse function, each included as a point, form a Morse–Bott family
(`TauCeti.IsMorse.exists_isMorseBottFamily`). At the other extreme, a constant function on a
nonempty connected manifold without boundary is Morse–Bott with the whole manifold as its only
critical submanifold (`TauCeti.isMorseBottFamily_const`). Without connectedness, on a locally
connected manifold without boundary, a constant function is Morse–Bott with one critical
submanifold for each connected component, embedded as an open subset
(`TauCeti.isMorseBottFamily_ofOpens_const`). Each of these pieces has full dimension, so its
normal spaces are zero (`TauCeti.SmoothEmbedding.subsingleton_normalSpace_ofOpens`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {E' : ι → Type*} [∀ a, NormedAddCommGroup (E' a)] [∀ a, NormedSpace ℝ (E' a)]
  {H' : ι → Type*} [∀ a, TopologicalSpace (H' a)] {J : ∀ a, ModelWithCorners ℝ (E' a) (H' a)}
  {S : ι → Type*} [∀ a, TopologicalSpace (S a)] [∀ a, ChartedSpace (H' a) (S a)]
  {n : ℕ∞ω} {i : ∀ a, SmoothEmbedding (J a) I n (S a) M} {f : M → ℝ} {x : M}

/-- A family of smooth embeddings `i a : S a → M`, each modelled on its own space, **exhibits `f`
as a Morse–Bott function** when `f` is smooth, each `i a` is a nondegenerate critical submanifold
of `f` whose source is a nonempty manifold without boundary, the images of the `i a` are exactly
the connected components of the critical set of `f`, each occurring for exactly one index, and the
family of images is locally finite. -/
structure IsMorseBottFamily (i : ∀ a, SmoothEmbedding (J a) I n (S a) M) (f : M → ℝ) : Prop where
  /-- The function is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ) ∞ f
  /-- Each piece is a nondegenerate critical submanifold. -/
  isNondegenerateCriticalSubmanifold (a : ι) : (i a).IsNondegenerateCriticalSubmanifold f
  /-- Each piece is nonempty. -/
  nonempty (a : ι) : Nonempty (S a)
  /-- Each piece is a manifold without boundary. -/
  boundarylessManifold (a : ι) : BoundarylessManifold (J a) (S a)
  /-- The image of each piece is the connected component of the critical set through any of its
  points. -/
  range_eq_connectedComponentIn (a : ι) (s : S a) :
    range (i a) = connectedComponentIn (criticalPoints I f) (i a s)
  /-- Distinct indices give distinct pieces. -/
  range_injective : Injective fun a ↦ range (i a)
  /-- Every critical point lies on some piece. -/
  criticalPoints_subset_iUnion_range : criticalPoints I f ⊆ ⋃ a, range (i a)
  /-- The family of pieces is locally finite. -/
  locallyFinite_range : LocallyFinite fun a ↦ range (i a)

namespace IsMorseBottFamily

variable (h : IsMorseBottFamily i f)
include h

/-- Every point of a piece is a critical point. -/
theorem range_subset_criticalPoints (a : ι) : range (i a) ⊆ criticalPoints I f := by
  rintro _ ⟨s, rfl⟩
  exact (h.isNondegenerateCriticalSubmanifold a).mem_criticalPoints s

/-- The pieces cover exactly the critical set. -/
theorem iUnion_range : ⋃ a, range (i a) = criticalPoints I f :=
  (iUnion_subset h.range_subset_criticalPoints).antisymm h.criticalPoints_subset_iUnion_range

/-- A point is critical exactly when it lies on some piece. -/
theorem mem_criticalPoints_iff : x ∈ criticalPoints I f ↔ ∃ a, x ∈ range (i a) := by
  rw [← h.iUnion_range, mem_iUnion]

/-- The image of a piece is the connected component of the critical set through any of its
points. -/
theorem range_eq_connectedComponentIn_of_mem (a : ι) (hx : x ∈ range (i a)) :
    range (i a) = connectedComponentIn (criticalPoints I f) x := by
  obtain ⟨s, rfl⟩ := hx
  exact h.range_eq_connectedComponentIn a s

/-- Every connected component of the critical set is the image of a piece. -/
theorem exists_range_eq_connectedComponentIn (hx : x ∈ criticalPoints I f) :
    ∃ a, range (i a) = connectedComponentIn (criticalPoints I f) x := by
  obtain ⟨a, ha⟩ := h.mem_criticalPoints_iff.1 hx
  exact ⟨a, h.range_eq_connectedComponentIn_of_mem a ha⟩

/-- Distinct pieces are disjoint. -/
theorem pairwise_disjoint_range : Pairwise (Disjoint on fun a ↦ range (i a)) := by
  intro a b hab
  exact disjoint_left.2 fun x hxa hxb ↦ hab (h.range_injective
    ((h.range_eq_connectedComponentIn_of_mem a hxa).trans
      (h.range_eq_connectedComponentIn_of_mem b hxb).symm))

/-- Each critical point lies on exactly one piece. -/
theorem existsUnique_mem_range (hx : x ∈ criticalPoints I f) : ∃! a, x ∈ range (i a) := by
  obtain ⟨a, ha⟩ := h.mem_criticalPoints_iff.1 hx
  refine ⟨a, ha, fun b hb ↦ ?_⟩
  by_contra hba
  exact disjoint_left.1 (h.pairwise_disjoint_range hba) hb ha

/-- On a compact manifold a Morse–Bott family has finitely many pieces. -/
theorem finite [CompactSpace M] : Finite ι :=
  finite_univ_iff.1 <| h.locallyFinite_range.finite_of_compact fun a ↦
    have := h.nonempty a
    range_nonempty (i a)

/-- Each piece is closed, as a connected component of the closed critical set. -/
theorem isClosed_range [IsManifold I 1 M] (a : ι) : IsClosed (range (i a)) := by
  obtain ⟨s⟩ := h.nonempty a
  rw [h.range_eq_connectedComponentIn a s]
  exact (isClosed_criticalPoints (h.contMDiff.of_le (by simp))).connectedComponentIn

/-- **A Morse–Bott function takes a single value on each piece**, its critical value: `f ∘ i a` is
locally constant, and the piece is connected because its image is a connected component of the
critical set. -/
theorem subsingleton_image_range [∀ a, IsManifold (J a) 1 (S a)] (hn : n ≠ 0) (a : ι) :
    (f '' range (i a)).Subsingleton := by
  obtain ⟨s₀⟩ := h.nonempty a
  have : PreconnectedSpace (S a) := by
    refine ⟨(i a).isEmbedding.isInducing.isPreconnected_image.1 ?_⟩
    rw [image_univ, h.range_eq_connectedComponentIn a s₀]
    exact isPreconnected_connectedComponentIn
  have hloc :=
    (h.isNondegenerateCriticalSubmanifold a).toIsCriticalSubmanifold.isLocallyConstant_comp hn
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩ _ ⟨_, ⟨s', rfl⟩, rfl⟩
  exact hloc.apply_eq_of_preconnectedSpace s s'

/-- **A Morse–Bott function on a compact manifold has finitely many critical values**: it has
finitely many pieces and takes a single value on each. -/
theorem finite_image_criticalPoints [CompactSpace M] [∀ a, IsManifold (J a) 1 (S a)]
    (hn : n ≠ 0) : (f '' criticalPoints I f).Finite := by
  have := h.finite
  rw [← h.iUnion_range, image_iUnion]
  exact finite_iUnion fun a ↦ (h.subsingleton_image_range hn a).finite

/-- A Morse–Bott family of `f` is also a Morse–Bott family of `-f`. -/
theorem neg : IsMorseBottFamily i (-f) where
  contMDiff := contDiff_neg.contMDiff.comp h.contMDiff
  isNondegenerateCriticalSubmanifold a := (h.isNondegenerateCriticalSubmanifold a).neg
  nonempty := h.nonempty
  boundarylessManifold := h.boundarylessManifold
  range_eq_connectedComponentIn a s := by
    rw [criticalPoints_neg]
    exact h.range_eq_connectedComponentIn a s
  range_injective := h.range_injective
  criticalPoints_subset_iUnion_range := by
    rw [criticalPoints_neg]
    exact h.criticalPoints_subset_iUnion_range
  locallyFinite_range := h.locallyFinite_range

/-- A Morse–Bott family depends on the embeddings only through their underlying maps, so it passes
to a family of embeddings with the same maps and possibly another order of smoothness. -/
theorem congr {n' : ℕ∞ω} {i' : ∀ a, SmoothEmbedding (J a) I n' (S a) M}
    (hi : ∀ a, ⇑(i' a) = ⇑(i a)) : IsMorseBottFamily i' f where
  contMDiff := h.contMDiff
  isNondegenerateCriticalSubmanifold a := (h.isNondegenerateCriticalSubmanifold a).congr (hi a)
  nonempty := h.nonempty
  boundarylessManifold := h.boundarylessManifold
  range_eq_connectedComponentIn a s := by
    rw [hi]
    exact h.range_eq_connectedComponentIn a s
  range_injective := by simpa only [hi] using h.range_injective
  criticalPoints_subset_iUnion_range := by
    simpa only [hi] using h.criticalPoints_subset_iUnion_range
  locallyFinite_range := by simpa only [hi] using h.locallyFinite_range

omit h in
/-- A family exhibits `-f` as a Morse–Bott function exactly when it exhibits `f` as one. -/
@[simp]
theorem _root_.TauCeti.isMorseBottFamily_neg_iff :
    IsMorseBottFamily i (-f) ↔ IsMorseBottFamily i f :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, IsMorseBottFamily.neg⟩

section Boundaryless

variable [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 2 M]

/-- A critical point is nondegenerate exactly when the piece through it is modelled on a trivial
space, that is, is zero-dimensional. -/
theorem isManifoldNondegenerateCriticalPoint_iff (hn : n ≠ 0) {a : ι} (hx : x ∈ range (i a)) :
    IsManifoldNondegenerateCriticalPoint I f x ↔ Subsingleton (E' a) := by
  obtain ⟨s, rfl⟩ := hx
  refine ⟨fun hs ↦ ?_, fun _ ↦ ?_⟩
  · exact (h.isNondegenerateCriticalSubmanifold a).toIsCriticalSubmanifold
      |>.subsingleton_of_isManifoldNondegenerateCriticalPoint hn hs
  · exact SmoothEmbedding.isNondegenerateCriticalSubmanifold_iff_of_subsingleton.1
      (h.isNondegenerateCriticalSubmanifold a) s

/-- **Zero-dimensional Morse–Bott functions are Morse.** A function with a Morse–Bott family whose
pieces are all modelled on trivial spaces is a Morse function. -/
theorem isMorse_of_subsingleton [∀ a, Subsingleton (E' a)] (hn : n ≠ 0) : IsMorse I f := by
  refine isMorseOn_univ.1
    (isMorseOn_iff_criticalPoints.2 ⟨h.contMDiff.contMDiffOn, fun x _ hx ↦ ?_⟩)
  obtain ⟨a, ha⟩ := h.mem_criticalPoints_iff.1 hx
  exact (h.isManifoldNondegenerateCriticalPoint_iff hn ha).2 inferInstance

end Boundaryless

end IsMorseBottFamily

/-- **Morse–Bott critical submanifolds partitioning the critical set form a Morse–Bott family.**
Let `f` be smooth and let each `i a` be a `C²` nondegenerate critical submanifold of `f`, with a
nonempty preconnected source modelled without boundary. If the images of the `i a` are pairwise
disjoint and cover the critical set, then they are exactly the connected components of the
critical set and form a locally finite family, so the family exhibits `f` as a Morse–Bott
function. -/
theorem IsMorseBottFamily.of_pairwise_disjoint [I.Boundaryless] [FiniteDimensional ℝ E]
    [IsManifold I 2 M] [∀ a, (J a).Boundaryless] [∀ a, Nonempty (S a)]
    [∀ a, PreconnectedSpace (S a)] (hn : 2 ≤ n) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hi : ∀ a, (i a).IsNondegenerateCriticalSubmanifold f)
    (hdisj : Pairwise (Disjoint on fun a ↦ range (i a)))
    (hcover : criticalPoints I f ⊆ ⋃ a, range (i a)) : IsMorseBottFamily i f := by
  choose U hUo hU using fun a ↦ (hi a).exists_isOpen_criticalPoints_inter_eq_range hn
  have hcrit : IsClosed (criticalPoints I f) := isClosed_criticalPoints (hf.of_le (by simp))
  have hrange (a : ι) : range (i a) ⊆ criticalPoints I f := by
    rintro _ ⟨s, rfl⟩
    exact (hi a).mem_criticalPoints s
  have hrangeU (a : ι) : range (i a) ⊆ U a := fun x hx ↦ by
    rw [← hU a] at hx
    exact hx.2
  -- A point of the `b`-th piece lying in `U a` forces `b = a`.
  have hindex {a b : ι} {x : M} (hxb : x ∈ range (i b)) (hxU : x ∈ U a) : b = a := by
    by_contra hba
    have hxa : x ∈ range (i a) := by
      rw [← hU a]
      exact ⟨hrange b hxb, hxU⟩
    exact disjoint_left.1 (hdisj hba : Disjoint (range (i b)) (range (i a))) hxb hxa
  -- Each piece is closed: within the closed critical set, it is the complement of the open sets
  -- `U b` cutting out the other pieces.
  have hclosed (a : ι) : IsClosed (range (i a)) := by
    have heq : range (i a) = criticalPoints I f ∩ (⋃ b, ⋃ (_ : b ≠ a), U b)ᶜ := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, not_exists]
      refine ⟨fun hx ↦ ⟨hrange a hx, fun b hba hxU ↦ hba (hindex hx hxU).symm⟩,
        fun ⟨hx, hxU⟩ ↦ ?_⟩
      obtain ⟨b, hb⟩ := mem_iUnion.1 (hcover hx)
      by_cases hba : b = a
      · exact hba ▸ hb
      · exact absurd (hrangeU b hb) (hxU b hba)
    rw [heq]
    exact hcrit.inter (isOpen_iUnion fun b ↦ isOpen_iUnion fun _ ↦ hUo b).isClosed_compl
  refine
    { contMDiff := hf
      isNondegenerateCriticalSubmanifold := hi
      nonempty := inferInstance
      boundarylessManifold := fun _ ↦ inferInstance
      range_eq_connectedComponentIn := fun a s ↦
        (hi a).range_eq_connectedComponentIn hn (hclosed a) s
      range_injective := fun a b hab ↦ by_contra fun hba ↦ ?_
      criticalPoints_subset_iUnion_range := hcover
      locallyFinite_range := fun x ↦ ?_ }
  · have hab' : range (i a) = range (i b) := hab
    have hd : Disjoint (range (i a)) (range (i b)) := hdisj hba
    rw [hab'] at hd
    exact (range_nonempty (i b)).ne_empty (disjoint_self.1 hd)
  · -- Near a critical point only its own piece occurs; away from the critical set, none does.
    by_cases hx : x ∈ criticalPoints I f
    · obtain ⟨a, ha⟩ := mem_iUnion.1 (hcover hx)
      exact ⟨U a, (hUo a).mem_nhds (hrangeU a ha),
        (finite_singleton a).subset fun b ⟨_, hyb, hyU⟩ ↦ hindex hyb hyU⟩
    · exact ⟨(criticalPoints I f)ᶜ, hcrit.isOpen_compl.mem_nhds hx,
        finite_empty.subset fun b ⟨_, hyb, hy⟩ ↦ hy (hrange b hyb)⟩

/-- **Morse functions are Morse–Bott.** On a boundaryless finite-dimensional manifold, the
critical points of a Morse function, each included as a point from a trivial model space, form a
Morse–Bott family. -/
theorem IsMorse.exists_isMorseBottFamily [I.Boundaryless] [FiniteDimensional ℝ E]
    [IsManifold I n M] (hf : IsMorse I f) (hn : 1 ≤ n) (Z : Type*) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [Subsingleton Z] :
    ∃ i : ∀ _ : criticalPoints I f, SmoothEmbedding 𝓘(ℝ, Z) I n Z M,
      (∀ a z, i a z = a) ∧ IsMorseBottFamily i f := by
  have : T1Space M := I.t1Space M
  have : IsManifold I 1 M := .of_le hn
  let i : ∀ _ : criticalPoints I f, SmoothEmbedding 𝓘(ℝ, Z) I n Z M := fun a ↦
    .ofIsSmoothEmbedding _ (isSmoothEmbedding_const_of_subsingleton hn (a : M))
  have hrange (a : criticalPoints I f) : range (i a) = {(a : M)} := by
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
    exact range_const
  have hi (a : criticalPoints I f) (z : Z) : i a z = a :=
    SmoothEmbedding.ofIsSmoothEmbedding_apply _ _ _
  refine ⟨i, hi, ⟨hf.contMDiff, fun a ↦ ?_, fun _ ↦ ⟨0⟩, fun _ ↦ inferInstance, fun a z ↦ ?_,
    fun a b hab ↦ ?_, ?_, ?_⟩⟩
  · exact SmoothEmbedding.isNondegenerateCriticalSubmanifold_iff_of_subsingleton.2 fun z ↦
      hi a z ▸ hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints a.2
  · rw [hrange, hi]
    exact (connectedComponentIn_eq_singleton a.2
      (hf.eventually_eq_of_mem_criticalPoints a)).symm
  · simpa [hrange, Subtype.ext_iff] using hab
  · intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, by rw [hrange]; exact mem_singleton x⟩
  · intro x
    obtain ⟨t, ht, hxt⟩ := (hf.eventually_eq_of_mem_criticalPoints x).exists_mem
    refine ⟨t, ht, Set.Subsingleton.finite fun a ha b hb ↦ ?_⟩
    obtain ⟨y, hya, hyt⟩ := ha
    obtain ⟨z, hzb, hzt⟩ := hb
    simp only [hrange, mem_singleton_iff] at hya hzb
    subst hya hzb
    exact Subtype.ext ((hxt _ hyt a.2).trans (hxt _ hzt b.2).symm)

/-- **A constant function is Morse–Bott.** On a nonempty connected manifold without boundary, the
identity embedding exhibits a constant function as a Morse–Bott function, with the whole manifold
as its only critical submanifold. -/
theorem isMorseBottFamily_const [IsManifold I n M] [BoundarylessManifold I M] [ConnectedSpace M]
    (c : ℝ) :
    IsMorseBottFamily (fun _ : Unit ↦ SmoothEmbedding.id (I := I) (n := n) (M := M))
      (fun _ ↦ c) := by
  have hcrit : criticalPoints I (fun _ : M ↦ c) = univ :=
    eq_univ_of_forall fun _ ↦ mem_criticalPoints.2 (mvfderiv_const c)
  have hrange : range (SmoothEmbedding.id (I := I) (n := n) (M := M)) = univ := by
    rw [SmoothEmbedding.coe_id, range_id]
  refine ⟨contMDiff_const, fun _ ↦ SmoothEmbedding.isNondegenerateCriticalSubmanifold_id_const c,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ x ↦ ?_, fun _ _ _ ↦ rfl, ?_,
    (locallyFinite_of_finite _)⟩
  · rw [hrange, hcrit, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  · rw [hcrit]
    exact subset_iUnion_of_subset () hrange.ge

/-- **A constant function is Morse–Bott, with one piece for each connected component.** On a
locally connected manifold without boundary, the inclusions of the connected components, each an
open subset, exhibit a constant function as a Morse–Bott function. Every point is critical, so the
critical set is the whole manifold and its connected components are those of the manifold. No
compactness or connectedness is assumed. -/
theorem isMorseBottFamily_ofOpens_const [IsManifold I n M] [BoundarylessManifold I M]
    [LocallyConnectedSpace M] (hn : n ≠ 0) (c : ℝ) :
    IsMorseBottFamily
      (fun C : ConnectedComponents M ↦ SmoothEmbedding.ofOpens (I := I) (n := n) C.opens)
      (fun _ ↦ c) := by
  have hcrit : criticalPoints I (fun _ : M ↦ c) = univ :=
    eq_univ_of_forall fun _ ↦ mem_criticalPoints.2 (mvfderiv_const c)
  have hrange (C : ConnectedComponents M) :
      range (SmoothEmbedding.ofOpens (I := I) (n := n) C.opens) = C.opens := by
    rw [SmoothEmbedding.coe_ofOpens, Subtype.range_coe]
  have hmem (x : M) : x ∈ ((ConnectedComponents.mk x).opens : Set M) :=
    ConnectedComponents.mem_opens.2 rfl
  refine ⟨contMDiff_const,
    fun C ↦ SmoothEmbedding.isNondegenerateCriticalSubmanifold_ofOpens_const hn C.opens c,
    fun C ↦ ?_, fun _ ↦ inferInstance, fun C x ↦ ?_, fun C D h ↦ ?_, ?_, fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    exact ⟨⟨x, hmem x⟩⟩
  · have hx : ConnectedComponents.mk (x : M) = C := ConnectedComponents.mem_opens.1 x.2
    rw [hrange, hcrit, connectedComponentIn_univ, SmoothEmbedding.ofOpens_apply,
      ← ConnectedComponents.coe_opens_mk, hx]
  · -- A component is recovered from any of its points.
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    have h' : ((ConnectedComponents.mk x).opens : Set M) = D.opens := by
      simpa only [hrange] using h
    have hx : x ∈ (D.opens : Set M) := h' ▸ hmem x
    exact ConnectedComponents.mem_opens.1 hx
  · rw [hcrit]
    exact fun x _ ↦ mem_iUnion.2 ⟨ConnectedComponents.mk x, by rw [hrange]; exact hmem x⟩
  · -- The component of `x` is a neighbourhood of `x` meeting no other component.
    refine ⟨_, (ConnectedComponents.mk x).opens.isOpen.mem_nhds (hmem x),
      (finite_singleton (ConnectedComponents.mk x)).subset fun C ⟨y, hyC, hyx⟩ ↦ ?_⟩
    simp only [hrange, SetLike.mem_coe, ConnectedComponents.mem_opens] at hyC hyx
    exact hyC.symm.trans hyx

end TauCeti
