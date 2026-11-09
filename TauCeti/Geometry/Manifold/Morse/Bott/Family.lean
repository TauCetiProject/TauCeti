/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
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
(`TauCeti.IsMorseBottFamily.isClosed_range`). The same family exhibits `-f` as a Morse–Bott
function (`TauCeti.IsMorseBottFamily.neg`).

Morse functions are the zero-dimensional case. On a boundaryless finite-dimensional manifold, a
critical point is nondegenerate exactly when the piece through it is modelled on a trivial space
(`TauCeti.IsMorseBottFamily.isManifoldNondegenerateCriticalPoint_iff`); so a function with a
Morse–Bott family of zero-dimensional pieces is Morse
(`TauCeti.IsMorseBottFamily.isMorse_of_subsingleton`), and conversely the critical points of a
Morse function, each included as a point, form a Morse–Bott family
(`TauCeti.IsMorse.exists_isMorseBottFamily`). At the other extreme, a constant function on a
nonempty connected manifold without boundary is Morse–Bott with the whole manifold as its only
critical submanifold (`TauCeti.isMorseBottFamily_const`).

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

end TauCeti
