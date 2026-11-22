/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Breaking

/-!
# The Morse–Smale condition for a pair of pseudo-gradients

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M` of dimension `n`, and
`X₀`, `X₁` pseudo-gradients adapted to them. The pair `(X₀, X₁)` is **Morse–Smale**
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`) when, for all critical points `a` of `f₀` and
`b` of `f₁`, the unstable manifold `W^u_{X₀}(a)` and the stable manifold `W^s_{X₁}(b)` meet
transversally. For `X₀ = X₁` this is the Morse–Smale condition
(`TauCeti.IsAdaptedPseudoGradient.isMorseSmalePair_self_iff`).

This is the transversality condition of continuation maps. A continuation from `(f₀, X₀)` to
`(f₁, X₁)` follows the time-dependent flow of a family of vector fields interpolating between
`X₀` and `X₁`. A continuation trajectory from a critical point `p` of `f₀` to a critical point `q`
of `f₁` starts on `W^u_{X₀}(p)` when the interpolation begins, and ends on `W^s_{X₁}(q)` when it
is over. Carrying `X₁` back along the transition diffeomorphism of the interpolation window
gives a pseudo-gradient adapted to `f₁` composed with that diffeomorphism, whose stable manifolds
are the preimages of those of `X₁`. The continuation trajectories from `p` to `q` then correspond
to the points of `W^u_{X₀}(p) ∩ W^s(q)` for the transported field, and the continuation is
transverse when the transported pair is Morse–Smale. Unlike the trajectories between critical
points of one function, these trajectories are not invariant under a translation of time, so the
intersection is not divided by an action of `ℝ`, and its expected dimension is `ind p - ind q`
rather than `ind p - ind q - 1`. The identification of continuation trajectories with these
intersections is
`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`.

For a Morse–Smale pair the following hold, for critical points `a` of `f₀` and `b` of `f₁`:

* **Dimension.** `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` is flattened near each of its points by a chart of
  the maximal atlas, and is a smooth manifold of dimension `ind a - ind b`
  (`IsMorseSmalePair.exists_unstableSet_inter_stableSet_isManifold`). In particular it is empty
  unless `ind b ≤ ind a` (`IsMorseSmalePair.manifoldMorseIndex_le`), and discrete when
  `ind a = ind b`.
* **Breaking.** If `X₀` and `X₁` are moreover Morse–Smale, a limit of points of
  `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` lies in `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` with `a = p` or
  `ind a < ind p`, and `b = q` or `ind q < ind b`
  (`IsMorseSmalePair.exists_mem_unstableSet_inter_stableSet_of_mem_closure`).
* **Finiteness.** Hence when `ind p ≤ ind q` the intersection is finite
  (`IsMorseSmalePair.finite_unstableSet_inter_stableSet`). Once continuation trajectories are
  identified with these intersections, its points are expected to give the counts of the
  continuation map between Morse complexes.
* **One-dimensional ends.** When `ind p = ind q + 1`, the intersection is one-dimensional, and its
  closure adds only once-broken configurations: a trajectory of `X₀` from `p` to a critical point
  `a` with `ind a = ind q`, followed by a point of `W^u_{X₀}(a) ∩ W^s_{X₁}(q)`, or a point of
  `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` with `ind b = ind p`, followed by a trajectory of `X₁` from `b` to `q`
  (`IsMorseSmalePair.closure_unstableSet_inter_stableSet_subset`). These are the two kinds of
  broken trajectories that pair up in the proof that a continuation map is a chain map.

Reversing both fields exchanges their roles: if `(X₀, X₁)` is Morse–Smale then so is
`(-X₁, -X₀)` (`IsMorseSmalePair.neg`), as for the continuation along the reversed path.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmalePair`: the Morse–Smale condition for a pair of pseudo-gradients.
* `isMorseSmalePair_iff` and `isMorseSmalePair_self_iff`: its unfolding, and the case of a single
  pseudo-gradient.
* `unstableSet_inter_stableSet_eq_neg`: reversing both fields exchanges the unstable and stable
  sets in an intersection.
* `IsMorseSmalePair.neg`: reversing the pair.
* `IsMorseSmalePair.exists_isSliceChart_unstableSet_inter_stableSet`,
  `IsMorseSmalePair.span_mtangentConeAt_unstableSet_inter_stableSet` and
  `IsMorseSmalePair.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex`:
  the intersection is flattened onto the intersection of the tangent spaces, of dimension
  `ind a - ind b`.
* `IsMorseSmalePair.exists_unstableSet_inter_stableSet_isManifold`: the intersection is a smooth
  manifold of dimension `ind a - ind b`.
* `IsMorseSmalePair.manifoldMorseIndex_le` and
  `IsMorseSmalePair.unstableSet_inter_stableSet_eq_empty`: the index cannot increase.
* `IsMorseSmalePair.isDiscrete_unstableSet_inter_stableSet`,
  `IsMorseSmalePair.isClosed_unstableSet_inter_stableSet` and
  `IsMorseSmalePair.finite_unstableSet_inter_stableSet`: when the index does not drop, the
  intersection is discrete, closed and finite.
* `IsMorseSmalePair.exists_mem_unstableSet_inter_stableSet_of_mem_closure` and
  `IsMorseSmalePair.closure_unstableSet_inter_stableSet_subset`: limits of points of the
  intersection break.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (continuation maps, the transversality of the
  time-dependent flow, and the dimension `ind p - ind q` of their moduli spaces).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.2 (the Smale condition) and Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f f₀ f₁ : M → ℝ} {X X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b p q y : M}

namespace IsAdaptedPseudoGradient

/-- **The Morse–Smale condition for a pair of pseudo-gradients** `X₀`, adapted to `f₀`, and `X₁`,
adapted to `f₁`: for all points `a` and `b`, the unstable manifold of `a` for `X₀` and the stable
manifold of `b` for `X₁` meet transversally at each common point `y`, that is, their tangent spaces
at `y` span the tangent space of `M`. The condition only concerns critical points `a` of `f₀` and
`b` of `f₁`, since the other unstable and stable manifolds are empty. -/
def IsMorseSmalePair (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) : Prop :=
  ∀ ⦃a b y : M⦄, y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b →
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤

/-- The unfolding of `TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`. -/
theorem isMorseSmalePair_iff {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} :
    IsMorseSmalePair hX₀ hX₁ ↔ ∀ ⦃a b y : M⦄, y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b →
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤ :=
  Iff.rfl

/-- **A single pseudo-gradient.** The pair `(X, X)` is Morse–Smale exactly when `X` is. -/
@[simp]
theorem isMorseSmalePair_self_iff (hX : IsAdaptedPseudoGradient f X) :
    IsMorseSmalePair hX hX ↔ hX.IsMorseSmale :=
  ⟨fun h ↦ IsMorseSmale.of_forall fun _ _ _ _ _ hy ↦ h hy,
    fun h _ _ _ hy ↦ h.span_mtangentConeAt_sup_eq_top hy⟩

/-- **Reversing both fields in an intersection.** Reversing `X₀` and `X₁` exchanges unstable and
stable sets: `W^u_{X₀}(a) ∩ W^s_{X₁}(b) = W^u_{-X₁}(b) ∩ W^s_{-X₀}(a)`. -/
theorem unstableSet_inter_stableSet_eq_neg (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (a b : M) :
    hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b =
      (hX₁.neg hf₁).flow.unstableSet b ∩ (hX₀.neg hf₀).flow.stableSet a := by
  rw [← hX₁.stableSet_eq_unstableSet_neg hf₁, ← hX₀.unstableSet_eq_stableSet_neg hf₀, inter_comm]

namespace IsMorseSmalePair

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}

/-- **The pointwise elimination rule for `IsMorseSmalePair`.** For a Morse–Smale pair, at a point
`y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` the tangent spaces of `W^u_{X₀}(a)` and `W^s_{X₁}(b)` span the
tangent space of `M`. -/
theorem span_mtangentConeAt_sup_eq_top (h : IsMorseSmalePair hX₀ hX₁)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤ :=
  h hy

/-- **Reversing a Morse–Smale pair.** If `(X₀, X₁)` is a Morse–Smale pair of pseudo-gradients
adapted to Morse functions `f₀` and `f₁`, then `(-X₁, -X₀)`, adapted to `(-f₁, -f₀)`, is a
Morse–Smale pair: reversing the flows exchanges unstable and stable manifolds. -/
theorem neg (h : IsMorseSmalePair hX₀ hX₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁) : IsMorseSmalePair (hX₁.neg hf₁) (hX₀.neg hf₀) := by
  intro a b y hy
  rw [← hX₀.unstableSet_inter_stableSet_eq_neg hX₁ hf₀ hf₁] at hy
  rw [← hX₁.stableSet_eq_unstableSet_neg hf₁, ← hX₀.unstableSet_eq_stableSet_neg hf₀, sup_comm]
  exact h hy

/-- **Transverse intersections for a pair are embedded submanifolds.** For a Morse–Smale pair, near
each point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` a chart of the maximal atlas flattens this
intersection onto the intersection of the tangent spaces of `W^u_{X₀}(a)` and `W^s_{X₁}(b)` at
`y`. -/
theorem exists_isSliceChart_unstableSet_inter_stableSet (h : IsMorseSmalePair hX₀ hX₁)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) :
          Submodule ℝ E) : Set E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) :=
  hX₀.exists_unstableSet_inter_stableSet_chart hX₁ hf₀ hy (h hy)

/-- **The tangent space of a transverse intersection for a pair.** For a Morse–Smale pair, the
tangent space of `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` at each of its points is the intersection of the
tangent spaces of `W^u_{X₀}(a)` and `W^s_{X₁}(b)`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet (h : IsMorseSmalePair hX₀ hX₁)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) :
    Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) :=
  hX₀.span_mtangentConeAt_unstableSet_inter_stableSet hX₁ hf₀ hy (h hy)

/-- **The intersection for a pair has dimension the index difference.** For a Morse–Smale pair, the
tangent space of `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` at each of its points has dimension `ind a - ind b`,
the indices being taken for `f₀` and `f₁`. -/
theorem finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex
    (h : IsMorseSmalePair hX₀ hX₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) :
    Module.finrank ℝ (Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₀ a :=
  hX₀.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX₁ hf₀ hy
    (h hy)

/-- **Intersections for a pair are manifolds.** For a Morse–Smale pair, if `W^u_{X₀}(a)` meets
`W^s_{X₁}(b)`, then their intersection carries a smooth manifold structure, modelled on a subspace
of dimension `ind a - ind b`, with its subspace topology and a smooth inclusion into `M`. -/
theorem exists_unstableSet_inter_stableSet_isManifold (h : IsMorseSmalePair hX₀ hX₁)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hne : (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₀ a ∧
      ∃ C : ChartedSpace L ↥(hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b), letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) → M) :=
  hX₀.exists_unstableSet_inter_stableSet_isManifold hX₁ hf₀ (fun _ hy ↦ h hy) hne

/-- **The index does not increase along a transverse pair.** For a Morse–Smale pair, if
`W^u_{X₀}(a)` meets `W^s_{X₁}(b)`, then the index of `b` for `f₁` is at most the index of `a` for
`f₀`. -/
theorem manifoldMorseIndex_le (h : IsMorseSmalePair hX₀ hX₁) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hne : (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f₁ b ≤ manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  obtain ⟨y, hy⟩ := hne
  have := h.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf₀ hy
  omega

/-- For a Morse–Smale pair, `W^u_{X₀}(a)` and `W^s_{X₁}(b)` are disjoint when the index of `a` for
`f₀` is smaller than the index of `b` for `f₁`. -/
theorem unstableSet_inter_stableSet_eq_empty (h : IsMorseSmalePair hX₀ hX₁)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hab : manifoldMorseIndex 𝓘(ℝ, E) f₀ a < manifoldMorseIndex 𝓘(ℝ, E) f₁ b) :
    hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b = ∅ :=
  not_nonempty_iff_eq_empty.1 fun hne ↦ (h.manifoldMorseIndex_le hf₀ hne).not_gt hab

/-- **Rigid intersections for a pair are discrete.** For a Morse–Smale pair, if the index of `a`
for `f₀` is at most the index of `b` for `f₁`, then `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` is discrete. -/
theorem isDiscrete_unstableSet_inter_stableSet (h : IsMorseSmalePair hX₀ hX₁)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ a ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ b) :
    IsDiscrete (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) := by
  refine isDiscrete_of_forall_exists_isSliceChart_zero (F := E) fun y hy ↦ ?_
  -- The intersection is zero-dimensional, so the chart at `y` flattens it onto the point `0`.
  have hdim :=
    h.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hf₀ hy
  obtain ⟨q, hyq, -, hq⟩ := h.exists_isSliceChart_unstableSet_inter_stableSet hf₀ hy
  have h0 : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b) y)) = 0 := by
    omega
  rw [← h.span_mtangentConeAt_unstableSet_inter_stableSet hf₀ hy,
    Submodule.finrank_eq_zero.1 h0, Submodule.bot_coe] at hq
  exact ⟨q, hyq, hq⟩

/-- **Limits of points of an intersection for a pair break.** Let `(X₀, X₁)` be a Morse–Smale pair
of Morse–Smale pseudo-gradients. A limit `y` of points of `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` lies in
`W^u_{X₀}(a) ∩ W^s_{X₁}(b)` for points `a` and `b` with `ind b ≤ ind a`, where `a = p` or
`ind a < ind p`, and `b = q` or `ind q < ind b`, the indices being taken for `f₀` at `a`, `p` and
for `f₁` at `b`, `q`. -/
theorem exists_mem_unstableSet_inter_stableSet_of_mem_closure (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hy : y ∈ closure (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q)) :
    ∃ a b, y ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet b ∧
      (a = p ∨ manifoldMorseIndex 𝓘(ℝ, E) f₀ a < manifoldMorseIndex 𝓘(ℝ, E) f₀ p) ∧
      (b = q ∨ manifoldMorseIndex 𝓘(ℝ, E) f₁ q < manifoldMorseIndex 𝓘(ℝ, E) f₁ b) ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b ≤ manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  -- The backward orbit of `y` for `X₀` and its forward orbit for `X₁` converge to critical points.
  obtain ⟨a, -, hya⟩ := hX₀.exists_tendsto_atBot hf₀ y
  obtain ⟨b, -, hyb⟩ := hX₁.exists_tendsto_atTop hf₁ y
  have hya : y ∈ hX₀.flow.unstableSet a := Flow.mem_unstableSet.2 hya
  have hyb : y ∈ hX₁.flow.stableSet b := Flow.mem_stableSet.2 hyb
  refine ⟨a, b, ⟨hya, hyb⟩, or_iff_not_imp_left.2 fun hap ↦ ?_, or_iff_not_imp_left.2 fun hbq ↦ ?_,
    h.manifoldMorseIndex_le hf₀ ⟨y, hya, hyb⟩⟩
  · exact h₀.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf₀ hap
      ⟨y, closure_mono inter_subset_left hy, hya⟩
  · exact h₁.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf₁ hbq
      ⟨y, closure_mono inter_subset_right hy, hyb⟩

/-- **Rigid intersections for a pair are closed.** Let `(X₀, X₁)` be a Morse–Smale pair of
Morse–Smale pseudo-gradients. If the index of `p` for `f₀` is at most the index of `q` for `f₁`,
then `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` is closed. -/
theorem isClosed_unstableSet_inter_stableSet (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    IsClosed (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) := by
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  -- A limit can break neither at the source nor at the target: either would leave the index
  -- strictly lower at the source than at the target.
  obtain ⟨a, b, hy', hap, hbq, hba⟩ :=
    h.exists_mem_unstableSet_inter_stableSet_of_mem_closure h₀ h₁ hf₀ hf₁ hy
  obtain rfl : a = p := hap.resolve_right fun hlt ↦ by rcases hbq with rfl | hbq <;> omega
  obtain rfl : b = q := hbq.resolve_right fun hlt ↦ by omega
  exact hy'

/-- **Rigid intersections for a pair are finite.** Let `(X₀, X₁)` be a Morse–Smale pair of
Morse–Smale pseudo-gradients. If the index of `p` for `f₀` is at most the index of `q` for `f₁`,
then `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` is finite. By `unstableSet_inter_stableSet_eq_empty` it is empty
unless the indices are equal. Once continuation trajectories are identified with these
intersections, they are expected to give the counts of a continuation map between Morse complexes.
-/
theorem finite_unstableSet_inter_stableSet (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≤ manifoldMorseIndex 𝓘(ℝ, E) f₁ q) :
    (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q).Finite :=
  (h.isClosed_unstableSet_inter_stableSet h₀ h₁ hf₀ hf₁ hind).isCompact.finite
    (h.isDiscrete_unstableSet_inter_stableSet hf₀ hind)

/-- **The ends of one-dimensional intersections for a pair are once broken.** Let `(X₀, X₁)` be a
Morse–Smale pair of Morse–Smale pseudo-gradients, and `ind p = ind q + 1`, for `f₀` at `p` and
`f₁` at `q`. Besides `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` itself, its closure meets only

* the intersections `W^u_{X₀}(a) ∩ W^s_{X₁}(q)` for the points `a` with `ind a = ind q` reached by
  a trajectory of `X₀` from `p`, and
* the intersections `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` for the points `b` with `ind b = ind p` from which
  a trajectory of `X₁` runs to `q`. -/
theorem closure_unstableSet_inter_stableSet_subset (h : IsMorseSmalePair hX₀ hX₁)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1) :
    closure (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) ⊆
      (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet q) ∪
        (⋃ a ∈ {a | manifoldMorseIndex 𝓘(ℝ, E) f₀ a = manifoldMorseIndex 𝓘(ℝ, E) f₁ q ∧
            (hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a).Nonempty},
          hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet q) ∪
        (⋃ b ∈ {b | manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₀ p ∧
            (hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet q).Nonempty},
          hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b) := by
  intro y hy
  obtain ⟨a, b, hy', hap, hbq, hba⟩ :=
    h.exists_mem_unstableSet_inter_stableSet_of_mem_closure h₀ h₁ hf₀ hf₁ hy
  have hyU : y ∈ closure (hX₀.flow.unstableSet p) := closure_mono inter_subset_left hy
  have hyS : y ∈ closure (hX₁.flow.stableSet q) := closure_mono inter_subset_right hy
  simp only [mem_union, mem_iUnion₂, mem_ofPred_eq, exists_prop]
  -- At most one end breaks, since the index can only drop at the source and rise at the target,
  -- and the indices of `p` and `q` differ by one.
  rcases hap with rfl | hap
  · rcases hbq with rfl | hbq
    · exact Or.inl (Or.inl hy')
    · have hbq' : b ≠ q := by rintro rfl; omega
      refine Or.inr ⟨b, ⟨by omega, ?_⟩, hy'⟩
      exact h₁.nonempty_unstableSet_inter_stableSet_of_mem_closure_stableSet_inter_stableSet
        hf₁ hbq' (by omega) ⟨y, hyS, hy'.2⟩
  · rcases hbq with rfl | hbq
    · have hap' : a ≠ p := by rintro rfl; omega
      refine Or.inl (Or.inr ⟨a, ⟨by omega, ?_⟩, hy'⟩)
      exact h₀.nonempty_unstableSet_inter_stableSet_of_mem_closure_unstableSet_inter_unstableSet
        hf₀ hap' (by omega) ⟨y, hyU, hy'.1⟩
    · omega

end IsMorseSmalePair

end IsAdaptedPseudoGradient

end TauCeti
