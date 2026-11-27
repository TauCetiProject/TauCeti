/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Basic

/-!
# Transverse Y-flow lines: the Morse–Smale condition for three pseudo-gradients

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M` of dimension
`n`, with pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them. The Morse cup product counts the
Y-shaped flow lines from a critical point `p` of `f₀` to critical points `q` of `f₁` and `r` of
`f₂`, recorded by their vertices: the points of the Y-slice
`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` (`TauCeti.IsAdaptedPseudoGradient.morseYSlice`).

The triple `(X₀, X₁, X₂)` is **Morse–Smale**
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmaleTriple`) when, at each point `y` of each Y-slice
`W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)`, the tangent spaces `U`, `S₁` and `S₂` of the three
manifolds at `y` satisfy `U + S₁ = T_y M` and `(U ∩ S₁) + S₂ = T_y M`. In a modular lattice the
two conditions together are symmetric in `S₁` and `S₂`
(`TauCeti.IsAdaptedPseudoGradient.isMorseSmaleTriple_comm`); in finite dimension they say that the
codimension of `U ∩ S₁ ∩ S₂` is the sum of the codimensions of `U`, `S₁` and `S₂`, that is, that
`W^u_{X₀}(a) × W^s_{X₁}(b) × W^s_{X₂}(c)` is transverse in `M × M × M` to the small diagonal. This
is the transversality condition under which the Y-flow lines are counted.

For a Morse–Smale triple the following hold, for critical points `a`, `b` and `c` of `f₀`, `f₁`
and `f₂`, the Morse indices being taken for these functions:

* **Dimension.** The Y-slice is flattened near each of its points by a chart of the maximal atlas
  onto `U ∩ S₁ ∩ S₂`, and is a smooth manifold of dimension `ind a - ind b - ind c`
  (`IsMorseSmaleTriple.exists_morseYSlice_isManifold`). In particular it is empty unless
  `ind b + ind c ≤ ind a` (`IsMorseSmaleTriple.manifoldMorseIndex_add_le`), and discrete when
  `ind a = ind b + ind c`.
* **Breaking.** If `X₀`, `X₁` and `X₂` are moreover Morse–Smale, a limit of points of the Y-slice
  from `p` to `q` and `r` lies in the Y-slice from `a` to `b` and `c`, where the root can only
  break downwards (`a = p` or `ind a < ind p`) and each leaf only upwards (`b = q` or
  `ind q < ind b`, and `c = r` or `ind r < ind c`)
  (`IsMorseSmaleTriple.exists_mem_morseYSlice_of_mem_closure`).
* **Finiteness.** Hence when `ind p ≤ ind q + ind r` the Y-slice is finite
  (`IsMorseSmaleTriple.finite_morseYSlice`): the rigid Y-flow lines are finitely many, so the
  coefficients of the Morse diagonal `TauCeti.morseDiagonalMap` of the Y-slices are their numbers
  modulo two.
* **One-dimensional ends.** When `ind p = ind q + ind r + 1`, the Y-slice is one-dimensional, and
  its closure adds only Y-flow lines broken once, along the root, along the first leaf or along the
  second leaf (`IsMorseSmaleTriple.closure_morseYSlice_subset`). These are the three kinds of
  broken Y-flow lines whose total number decides the Leibniz rule of the cup product.

With the finiteness of the rigid Y-slices, the algebraic criterion of
`TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Basic` holds without a finiteness hypothesis:
for a Morse–Smale triple of Morse–Smale pseudo-gradients, the Morse diagonal of the Y-slices is a
chain map, and its cup product satisfies the Leibniz rule `δ(a ∪ b) = δa ∪ b + a ∪ δb`, exactly
when the broken Y-flow lines between any three critical points are evenly many in total
(`IsMorseSmaleTriple.morseDiagonalMap_comp_morseBoundary_eq_iff`,
`IsMorseSmaleTriple.morseCupProduct_comp_morseBoundary_eq_iff`). That they are, because they are
the ends of the compactified one-dimensional Y-slices, needs the gluing of Y-flow lines and is not
proved here.

The arguments follow those for a pair of pseudo-gradients in
`TauCeti.Geometry.Manifold.Morse.Stable.Pair`: the Y-slice is the intersection of the transverse
pair intersection `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` with `W^s_{X₂}(c)`, and each of the three edges
breaks as the corresponding unstable or stable manifold does.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmaleTriple`: the Morse–Smale condition for a triple of pseudo-gradients, with its
  unfolding `isMorseSmaleTriple_iff`, its pointwise form
  `IsMorseSmaleTriple.span_mtangentConeAt_sup_eq_top_and_inf_sup_eq_top`, and the exchange of the
  two leaves `IsMorseSmaleTriple.swap` and `isMorseSmaleTriple_comm`.
* `IsMorseSmaleTriple.exists_isSliceChart_morseYSlice`,
  `IsMorseSmaleTriple.span_mtangentConeAt_morseYSlice` and
  `IsMorseSmaleTriple.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex`: the Y-slice
  is flattened onto the intersection of the three tangent spaces, of dimension
  `ind a - ind b - ind c`. Each specializes the lemma of the same name in
  `TauCeti.IsAdaptedPseudoGradient`, which assumes the transversality only at the point considered.
* `IsMorseSmaleTriple.exists_morseYSlice_isManifold`: the Y-slice is a smooth manifold of dimension
  `ind a - ind b - ind c`.
* `IsMorseSmaleTriple.manifoldMorseIndex_add_le`, `IsMorseSmaleTriple.morseYSlice_eq_empty` and
  `IsMorseSmaleTriple.isDiscrete_morseYSlice`: the index count.
* `IsMorseSmaleTriple.exists_mem_morseYSlice_of_mem_closure`,
  `IsMorseSmaleTriple.isClosed_morseYSlice`, `IsMorseSmaleTriple.finite_morseYSlice` and
  `IsMorseSmaleTriple.closure_morseYSlice_subset`: breaking, finiteness of the rigid Y-slices and
  the ends of the one-dimensional ones.
* `IsMorseSmaleTriple.morseDiagonalMap_comp_morseBoundary_eq_iff` and
  `IsMorseSmaleTriple.morseCupProduct_comp_morseBoundary_eq_iff`: the chain-map and Leibniz
  criteria for the Y-slices of a Morse–Smale triple.

## References

* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  [arXiv:1611.07916](https://arxiv.org/abs/1611.07916), §§1–5 (transversality, compactness and the
  boundary of the moduli spaces of Y-shaped flow trees).
* K. Fukaya, *Morse homotopy, A∞-category, and Floer homologies*, Proceedings of GARC Workshop on
  Geometry and Topology '93, Lecture Notes Ser. 18, Seoul Nat. Univ., 1993, 1–102 (the Morse cup
  product by counting Y-shaped flow lines).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b c p q r y : M}

namespace IsAdaptedPseudoGradient

/-- **The Morse–Smale condition for a triple of pseudo-gradients** `X₀`, `X₁` and `X₂`, adapted to
`f₀`, `f₁` and `f₂`: at each point `y` of each Y-slice `W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)`,
the tangent spaces `U`, `S₁` and `S₂` of `W^u_{X₀}(a)`, `W^s_{X₁}(b)` and `W^s_{X₂}(c)` at `y`
satisfy `U + S₁ = T_y M` and `(U ∩ S₁) + S₂ = T_y M`. Together these say that the codimension of
`U ∩ S₁ ∩ S₂` is the sum of those of `U`, `S₁` and `S₂`; the condition is symmetric in the two
leaves (`TauCeti.IsAdaptedPseudoGradient.isMorseSmaleTriple_comm`). Only critical points `a`, `b`
and `c` matter, since the other unstable and stable manifolds are empty. -/
def IsMorseSmaleTriple (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hX₂ : IsAdaptedPseudoGradient f₂ X₂) : Prop :=
  ∀ ⦃a b c y : M⦄, y ∈ hX₀.morseYSlice hX₁ hX₂ a b c →
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤ ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤

/-- The unfolding of `TauCeti.IsAdaptedPseudoGradient.IsMorseSmaleTriple`. -/
theorem isMorseSmaleTriple_iff {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} {hX₂ : IsAdaptedPseudoGradient f₂ X₂} :
    IsMorseSmaleTriple hX₀ hX₁ hX₂ ↔ ∀ ⦃a b c y : M⦄, y ∈ hX₀.morseYSlice hX₁ hX₂ a b c →
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤ ∧
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
            Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤ :=
  Iff.rfl

namespace IsMorseSmaleTriple

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}

/-- **Exchanging the leaves of a Morse–Smale triple.** If `(X₀, X₁, X₂)` is Morse–Smale, so is
`(X₀, X₂, X₁)`. -/
theorem swap (h : IsMorseSmaleTriple hX₀ hX₁ hX₂) : IsMorseSmaleTriple hX₀ hX₂ hX₁ := by
  intro a c b y hy
  rw [hX₀.morseYSlice_comm hX₁ hX₂] at hy
  -- In the modular lattice of subspaces, `U ⊔ S₁ = ⊤` and `(U ⊓ S₁) ⊔ S₂ = ⊤` give
  -- `U ⊔ (S₁ ⊓ S₂) = ⊤`, hence `U ⊔ S₂ = ⊤` and `(U ⊓ S₂) ⊔ S₁ = ⊤`.
  have h' := h hy
  simp_rw [← codisjoint_iff] at h' ⊢
  have hU : Codisjoint _ (_ ⊓ _) := h'.1.codisjoint_inf_right_of_codisjoint_inf_left h'.2
  exact ⟨hU.mono_right inf_le_right, Codisjoint.codisjoint_inf_left_of_codisjoint_inf_right
    (h'.2.mono_left inf_le_right).symm (by rwa [inf_comm] at hU)⟩

end IsMorseSmaleTriple

/-- **Exchanging the leaves of a Morse–Smale triple.** The triple `(X₀, X₁, X₂)` is Morse–Smale
exactly when `(X₀, X₂, X₁)` is. -/
theorem isMorseSmaleTriple_comm {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} {hX₂ : IsAdaptedPseudoGradient f₂ X₂} :
    IsMorseSmaleTriple hX₀ hX₂ hX₁ ↔ IsMorseSmaleTriple hX₀ hX₁ hX₂ :=
  ⟨IsMorseSmaleTriple.swap, IsMorseSmaleTriple.swap⟩

section TransverseAt

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂)

/-- The slice chart and the tangent space of a Y-slice at a point where it is transverse, proved
together since they share the charts of the pair intersection and of the second leaf. -/
private theorem exists_isSliceChart_morseYSlice_and_span_mtangentConeAt
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c)
    (h₁ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤)
    (h₂ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤) :
    (∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) :
          Submodule ℝ E) : Set E) (hX₀.morseYSlice hX₁ hX₂ a b c)) ∧
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) := by
  obtain ⟨hya, hyb, hyc⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  -- Flatten `W^u_{X₀}(a) ∩ W^s_{X₁}(b)` as for a pair, then intersect with `W^s_{X₂}(c)`.
  obtain ⟨q₁, hy₁, hq₁, hs₁⟩ := hX₀.exists_unstableSet_inter_stableSet_chart hX₁ hf₀ ⟨hya, hyb⟩ h₁
  obtain ⟨L₂, q₂, -, hy₂, hq₂, hs₂⟩ :=
    hX₂.exists_isSliceChart_stableSet (hX₂.mfderiv_eq_zero_of_mem_stableSet hyc) hyc
  have hT := hX₀.span_mtangentConeAt_unstableSet_inter_stableSet hX₁ hf₀ ⟨hya, hyb⟩ h₁
  have hc (L : Submodule ℝ E) : L.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _)
  rw [morseYSlice_def, ← hT]
  exact ⟨exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hq₁ hq₂ hs₁ hs₂
    hy₁ hy₂ (hT ▸ h₂) (hc _) (hc _) (hc _),
    span_mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hq₁ hq₂ hs₁ hs₂ hy₁ hy₂
      (hT ▸ h₂) (hc _) (hc _) (hc _)⟩

/-- **Transverse Y-slices are embedded submanifolds.** Let `X₀`, `X₁` and `X₂` be pseudo-gradients
adapted to `f₀`, `f₁` and `f₂`, with `f₀` Morse. If at a point `y` of
`W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` the tangent spaces `U`, `S₁` and `S₂` of the three
manifolds satisfy `U + S₁ = T_y M` and `(U ∩ S₁) + S₂ = T_y M`, then near `y` a chart of the
maximal atlas flattens this Y-slice onto `U ∩ S₁ ∩ S₂`. -/
theorem exists_isSliceChart_morseYSlice (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c)
    (h₁ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤)
    (h₂ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) :
          Submodule ℝ E) : Set E) (hX₀.morseYSlice hX₁ hX₂ a b c) :=
  (hX₀.exists_isSliceChart_morseYSlice_and_span_mtangentConeAt hX₁ hX₂ hf₀ hy h₁ h₂).1

/-- **The tangent space of a transverse Y-slice.** Let `X₀`, `X₁` and `X₂` be pseudo-gradients
adapted to `f₀`, `f₁` and `f₂`, with `f₀` Morse. If at a point `y` of
`W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` the tangent spaces `U`, `S₁` and `S₂` of the three
manifolds satisfy `U + S₁ = T_y M` and `(U ∩ S₁) + S₂ = T_y M`, then the tangent space of this
Y-slice at `y` is `U ∩ S₁ ∩ S₂`. -/
theorem span_mtangentConeAt_morseYSlice (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c)
    (h₁ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤)
    (h₂ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) :=
  (hX₀.exists_isSliceChart_morseYSlice_and_span_mtangentConeAt hX₁ hX₂ hf₀ hy h₁ h₂).2

/-- **A transverse Y-slice has dimension `ind a - ind b - ind c`.** Let `X₀`, `X₁` and `X₂` be
pseudo-gradients adapted to `f₀`, `f₁` and `f₂`, with `f₀` Morse. If at a point `y` of
`W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` the tangent spaces `U`, `S₁` and `S₂` of the three
manifolds satisfy `U + S₁ = T_y M` and `(U ∩ S₁) + S₂ = T_y M`, then the tangent space of this
Y-slice at `y` has dimension `ind a - ind b - ind c`, the indices being taken for `f₀`, `f₁` and
`f₂`. -/
theorem finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c)
    (h₁ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤)
    (h₂ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤) :
    Module.finrank ℝ (Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c =
        manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  obtain ⟨hya, hyb, hyc⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  -- `dim (A ⊓ B) = ind a - ind b` for the pair, and `(A ⊓ B) ⊔ C = ⊤` with `dim C = n - ind c`.
  have hpair :=
    hX₀.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX₁ hf₀
      ⟨hya, hyb⟩ h₁
  rw [hX₀.span_mtangentConeAt_unstableSet_inter_stableSet hX₁ hf₀ ⟨hya, hyb⟩ h₁] at hpair
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y))
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y))
  rw [h₂, finrank_top, ← hX₀.span_mtangentConeAt_morseYSlice hX₁ hX₂ hf₀ hy h₁ h₂] at hdim
  have hs := hX₂.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hyc
  omega

end TransverseAt

namespace IsMorseSmaleTriple

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}

/-- **The pointwise elimination rule for `IsMorseSmaleTriple`.** For a Morse–Smale triple, at a
point of a Y-slice the unstable manifold of the root and the stable manifold of the first leaf are
transverse, and their intersection is transverse to the stable manifold of the second leaf. -/
theorem span_mtangentConeAt_sup_eq_top_and_inf_sup_eq_top (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤ ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) = ⊤ :=
  h hy

/-- **Transverse Y-slices are embedded submanifolds.** For a Morse–Smale triple, near each point
`y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` a chart of the maximal atlas flattens this Y-slice
onto the intersection of the tangent spaces of the three manifolds at `y`. -/
theorem exists_isSliceChart_morseYSlice (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) :
          Submodule ℝ E) : Set E) (hX₀.morseYSlice hX₁ hX₂ a b c) :=
  hX₀.exists_isSliceChart_morseYSlice hX₁ hX₂ hf₀ hy (h hy).1 (h hy).2

/-- **The tangent space of a transverse Y-slice.** For a Morse–Smale triple, the tangent space of
`W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` at each of its points is the intersection of the tangent
spaces of the three manifolds. -/
theorem span_mtangentConeAt_morseYSlice (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet c) y) :=
  hX₀.span_mtangentConeAt_morseYSlice hX₁ hX₂ hf₀ hy (h hy).1 (h hy).2

/-- **A transverse Y-slice has dimension `ind a - ind b - ind c`.** For a Morse–Smale triple, the
tangent space of `W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` at each of its points has dimension
`ind a - ind b - ind c`, the indices being taken for `f₀`, `f₁` and `f₂`. -/
theorem finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex
    (h : IsMorseSmaleTriple hX₀ hX₁ hX₂) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c) :
    Module.finrank ℝ (Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c =
        manifoldMorseIndex 𝓘(ℝ, E) f₀ a :=
  hX₀.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex hX₁ hX₂ hf₀ hy (h hy).1
    (h hy).2


/-- **Transverse Y-slices are manifolds.** For a Morse–Smale triple, if the Y-slice
`W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` is nonempty, then it carries a smooth manifold structure,
modelled on a subspace of dimension `ind a - ind b - ind c`, with its subspace topology and a
smooth inclusion into `M`. -/
theorem exists_morseYSlice_isManifold (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hne : (hX₀.morseYSlice hX₁ hX₂ a b c).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c =
        manifoldMorseIndex 𝓘(ℝ, E) f₀ a ∧
      ∃ C : ChartedSpace L ↥(hX₀.morseYSlice hX₁ hX₂ a b c), letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX₀.morseYSlice hX₁ hX₂ a b c) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ (Subtype.val : ↥(hX₀.morseYSlice hX₁ hX₂ a b c) → M) := by
  obtain ⟨y₀, hy₀⟩ := hne
  -- Every tangent space of the Y-slice has the same dimension; model it on one of them.
  refine ⟨Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y₀),
    h.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex hf₀ hy₀,
    exists_isManifold_of_finrankSubspaceCharts fun y hy ↦ ?_⟩
  obtain ⟨q, hyq, hq, hs⟩ := h.exists_isSliceChart_morseYSlice hf₀ hy
  have hdim₀ := h.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex hf₀ hy₀
  have hdim := h.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex hf₀ hy
  rw [h.span_mtangentConeAt_morseYSlice hf₀ hy] at hdim
  exact ⟨q, _, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs, by omega⟩

/-- **The index does not increase along a transverse Y-flow line.** For a Morse–Smale triple, if
the Y-slice `W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` is nonempty, then
`ind b + ind c ≤ ind a`, the indices being taken for `f₁`, `f₂` and `f₀`. -/
theorem manifoldMorseIndex_add_le (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hne : (hX₀.morseYSlice hX₁ hX₂ a b c).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c ≤
      manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  obtain ⟨y, hy⟩ := hne
  have := h.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex hf₀ hy
  omega

/-- For a Morse–Smale triple, the Y-slice `W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` is empty when
`ind a < ind b + ind c`. -/
theorem morseYSlice_eq_empty (h : IsMorseSmaleTriple hX₀ hX₁ hX₂) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (habc : manifoldMorseIndex 𝓘(ℝ, E) f₀ a <
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c) :
    hX₀.morseYSlice hX₁ hX₂ a b c = ∅ :=
  not_nonempty_iff_eq_empty.1 fun hne ↦ (h.manifoldMorseIndex_add_le hf₀ hne).not_gt habc

/-- **Rigid Y-slices are discrete.** For a Morse–Smale triple, if `ind a ≤ ind b + ind c`, then
the Y-slice `W^u_{X₀}(a) ∩ W^s_{X₁}(b) ∩ W^s_{X₂}(c)` is discrete. -/
theorem isDiscrete_morseYSlice (h : IsMorseSmaleTriple hX₀ hX₁ hX₂) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ a ≤
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c) :
    IsDiscrete (hX₀.morseYSlice hX₁ hX₂ a b c) := by
  refine isDiscrete_of_forall_exists_isSliceChart_zero (F := E) fun y hy ↦ ?_
  -- The Y-slice is zero-dimensional, so the chart at `y` flattens it onto the point `0`.
  have hdim := h.finrank_span_mtangentConeAt_morseYSlice_add_manifoldMorseIndex hf₀ hy
  obtain ⟨q, hyq, -, hq⟩ := h.exists_isSliceChart_morseYSlice hf₀ hy
  have h0 : Module.finrank ℝ (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX₀.morseYSlice hX₁ hX₂ a b c) y)) = 0 := by
    omega
  rw [← h.span_mtangentConeAt_morseYSlice hf₀ hy, Submodule.finrank_eq_zero.1 h0,
    Submodule.bot_coe] at hq
  exact ⟨q, hyq, hq⟩

/-- **Limits of Y-flow lines break.** Let `(X₀, X₁, X₂)` be a Morse–Smale triple of Morse–Smale
pseudo-gradients. A limit `y` of points of the Y-slice from `p` to `q` and `r` lies in the Y-slice
from `a` to `b` and `c` for points with `ind b + ind c ≤ ind a`, where `a = p` or `ind a < ind p`,
`b = q` or `ind q < ind b`, and `c = r` or `ind r < ind c`, the indices being taken for `f₀` at `a`
and `p`, for `f₁` at `b` and `q`, and for `f₂` at `c` and `r`. -/
theorem exists_mem_morseYSlice_of_mem_closure (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (h₂ : hX₂.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hy : y ∈ closure (hX₀.morseYSlice hX₁ hX₂ p q r)) :
    ∃ a b c, y ∈ hX₀.morseYSlice hX₁ hX₂ a b c ∧
      (a = p ∨ manifoldMorseIndex 𝓘(ℝ, E) f₀ a < manifoldMorseIndex 𝓘(ℝ, E) f₀ p) ∧
      (b = q ∨ manifoldMorseIndex 𝓘(ℝ, E) f₁ q < manifoldMorseIndex 𝓘(ℝ, E) f₁ b) ∧
      (c = r ∨ manifoldMorseIndex 𝓘(ℝ, E) f₂ r < manifoldMorseIndex 𝓘(ℝ, E) f₂ c) ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ c ≤
        manifoldMorseIndex 𝓘(ℝ, E) f₀ a := by
  rw [morseYSlice_def] at hy
  -- The backward orbit of `y` for `X₀` and its forward orbits for `X₁` and `X₂` converge to
  -- critical points.
  obtain ⟨a, -, hya⟩ := hX₀.exists_tendsto_atBot y
  obtain ⟨b, -, hyb⟩ := hX₁.exists_tendsto_atTop y
  obtain ⟨c, -, hyc⟩ := hX₂.exists_tendsto_atTop y
  have hya : y ∈ hX₀.flow.unstableSet a := Flow.mem_unstableSet.2 hya
  have hyb : y ∈ hX₁.flow.stableSet b := Flow.mem_stableSet.2 hyb
  have hyc : y ∈ hX₂.flow.stableSet c := Flow.mem_stableSet.2 hyc
  have hyY : y ∈ hX₀.morseYSlice hX₁ hX₂ a b c :=
    (hX₀.mem_morseYSlice hX₁ hX₂).2 ⟨hya, hyb, hyc⟩
  refine ⟨a, b, c, hyY, or_iff_not_imp_left.2 fun hap ↦ ?_, or_iff_not_imp_left.2 fun hbq ↦ ?_,
    or_iff_not_imp_left.2 fun hcr ↦ ?_, h.manifoldMorseIndex_add_le hf₀ ⟨y, hyY⟩⟩
  · exact h₀.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf₀ hap
      ⟨y, closure_mono (inter_subset_left.trans inter_subset_left) hy, hya⟩
  · exact h₁.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf₁ hbq
      ⟨y, closure_mono (inter_subset_left.trans inter_subset_right) hy, hyb⟩
  · exact h₂.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf₂ hcr
      ⟨y, closure_mono inter_subset_right hy, hyc⟩

/-- **Rigid Y-slices are closed.** Let `(X₀, X₁, X₂)` be a Morse–Smale triple of Morse–Smale
pseudo-gradients. If `ind p ≤ ind q + ind r`, for `f₀` at `p`, `f₁` at `q` and `f₂` at `r`, then
the Y-slice from `p` to `q` and `r` is closed. -/
theorem isClosed_morseYSlice (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (h₂ : hX₂.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≤
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    IsClosed (hX₀.morseYSlice hX₁ hX₂ p q r) := by
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  -- A limit can break nowhere: any break would leave the index of the root strictly smaller than
  -- the sum of the indices of the leaves.
  obtain ⟨a, b, c, hy', hap, hbq, hcr, hle⟩ :=
    h.exists_mem_morseYSlice_of_mem_closure h₀ h₁ h₂ hf₀ hf₁ hf₂ hy
  obtain rfl : a = p := hap.resolve_right fun hlt ↦ by
    rcases hbq with rfl | hbq <;> rcases hcr with rfl | hcr <;> omega
  obtain rfl : b = q := hbq.resolve_right fun hlt ↦ by rcases hcr with rfl | hcr <;> omega
  obtain rfl : c = r := hcr.resolve_right fun hlt ↦ by omega
  exact hy'

/-- **Rigid Y-slices are finite.** Let `(X₀, X₁, X₂)` be a Morse–Smale triple of Morse–Smale
pseudo-gradients. If `ind p ≤ ind q + ind r`, for `f₀` at `p`, `f₁` at `q` and `f₂` at `r`, then
the Y-slice from `p` to `q` and `r` is finite. By `morseYSlice_eq_empty` it is empty unless
`ind p = ind q + ind r`, and then its points are the rigid Y-flow lines counted by the Morse
diagonal. -/
theorem finite_morseYSlice (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (h₂ : hX₂.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p ≤
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    (hX₀.morseYSlice hX₁ hX₂ p q r).Finite :=
  (h.isClosed_morseYSlice h₀ h₁ h₂ hf₀ hf₁ hf₂ hind).isCompact.finite
    (h.isDiscrete_morseYSlice hf₀ hind)

/-- **The ends of one-dimensional Y-slices are once broken.** Let `(X₀, X₁, X₂)` be a Morse–Smale
triple of Morse–Smale pseudo-gradients, and `ind p = ind q + ind r + 1`, for `f₀` at `p`, `f₁` at
`q` and `f₂` at `r`. Besides the Y-slice from `p` to `q` and `r` itself, its closure meets only

* the Y-slices from `a` to `q` and `r` for the points `a` with `ind a = ind q + ind r` reached by a
  trajectory of `X₀` from `p`, broken at the root;
* the Y-slices from `p` to `b` and `r` for the points `b` with `ind p = ind b + ind r` from which a
  trajectory of `X₁` runs to `q`, broken at the first leaf;
* the Y-slices from `p` to `q` and `c` for the points `c` with `ind p = ind q + ind c` from which a
  trajectory of `X₂` runs to `r`, broken at the second leaf. -/
theorem closure_morseYSlice_subset (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (h₂ : hX₂.IsMorseSmale)
    (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1) :
    closure (hX₀.morseYSlice hX₁ hX₂ p q r) ⊆
      hX₀.morseYSlice hX₁ hX₂ p q r ∪
        (⋃ a ∈ {a | manifoldMorseIndex 𝓘(ℝ, E) f₀ a =
              manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
            (hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a).Nonempty},
          hX₀.morseYSlice hX₁ hX₂ a q r) ∪
        (⋃ b ∈ {b | manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
              manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
            (hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet q).Nonempty},
          hX₀.morseYSlice hX₁ hX₂ p b r) ∪
        (⋃ c ∈ {c | manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
              manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ c ∧
            (hX₂.flow.unstableSet c ∩ hX₂.flow.stableSet r).Nonempty},
          hX₀.morseYSlice hX₁ hX₂ p q c) := by
  intro y hy
  obtain ⟨a, b, c, hy', hap, hbq, hcr, hle⟩ :=
    h.exists_mem_morseYSlice_of_mem_closure h₀ h₁ h₂ hf₀ hf₁ hf₂ hy
  obtain ⟨hya, hyb, hyc⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy'
  rw [morseYSlice_def] at hy
  have hyU : y ∈ closure (hX₀.flow.unstableSet p) :=
    closure_mono (inter_subset_left.trans inter_subset_left) hy
  have hyS₁ : y ∈ closure (hX₁.flow.stableSet q) :=
    closure_mono (inter_subset_left.trans inter_subset_right) hy
  have hyS₂ : y ∈ closure (hX₂.flow.stableSet r) := closure_mono inter_subset_right hy
  simp only [mem_union, mem_iUnion₂, mem_ofPred_eq, exists_prop]
  -- At most one edge breaks: the index can only drop at the root and rise at the leaves, and the
  -- index of `p` exceeds the sum of those of `q` and `r` by one.
  rcases hap with rfl | hap
  · rcases hbq with rfl | hbq
    · rcases hcr with rfl | hcr
      · exact Or.inl (Or.inl (Or.inl hy'))
      · have hcr' : c ≠ r := by rintro rfl; omega
        refine Or.inr ⟨c, ⟨by omega, ?_⟩, hy'⟩
        exact h₂.nonempty_unstableSet_inter_stableSet_of_mem_closure_stableSet_inter_stableSet
          hf₂ hcr' (by omega) ⟨y, hyS₂, hyc⟩
    · rcases hcr with rfl | hcr
      · have hbq' : b ≠ q := by rintro rfl; omega
        refine Or.inl (Or.inr ⟨b, ⟨by omega, ?_⟩, hy'⟩)
        exact h₁.nonempty_unstableSet_inter_stableSet_of_mem_closure_stableSet_inter_stableSet
          hf₁ hbq' (by omega) ⟨y, hyS₁, hyb⟩
      · omega
  · rcases hbq with rfl | hbq
    · rcases hcr with rfl | hcr
      · have hap' : a ≠ p := by rintro rfl; omega
        refine Or.inl (Or.inl (Or.inr ⟨a, ⟨by omega, ?_⟩, hy'⟩))
        exact h₀.nonempty_unstableSet_inter_stableSet_of_mem_closure_unstableSet_inter_unstableSet
          hf₀ hap' (by omega) ⟨y, hyU, hya⟩
      · omega
    · rcases hcr with rfl | hcr <;> omega

end IsMorseSmaleTriple

end IsAdaptedPseudoGradient

/-! ### Counting transverse Y-flow lines -/

namespace IsAdaptedPseudoGradient.IsMorseSmaleTriple

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (h₂ : hX₂.IsMorseSmale) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
include h h₀ hf₀ h₁ hf₁ h₂ hf₂

/-- **The Morse diagonal of a Morse–Smale triple is a chain map exactly when the broken Y-flow lines
come in pairs.** For a Morse–Smale triple of Morse–Smale pseudo-gradients adapted to Morse
functions, the Morse diagonal `Δ` of the Y-slices satisfies
`Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ` exactly when, for all critical points `p`, `q` and `r` of `f₀`,
`f₁` and `f₂` with `ind p = ind q + ind r + 1`, the Y-flow lines from `p` to `q` and `r` broken at
the root, at the first leaf and at the second leaf are evenly many in total. -/
theorem morseDiagonalMap_comp_morseBoundary_eq_iff :
    morseDiagonalMap f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) ∘ₗ h₀.morseBoundary hf₀ =
        ((h₁.morseBoundary hf₁).rTensor _ + (h₂.morseBoundary hf₂).lTensor _) ∘ₗ
          morseDiagonalMap f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
        (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 →
        Even ((morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r).ncard +
          (morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r).ncard +
          (morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r).ncard) :=
  TauCeti.morseDiagonalMap_comp_morseBoundary_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂ fun _ _ _ hind ↦
    h.finite_morseYSlice h₀ h₁ h₂ hf₀ hf₁ hf₂ hind.le

/-- **The Leibniz rule of the cup product of a Morse–Smale triple holds exactly when the broken
Y-flow lines come in pairs.** For a Morse–Smale triple of Morse–Smale pseudo-gradients adapted to
Morse functions, the cup product of the Y-slices satisfies `δ(a ∪ b) = δa ∪ b + a ∪ δb` for all
linear forms `a` and `b` on the mod-two Morse chains exactly when, for all critical points `p`, `q`
and `r` of `f₀`, `f₁` and `f₂` with `ind p = ind q + ind r + 1`, the Y-flow lines from `p` to `q`
and `r` broken at the root, at the first leaf and at the second leaf are evenly many in total. -/
theorem morseCupProduct_comp_morseBoundary_eq_iff :
    (∀ (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2),
        morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) a b ∘ₗ h₀.morseBoundary hf₀ =
          morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) (a ∘ₗ h₁.morseBoundary hf₁) b +
            morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) a
              (b ∘ₗ h₂.morseBoundary hf₂)) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁)
        (r : criticalPoints 𝓘(ℝ, E) f₂), manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
          manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1 →
        Even ((morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r).ncard +
          (morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r).ncard +
          (morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r).ncard) :=
  TauCeti.morseCupProduct_comp_morseBoundary_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂ fun _ _ _ hind ↦
    h.finite_morseYSlice h₀ h₁ h₂ hf₀ hf₁ hf₂ hind.le

end IsAdaptedPseudoGradient.IsMorseSmaleTriple

end TauCeti
