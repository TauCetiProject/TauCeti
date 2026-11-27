/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diagonal.Transverse
import TauCeti.Geometry.Manifold.Morse.Gluing.Transverse
import TauCeti.Geometry.Manifold.Morse.Stable.Breaking
import TauCeti.Geometry.Manifold.Boundary.LocalModels
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Topology.Closure

/-!
# The mod-two Morse diagonal is a chain map

Let `f₀`, `f₁` and `f₂` be Morse functions on a compact boundaryless manifold `M`, with
Morse–Smale pseudo-gradients `X₀`, `X₁` and `X₂` adapted to them and forming a Morse–Smale triple
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmaleTriple`). The Morse diagonal `Δ` counts the Y-flow
lines, recorded by their vertices, the points of the Y-slices
`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)` (`TauCeti.IsAdaptedPseudoGradient.morseYSlice`). By
`IsMorseSmaleTriple.morseDiagonalMap_comp_morseBoundary_eq_iff`, `Δ` is a chain map modulo two
exactly when, for `ind p = ind q + ind r + 1`, the Y-flow lines broken at the root, at the first
leaf and at the second leaf (`TauCeti.morseRootBrokenDiagonalSet`,
`TauCeti.morseFirstLeafBrokenDiagonalSet`, `TauCeti.morseSecondLeafBrokenDiagonalSet`) are evenly
many in total. This file proves that they are
(`IsMorseSmaleTriple.even_ncard_root_add_ncard_firstLeaf_add_ncard_secondLeaf`): they are the
endpoints of the compactified one-dimensional Y-slice. Hence the Morse diagonal is a chain map
(`IsMorseSmaleTriple.morseDiagonalMap_comp_morseBoundary`) and the Morse cup product satisfies the
Leibniz rule `δ(a ∪ b) = δa ∪ b + a ∪ δb` (`IsMorseSmaleTriple.morseCupProduct_comp_morseBoundary`).

The compactification is built inside `M × M × M × M`, as for a Morse–Smale pair in
`TauCeti.Geometry.Manifold.Morse.Boundary.Pair.ChainMap`. Choose a level `c₀` below `f₀ p` and
above every critical value of `f₀` below `f₀ p`, and levels `cᵢ` above `f₁ q`, respectively `f₂ r`,
and below every critical value of `fᵢ` above it. A point `x` of the Y-slice is recorded by the
quadruple of

* the point of its `X₀`-orbit on the level `max (f₀ x) c₀`,
* the point `x` itself,
* the point of its `X₁`-orbit on the level `min (f₁ x) c₁`, and
* the point of its `X₂`-orbit on the level `min (f₂ x) c₂`.

The records of the points of the Y-slice form a copy of it, hence a one-manifold. Their limits
break once (`IsMorseSmaleTriple.closure_morseYSlice_subset`), along one of the three edges, and the
limit of the corresponding component of the records is then a point of the trajectory along which
the edge breaks. The records of the broken Y-flow lines are in bijection with the broken Y-flow
lines themselves.

Near each broken record, the half-open gluing chart into a transverse set
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_Ico_of_isSliceChart`) shows that
it is an endpoint:

* at the root, glue the trajectory of `X₀` from `p` to `a` into the intersection
  `W^s_{X₁}(q) ∩ W^s_{X₂}(r)`, of dimension `n - ind a`, which the Morse–Smale condition of the
  triple makes transverse to `W^u_{X₀}(a)`;
* at the first leaf, glue the trajectory of `-X₁` from `q` to `b` into `W^u_{X₀}(p) ∩ W^s_{X₂}(r)`,
  of dimension `ind b`, transverse to `W^s_{X₁}(b)`;
* at the second leaf, exchange the two leaves (`IsMorseSmaleTriple.swap`).

In each case the remaining components of the records are continuous functions of the vertex.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmaleTriple`:

* `even_ncard_root_add_ncard_firstLeaf_add_ncard_secondLeaf`: between any three critical points,
  the Y-flow lines broken at the root, at the first leaf and at the second leaf are evenly many in
  total.
* `morseDiagonalMap_comp_morseBoundary`: the mod-two Morse diagonal of the Y-slices is a chain map,
  `Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ`.
* `morseCupProduct_comp_morseBoundary`: the Leibniz rule `δ(a ∪ b) = δa ∪ b + a ∪ δb` of the
  mod-two Morse cup product.

## References

* K. Fukaya, *Morse homotopy, A∞-category, and Floer homologies*, Proceedings of GARC Workshop on
  Geometry and Topology '93, Lecture Notes Ser. 18, Seoul Nat. Univ., 1993, 1–102 (the Morse cup
  product by counting Y-shaped flow lines).
* S. Mescher, *Perturbed gradient flow trees and A∞-algebra structures in Morse cohomology*,
  [arXiv:1611.07916](https://arxiv.org/abs/1611.07916), §§1–5 (transversality, compactness and the
  boundary of the moduli spaces of Y-shaped flow trees).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ f₂ : M → ℝ} {X₀ X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### Transverse sets at a broken Y-flow line -/

namespace IsMorseSmaleTriple

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂}

/-- **The leaves of a Y-flow line broken at the root.** At a point `y` of the Y-slice from `a` to
`q` and `r` of a Morse–Smale triple, with `ind a = ind q + ind r`, the intersection
`W^s_{X₁}(q) ∩ W^s_{X₂}(r)` is flattened near `y` by a chart of the maximal atlas onto a subspace of
dimension `n - ind a`, and is transverse to `W^u_{X₀}(a)` at `y`. -/
private theorem exists_isSliceChart_stableSet_inter_stableSet (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    {a q r y : M} (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a q r)
    (haqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ a =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    ∃ (L : Submodule ℝ E) (φ : OpenPartialHomeomorph M E), y ∈ φ.source ∧
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart φ (L : Set E) (hX₁.flow.stableSet q ∩ hX₂.flow.stableSet r) ∧
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f₀ a = Module.finrank ℝ E ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet q ∩ hX₂.flow.stableSet r) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet a) y) = ⊤ := by
  obtain ⟨-, hyq, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  obtain ⟨hU₁, hU₁₂⟩ := h.span_mtangentConeAt_sup_eq_top_and_inf_sup_eq_top hy
  -- In the modular lattice of subspaces, `U ⊔ S₁ = ⊤` and `(U ⊓ S₁) ⊔ S₂ = ⊤` give
  -- `S₁ ⊔ S₂ = ⊤` and `U ⊔ (S₁ ⊓ S₂) = ⊤`.
  have h₁₂ : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet q) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet r) y) = ⊤ :=
    top_unique (hU₁₂.symm.le.trans (sup_le_sup_right inf_le_right _))
  have hU := codisjoint_iff.1 ((codisjoint_iff.2 hU₁).codisjoint_inf_right_of_codisjoint_inf_left
    (codisjoint_iff.2 hU₁₂))
  obtain ⟨L₁, φ₁, -, hy₁, hφ₁, hs₁⟩ :=
    hX₁.exists_isSliceChart_stableSet (hX₁.mfderiv_eq_zero_of_mem_stableSet hyq) hyq
  obtain ⟨L₂, φ₂, -, hy₂, hφ₂, hs₂⟩ :=
    hX₂.exists_isSliceChart_stableSet (hX₂.mfderiv_eq_zero_of_mem_stableSet hyr) hyr
  have hc (L : Submodule ℝ E) : L.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient
      (Submodule.isClosed_of_finiteDimensional _)
  obtain ⟨φ, hyφ, hφ, hZ⟩ := exists_isSliceChart_inter_of_span_mtangentConeAt_sup_eq_top (by simp)
    hφ₁ hφ₂ hs₁ hs₂ hy₁ hy₂ h₁₂ (hc _) (hc _) (hc _)
  have hT := span_mtangentConeAt_inter_of_span_mtangentConeAt_sup_eq_top (by simp) hφ₁ hφ₂ hs₁ hs₂
    hy₁ hy₂ h₁₂ (hc _) (hc _) (hc _)
  refine ⟨_, φ, hyφ, hφ, hZ, ?_, by rw [hT, sup_comm, hU]⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet q) y))
    (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₂.flow.stableSet r) y))
  rw [h₁₂, finrank_top] at hdim
  have := hX₁.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hyq
  have := hX₂.finrank_span_mtangentConeAt_stableSet_add_manifoldMorseIndex hyr
  omega

/-- **The root and second leaf of a Y-flow line broken at the first leaf.** At a point `y` of the
Y-slice from `p` to `b` and `r` of a Morse–Smale triple, with `ind p = ind b + ind r`, the
intersection `W^u_{X₀}(p) ∩ W^s_{X₂}(r)` is flattened near `y` by a chart of the maximal atlas onto
a subspace of dimension `ind b`, and is transverse to `W^s_{X₁}(b)` at `y`. -/
private theorem exists_isSliceChart_unstableSet_inter_stableSet
    (h : IsMorseSmaleTriple hX₀ hX₁ hX₂) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) {p b r y : M}
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ p b r)
    (hpbr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ r) :
    ∃ (L : Submodule ℝ E) (φ : OpenPartialHomeomorph M E), y ∈ φ.source ∧
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart φ (L : Set E) (hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r) ∧
      Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f₁ b ∧
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX₁.flow.stableSet b) y) = ⊤ := by
  obtain ⟨hyp, -, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  -- Exchanging the leaves, `U ⊔ S₂ = ⊤` and `(U ⊓ S₂) ⊔ S₁ = ⊤`.
  obtain ⟨hU₂, hU₂₁⟩ := h.swap.span_mtangentConeAt_sup_eq_top_and_inf_sup_eq_top
    (by rwa [morseYSlice_comm] : y ∈ hX₀.morseYSlice hX₂ hX₁ p r b)
  obtain ⟨φ, hyφ, hφ, hZ⟩ := hX₀.exists_unstableSet_inter_stableSet_chart hX₂ hf₀ ⟨hyp, hyr⟩ hU₂
  have hT := hX₀.span_mtangentConeAt_unstableSet_inter_stableSet hX₂ hf₀ ⟨hyp, hyr⟩ hU₂
  have hdim := hX₀.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex
    hX₂ hf₀ ⟨hyp, hyr⟩ hU₂
  rw [hT] at hdim
  exact ⟨_, φ, hyφ, hφ, hZ, by omega, by rw [hT, hU₂₁]⟩

/-- **Gluing at the root.** The trajectory of `X₀` from `p` to `a` glues into
`W^s_{X₁}(q) ∩ W^s_{X₂}(r)`. Record a point `x` of the Y-slice from `p` to `q` and `r` by the pair
`(w, x)`, where `w` is the point of its `X₀`-orbit on the level of a point `a₁` of the trajectory,
and a Y-flow line broken at the root, with vertex `y` in the Y-slice from `a` to `q` and `r`, by
`(a₁, y)`. Then `(a₁, y)` has a neighbourhood among these pairs homeomorphic to `[0, δ)`, with
`(a₁, y)` corresponding to `0`. -/
private theorem exists_homeomorph_Ico_of_root (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) {p a q r a₁ y : M}
    (hpa : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1)
    (haqr : manifoldMorseIndex 𝓘(ℝ, E) f₀ a =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (ha₁ : a₁ ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a)
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ a q r) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, y) ∧
      N ⊆ insert (a₁, y) {v | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧ f₀ v.1 = f₀ a₁ ∧
        ∃ t, hX₀.flow t v.1 = v.2} ∧
      N ∈ 𝓝[insert (a₁, y) {v | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧ f₀ v.1 = f₀ a₁ ∧
        ∃ t, hX₀.flow t v.1 = v.2}] (a₁, y) := by
  obtain ⟨L, φ, hyφ, hφ, hZ, hdim, htr⟩ := h.exists_isSliceChart_stableSet_inter_stableSet hy haqr
  obtain ⟨hya, hyq, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  rw [morseYSlice_def, inter_assoc]
  exact h₀.exists_homeomorph_Ico_of_isSliceChart hf₀ hpa ha₁ hya hφ hZ hyφ ⟨hyq, hyr⟩ hdim htr

/-- **Gluing at the first leaf.** Reversing `X₁`, the trajectory of `X₁` from `b` to `q` glues into
`W^u_{X₀}(p) ∩ W^s_{X₂}(r)`. Record a point `x` of the Y-slice from `p` to `q` and `r` by the pair
`(w, x)`, where `w` is the point of its `X₁`-orbit on the level of a point `a₂` of the trajectory,
and a Y-flow line broken at the first leaf, with vertex `y` in the Y-slice from `p` to `b` and `r`,
by `(a₂, y)`. Then `(a₂, y)` has a neighbourhood among these pairs homeomorphic to `[0, δ)`, with
`(a₂, y)` corresponding to `0`. -/
private theorem exists_homeomorph_Ico_of_firstLeaf (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
    {p b q r a₂ y : M}
    (hpbr : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ r)
    (hbq : manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1)
    (ha₂ : a₂ ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet q)
    (hy : y ∈ hX₀.morseYSlice hX₁ hX₂ p b r) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₂, y) ∧
      N ⊆ insert (a₂, y) {v | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧ f₁ v.1 = f₁ a₂ ∧
        ∃ t, hX₁.flow t v.1 = v.2} ∧
      N ∈ 𝓝[insert (a₂, y) {v | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧ f₁ v.1 = f₁ a₂ ∧
        ∃ t, hX₁.flow t v.1 = v.2}] (a₂, y) := by
  obtain ⟨hyp, hyb, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  obtain ⟨L, φ, hyφ, hφ, hZ, hL, htr⟩ :=
    h.exists_isSliceChart_unstableSet_inter_stableSet hf₀ hy hpbr
  -- For `-X₁` the trajectory runs from `q` to `b`, with the Morse indices `n - ind` of `-f₁`.
  have hb := hf₁.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₁.mfderiv_eq_zero_of_mem_stableSet hyb)
  have hq := hf₁.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (hX₁.mfderiv_eq_zero_of_mem_stableSet ha₂.2)
  have := hb.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have hset : {v : M × M | v.2 ∈ (hX₁.neg hf₁).flow.unstableSet q ∩
      (hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r) ∧ (-f₁) v.1 = (-f₁) a₂ ∧
        ∃ t, (hX₁.neg hf₁).flow t v.1 = v.2} =
      {v | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧ f₁ v.1 = f₁ a₂ ∧ ∃ t, hX₁.flow t v.1 = v.2} := by
    ext v
    simp only [mem_ofPred_eq, mem_inter_iff, hX₀.mem_morseYSlice hX₁ hX₂, hX₁.neg_flow hf₁,
      Flow.unstableSet_reverse, Flow.reverse_apply, Pi.neg_apply, neg_inj]
    exact and_congr (by tauto) (and_congr_right fun _ ↦
      ⟨fun ⟨t, ht⟩ ↦ ⟨-t, ht⟩, fun ⟨t, ht⟩ ↦ ⟨-t, by rwa [neg_neg]⟩⟩)
  rw [hX₁.stableSet_eq_unstableSet_neg hf₁] at htr hyb
  rw [← hset]
  exact (h₁.neg hf₁).exists_homeomorph_Ico_of_isSliceChart hf₁.neg
    (hb.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hbq)
    (by rw [← hX₁.stableSet_eq_unstableSet_neg hf₁, ← hX₁.unstableSet_eq_stableSet_neg hf₁]
        exact ⟨ha₂.2, ha₂.1⟩) hyb hφ hZ hyφ ⟨hyp, hyr⟩ (by omega) htr

end IsMorseSmaleTriple

/-! ### The compactified Y-slice -/

section Records

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (hX₂ : IsAdaptedPseudoGradient f₂ X₂)

/-- The record of a point `x` of a Y-slice: the point of its `X₀`-orbit on the level
`max (f₀ x) c₀`, the point itself, and the points of its `X₁`- and `X₂`-orbits on the levels
`min (f₁ x) c₁` and `min (f₂ x) c₂`. -/
private noncomputable def yRecord (c₀ c₁ c₂ : ℝ) (x : M) : M × M × M × M :=
  (hX₀.upperLevelPoint c₀ x, x, hX₁.lowerLevelPoint c₁ x, hX₂.lowerLevelPoint c₂ x)

private theorem yRecord_apply (c₀ c₁ c₂ : ℝ) (x : M) :
    hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ x =
      (hX₀.upperLevelPoint c₀ x, x, hX₁.lowerLevelPoint c₁ x, hX₂.lowerLevelPoint c₂ x) :=
  rfl

/-- The records of the Y-flow lines broken at the root: a point of a trajectory of `X₀` from `p` to
a critical point `a` on the level `c₀`, a point `y` of the Y-slice from `a` to `q` and `r`, and the
points of the `X₁`- and `X₂`-orbits of `y` on the levels `min (f₁ y) c₁` and `min (f₂ y) c₂`. -/
private def rootBrokenRecords (p q r : M) (c₀ c₁ c₂ : ℝ) : Set (M × M × M × M) :=
  {w | ∃ a, manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₀ a =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
    w.1 ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a ∧ f₀ w.1 = c₀ ∧
    w.2.1 ∈ hX₀.morseYSlice hX₁ hX₂ a q r ∧
    w.2.2.1 = hX₁.lowerLevelPoint c₁ w.2.1 ∧ w.2.2.2 = hX₂.lowerLevelPoint c₂ w.2.1}

/-- The records of the Y-flow lines broken at the first leaf: the point of the `X₀`-orbit of a point
`y` of the Y-slice from `p` to `b` and `r` on the level `max (f₀ y) c₀`, the point `y`, a point of a
trajectory of `X₁` from `b` to `q` on the level `c₁`, and the point of the `X₂`-orbit of `y` on the
level `min (f₂ y) c₂`. -/
private def firstLeafBrokenRecords (p q r : M) (c₀ c₁ c₂ : ℝ) : Set (M × M × M × M) :=
  {w | ∃ b, manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ b + manifoldMorseIndex 𝓘(ℝ, E) f₂ r ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₁ q + 1 ∧
    w.2.1 ∈ hX₀.morseYSlice hX₁ hX₂ p b r ∧ w.1 = hX₀.upperLevelPoint c₀ w.2.1 ∧
    w.2.2.1 ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet q ∧ f₁ w.2.2.1 = c₁ ∧
    w.2.2.2 = hX₂.lowerLevelPoint c₂ w.2.1}

/-- The records of the Y-flow lines broken at the second leaf: those broken at the first leaf for
the triple with its two leaves exchanged, with the last two components exchanged. -/
private def secondLeafBrokenRecords (p q r : M) (c₀ c₁ c₂ : ℝ) : Set (M × M × M × M) :=
  (fun w : M × M × M × M ↦ (w.1, w.2.1, w.2.2.2, w.2.2.1)) ⁻¹'
    hX₀.firstLeafBrokenRecords hX₂ hX₁ p r q c₀ c₂ c₁

/-- No Y-flow line breaks along two different edges. -/
private theorem disjoint_brokenRecords (p q r : M) (c₀ c₁ c₂ : ℝ) :
    Disjoint (hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂)
        (hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) ∧
      Disjoint (hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
          hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂)
        (hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) := by
  -- At the root the vertex lies on `W^u_{X₀}(a)` with `a ≠ p`, at the first leaf on
  -- `W^s_{X₁}(b)` with `b ≠ q`, and otherwise on `W^u_{X₀}(p)` and `W^s_{X₁}(q)`.
  have hroot {w} (hw : w ∈ hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) :
      w.2.1 ∉ hX₀.flow.unstableSet p := by
    obtain ⟨a, hpa, -, -, -, hy, -⟩ := hw
    exact (Flow.disjoint_unstableSet (x := p) (y := a) (by rintro rfl; omega)).notMem_of_mem_right
      ((hX₀.mem_morseYSlice hX₁ hX₂).1 hy).1
  refine ⟨disjoint_left.2 fun w hw hw' ↦ ?_, disjoint_left.2 fun w hw hw' ↦ ?_⟩
  · obtain ⟨b, -, -, hy, -⟩ := hw'
    exact hroot hw ((hX₀.mem_morseYSlice hX₁ hX₂).1 hy).1
  obtain ⟨c, -, -, hy, -⟩ := hw'
  obtain ⟨hyp, -, hyq⟩ := (hX₀.mem_morseYSlice hX₂ hX₁).1 hy
  rcases hw with hw | ⟨b, -, hbq, hy', -⟩
  · exact hroot hw hyp
  · exact (Flow.disjoint_stableSet (x := b) (y := q) (by rintro rfl; omega)).notMem_of_mem_right
      hyq ((hX₀.mem_morseYSlice hX₁ hX₂).1 hy').2.1

variable {p q r : M} {c₀ c₁ c₂ : ℝ}

/-- The records of the Y-flow lines broken at the root are the images of these Y-flow lines,
moving the point of the trajectory from `p` to the level `c₀`. -/
private theorem rootBrokenRecords_eq_image (hc₀ : c₀ < f₀ p)
    (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀) :
    hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ =
      (fun x : criticalPoints 𝓘(ℝ, E) f₀ × M × M ↦ (hX₀.levelPoint c₀ x.2.1, x.2.2,
        hX₁.lowerLevelPoint c₁ x.2.2, hX₂.lowerLevelPoint c₂ x.2.2)) ''
        morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r := by
  ext w
  constructor
  · rintro ⟨a, hpa, haqr, hw₁, hw₁c, hy, hw₃, hw₄⟩
    have ha := mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₀.mfderiv_eq_zero_of_mem_stableSet hw₁.2)
    obtain ⟨hpa', hac⟩ := hX₀.ne_and_apply_lt_of_manifoldMorseIndex_eq_add_one hgap₀ hpa hw₁
    -- `w.1` is the level point of a point of the middle-level slice.
    obtain ⟨z, hz, hzw⟩ := (hX₀.bijOn_levelPoint_midpoint hpa' hac hc₀).surjOn ⟨hw₁, hw₁c⟩
    exact ⟨(⟨a, ha⟩, z, w.2.1), (mem_morseRootBrokenDiagonalSet hX₀).2
      ⟨hpa, haqr, (hX₀.mem_morseTrajectorySlice).2 ⟨hz.1.1, hz.1.2, hz.2⟩, hy⟩,
      Prod.ext hzw (Prod.ext rfl (Prod.ext hw₃.symm hw₄.symm))⟩
  · rintro ⟨⟨a, z, y⟩, hx, rfl⟩
    obtain ⟨hpa, haqr, hz, hy⟩ := (mem_morseRootBrokenDiagonalSet hX₀).1 hx
    dsimp only at hpa haqr hz hy
    rw [mem_morseTrajectorySlice] at hz
    obtain ⟨hpa', hac⟩ := hX₀.ne_and_apply_lt_of_manifoldMorseIndex_eq_add_one hgap₀
      hpa ⟨hz.1, hz.2.1⟩
    obtain ⟨hmem, hc⟩ := hX₀.mapsTo_levelPoint hpa' hac hc₀ ⟨hz.1, hz.2.1⟩
    exact ⟨a, hpa, haqr, hmem, hc, hy, rfl, rfl⟩

/-- Distinct Y-flow lines broken at the root have distinct records. -/
private theorem injOn_rootBrokenRecords (hc₀ : c₀ < f₀ p)
    (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀) :
    InjOn (fun x : criticalPoints 𝓘(ℝ, E) f₀ × M × M ↦ (hX₀.levelPoint c₀ x.2.1, x.2.2,
        hX₁.lowerLevelPoint c₁ x.2.2, hX₂.lowerLevelPoint c₂ x.2.2))
      (morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r) := by
  rintro ⟨a, z, y⟩ hx ⟨a', z', y'⟩ hx' heq
  obtain ⟨hpa, -, hz, -⟩ := (mem_morseRootBrokenDiagonalSet hX₀).1 hx
  obtain ⟨hpa₂, -, hz', -⟩ := (mem_morseRootBrokenDiagonalSet hX₀).1 hx'
  dsimp only at hpa hz hpa₂ hz'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨heq, rfl, -⟩ := heq
  rw [mem_morseTrajectorySlice] at hz hz'
  obtain ⟨hpa', hac⟩ := hX₀.ne_and_apply_lt_of_manifoldMorseIndex_eq_add_one hgap₀
    hpa ⟨hz.1, hz.2.1⟩
  obtain ⟨hpa₂', hac'⟩ := hX₀.ne_and_apply_lt_of_manifoldMorseIndex_eq_add_one hgap₀
    hpa₂ ⟨hz'.1, hz'.2.1⟩
  obtain ⟨-, ha, rfl⟩ := hX₀.eq_of_levelPoint_eq_of_mem_midpoint hpa' hac hc₀ hpa₂' hac' hc₀
    ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩ heq
  rw [Subtype.ext ha]

/-- The records of the Y-flow lines broken at the first leaf are the images of these Y-flow lines,
moving the point of the trajectory to `q` to the level `c₁`. -/
private theorem firstLeafBrokenRecords_eq_image (hc₁ : f₁ q < c₁)
    (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ q < f₁ x → c₁ < f₁ x) :
    hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ =
      (fun x : criticalPoints 𝓘(ℝ, E) f₁ × M × M ↦ (hX₀.upperLevelPoint c₀ x.2.1, x.2.1,
        hX₁.levelPoint c₁ x.2.2, hX₂.lowerLevelPoint c₂ x.2.1)) ''
        morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r := by
  ext w
  constructor
  · rintro ⟨b, hpbr, hbq, hy, hw₁, hw₃, hw₃c, hw₄⟩
    have hb := mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₁.mfderiv_eq_zero_of_mem_unstableSet hw₃.1)
    obtain ⟨hbq', hcb⟩ := hX₁.ne_and_lt_apply_of_manifoldMorseIndex_eq_add_one hgap₁ hbq hw₃
    -- `w.2.2.1` is the level point of a point of the middle-level slice.
    obtain ⟨z, hz, hzw⟩ := (hX₁.bijOn_levelPoint_midpoint hbq' hc₁ hcb).surjOn ⟨hw₃, hw₃c⟩
    exact ⟨(⟨b, hb⟩, w.2.1, z), (mem_morseFirstLeafBrokenDiagonalSet hX₁).2
      ⟨hpbr, hbq, hy, (hX₁.mem_morseTrajectorySlice).2 ⟨hz.1.1, hz.1.2, hz.2⟩⟩,
      Prod.ext hw₁.symm (Prod.ext rfl (Prod.ext hzw hw₄.symm))⟩
  · rintro ⟨⟨b, y, z⟩, hx, rfl⟩
    obtain ⟨hpbr, hbq, hy, hz⟩ := (mem_morseFirstLeafBrokenDiagonalSet hX₁).1 hx
    dsimp only at hpbr hbq hy hz
    rw [mem_morseTrajectorySlice] at hz
    obtain ⟨hbq', hcb⟩ := hX₁.ne_and_lt_apply_of_manifoldMorseIndex_eq_add_one hgap₁
      hbq ⟨hz.1, hz.2.1⟩
    obtain ⟨hmem, hc⟩ := hX₁.mapsTo_levelPoint hbq' hc₁ hcb ⟨hz.1, hz.2.1⟩
    exact ⟨b, hpbr, hbq, hy, rfl, hmem, hc, rfl⟩

/-- Distinct Y-flow lines broken at the first leaf have distinct records. -/
private theorem injOn_firstLeafBrokenRecords (hc₁ : f₁ q < c₁)
    (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ q < f₁ x → c₁ < f₁ x) :
    InjOn (fun x : criticalPoints 𝓘(ℝ, E) f₁ × M × M ↦ (hX₀.upperLevelPoint c₀ x.2.1, x.2.1,
        hX₁.levelPoint c₁ x.2.2, hX₂.lowerLevelPoint c₂ x.2.1))
      (morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r) := by
  rintro ⟨b, y, z⟩ hx ⟨b', y', z'⟩ hx' heq
  obtain ⟨-, hbq, -, hz⟩ := (mem_morseFirstLeafBrokenDiagonalSet hX₁).1 hx
  obtain ⟨-, hbq₂, -, hz'⟩ := (mem_morseFirstLeafBrokenDiagonalSet hX₁).1 hx'
  dsimp only at hbq hz hbq₂ hz'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl, heq, -⟩ := heq
  rw [mem_morseTrajectorySlice] at hz hz'
  obtain ⟨hbq', hcb⟩ := hX₁.ne_and_lt_apply_of_manifoldMorseIndex_eq_add_one hgap₁
    hbq ⟨hz.1, hz.2.1⟩
  obtain ⟨hbq₂', hcb'⟩ := hX₁.ne_and_lt_apply_of_manifoldMorseIndex_eq_add_one hgap₁
    hbq₂ ⟨hz'.1, hz'.2.1⟩
  obtain ⟨hb, -, rfl⟩ := hX₁.eq_of_levelPoint_eq_of_mem_midpoint hbq' hc₁ hcb hbq₂' hc₁ hcb'
    ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩ heq
  rw [Subtype.ext hb]

end Records

namespace IsMorseSmaleTriple

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} {p : criticalPoints 𝓘(ℝ, E) f₀}
  {q : criticalPoints 𝓘(ℝ, E) f₁} {r : criticalPoints 𝓘(ℝ, E) f₂} {c₀ c₁ c₂ : ℝ}
  (h : IsMorseSmaleTriple hX₀ hX₁ hX₂) (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
  (h₂ : hX₂.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
  (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1)
  (hc₀ : c₀ < f₀ p) (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀)
  (hc₁ : f₁ q < c₁) (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ q < f₁ x → c₁ < f₁ x)
  (hc₂ : f₂ r < c₂) (hgap₂ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₂, f₂ r < f₂ x → c₂ < f₂ x)

include h h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂

/-- **The limits of records of the Y-slice**, for `ind p = ind q + ind r + 1`, are records of its
points or of Y-flow lines broken at the root, at the first leaf or at the second leaf. -/
private theorem closure_yRecords_subset :
    closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r) ⊆
      hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r ∪
        (hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
          hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
          hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  intro w hw
  obtain ⟨v, hvP, hvw⟩ := mem_closure_iff_seq_limit.1 hw
  choose x hxS hxv using hvP
  obtain rfl : (fun n ↦ hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ (x n)) = v := funext hxv
  set y := w.2.1
  have hx : Tendsto x atTop (𝓝 y) := ((continuous_fst.comp continuous_snd).tendsto w).comp hvw
  have hx' n := (hX₀.mem_morseYSlice hX₁ hX₂).1 (hxS n)
  have h₁w : Tendsto (fun n ↦ hX₀.upperLevelPoint c₀ (x n)) atTop (𝓝 w.1) :=
    (continuous_fst.tendsto w).comp hvw
  have h₃w : Tendsto (fun n ↦ hX₁.lowerLevelPoint c₁ (x n)) atTop (𝓝 w.2.2.1) :=
    (((continuous_fst.comp continuous_snd).comp continuous_snd).tendsto w).comp hvw
  have h₄w : Tendsto (fun n ↦ hX₂.lowerLevelPoint c₂ (x n)) atTop (𝓝 w.2.2.2) :=
    (((continuous_snd.comp continuous_snd).comp continuous_snd).tendsto w).comp hvw
  -- Where the limit lies on the unstable or stable manifolds, its records are the limits.
  have hup (hy : y ∈ hX₀.flow.unstableSet p) : w.1 = hX₀.upperLevelPoint c₀ y :=
    tendsto_nhds_unique h₁w ((hX₀.continuousOn_upperLevelPoint hc₀ y hy).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx, .of_forall fun n ↦ (hx' n).1⟩))
  have hlow₁ (hy : y ∈ hX₁.flow.stableSet q) : w.2.2.1 = hX₁.lowerLevelPoint c₁ y :=
    tendsto_nhds_unique h₃w ((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁ y hy).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx, .of_forall fun n ↦ (hx' n).2.1⟩))
  have hlow₂ (hy : y ∈ hX₂.flow.stableSet r) : w.2.2.2 = hX₂.lowerLevelPoint c₂ y :=
    tendsto_nhds_unique h₄w ((hX₂.continuousOn_lowerLevelPoint hf₂ hc₂ y hy).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx, .of_forall fun n ↦ (hx' n).2.2⟩))
  rcases h.closure_morseYSlice_subset h₀ h₁ h₂ hf₀ hf₁ hf₂ hind
    (mem_closure_of_tendsto hx (.of_forall hxS)) with ((hy | hy) | hy) | hy
  · obtain ⟨hyp, hyq, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
    exact Or.inl ⟨y, hy, by rw [yRecord_apply, ← hup hyp, ← hlow₁ hyq, ← hlow₂ hyr]⟩
  · -- Breaking at the root, at a critical point `a` below the level `c₀`.
    obtain ⟨a, ⟨haqr, z, hz⟩, hya⟩ := mem_iUnion₂.1 hy
    obtain ⟨hya', hyq, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hya
    obtain ⟨-, hac⟩ := hX₀.ne_and_apply_lt_of_manifoldMorseIndex_eq_add_one hgap₀ (by omega) hz
    obtain ⟨hw₁, hw₁c⟩ := h₀.mem_of_tendsto_upperLevelPoint_of_mem_unstableSet hf₀
      (by omega) hya' hac hc₀ (fun n ↦ (hx' n).1) hx h₁w
    exact Or.inr (Or.inl (Or.inl ⟨a, by omega, haqr, hw₁, hw₁c, hya, hlow₁ hyq, hlow₂ hyr⟩))
  · -- Breaking at the first leaf, at a critical point `b` above the level `c₁`.
    obtain ⟨b, ⟨hpbr, z, hz⟩, hyb⟩ := mem_iUnion₂.1 hy
    obtain ⟨hyp, hyb', hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hyb
    obtain ⟨-, hcb⟩ := hX₁.ne_and_lt_apply_of_manifoldMorseIndex_eq_add_one hgap₁ (by omega) hz
    obtain ⟨hw₃, hw₃c⟩ := h₁.mem_of_tendsto_lowerLevelPoint_of_mem_stableSet hf₁
      (by omega) hyb' hc₁ hcb (fun n ↦ (hx' n).2.1) hx h₃w
    exact Or.inr (Or.inl (Or.inr ⟨b, hpbr, by omega, hyb, hup hyp, hw₃, hw₃c, hlow₂ hyr⟩))
  · -- Breaking at the second leaf, at a critical point `c` above the level `c₂`.
    obtain ⟨c, ⟨hpqc, z, hz⟩, hyc⟩ := mem_iUnion₂.1 hy
    obtain ⟨hyp, hyq, hyc'⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hyc
    obtain ⟨-, hcc⟩ := hX₂.ne_and_lt_apply_of_manifoldMorseIndex_eq_add_one hgap₂ (by omega) hz
    obtain ⟨hw₄, hw₄c⟩ := h₂.mem_of_tendsto_lowerLevelPoint_of_mem_stableSet hf₂
      (by omega) hyc' hc₂ hcc (fun n ↦ (hx' n).2.2) hx h₄w
    exact Or.inr (Or.inr ⟨c, by omega, by omega, by rwa [morseYSlice_comm], hup hyp, hw₄, hw₄c,
      hlow₁ hyq⟩)

omit hind in
/-- There are finitely many records of broken Y-flow lines. -/
private theorem finite_brokenRecords :
    (hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
      hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
      hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂).Finite := by
  have hS {p' q' r' : M} (hp' : manifoldMorseIndex 𝓘(ℝ, E) f₀ p' =
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q' + manifoldMorseIndex 𝓘(ℝ, E) f₂ r') :=
    h.finite_morseYSlice h₀ h₁ h₂ hf₀ hf₁ hf₂ hp'.le
  rw [hX₀.rootBrokenRecords_eq_image hX₁ hX₂ hc₀ hgap₀,
    hX₀.firstLeafBrokenRecords_eq_image hX₁ hX₂ hc₁ hgap₁, secondLeafBrokenRecords,
    hX₀.firstLeafBrokenRecords_eq_image hX₂ hX₁ hc₂ hgap₂,
    morseFirstLeafBrokenDiagonalSet_swap hX₀ hX₁ hX₂ p q r]
  exact (((finite_morseRootBrokenDiagonalSet h₀ hf₀ p q r fun _ ↦ hS).image _).union
    ((finite_morseFirstLeafBrokenDiagonalSet h₁ hf₁ p q r fun _ ↦ hS).image _)).union
    (((finite_morseSecondLeafBrokenDiagonalSet h₂ hf₂ p q r fun _ ↦ hS).image _).preimage
      ((Equiv.refl M).prodCongr ((Equiv.refl M).prodCongr (Equiv.prodComm M M))).injective.injOn)

omit hind in
/-- The records of the broken Y-flow lines are as many as the broken Y-flow lines. -/
private theorem ncard_brokenRecords :
    (hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
      hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
      hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂).ncard =
      (morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r).ncard +
        (morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r).ncard +
        (morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r).ncard := by
  have hfin := h.finite_brokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂
  obtain ⟨hdisj₀₁, hdisj₂⟩ := hX₀.disjoint_brokenRecords hX₁ hX₂ p q r c₀ c₁ c₂
  rw [ncard_union_eq hdisj₂ (hfin.subset subset_union_left) (hfin.subset subset_union_right),
    ncard_union_eq hdisj₀₁ (hfin.subset (subset_union_left.trans subset_union_left))
      (hfin.subset (subset_union_right.trans subset_union_left)),
    hX₀.rootBrokenRecords_eq_image hX₁ hX₂ hc₀ hgap₀,
    (hX₀.injOn_rootBrokenRecords hX₁ hX₂ hc₀ hgap₀).ncard_image,
    hX₀.firstLeafBrokenRecords_eq_image hX₁ hX₂ hc₁ hgap₁,
    (hX₀.injOn_firstLeafBrokenRecords hX₁ hX₂ hc₁ hgap₁).ncard_image,
    secondLeafBrokenRecords, ncard_preimage_of_injective_subset_range
      (f := fun w : M × M × M × M ↦ (w.1, w.2.1, w.2.2.2, w.2.2.1))
      ((Equiv.refl M).prodCongr ((Equiv.refl M).prodCongr (Equiv.prodComm M M))).injective
      fun w _ ↦ ⟨(w.1, w.2.1, w.2.2.2, w.2.2.1), rfl⟩,
    hX₀.firstLeafBrokenRecords_eq_image hX₂ hX₁ hc₂ hgap₂,
    (hX₀.injOn_firstLeafBrokenRecords hX₂ hX₁ hc₂ hgap₂).ncard_image,
    morseFirstLeafBrokenDiagonalSet_swap hX₀ hX₁ hX₂ p q r]

/-- The compactified Y-slice adds finitely many records to those of its points. -/
private theorem finite_closure_diff_yRecords :
    (closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r) \
      hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r).Finite :=
  (h.finite_brokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂).subset fun _ hw ↦
    (h.closure_yRecords_subset h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂
      hw.1).resolve_left hw.2

/-- **The compactified Y-slice is one-dimensional at unbroken records.** Every record of a point of
the Y-slice has a neighbourhood in the closure of the records homeomorphic to an open subset of
`ℝ`. -/
private theorem exists_nhds_homeomorph_of_mem_yRecords {w : M × M × M × M}
    (hw : w ∈ closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r))
    (hwP : w ∈ hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r) :
    ∃ N ∈ 𝓝 (⟨w, hw⟩ : closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)),
      ∃ V : Set ℝ, IsOpen V ∧ Nonempty (V ≃ₜ N) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hwP
  set S := hX₀.morseYSlice hX₁ hX₂ p q r
  set P := hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' S
  have hS (x) (hx : x ∈ S) := (hX₀.mem_morseYSlice hX₁ hX₂).1 hx
  have hcont : ContinuousOn (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂) S :=
    ((hX₀.continuousOn_upperLevelPoint hc₀).mono fun x hx ↦ (hS x hx).1).prodMk
      (continuousOn_id.prodMk
        (((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁).mono fun x hx ↦ (hS x hx).2.1).prodMk
          ((hX₂.continuousOn_lowerLevelPoint hf₂ hc₂).mono fun x hx ↦ (hS x hx).2.2)))
  -- The records of the points of `S` form a copy of `S`.
  have hmemS (w : P) : (w : M × M × M × M).2.1 ∈ S := by
    obtain ⟨_, x, hx, rfl⟩ := w
    exact hx
  let Φ : P ≃ₜ S :=
    { toFun w := ⟨(w : M × M × M × M).2.1, hmemS w⟩
      invFun x := ⟨hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ x, mem_image_of_mem _ x.property⟩
      left_inv := by rintro ⟨_, ⟨x, hx, rfl⟩⟩; rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_fst.comp continuous_snd).comp continuous_subtypeVal).subtype_mk hmemS
      continuous_invFun :=
        (hcont.comp_continuous continuous_subtypeVal fun x ↦ x.property).subtype_mk _ }
  -- `S` is a manifold modelled on a line `L`.
  obtain ⟨L, hL, C, -, -⟩ := h.exists_morseYSlice_isManifold hf₀ ⟨x₀, hx₀⟩
  let _ := C
  exact exists_nhds_homeomorph_of_isOpen_preimage_val (F := L)
    (isLocallyClosed_iff_isOpen_coborder.2 (h.finite_closure_diff_yRecords h₀ h₁ h₂ hf₀ hf₁ hf₂
      hind hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂).isClosed.isOpen_compl).isOpen_preimage_val_closure
    (by omega) Φ hw (mem_image_of_mem _ hx₀)

/-- **A Y-flow line broken at the root is an endpoint.** Its record lies in the closure of the
records of the Y-slice, and has a neighbourhood there homeomorphic to a half-open interval
`[0, δ)`, by a homeomorphism sending `0` to it. -/
private theorem exists_homeomorph_Ico_of_mem_rootBrokenRecords {w : M × M × M × M}
    (hw : w ∈ hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) :
    ∃ hb : w ∈ closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ :
          closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ :
            closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)) =
            ⟨w, hb⟩ := by
  have hcont₀ : Continuous f₀ := hX₀.mdifferentiable.continuous
  -- Near `w`, the compactified space adds no broken record other than `w`.
  have hnear := nhdsWithin_closure_le_nhdsWithin_insert
    (h.finite_closure_diff_yRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂) w
    self_mem_nhdsWithin
  obtain ⟨a₁, y, w₃, w₄⟩ := w
  obtain ⟨a, hpa, haqr, ha₁, ha₁c, hy, hw₃, hw₄⟩ := hw
  dsimp only at ha₁ ha₁c hy hw₃ hw₄
  subst hw₃ hw₄
  obtain ⟨hya, hyq, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  have hyc : f₀ y < c₀ := (Flow.le_of_mem_unstableSet_of_antitone hya hcont₀.continuousAt
    (hX₀.antitone_flow y)).trans_lt (ha₁c ▸ (hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet
      (by rintro rfl; omega) ha₁).1)
  obtain ⟨N, δ, hδ, e, he, hNsub, hN⟩ := h.exists_homeomorph_Ico_of_root h₀ hf₀ hpa haqr ha₁ hy
  -- The gluing chart records a point by its `X₀`-orbit on the level `c₀`; the last two components
  -- of the records are continuous functions of the second.
  have hR (v : M × M) (hv : v ∈ insert (a₁, y) {v : M × M | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧
      f₀ v.1 = f₀ a₁ ∧ ∃ t, hX₀.flow t v.1 = v.2}) :
      v.2 ∈ hX₁.flow.stableSet q ∩ hX₂.flow.stableSet r :=
    hv.elim (fun hv ↦ hv ▸ ⟨hyq, hyr⟩) fun hv ↦ ((hX₀.mem_morseYSlice hX₁ hX₂).1 hv.1).2
  refine exists_homeomorph_Ico_closure_of_homeomorph_Ico (fun u ↦ (u.1, u.2.1))
    (fun v ↦ (v.1, v.2, hX₁.lowerLevelPoint c₁ v.2, hX₂.lowerLevelPoint c₂ v.2)) (by fun_prop)
    (continuousOn_fst.prodMk (continuousOn_snd.prodMk
      (((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁).comp continuousOn_snd fun v hv ↦
        (hR v hv).1).prodMk
        ((hX₂.continuousOn_lowerLevelPoint hf₂ hc₂).comp continuousOn_snd fun v hv ↦
          (hR v hv).2))))
    (fun _ _ ↦ rfl) rfl ?_ ?_ hδ e he hNsub hN
  · -- Near `(a₁, y)`, the points of the chart lie below the level `c₀`, so they are records.
    have hev : ∀ᶠ v in 𝓝 (a₁, y), f₀ v.2 < c₀ :=
      ((hcont₀.comp continuous_snd).tendsto (a₁, y)).eventually (gt_mem_nhds hyc)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvR
    obtain ⟨hvY, hv₁, t, ht⟩ := hvR.1.resolve_left hvR.2
    exact ⟨v.2, hvY, by rw [yRecord_apply, hX₀.upperLevelPoint_eq_of_flow_eq
      ((hX₀.mem_morseYSlice hX₁ hX₂).1 hvY).1 hc₀ hv (hv₁.trans ha₁c) ht]⟩
  · -- Near the broken record, the records lie below the level `c₀` and come from the chart.
    have hev : ∀ᶠ u in 𝓝 (a₁, y, hX₁.lowerLevelPoint c₁ y, hX₂.lowerLevelPoint c₂ y),
        f₀ u.2.1 < c₀ :=
      (((hcont₀.comp continuous_fst).comp continuous_snd).tendsto _).eventually (gt_mem_nhds hyc)
    filter_upwards [hnear, nhdsWithin_le_nhds hev] with u hu huc
    rcases hu with rfl | ⟨x, hxY, rfl⟩
    · exact ⟨mem_insert _ _, rfl⟩
    · rw [yRecord_apply] at huc ⊢
      have hup := hX₀.upperLevelPoint_of_lt huc
      have hex := hX₀.exists_flow_eq_of_mem_unstableSet ((hX₀.mem_morseYSlice hX₁ hX₂).1 hxY).1
        hc₀ huc
      refine ⟨Or.inr ⟨hxY, ?_, -Flow.levelCrossingTime hX₀.flow f₀ c₀ x, ?_⟩, rfl⟩ <;> dsimp only
      · rw [hup, hX₀.apply_levelPoint hex, ha₁c]
      · rw [hup, hX₀.levelPoint_def, Flow.map_neg_apply_map]

/-- **A Y-flow line broken at the first leaf is an endpoint.** Its record lies in the closure of
the records of the Y-slice, and has a neighbourhood there homeomorphic to a half-open interval
`[0, δ)`, by a homeomorphism sending `0` to it. -/
private theorem exists_homeomorph_Ico_of_mem_firstLeafBrokenRecords {w : M × M × M × M}
    (hw : w ∈ hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) :
    ∃ hb : w ∈ closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ :
          closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ :
            closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)) =
            ⟨w, hb⟩ := by
  have hcont₁ : Continuous f₁ := hX₁.mdifferentiable.continuous
  -- Near `w`, the compactified space adds no broken record other than `w`.
  have hnear := nhdsWithin_closure_le_nhdsWithin_insert
    (h.finite_closure_diff_yRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂) w
    self_mem_nhdsWithin
  obtain ⟨w₁, y, a₂, w₄⟩ := w
  obtain ⟨b, hpbr, hbq, hy, hw₁, ha₂, ha₂c, hw₄⟩ := hw
  dsimp only at hy hw₁ ha₂ ha₂c hw₄
  subst hw₁ hw₄
  obtain ⟨hyp, hyb, hyr⟩ := (hX₀.mem_morseYSlice hX₁ hX₂).1 hy
  have hyc : c₁ < f₁ y := (ha₂c ▸ (hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet
    (by rintro rfl; omega) ha₂).2 : c₁ < f₁ b).trans_le
      (Flow.le_of_mem_stableSet_of_antitone hyb hcont₁.continuousAt (hX₁.antitone_flow y))
  obtain ⟨N, δ, hδ, e, he, hNsub, hN⟩ :=
    h.exists_homeomorph_Ico_of_firstLeaf h₁ hf₀ hf₁ hpbr hbq ha₂ hy
  -- The gluing chart records a point by its `X₁`-orbit on the level `c₁`; the other components of
  -- the records are continuous functions of the second.
  have hR (v : M × M) (hv : v ∈ insert (a₂, y) {v : M × M | v.2 ∈ hX₀.morseYSlice hX₁ hX₂ p q r ∧
      f₁ v.1 = f₁ a₂ ∧ ∃ t, hX₁.flow t v.1 = v.2}) :
      v.2 ∈ hX₀.flow.unstableSet p ∩ hX₂.flow.stableSet r :=
    hv.elim (fun hv ↦ hv ▸ ⟨hyp, hyr⟩) fun hv ↦ ⟨((hX₀.mem_morseYSlice hX₁ hX₂).1 hv.1).1,
      ((hX₀.mem_morseYSlice hX₁ hX₂).1 hv.1).2.2⟩
  refine exists_homeomorph_Ico_closure_of_homeomorph_Ico (fun u ↦ (u.2.2.1, u.2.1))
    (fun v ↦ (hX₀.upperLevelPoint c₀ v.2, v.2, v.1, hX₂.lowerLevelPoint c₂ v.2)) (by fun_prop)
    (((hX₀.continuousOn_upperLevelPoint hc₀).comp continuousOn_snd fun v hv ↦ (hR v hv).1).prodMk
      (continuousOn_snd.prodMk (continuousOn_fst.prodMk
        ((hX₂.continuousOn_lowerLevelPoint hf₂ hc₂).comp continuousOn_snd fun v hv ↦
          (hR v hv).2))))
    (fun _ _ ↦ rfl) rfl ?_ ?_ hδ e he hNsub hN
  · -- Near `(a₂, y)`, the points of the chart lie above the level `c₁`, so they are records.
    have hev : ∀ᶠ v in 𝓝 (a₂, y), c₁ < f₁ v.2 :=
      ((hcont₁.comp continuous_snd).tendsto (a₂, y)).eventually (lt_mem_nhds hyc)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvR
    obtain ⟨hvY, hv₁, t, ht⟩ := hvR.1.resolve_left hvR.2
    exact ⟨v.2, hvY, by rw [yRecord_apply, hX₁.lowerLevelPoint_eq_of_flow_eq
      ((hX₀.mem_morseYSlice hX₁ hX₂).1 hvY).2.1 hc₁ hv (hv₁.trans ha₂c) ht]⟩
  · -- Near the broken record, the records lie above the level `c₁` and come from the chart.
    have hev : ∀ᶠ u in 𝓝 (hX₀.upperLevelPoint c₀ y, y, a₂, hX₂.lowerLevelPoint c₂ y),
        c₁ < f₁ u.2.1 :=
      (((hcont₁.comp continuous_fst).comp continuous_snd).tendsto _).eventually (lt_mem_nhds hyc)
    filter_upwards [hnear, nhdsWithin_le_nhds hev] with u hu huc
    rcases hu with rfl | ⟨x, hxY, rfl⟩
    · exact ⟨mem_insert _ _, rfl⟩
    · rw [yRecord_apply] at huc ⊢
      have hlow := hX₁.lowerLevelPoint_of_lt huc
      have hex := hX₁.exists_flow_eq_of_mem_stableSet ((hX₀.mem_morseYSlice hX₁ hX₂).1 hxY).2.1
        hc₁ huc
      refine ⟨Or.inr ⟨hxY, ?_, -Flow.levelCrossingTime hX₁.flow f₁ c₁ x, ?_⟩, rfl⟩ <;> dsimp only
      · rw [hlow, hX₁.apply_levelPoint hex, ha₂c]
      · rw [hlow, hX₁.levelPoint_def, Flow.map_neg_apply_map]

/-- **A Y-flow line broken at the second leaf is an endpoint.** Its record lies in the closure of
the records of the Y-slice, and has a neighbourhood there homeomorphic to a half-open interval
`[0, δ)`, by a homeomorphism sending `0` to it. -/
private theorem exists_homeomorph_Ico_of_mem_secondLeafBrokenRecords {w : M × M × M × M}
    (hw : w ∈ hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) :
    ∃ hb : w ∈ closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ :
          closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ :
            closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)) =
            ⟨w, hb⟩ := by
  -- Exchanging the leaves, the Y-flow line breaks at the first leaf of `(X₀, X₂, X₁)`.
  obtain ⟨hb', N, hN, δ, hδ, e, he⟩ :=
    h.swap.exists_homeomorph_Ico_of_mem_firstLeafBrokenRecords h₀ h₂ h₁ hf₀ hf₂ hf₁ (by omega)
      hc₀ hgap₀ hc₂ hgap₂ hc₁ hgap₁ hw
  -- Exchanging the last two components carries the records of `(X₀, X₂, X₁)` to those of
  -- `(X₀, X₁, X₂)`, hence the closure of the former onto that of the latter.
  let σ := (Homeomorph.refl M).prodCongr ((Homeomorph.refl M).prodCongr (Homeomorph.prodComm M M))
  have hσ (u : M × M × M × M) : σ u = (u.1, u.2.1, u.2.2.2, u.2.2.1) := rfl
  have hσy : (fun x ↦ σ (hX₀.yRecord hX₂ hX₁ c₀ c₂ c₁ x)) = hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ := by
    funext x
    simp only [hσ, yRecord_apply]
  have hcl (u : M × M × M × M) :
      u ∈ closure (hX₀.yRecord hX₂ hX₁ c₀ c₂ c₁ '' hX₀.morseYSlice hX₂ hX₁ p r q) ↔
        σ u ∈ closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r) := by
    rw [← σ.injective.mem_set_image, σ.image_closure, image_image, hσy, morseYSlice_comm]
  -- Transport the half-open chart along the induced homeomorphism of the closures.
  let Φ := σ.subtype hcl
  have hΦ : Φ ⟨_, hb'⟩ = ⟨w, (hcl _).1 hb'⟩ :=
    Subtype.ext ((Homeomorph.subtype_apply_coe _ _ _).trans (hσ _))
  refine ⟨(hcl _).1 hb', Φ '' N, hΦ ▸ Φ.isOpenMap.image_mem_nhds hN, δ, hδ, e.trans (Φ.image N),
    ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.image_apply_coe, he, hΦ]

/-- **Broken Y-flow lines are endpoints.** The record of a Y-flow line broken at the root, at the
first leaf or at the second leaf lies in the closure of the records of the Y-slice, and has a
neighbourhood there homeomorphic to a half-open interval `[0, δ)`, by a homeomorphism sending `0`
to it. -/
private theorem exists_homeomorph_Ico_of_mem_brokenRecords {w : M × M × M × M}
    (hw : w ∈ hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
      hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂ ∪
      hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂) :
    ∃ hb : w ∈ closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ :
          closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ :
            closure (hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r)) =
            ⟨w, hb⟩ := by
  rcases hw with (hw | hw) | hw
  · exact h.exists_homeomorph_Ico_of_mem_rootBrokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀
      hc₁ hgap₁ hc₂ hgap₂ hw
  · exact h.exists_homeomorph_Ico_of_mem_firstLeafBrokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀
      hgap₀ hc₁ hgap₁ hc₂ hgap₂ hw
  · exact h.exists_homeomorph_Ico_of_mem_secondLeafBrokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀
      hgap₀ hc₁ hgap₁ hc₂ hgap₂ hw

end IsMorseSmaleTriple

namespace IsMorseSmaleTriple

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {hX₂ : IsAdaptedPseudoGradient f₂ X₂} (h : IsMorseSmaleTriple hX₀ hX₁ hX₂)
  (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (h₂ : hX₂.IsMorseSmale)
  (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) (hf₂ : IsMorse 𝓘(ℝ, E) f₂)
include h h₀ h₁ h₂ hf₀ hf₁ hf₂

/-- **Broken Y-flow lines come in pairs.** Let `(X₀, X₁, X₂)` be a Morse–Smale triple of
Morse–Smale pseudo-gradients adapted to Morse functions `f₀`, `f₁` and `f₂` on a compact
boundaryless manifold. Between any critical points `p` of `f₀`, `q` of `f₁` and `r` of `f₂`, the
Y-flow lines broken at the root, at the first leaf and at the second leaf are evenly many in total:
when `ind p = ind q + ind r + 1` they are the endpoints of the compactified one-dimensional Y-slice
`W^u_{X₀}(p) ∩ W^s_{X₁}(q) ∩ W^s_{X₂}(r)`, and otherwise there are none. -/
theorem even_ncard_root_add_ncard_firstLeaf_add_ncard_secondLeaf (p : criticalPoints 𝓘(ℝ, E) f₀)
    (q : criticalPoints 𝓘(ℝ, E) f₁) (r : criticalPoints 𝓘(ℝ, E) f₂) :
    Even ((morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r).ncard +
      (morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r).ncard +
      (morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r).ncard) := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p =
    manifoldMorseIndex 𝓘(ℝ, E) f₁ q + manifoldMorseIndex 𝓘(ℝ, E) f₂ r + 1
  swap
  · -- Without an index drop by one, no Y-flow line breaks.
    have hroot : morseRootBrokenDiagonalSet f₁ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₀ p q r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ by
        obtain ⟨hp, hq, -⟩ := (mem_morseRootBrokenDiagonalSet hX₀).1 hx
        omega
    have hfirst : morseFirstLeafBrokenDiagonalSet f₀ f₂ (hX₀.morseYSlice hX₁ hX₂) hX₁ p q r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ by
        obtain ⟨hp, hq, -⟩ := (mem_morseFirstLeafBrokenDiagonalSet hX₁).1 hx
        omega
    have hsecond :
        morseSecondLeafBrokenDiagonalSet f₀ f₁ (hX₀.morseYSlice hX₁ hX₂) hX₂ p q r = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ by
        obtain ⟨hp, hq, -⟩ := (mem_morseSecondLeafBrokenDiagonalSet hX₂).1 hx
        omega
    simp [hroot, hfirst, hsecond]
  -- Record the points of the Y-slice on levels `c₀` below `p`, `c₁` above `q` and `c₂` above `r`.
  obtain ⟨c₀, hc₀, hgap₀⟩ := hf₀.exists_lt_forall_lt (f₀ p)
  obtain ⟨c₁, hc₁, hgap₁⟩ := hf₁.exists_gt_forall_gt (f₁ q)
  obtain ⟨c₂, hc₂, hgap₂⟩ := hf₂.exists_gt_forall_gt (f₂ r)
  set P := hX₀.yRecord hX₁ hX₂ c₀ c₁ c₂ '' hX₀.morseYSlice hX₁ hX₂ p q r
  set B₀ := hX₀.rootBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂
  set B₁ := hX₀.firstLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂
  set B₂ := hX₀.secondLeafBrokenRecords hX₁ hX₂ p q r c₀ c₁ c₂
  have hcl := h.closure_yRecords_subset h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂
  have hB (w : M × M × M × M) (hw : w ∈ B₀ ∪ B₁ ∪ B₂) :=
    h.exists_homeomorph_Ico_of_mem_brokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁ hc₂
      hgap₂ hw
  -- The closure of the records is a compact space locally modelled on the half-line, whose
  -- endpoints are the records of broken Y-flow lines.
  have : CompactSpace (closure P) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  have hE : Even (((↑) : closure P → M × M × M × M) ⁻¹' (B₀ ∪ B₁ ∪ B₂)).ncard := by
    refine even_ncard_of_forall_exists_homeomorph_Ico (F := ℝ) (Module.finrank_self ℝ)
      (fun u hu ↦ ?_) fun u hu ↦ ?_
    · obtain ⟨_, N, hN, δ, hδ, e, he⟩ := hB _ hu
      exact ⟨N, hN, δ, hδ, e, he⟩
    · exact h.exists_nhds_homeomorph_of_mem_yRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hind hc₀ hgap₀ hc₁ hgap₁
        hc₂ hgap₂ u.property ((hcl u.property).resolve_right hu)
  -- Count the endpoints through the records of the broken Y-flow lines.
  rw [ncard_preimage_of_injective_subset_range Subtype.val_injective (by
      rw [Subtype.range_coe]
      exact fun w hw ↦ (hB w hw).1),
    h.ncard_brokenRecords h₀ h₁ h₂ hf₀ hf₁ hf₂ hc₀ hgap₀ hc₁ hgap₁ hc₂ hgap₂] at hE
  exact hE

/-- **The mod-two Morse diagonal is a chain map.** For a Morse–Smale triple `(X₀, X₁, X₂)` of
Morse–Smale pseudo-gradients adapted to Morse functions on a compact boundaryless manifold, the
Morse diagonal `Δ` of the Y-slices satisfies `Δ ∘ ∂₀ = (∂₁ ⊗ 1 + 1 ⊗ ∂₂) ∘ Δ`. -/
theorem morseDiagonalMap_comp_morseBoundary :
    morseDiagonalMap f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) ∘ₗ h₀.morseBoundary hf₀ =
      ((h₁.morseBoundary hf₁).rTensor _ + (h₂.morseBoundary hf₂).lTensor _) ∘ₗ
        morseDiagonalMap f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) :=
  (h.morseDiagonalMap_comp_morseBoundary_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂).2 fun p q r _ ↦
    h.even_ncard_root_add_ncard_firstLeaf_add_ncard_secondLeaf h₀ h₁ h₂ hf₀ hf₁ hf₂ p q r

/-- **The Leibniz rule of the mod-two Morse cup product.** For a Morse–Smale triple
`(X₀, X₁, X₂)` of Morse–Smale pseudo-gradients adapted to Morse functions on a compact
boundaryless manifold, the cup product of the Y-slices satisfies `δ(a ∪ b) = δa ∪ b + a ∪ δb` for
all linear forms `a` and `b` on the mod-two Morse chains, where `δa = a ∘ ∂` is the Morse
coboundary. -/
theorem morseCupProduct_comp_morseBoundary
    (a : (criticalPoints 𝓘(ℝ, E) f₁ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : (criticalPoints 𝓘(ℝ, E) f₂ →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) a b ∘ₗ h₀.morseBoundary hf₀ =
      morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) (a ∘ₗ h₁.morseBoundary hf₁) b +
        morseCupProduct f₀ hf₁ hf₂ (hX₀.morseYSlice hX₁ hX₂) a (b ∘ₗ h₂.morseBoundary hf₂) :=
  (h.morseCupProduct_comp_morseBoundary_eq_iff h₀ hf₀ h₁ hf₁ h₂ hf₂).2 (fun p q r _ ↦
    h.even_ncard_root_add_ncard_firstLeaf_add_ncard_secondLeaf h₀ h₁ h₂ hf₀ hf₁ hf₂ p q r) a b

end IsMorseSmaleTriple

end IsAdaptedPseudoGradient

end TauCeti
