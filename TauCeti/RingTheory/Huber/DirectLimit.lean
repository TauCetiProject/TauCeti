/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic

/-!
# The ideal of definition of a directed colimit of Tate rings

Let `(Aᵢ, tᵢⱼ)` be a directed system of topological rings with continuous transition maps, and
let `φᵢ : Aᵢ → L` be compatible ring homomorphisms into a topological ring `L`. For a filtered
colimit of Tate rings with compatible rings of definition `A_{i,0}` containing a common
pseudouniformiser `ϖ`, topologised so that `L₀ = colim A_{i,0}` is open with its
`ϖ`-adic topology, the pair of definition `(L₀, ϖ L₀)` of `L` has an ideal of definition
consisting of images of topologically nilpotent elements of the stages
(`TauCeti.Huber.exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition`): an element `ϖ c`
with `c` coming from `A_{j,0}` is the image of a product of a power-bounded and a topologically
nilpotent element of a later stage.

This is the condition under which continuity of a valuation on `L`, and hence membership in the
adic spectrum of `L`, can be tested on the stages; see
`TauCeti/AlgebraicGeometry/AdicSpace/Spa/DirectLimit.lean`.

## Main results

* `TauCeti.Huber.exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition`: the ideal of
  definition `ϖ L₀` of a colimit of Tate rings consists of images of topologically nilpotent
  elements of the stages.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §6, proof of Lemma 6.13(ii).
-/

public section

namespace TauCeti.Huber

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {A : ι → Type*} [∀ i, CommRing (A i)]
  [∀ i, TopologicalSpace (A i)] {t : ∀ i j, i ≤ j → A i →+* A j}
  {L : Type*} [CommRing L] [TopologicalSpace L] {φ : ∀ i, A i →+* L}
  (hφt : ∀ i j (h : i ≤ j) a, φ j (t i j h a) = φ i a)

include hφt in
/-- **The ideal of definition of a colimit of Tate rings consists of images of topologically
nilpotent elements.** Let `Qᵢ ⊆ Aᵢ` be subrings of power-bounded elements preserved by the
transition maps (for instance compatible rings of definition `A_{i,0}`), and let `(L₀, I)` be a
pair of definition of `L` with `L₀` contained in the union of the images of the `Qᵢ` and
`I = ϖ L₀` for the image of a topologically nilpotent `ϖ ∈ A_{i₀}`. Then every element of `I` is
the image of a topologically nilpotent element of some stage. -/
theorem exists_isTopologicallyNilpotent_eq_of_mem_idealOfDefinition
    (ht : ∀ i j (h : i ≤ j), Continuous (t i j h)) (Q : ∀ i, Subring (A i))
    (hQ : ∀ i, ∀ c ∈ Q i, IsPowerBounded c)
    (htQ : ∀ i j (h : i ≤ j), ∀ c ∈ Q i, t i j h c ∈ Q j)
    (P : PairOfDefinition L) (hP : ∀ c ∈ P.ringOfDefinition, ∃ i, ∃ c' ∈ Q i, φ i c' = c)
    {i₀ : ι} {ϖ : A i₀} (hϖ : IsTopologicallyNilpotent ϖ) {ϖ' : P.ringOfDefinition}
    (hϖ' : (ϖ' : L) = φ i₀ ϖ) (hI : P.idealOfDefinition = Ideal.span {ϖ'})
    {a : P.ringOfDefinition} (ha : a ∈ P.idealOfDefinition) :
    ∃ i, ∃ y : A i, IsTopologicallyNilpotent y ∧ φ i y = a := by
  rw [hI, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  -- `c ϖ` with `c` the image of `c' ∈ Qⱼ` is the image of the product of the power-bounded `c'`
  -- and the topologically nilpotent `ϖ` at a stage above `i₀` and `j`
  obtain ⟨j, c', hc', hc'c⟩ := hP c c.2
  obtain ⟨k, hjk, hi₀k⟩ := directed_of (· ≤ ·) j i₀
  refine ⟨k, t j k hjk c' * t i₀ k hi₀k ϖ,
    (hQ k _ (htQ j k hjk c' hc')).isTopologicallyNilpotent_mul (hϖ.map (ht i₀ k hi₀k)), ?_⟩
  rw [map_mul, hφt, hφt, hc'c, ← hϖ', Subring.coe_mul]

end TauCeti.Huber
