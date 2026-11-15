/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Locally compact second-countable Hausdorff spaces are Polish

Every weakly locally compact, second-countable Hausdorff space `X` is completely metrizable and
Polish. The proof passes through the Alexandroff one-point compactification `OnePoint X`:

1. A countable basis of `X` together with the complements of a compact exhaustion
   `CompactExhaustion.choice X` forms a countable basis of `OnePoint X`, giving
   `SecondCountableTopology (OnePoint X)`.
2. Since `OnePoint X` is compact and normal (`OnePoint` of a weakly locally compact Hausdorff
   space), Urysohn's metrization theorem makes `OnePoint X` metrizable, and compactness makes any
   compatible uniformity complete, giving `PolishSpace (OnePoint X)`.
3. The canonical inclusion `X → OnePoint X` is an open embedding (`OnePoint.isOpenEmbedding_coe`),
   and open embeddings pull back both complete metrizability and Polishness via Mathlib's
   `IsOpen.isCompletelyMetrizableSpace` and `IsOpen.polishSpace`.

In particular, every second-countable locally compact Hausdorff topological group is a Polish
group.

## Main results

* `Topology.IsOpenEmbedding.isCompletelyMetrizableSpace` and
  `Topology.IsOpenEmbedding.polishSpace`: open embeddings pull back complete metrizability and
  Polishness.
* `OnePoint.instSecondCountableTopology` and `OnePoint.instPolishSpace`: the one-point
  compactification of a weakly locally compact, second-countable Hausdorff space is second-countable
  and Polish.
* `TauCeti.isCompletelyMetrizableSpace_of_weaklyLocallyCompactSpace` and
  `TauCeti.polishSpace_of_weaklyLocallyCompactSpace`: every weakly locally compact (in particular,
  locally compact), second-countable Hausdorff space is completely metrizable and Polish.

## Implementation notes

While `OnePoint.instSecondCountableTopology` and `OnePoint.instPolishSpace` are registered as
global instances (their heads have the type constructor `OnePoint`), the conclusions on a bare type
variable `X` are stated as theorems rather than global instances: registering
`[WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] : PolishSpace X` globally
would create typeclass synthesis cycles with `PolishSpace.toSecondCountableTopology` and
`TopologicalSpace.t2Space_of_metrizableSpace`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 5.3.
-/

public section

open Set Filter Topology TopologicalSpace
open scoped OnePoint Uniformity

namespace Topology.IsOpenEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- An open embedding into a completely metrizable space makes the domain completely metrizable. -/
theorem isCompletelyMetrizableSpace [IsCompletelyMetrizableSpace Y] (hf : IsOpenEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  have : IsCompletelyMetrizableSpace (range f) := hf.isOpen_range.isCompletelyMetrizableSpace
  exact hf.isEmbedding.toHomeomorph.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- An open embedding into a Polish space makes the domain Polish. -/
theorem polishSpace [PolishSpace Y] (hf : IsOpenEmbedding f) : PolishSpace X := by
  have : PolishSpace (range f) := hf.isOpen_range.polishSpace
  exact hf.isEmbedding.toHomeomorph.isClosedEmbedding.polishSpace

end Topology.IsOpenEmbedding

namespace OnePoint

variable {X : Type*} [TopologicalSpace X]

/-- The one-point compactification of a weakly locally compact, second-countable Hausdorff space is
second-countable: adding the complements of a compact exhaustion to a countable basis of `X` yields
a countable basis at infinity as well as at finite points. -/
instance instSecondCountableTopology [WeaklyLocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X] : SecondCountableTopology (OnePoint X) := by
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis X
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let B' : Set (Set (OnePoint X)) :=
    ((fun U : Set X => ((↑) '' U : Set (OnePoint X))) '' B) ∪
      range fun n : ℕ => (((↑) '' K n : Set (OnePoint X))ᶜ)
  have hB'c : B'.Countable := (hBc.image _).union (countable_range _)
  have hB' : IsTopologicalBasis B' := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro s (⟨U, hU, rfl⟩ | ⟨n, rfl⟩)
      · exact isOpen_image_coe.2 (hB.isOpen hU)
      · exact isOpen_compl_image_coe.2 ⟨K.isClosed n, K.isCompact n⟩
    · intro z s hzs hs
      induction z using OnePoint.rec with
      | infty =>
        obtain ⟨_, hKcomp⟩ := (isOpen_iff_of_mem hzs).1 hs
        obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hKcomp
        refine ⟨(((↑) '' K n : Set (OnePoint X))ᶜ), Or.inr ⟨n, rfl⟩,
          mem_compl infty_notMem_image_coe, ?_⟩
        intro w hw
        induction w using OnePoint.rec with
        | infty => exact hzs
        | coe x =>
          by_contra hx
          exact hw ⟨x, hn hx, rfl⟩
      | coe x =>
        obtain ⟨U, hUB, hxU, hUs⟩ := hB.exists_subset_of_mem_open hzs hs.2
        exact ⟨(↑) '' U, Or.inl ⟨U, hUB, rfl⟩, ⟨x, hxU, rfl⟩, image_subset_iff.2 hUs⟩
  exact ⟨⟨B', hB'c, hB'.eq_generateFrom⟩⟩

/-- The one-point compactification of a weakly locally compact, second-countable Hausdorff space is
completely metrizable: it is compact, Hausdorff, normal, and second-countable, hence metrizable by
Urysohn's theorem and complete by compactness. -/
instance instIsCompletelyMetrizableSpace [WeaklyLocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X] : IsCompletelyMetrizableSpace (OnePoint X) := by
  let _ : UniformSpace (OnePoint X) := pseudoMetrizableSpaceUniformity (OnePoint X)
  have : (𝓤 (OnePoint X)).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated (OnePoint X)
  infer_instance

/-- The one-point compactification of a weakly locally compact, second-countable Hausdorff space is
Polish. -/
instance instPolishSpace [WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] :
    PolishSpace (OnePoint X) :=
  inferInstance

end OnePoint

namespace TauCeti

/-- Every weakly locally compact (in particular, locally compact), second-countable Hausdorff space
is completely metrizable, as an open subspace of its one-point compactification. -/
theorem isCompletelyMetrizableSpace_of_weaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] :
    IsCompletelyMetrizableSpace X :=
  OnePoint.isOpenEmbedding_coe.isCompletelyMetrizableSpace

/-- **Every second-countable locally compact Hausdorff space is Polish.** Stated for weakly locally
compact spaces, which includes all `LocallyCompactSpace` instances automatically. -/
theorem polishSpace_of_weaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] :
    PolishSpace X :=
  OnePoint.isOpenEmbedding_coe.polishSpace

end TauCeti
