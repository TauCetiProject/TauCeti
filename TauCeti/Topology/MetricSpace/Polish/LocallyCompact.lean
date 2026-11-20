/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Compactification.OnePoint.SecondCountable
public import TauCeti.Topology.MetricSpace.Polish.OpenEmbedding
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Locally compact second-countable Hausdorff spaces are Polish

Every weakly locally compact, second-countable Hausdorff space `X` is completely metrizable and
Polish. The proof passes through the Alexandroff one-point compactification `OnePoint X`:

1. By `OnePoint.instSecondCountableTopology`, `OnePoint X` is second-countable.
2. Since `OnePoint X` is compact and normal (`OnePoint` of a weakly locally compact Hausdorff
   space), Urysohn's metrization theorem makes `OnePoint X` metrizable, and compactness makes any
   compatible uniformity complete, giving `IsCompletelyMetrizableSpace (OnePoint X)` and hence
   `PolishSpace (OnePoint X)`.
3. The canonical inclusion `X → OnePoint X` is an open embedding (`OnePoint.isOpenEmbedding_coe`),
   and open embeddings pull back both complete metrizability and Polishness
   (`Topology.IsOpenEmbedding.isCompletelyMetrizableSpace`,
   `Topology.IsOpenEmbedding.polishSpace`).

In particular, every second-countable locally compact Hausdorff topological group is a Polish
group.

## Main results

* `OnePoint.instIsCompletelyMetrizableSpace`: the one-point compactification of a weakly locally
  compact, second-countable Hausdorff space is completely metrizable (and therefore Polish).
* `TauCeti.isCompletelyMetrizableSpace_of_weaklyLocallyCompactSpace` and
  `TauCeti.polishSpace_of_weaklyLocallyCompactSpace`: every weakly locally compact (in particular,
  locally compact), second-countable Hausdorff space is completely metrizable and Polish.

## Implementation notes

While `OnePoint.instIsCompletelyMetrizableSpace` is registered as a global instance (its head has
the type constructor `OnePoint`), the conclusions on a bare type variable `X` are stated as
theorems rather than global instances: registering
`[WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] : PolishSpace X` globally
would create typeclass synthesis cycles with `PolishSpace.toSecondCountableTopology` and
`TopologicalSpace.t2Space_of_metrizableSpace`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 5.3.
-/

public section

open Filter Topology TopologicalSpace
open scoped OnePoint Uniformity

namespace OnePoint

/-- The one-point compactification of a weakly locally compact, second-countable Hausdorff space is
completely metrizable. -/
instance instIsCompletelyMetrizableSpace {X : Type*} [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] :
    IsCompletelyMetrizableSpace (OnePoint X) := by
  let _ : UniformSpace (OnePoint X) := pseudoMetrizableSpaceUniformity (OnePoint X)
  have : (𝓤 (OnePoint X)).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated (OnePoint X)
  infer_instance

end OnePoint

namespace TauCeti

/-- Every weakly locally compact (in particular, locally compact), second-countable Hausdorff space
is completely metrizable. -/
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
