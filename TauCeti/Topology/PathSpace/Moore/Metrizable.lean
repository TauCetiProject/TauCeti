/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.FreeLoop
public import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Metrizability of Moore path and loop spaces

The stopped Moore path space of a metrizable space is metrizable in its existing topology:
the topology induced by duration and the compact-open map on `[0, ∞)`. The same holds for
based and free Moore loops. No bound on duration, compactness of the target, or geometric
length hypothesis is needed. We also retain the pseudometrizable versions.

The key input is Mathlib's compact-open metrizability theorem for continuous maps from a
weakly locally compact, sigma-compact source. In particular it applies to `[0, ∞)`, not just
to compact intervals. The existing embeddings of the Moore carriers then transfer this
property without changing their topologies.

Subspaces such as paths with prescribed endpoints and contractible free loops inherit these
instances. Consequently these carriers, and finite products of them, are first countable
and compactly generated when the target is metrizable. After importing
`Mathlib.Topology.Compactness.CompactlyGeneratedSpace`, the generic theorem
`eq_compactlyGenerated` identifies their raw topology with its
compactly generated refinement. This is the homeomorphism case of the comparison between
raw compact-open spaces and their compactly generated models; it does not assert that an
arbitrary product of compactly generated spaces is compactly generated.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter III (Moore paths).
-/

public section

open TopologicalSpace

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

namespace MoorePath

/-- Stopped Moore paths in a pseudometrizable space are pseudometrizable. -/
instance [PseudoMetrizableSpace X] : PseudoMetrizableSpace (MoorePath X) :=
  isEmbedding_length_toContinuousMap.isInducing.pseudoMetrizableSpace

/-- Stopped Moore paths in a metrizable space are metrizable, with their original
compact-open and duration topology. -/
instance [MetrizableSpace X] : MetrizableSpace (MoorePath X) :=
  isEmbedding_length_toContinuousMap.metrizableSpace

end MoorePath

namespace MooreLoopSpace

/-- Based Moore loops in a pseudometrizable space are pseudometrizable. -/
instance [PseudoMetrizableSpace X] (x : X) : PseudoMetrizableSpace (MooreLoopSpace X x) :=
  isEmbedding_toMoorePath.isInducing.pseudoMetrizableSpace

/-- Based Moore loops in a metrizable space are metrizable. -/
instance [MetrizableSpace X] (x : X) : MetrizableSpace (MooreLoopSpace X x) :=
  isEmbedding_toMoorePath.metrizableSpace

end MooreLoopSpace

namespace MooreFreeLoopSpace

/-- Free Moore loops in a pseudometrizable space are pseudometrizable. -/
instance [PseudoMetrizableSpace X] : PseudoMetrizableSpace (MooreFreeLoopSpace X) :=
  isEmbedding_toMoorePath.isInducing.pseudoMetrizableSpace

/-- Free Moore loops in a metrizable space are metrizable. -/
instance [MetrizableSpace X] : MetrizableSpace (MooreFreeLoopSpace X) :=
  isEmbedding_toMoorePath.metrizableSpace

end MooreFreeLoopSpace

end TauCeti
