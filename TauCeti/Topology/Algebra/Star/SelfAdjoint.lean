/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Topology.Algebra.Star

/-!
# Topological instances for self-adjoint elements

The self-adjoint part of a star additive group inherits second countability from the ambient
space. With a continuous star on a Hausdorff locally compact space, it is also locally compact.
These instances allow Haar measure constructions on self-adjoint subgroups.
-/

public section

namespace selfAdjoint

variable {A : Type*} [AddGroup A] [StarAddMonoid A] [TopologicalSpace A]

/-- The self-adjoint part of a Hausdorff locally compact space with continuous star is locally
compact. -/
instance instLocallyCompactSpace [T2Space A] [LocallyCompactSpace A] [ContinuousStar A] :
    LocallyCompactSpace (selfAdjoint A) :=
  (isClosed_eq continuous_star continuous_id : IsClosed {a : A | star a = a})
    |>.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The self-adjoint part of a second countable space is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology A] :
    SecondCountableTopology (selfAdjoint A) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end selfAdjoint
