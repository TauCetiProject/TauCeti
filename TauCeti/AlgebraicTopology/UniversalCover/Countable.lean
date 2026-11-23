/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Covering
public import TauCeti.Topology.Covering.Countable

/-!
# Countability of universal covers and fundamental groups

The universal cover of a second-countable, locally path-connected, semilocally simply connected
space is second countable: it is a connected covering space, so
`IsCoveringMap.secondCountableTopology` applies. Its discrete fibres are therefore countable.
The basepoint-fibre equivalence then makes the fundamental group countable, without any
connectedness assumption on the base.

## Main results

* `TauCeti.UniversalCover.instSecondCountableTopology`: second countability of the universal cover.
* `TauCeti.countable_fundamentalGroup`: countability of the fundamental group.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 4.40.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The universal cover of a second-countable space is second countable. -/
instance UniversalCover.instSecondCountableTopology [SecondCountableTopology X] :
    SecondCountableTopology (UniversalCover x₀) :=
  (UniversalCover.isCoveringMap x₀).secondCountableTopology

/-- A locally path-connected, semilocally simply connected, second-countable space has countable
fundamental group. -/
instance countable_fundamentalGroup [SecondCountableTopology X] :
    Countable (FundamentalGroup X x₀) :=
  have := (UniversalCover.isCoveringMap x₀).countable_fiber x₀
  Countable.of_equiv _ (UniversalCover.fiberEquivFundamentalGroup x₀)

end TauCeti
