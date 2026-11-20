/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.MappingPath.Basic

/-!
# Weak homotopy equivalence of the mapping-path inclusion

For any continuous map `f : C(B, K)`, the constant-path inclusion
`TauCeti.MappingPathSpace.incl f : C(B, MappingPathSpace f)` is the forward map of the homotopy
equivalence `TauCeti.MappingPathSpace.homotopyEquiv f`, and is therefore a weak homotopy
equivalence.

## Main results

* `TauCeti.MappingPathSpace.isWeakHomotopyEquivalence_incl`: `MappingPathSpace.incl f` is a weak
  homotopy equivalence for every continuous map `f`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

universe u v

namespace TauCeti.MappingPathSpace

/-- `MappingPathSpace.incl` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_incl {B : Type u} {K : Type v}
    [TopologicalSpace B] [TopologicalSpace K] (f : C(B, K)) :
    (incl f).IsWeakHomotopyEquivalence := by
  convert (homotopyEquiv f).isWeakHomotopyEquivalence using 1
  ext x : 1
  exact (homotopyEquiv_apply f x).symm

end TauCeti.MappingPathSpace
