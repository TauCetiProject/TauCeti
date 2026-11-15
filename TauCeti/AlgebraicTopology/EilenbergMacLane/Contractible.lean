/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.Topology.CWComplex.Classical.Covering

/-!
# The universal cover of an aspherical CW complex is contractible

Let `p : E → B` be a covering map. If `B` carries a CW structure on the whole space and is
aspherical, and `E` is simply connected, then `E` is weakly contractible
(`IsCoveringMap.subsingleton_homotopyGroup_of_isAspherical`). It has CW type through the lifted CW
structure `TauCeti.cwComplexPreimage`, so it is contractible by Whitehead's theorem
(`TauCeti.contractibleSpace_of_subsingleton_homotopyGroup`).

This is the contractibility needed to apply the cellular projective resolution
`TauCeti.cellularResolution` to the universal cover of a `K(G, 1)` CW complex.

## Main results

* `IsCoveringMap.contractibleSpace_of_isAspherical`: the simply connected cover of an aspherical
  CW complex is contractible.
* `IsCoveringMap.contractibleSpace_preimage_univ_of_isAspherical`: the same for the lift
  `p ⁻¹' univ` of the CW structure on the whole base.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1, Theorem 4.5
  and the corollary after it.
-/

public section

open Set Topology

universe w

namespace IsCoveringMap

open TauCeti

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {e : E} {b : B}

/-- **The simply connected cover of an aspherical CW complex is contractible.** If `B` carries a
CW structure on the whole space and is aspherical at a point `b` lifting to `e`, and `E` is simply
connected, then `E` is weakly contractible; it has CW type, through the lifted CW structure, so it
is contractible by Whitehead's theorem. -/
theorem contractibleSpace_of_isAspherical (hp : IsCoveringMap p) [T2Space B]
    [CWComplex (univ : Set B)] [SimplyConnectedSpace E] (he : p e = b) (hb : IsAspherical B b) :
    ContractibleSpace E := by
  let := cwComplexPreimage (univ : Set B) hp
  have := hp.t2Space
  let φ : (p ⁻¹' (univ : Set B)) ≃ₜ E :=
    (Homeomorph.setCongr preimage_univ).trans (Homeomorph.Set.univ E)
  have : CWType E := φ.symm.cwType
  exact contractibleSpace_of_subsingleton_homotopyGroup e
    (hp.subsingleton_homotopyGroup_of_isAspherical he hb)

/-- **The lift of an aspherical CW complex to a simply connected cover is contractible**: the form
of `IsCoveringMap.contractibleSpace_of_isAspherical` for `p ⁻¹' univ`, the space carrying the
lifted CW structure. -/
theorem contractibleSpace_preimage_univ_of_isAspherical (hp : IsCoveringMap p) [T2Space B]
    [CWComplex (univ : Set B)] [SimplyConnectedSpace E] (he : p e = b) (hb : IsAspherical B b) :
    ContractibleSpace (p ⁻¹' (univ : Set B)) :=
  have := hp.contractibleSpace_of_isAspherical he hb
  ((Homeomorph.setCongr preimage_univ).trans (Homeomorph.Set.univ E)).contractibleSpace

end IsCoveringMap
