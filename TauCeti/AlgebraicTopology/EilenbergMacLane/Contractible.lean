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
# Simply connected covers of CW type over aspherical spaces are contractible

Let `p : E → B` be a covering map into an aspherical space `B` with simply connected total space
`E`. Then `E` is weakly contractible (`IsCoveringMap.subsingleton_homotopyGroup_of_isAspherical`),
so whenever `E` has CW type (`TauCeti.CWType E`) both `E` and `(univ : Set E)` are contractible by
Whitehead's theorem (`IsCoveringMap.contractibleSpace_of_cwType_of_isAspherical` and
`IsCoveringMap.contractibleSpace_univ_of_isAspherical`). In particular, if `B` is Hausdorff and
carries a CW structure on `univ : Set B`, then `E` has CW type through the lifted CW structure
`TauCeti.cwComplexPreimage`, so both `E` and `p ⁻¹' univ` are contractible
(`IsCoveringMap.contractibleSpace_of_isAspherical` and
`IsCoveringMap.contractibleSpace_preimage_univ_of_isAspherical`).

These supply the contractibility hypotheses for `TauCeti.cellActionResolution` and
`TauCeti.cellularResolution`.

## Main results

* `IsCoveringMap.contractibleSpace_of_cwType_of_isAspherical`: a simply connected cover of CW type
  over an aspherical base is contractible.
* `IsCoveringMap.contractibleSpace_univ_of_isAspherical`: the subspace `univ : Set E` is
  contractible when `E` is a simply connected cover of CW type over an aspherical base.
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

section CWType

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {e : E} {b : B}

/-- **A simply connected cover of CW type over an aspherical space is contractible.** -/
theorem contractibleSpace_of_cwType_of_isAspherical (hp : IsCoveringMap p) [CWType E]
    [SimplyConnectedSpace E] (he : p e = b) (hb : IsAspherical B b) :
    ContractibleSpace E :=
  contractibleSpace_of_subsingleton_homotopyGroup e
    (hp.subsingleton_homotopyGroup_of_isAspherical he hb)

/-- **The subspace `univ : Set E` of a simply connected cover `E` of CW type over an aspherical
space is contractible.** -/
theorem contractibleSpace_univ_of_isAspherical (hp : IsCoveringMap p) [CWType E]
    [SimplyConnectedSpace E] (he : p e = b) (hb : IsAspherical B b) :
    ContractibleSpace (univ : Set E) :=
  have := hp.contractibleSpace_of_cwType_of_isAspherical he hb
  (Homeomorph.Set.univ E).contractibleSpace

end CWType

section BaseCW

variable {E B : Type w} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {e : E} {b : B}

/-- **The simply connected cover of an aspherical CW complex is contractible.** -/
theorem contractibleSpace_of_isAspherical (hp : IsCoveringMap p) [T2Space B]
    [CWComplex (univ : Set B)] [SimplyConnectedSpace E] (he : p e = b) (hb : IsAspherical B b) :
    ContractibleSpace E := by
  let := cwComplexPreimage (univ : Set B) hp
  have := hp.t2Space
  let φ : (p ⁻¹' (univ : Set B)) ≃ₜ E :=
    (Homeomorph.setCongr preimage_univ).trans (Homeomorph.Set.univ E)
  have : CWType E := φ.symm.cwType
  exact hp.contractibleSpace_of_cwType_of_isAspherical he hb

/-- **The lift of an aspherical CW complex to a simply connected cover is contractible**: the form
of `IsCoveringMap.contractibleSpace_of_isAspherical` for `p ⁻¹' univ`, the space carrying the
lifted CW structure. -/
theorem contractibleSpace_preimage_univ_of_isAspherical (hp : IsCoveringMap p) [T2Space B]
    [CWComplex (univ : Set B)] [SimplyConnectedSpace E] (he : p e = b) (hb : IsAspherical B b) :
    ContractibleSpace (p ⁻¹' (univ : Set B)) :=
  have := hp.contractibleSpace_of_isAspherical he hb
  ((Homeomorph.setCongr preimage_univ).trans (Homeomorph.Set.univ E)).contractibleSpace

end BaseCW

end IsCoveringMap
