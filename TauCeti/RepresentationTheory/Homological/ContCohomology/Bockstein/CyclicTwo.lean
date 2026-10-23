/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CyclicTwo

/-!
# The Bockstein of the cyclic order-two character

The identity character of `ℤ/2` has Bockstein equal to the non-split extension class of `ℤ/4`.
This computes a nonzero value of the mod-two connecting map, using the existing cup-square
calculation and extension class. In particular, the Bockstein is not the zero operation.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
-/

public section

namespace TauCeti

/-- The Bockstein of the identity character of `ℤ/2` is the class of the extension `ℤ/4`. -/
@[simp]
theorem bockstein1_cyclicTwoClass_eq_zmodFourExtensionClass :
    bockstein1 (Multiplicative (ZMod 2)) cyclicTwoClass = zmodFourExtensionClass := by
  rw [bockstein1_eq_cupFp_self, cupFp_cyclicTwoClass_self_eq_zmodFourExtensionClass]

end TauCeti
