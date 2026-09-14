/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Topology.Covering.Quotient

/-!
# The compact real Spin double cover

The projection from the compact real Spin group to the special orthogonal group is a covering map
whenever its domain is compact. Indeed, the projection is a continuous surjection from a compact
space to a Hausdorff space, hence a quotient map. Its kernel is the finite image of the included
group `Multiplicative (ZMod 2)`, so the standard quotient-covering construction applies.

## Main results

* `CliffordAlgebra.isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom` packages the
  compact real Spin projection as a quotient covering map by its kernel.
* `CliffordAlgebra.isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom` packages the projection
  as an ordinary covering map.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

namespace CliffordAlgebra

open TauCeti

/-- The compact real Spin projection is a quotient covering map by its kernel. -/
theorem isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom
    (n : ℕ) [NeZero n] [CompactSpace (realCliffordSpinGroupZero n)] :
    IsQuotientCoveringMap (realCliffordSpinDoubleCoverZero n).rightHom
      (realCliffordSpinDoubleCoverZero n).rightHom.ker := by
  let S := realCliffordSpinDoubleCoverZero n
  have hquot : Topology.IsQuotientMap S.rightHom :=
    Topology.IsQuotientMap.of_surjective_continuous S.rightHom_surjective
      (continuous_realCliffordSpinDoubleCoverZero_rightHom n)
  apply hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
  rw [← S.range_inl_eq_ker_rightHom]
  exact (Set.finite_range S.inl).isDiscrete

/-- The projection from the compact real Spin group to the special orthogonal group is a covering
map. -/
theorem isCoveringMap_realCliffordSpinDoubleCoverZero_rightHom
    (n : ℕ) [NeZero n] [CompactSpace (realCliffordSpinGroupZero n)] :
    IsCoveringMap (realCliffordSpinDoubleCoverZero n).rightHom :=
  (isQuotientCoveringMap_realCliffordSpinDoubleCoverZero_rightHom n).isCoveringMap

end CliffordAlgebra
