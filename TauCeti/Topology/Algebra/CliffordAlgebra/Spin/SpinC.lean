/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Proper
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.SpinorNorm

/-!
# The two topological double covers of `Spinᶜ`

The quotient map `Spin(Q) × Circle → Spinᶜ(Q)` is a covering map with two-element fibres for
the quotient topology on the existing group `CliffordAlgebra.spinCGroup`. Its kernel is the
diagonal subgroup `{1, (-1, -1)}`.

There is a different double cover `Spinᶜ(n) → SO(n) × Circle`, sending `[s, z]` to `(π(s), z²)`.
For definite real coordinate forms in positive dimension, this file proves that the
actual product of the rotation homomorphism and determinant character is a covering map for the
native coordinate topology on `SO(n)`. Its kernel is `{1, [1, -1]}`. The determinant character
and rotation map are continuous; compactness of `Spin(n)` makes their surjective product a
quotient map, and its finite kernel gives the covering.

These are topological group covers. No smoothness or covering statement about classifying
spaces is asserted.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti Topology

variable {M : Type*} [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ M) (hQ : Q ≠ 0)

namespace spinCGroup

/-- The quotient topology on `Spinᶜ(Q)` is Hausdorff when Clifford multiplication is continuous. -/
instance instT2Space [ContinuousMul (CliffordAlgebra Q)] : T2Space (spinCGroup Q hQ) := by
  let : IsClosed (spinCKernel Q hQ : Set (spinGroup Q × Circle)) :=
    (finite_spinCKernel Q hQ).isClosed
  infer_instance

/-- The actual quotient map from `Spin(Q) × Circle` to `Spinᶜ(Q)` is a quotient covering map
by its diagonal order-two kernel. -/
theorem isQuotientCoveringMap_mk [ContinuousMul (CliffordAlgebra Q)] :
    IsQuotientCoveringMap (mk Q hQ) (spinCKernel Q hQ) := by
  have hquot : IsQuotientMap (mk Q hQ) := by
    convert QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ) using 1
    funext p
    exact mk_apply Q hQ p
  exact (IsQuotientCoveringMap.subgroup_congr (mk Q hQ) (spinGroup Q × Circle)
    (mk Q hQ).ker (spinCKernel Q hQ) (ker_mk Q hQ)).mp <|
    hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom (by
      rw [ker_mk]
      exact (finite_spinCKernel Q hQ).isDiscrete)

/-- The determinant character `[s, z] ↦ z²` is continuous for the quotient topology. -/
@[fun_prop]
theorem continuous_det : Continuous (det Q hQ) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous_iff.mpr
  simp only [Function.comp_def, ← mk_apply, det_mk]
  -- Function powers are pointwise, so this is the square of the second projection.
  exact continuous_snd.pow 2

section Coordinates

variable {ι : Type*} [Fintype ι] (Q : QuadraticForm ℝ (ι → ℝ)) (hQ : Q ≠ 0)

/-- The rotation map on `Spinᶜ(Q)` is continuous into the special orthogonal group with its
native coordinate topology. -/
@[fun_prop]
theorem continuous_toSpecialOrthogonal : Continuous (toSpecialOrthogonal Q hQ) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous_iff.mpr
  simpa only [Function.comp_def, ← mk_apply, toSpecialOrthogonal_mk] using
    (continuous_spinToSpecialOrthogonal_pi Q).comp continuous_fst

/-- The frame-and-determinant map `[s, z] ↦ (π(s), z²)` is continuous. -/
@[fun_prop]
theorem continuous_toSpecialOrthogonal_prod_det :
    Continuous ((toSpecialOrthogonal Q hQ).prod (det Q hQ)) :=
  (continuous_toSpecialOrthogonal Q hQ).prodMk (continuous_det Q hQ)

end Coordinates

/-- For a positive- or negative-definite real coordinate form in positive dimension, the
frame-and-determinant map is a quotient covering map by `{1, [1, -1]}`. Compactness and
surjectivity follow from definiteness. The topologies are the native Clifford subtype, quotient,
and special orthogonal coordinate topologies. -/
theorem isQuotientCoveringMap_toSpecialOrthogonal_prod_det
    {ι : Type*} [Fintype ι] (Q : QuadraticForm ℝ (ι → ℝ)) (hQ : Q ≠ 0)
    (hdef : Q.PosDef ∨ (-Q).PosDef) :
    IsQuotientCoveringMap ((toSpecialOrthogonal Q hQ).prod (det Q hQ))
      ((toSpecialOrthogonal Q hQ).prod (det Q hQ)).ker := by
  have hQn : Q.Nondegenerate := by
    rcases hdef with hpos | hneg
    · exact hpos.anisotropic.nondegenerate
    · exact (QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate
  let _ : CompactSpace (spinGroup Q) :=
    isCompact_iff_compactSpace.mp ((isCompact_spinGroup_iff_posDef_or_negDef Q hQn).mpr hdef)
  have hsurj : Function.Surjective (spinToSpecialOrthogonal Q) := by
    rcases hdef with hpos | hneg
    · exact spinToSpecialOrthogonal_surjective_of_posDef Q hpos
    · exact spinToSpecialOrthogonal_surjective_of_negDef Q hneg
  have hquot : IsQuotientMap ((toSpecialOrthogonal Q hQ).prod (det Q hQ)) :=
    IsQuotientMap.of_surjective_continuous
      (toSpecialOrthogonal_prod_det_surjective Q hQ hsurj)
      (continuous_toSpecialOrthogonal_prod_det Q hQ)
  exact hquot.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (finite_ker_toSpecialOrthogonal_prod_det Q hQ hQn).isDiscrete

end spinCGroup

end CliffordAlgebra
