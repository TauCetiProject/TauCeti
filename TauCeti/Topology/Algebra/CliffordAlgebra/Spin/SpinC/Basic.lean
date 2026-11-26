/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Proper
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.SpinorNorm
import TauCeti.LinearAlgebra.QuadraticForm.Real

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
quotient map, and its finite kernel gives the covering. Charge conjugation `[s, z] ↦ [s, z⁻¹]`
is a continuous automorphism (`CliffordAlgebra.spinCGroup.chargeConjContinuousMulEquiv`), and the
homomorphism `[s, z] ↦ [f s, z]` induced by a quadratic isometry `f` is continuous
(`QuadraticMap.Isometry.continuous_spinCGroupMap`).

For a positive- or negative-definite form on a finite-dimensional real space, `Spinᶜ(Q)` is
compact (`CliffordAlgebra.spinCGroup.compactSpace_of_posDef_or_negDef`), as a quotient of the
compact group `Spin(Q) × U(1)`. The quotient map
(`CliffordAlgebra.spinCGroup.continuous_mk`), the inclusions `s ↦ [s, 1]` and `z ↦ [1, z]`
(`CliffordAlgebra.spinCGroup.continuous_ofSpin`, `CliffordAlgebra.spinCGroup.continuous_ofCircle`)
and the map `[s, z] ↦ [f s, z]` induced by a quadratic isometry `f`
(`QuadraticMap.Isometry.continuous_spinCGroupMap`) are continuous. On any finite-dimensional real
space, the rotation map `Spinᶜ(Q) → SO(Q)` is continuous for the topology of `SO(Q)` as a
subgroup of the linear automorphisms (`CliffordAlgebra.spinCGroup.continuous_toSpecialOrthogonal`);
for coordinate forms, `CliffordAlgebra.spinCGroup.continuous_toSpecialOrthogonal_pi` is the same
statement for the native coordinate topology on `SO(n)`.

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

/-- The finite diagonal kernel has the discrete topology inherited from `Spin(Q) × Circle`. -/
instance instDiscreteTopologySpinCKernel :
    DiscreteTopology (spinCKernel Q hQ) :=
  isDiscrete_iff_discreteTopology.mp (finite_spinCKernel Q hQ).isDiscrete

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

/-- The quotient map `Spin(Q) × U(1) → Spinᶜ(Q)`, `(s, z) ↦ [s, z]`, is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk Q hQ) := by
  rw [coe_mk]
  exact (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous

/-- The inclusion `Spin(Q) → Spinᶜ(Q)`, `s ↦ [s, 1]`, is continuous for the quotient topology. -/
@[fun_prop]
theorem continuous_ofSpin : Continuous (ofSpin Q hQ) :=
  ((continuous_mk Q hQ).comp (continuous_id.prodMk continuous_const)).congr
    fun s ↦ (ofSpin_apply Q hQ s).symm

/-- The weight-one central circle inclusion is continuous for the quotient topology. -/
@[fun_prop]
theorem continuous_ofCircle : Continuous (ofCircle Q hQ) :=
  ((continuous_mk Q hQ).comp (continuous_const.prodMk continuous_id)).congr
    fun z ↦ (ofCircle_apply Q hQ z).symm

/-- Multiplication by the central circle is continuous. -/
@[fun_prop]
theorem continuous_mulCircle [ContinuousMul (spinCGroup Q hQ)] : Continuous (mulCircle Q hQ) := by
  have h : Continuous fun g : spinCGroup Q hQ × Circle ↦ g.1 * ofCircle Q hQ g.2 :=
    continuous_fst.mul ((continuous_ofCircle Q hQ).comp continuous_snd)
  exact h.congr fun g ↦ (mulCircle_apply Q hQ g.1 g.2).symm

/-- Charge conjugation `[s, z] ↦ [s, z⁻¹]` is continuous for the quotient topology. -/
@[fun_prop]
theorem continuous_chargeConj : Continuous (chargeConj Q hQ) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous_iff.mpr
  simp only [Function.comp_def, ← mk_apply, chargeConj_mk]
  simpa only [coe_mk, Function.comp_def] using
    (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous.comp
      (continuous_fst.prodMk (continuous_inv.comp continuous_snd))

/-- Charge conjugation as a continuous automorphism of the Spinᶜ quotient. -/
def chargeConjContinuousMulEquiv : spinCGroup Q hQ ≃ₜ* spinCGroup Q hQ where
  toMulEquiv := chargeConj Q hQ
  continuous_toFun := continuous_chargeConj Q hQ
  continuous_invFun := by
    rw [MulEquiv.invFun_eq_symm, chargeConj_symm]
    exact continuous_chargeConj Q hQ

/-- The bundled continuous charge conjugation is charge conjugation. -/
@[simp]
theorem chargeConjContinuousMulEquiv_apply (x : spinCGroup Q hQ) :
    chargeConjContinuousMulEquiv Q hQ x = chargeConj Q hQ x := (rfl)

/-- The determinant character as a continuous homomorphism on the Spinᶜ quotient. -/
def detContinuousMonoidHom : spinCGroup Q hQ →ₜ* Circle where
  toMonoidHom := det Q hQ
  continuous_toFun := continuous_det Q hQ

/-- The weight-one central circle as a continuous homomorphism into the Spinᶜ quotient. -/
def ofCircleContinuousMonoidHom : Circle →ₜ* spinCGroup Q hQ where
  toMonoidHom := ofCircle Q hQ
  continuous_toFun := continuous_ofCircle Q hQ

/-- The bundled determinant character is the original quotient determinant. -/
@[simp]
theorem detContinuousMonoidHom_apply (x : spinCGroup Q hQ) :
    detContinuousMonoidHom Q hQ x = det Q hQ x := (rfl)

/-- The bundled central inclusion is the original weight-one circle inclusion. -/
@[simp]
theorem ofCircleContinuousMonoidHom_apply (z : Circle) :
    ofCircleContinuousMonoidHom Q hQ z = ofCircle Q hQ z := (rfl)

/-- The determinant restricted to the central circle is the square character. -/
@[simp]
theorem detContinuousMonoidHom_comp_ofCircleContinuousMonoidHom :
    (detContinuousMonoidHom Q hQ).comp (ofCircleContinuousMonoidHom Q hQ) =
      (ContinuousMonoidHom.id Circle) ^ 2 := by
  ext z
  simp [ContinuousMonoidHom.pow_apply, det_ofCircle]

/-- **`Spinᶜ(Q)` is compact** for a positive- or negative-definite form on a finite-dimensional
real space, such as `Q v = -‖v‖²`: it is a quotient of `Spin(Q) × U(1)`, and `Spin(Q)` is
compact (`CliffordAlgebra.compactSpace_spinGroup_of_posDef_or_negDef`). -/
theorem compactSpace_of_posDef_or_negDef [FiniteDimensional ℝ M] (hdef : Q.PosDef ∨ (-Q).PosDef) :
    CompactSpace (spinCGroup Q hQ) := by
  have := compactSpace_spinGroup_of_posDef_or_negDef Q hdef
  infer_instance

/-- The rotation map on `Spinᶜ(Q)` is continuous into the special orthogonal group with its
topology as a subgroup of the linear automorphisms. -/
@[fun_prop]
theorem continuous_toSpecialOrthogonal [FiniteDimensional ℝ M] :
    Continuous (toSpecialOrthogonal Q hQ) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous_iff.mpr
  simpa only [Function.comp_def, ← mk_apply, toSpecialOrthogonal_mk] using
    (TauCeti.CliffordAlgebra.continuous_spinToSpecialOrthogonal Q).comp continuous_fst

section Coordinates

variable {ι : Type*} [Fintype ι] (Q : QuadraticForm ℝ (ι → ℝ)) (hQ : Q ≠ 0)

/-- The rotation map on `Spinᶜ(Q)` is continuous into the special orthogonal group with its
native coordinate topology. -/
@[fun_prop]
theorem continuous_toSpecialOrthogonal_pi : Continuous (toSpecialOrthogonal Q hQ) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous_iff.mpr
  simpa only [Function.comp_def, ← mk_apply, toSpecialOrthogonal_mk] using
    (continuous_spinToSpecialOrthogonal_pi Q).comp continuous_fst

/-- The frame-and-determinant map `[s, z] ↦ (π(s), z²)` is continuous. -/
@[fun_prop]
theorem continuous_toSpecialOrthogonal_prod_det :
    Continuous ((toSpecialOrthogonal Q hQ).prod (det Q hQ)) :=
  (continuous_toSpecialOrthogonal_pi Q hQ).prodMk (continuous_det Q hQ)

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
  have hQn : Q.Nondegenerate :=
    ((_root_.QuadraticForm.anisotropic_iff_posDef_or_negDef Q).mpr hdef).nondegenerate
  let _ : CompactSpace (spinGroup Q) := compactSpace_spinGroup_of_posDef_or_negDef Q hdef
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

namespace QuadraticMap.Isometry

open CliffordAlgebra

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {Q : QuadraticForm ℝ M} {P : QuadraticForm ℝ N} (f : Q →qᵢ P) (hQ : Q ≠ 0) (hP : P ≠ 0)

/-- The homomorphism `[s, z] ↦ [f s, z]` of `Spinᶜ` groups induced by a quadratic isometry `f` is
continuous for the quotient topologies. -/
@[fun_prop]
theorem continuous_spinCGroupMap : Continuous (f.spinCGroupMap hQ hP) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ)).continuous_iff.mpr
  simp only [Function.comp_def, ← spinCGroup.mk_apply, spinCGroupMap_mk]
  exact (spinCGroup.continuous_mk P hP).comp
    ((f.continuous_spinGroupMap.comp continuous_fst).prodMk continuous_snd)

end QuadraticMap.Isometry
