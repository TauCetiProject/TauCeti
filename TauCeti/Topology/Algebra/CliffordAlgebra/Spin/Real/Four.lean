/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Stabilization
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

import Mathlib.Topology.Algebra.Star.Unitary
import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalMonoid

/-!
# Topology and higher homotopy groups of compact `Spin(4)` and `SO(4)`

Both quaternion-pair models of compact `Spin(4)` from
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Four` — the native reduction
`TauCeti.realSpinFourEquivQuaternionUnitaryProd` and the calibrated `(1, i, j, k)` model
`TauCeti.realSpinFourCalibratedEquivQuaternionUnitaryProd` — factor through linear equivalences on
the finite-dimensional even Clifford algebra `Cl⁺(4,0)`. Since compact `Spin(4)` is compact and
`unitary ℍ[ℝ] × unitary ℍ[ℝ]` is Hausdorff, both equivalences are isomorphisms of topological
groups, and yield corresponding topological group isomorphisms with `SU(2) × SU(2)` and
homeomorphisms with the sphere product `S³ × S³ ⊆ ℍ × ℍ`.

Using the calibrated `(1, i, j, k)` model, positive-dimensional homotopy groups of `Spin(4)` and
higher homotopy groups (`k ≥ 2`) of `SO(4)` decompose as products of two copies of `πₖ(S³, 1)`:

* `πₖ(Spin(4), 1) ≃* πₖ(S³, 1) × πₖ(S³, 1)` for `k ≥ 1`;
* `πₖ(SO(4), 1) ≃* πₖ(S³, 1) × πₖ(S³, 1)` for `k ≥ 2`, and likewise for the matrix group;
* `πₖ(Spin(3), g) = 0` and `πₖ(Spin(4), g) = 0` for `k < 3`, and `π₂(SO(4), g) = 0`, at every
  basepoint `g`.

Moreover, the two `πₖ(S³, 1)` factors are pinned geometrically:

* **First-coordinate stabilization** (`Spin(3) → Spin(4)` and `SO(3) → SO(4)`) induces the
  diagonal map `a ↦ (e₃ a, e₃ a)`. Algebraically, stabilization is diagonal up to inner conjugation
  by `(1 + k) / √2` in `unitary ℍ[ℝ]`, and inner conjugation in the path-connected topological
  group `unitary ℍ[ℝ]` acts trivially on homotopy groups at `1`
  (`HomotopyGroup.map_conj_eq_id`).
* **First-coordinate reflection** (`v ↦ Fin.cons (-v 0) (Fin.tail v)`) acts by conjugation on
  `Spin(4)` and `SO(4)` by swapping the two `πₖ(S³, 1)` factors (`Prod.swap`).

## Main definitions

* `TauCeti.realSpinFourContinuousMulEquivQuaternionUnitaryProd`,
  `TauCeti.realSpinFourContinuousMulEquivSpecialUnitaryProd`, and
  `TauCeti.realSpinFourHomeomorphQuaternionSphereProd`: native topological group and
  `S³ × S³` homeomorphism models of compact `Spin(4)`.
* `TauCeti.realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd`,
  `TauCeti.realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd`, and
  `TauCeti.realSpinFourCalibratedHomeomorphQuaternionSphereProd`: calibrated `(1, i, j, k)`
  topological group and `S³ × S³` homeomorphism models of compact `Spin(4)`.
* `CliffordAlgebra.realSpinThreeHomotopyGroupMulEquivSphere`:
  `π_N(Spin(3), 1) ≃* π_N(S³, 1)` for nonempty `N`.
* `CliffordAlgebra.realSpinFourCalibratedHomotopyGroupMulEquivSphereProd`:
  `π_N(Spin(4), 1) ≃* π_N(S³, 1) × π_N(S³, 1)` for nonempty `N`.
* `CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd` and
  `TauCeti.specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd`:
  `π_N(SO(4), 1) ≃* π_N(S³, 1) × π_N(S³, 1)` for nontrivial `N`, on the quadratic-form and matrix
  models of `SO(4)`.

## Main results

* `CliffordAlgebra.subsingleton_homotopyGroup_realSpin_three` and
  `CliffordAlgebra.subsingleton_homotopyGroup_realSpin_four`: compact `Spin(3)` and `Spin(4)` are
  `2`-connected at every basepoint.
* `CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_four` and
  `TauCeti.subsingleton_homotopyGroup_specialOrthogonalGroup_four`: `π₂(SO(4), g) = 0` at every
  basepoint.
* `CliffordAlgebra.realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion` and
  `realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion`:
  first-coordinate stabilization induces the diagonal map on homotopy groups.
* `CliffordAlgebra.realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection` and
  `realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection`:
  conjugation by first-coordinate reflection swaps the two sphere factors on homotopy groups.

## References

* A. Hatcher, *Algebraic Topology* (2002), Proposition 4.1 and Section 4.2.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Theorem 3.7 and §4.
-/

public section

open Metric
open scoped Quaternion Topology.Homotopy

namespace TauCeti

/-! ### Topological group and sphere-product models of compact `Spin(4)` -/

private theorem continuous_spinFourToQuaternionUnitaryProd
    (e : CliffordAlgebra.even (realCliffordForm 4 0) ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ])
    (f : spinGroup (realCliffordForm 4 0) → unitary ℍ[ℝ] × unitary ℍ[ℝ])
    (hf : ∀ s, (((f s).1 : ℍ[ℝ]), ((f s).2 : ℍ[ℝ])) =
      e (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s))) :
    Continuous f := by
  let _ : IsTopologicalAddGroup (CliffordAlgebra.even (realCliffordForm 4 0)) :=
    (CliffordAlgebra.even (realCliffordForm 4 0)).toSubmodule.isTopologicalAddGroup
  have hinner : Continuous (fun s ↦
      CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) := by
    apply continuous_induced_rng.2
    have hinnerFun : Subtype.val ∘ (fun s ↦
        CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
          (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s)) =
        fun s : spinGroup (realCliffordForm 4 0) ↦
          (s : CliffordAlgebra (realCliffordForm 4 0)) := by
      funext s
      simp only [Function.comp_apply, CliffordAlgebra.coe_evenUnitaryGroupEvenPart,
        CliffordAlgebra.coe_spinGroupToEvenUnitary_apply]
      rfl
    rw [hinnerFun]
    exact continuous_subtype_val
  have hpair : Continuous (fun s ↦
      e (CliffordAlgebra.evenUnitaryGroupEvenPart (realCliffordForm 4 0)
        (CliffordAlgebra.spinGroupToEvenUnitary (realCliffordForm 4 0) s))) :=
    e.toLinearMap.continuous_of_finiteDimensional.comp hinner
  refine Continuous.prodMk (continuous_induced_rng.2 ?_) (continuous_induced_rng.2 ?_)
  · exact (continuous_fst.comp hpair).congr fun s ↦ (congrArg Prod.fst (hf s)).symm
  · exact (continuous_snd.comp hpair).congr fun s ↦ (congrArg Prod.snd (hf s)).symm

/-- The native algebraic equivalence from compact `Spin(4)` to pairs of unit Hamilton quaternions
is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourEquivQuaternionUnitaryProd :
    Continuous (realSpinFourEquivQuaternionUnitaryProd :
      spinGroup (realCliffordForm 4 0) → unitary ℍ[ℝ] × unitary ℍ[ℝ]) :=
  continuous_spinFourToQuaternionUnitaryProd realCliffordFourZeroEvenEquivQuaternionProd
    realSpinFourEquivQuaternionUnitaryProd coe_realSpinFourEquivQuaternionUnitaryProd_apply

/-- **Native topological group isomorphism `Spin(4) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]`.** -/
noncomputable def realSpinFourContinuousMulEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  ContinuousMulEquiv.mk realSpinFourEquivQuaternionUnitaryProd
    continuous_realSpinFourEquivQuaternionUnitaryProd
    (continuous_realSpinFourEquivQuaternionUnitaryProd.continuous_symm_of_equiv_compact_to_t2
      (f := realSpinFourEquivQuaternionUnitaryProd.toEquiv))

/-- `realSpinFourContinuousMulEquivQuaternionUnitaryProd` has
`realSpinFourEquivQuaternionUnitaryProd` as its forward map. -/
@[simp]
theorem realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourContinuousMulEquivQuaternionUnitaryProd s =
      realSpinFourEquivQuaternionUnitaryProd s :=
  (rfl)

/-- The inverse of `realSpinFourContinuousMulEquivQuaternionUnitaryProd` is
`realSpinFourEquivQuaternionUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    realSpinFourContinuousMulEquivQuaternionUnitaryProd.symm q =
      realSpinFourEquivQuaternionUnitaryProd.symm q :=
  (rfl)

/-- The native algebraic equivalence `Spin(4) ≃* SU(2) × SU(2)` is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourEquivSpecialUnitaryProd :
    Continuous (realSpinFourEquivSpecialUnitaryProd :
      spinGroup (realCliffordForm 4 0) →
        Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ((Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.continuous.prodMap
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.continuous).comp
      continuous_realSpinFourEquivQuaternionUnitaryProd).congr fun s ↦ ?_
  have h := coe_realSpinFourEquivSpecialUnitaryProd_apply s
  apply Prod.ext <;> apply Subtype.ext
  · simpa using (congrArg Prod.fst h).symm
  · simpa using (congrArg Prod.snd h).symm

/-- **Native topological group isomorphism `Spin(4) ≃ₜ* SU(2) × SU(2)`.** -/
noncomputable def realSpinFourContinuousMulEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ContinuousMulEquiv.mk realSpinFourEquivSpecialUnitaryProd
    continuous_realSpinFourEquivSpecialUnitaryProd
    (continuous_realSpinFourEquivSpecialUnitaryProd.continuous_symm_of_equiv_compact_to_t2
      (f := realSpinFourEquivSpecialUnitaryProd.toEquiv))

/-- `realSpinFourContinuousMulEquivSpecialUnitaryProd` has `realSpinFourEquivSpecialUnitaryProd`
as its forward map. -/
@[simp]
theorem realSpinFourContinuousMulEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourContinuousMulEquivSpecialUnitaryProd s = realSpinFourEquivSpecialUnitaryProd s :=
  (rfl)

/-- The inverse of `realSpinFourContinuousMulEquivSpecialUnitaryProd` is
`realSpinFourEquivSpecialUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourContinuousMulEquivSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    realSpinFourContinuousMulEquivSpecialUnitaryProd.symm M =
      realSpinFourEquivSpecialUnitaryProd.symm M :=
  (rfl)

/-- Native homeomorphism from compact `Spin(4)` to the product of two unit quaternion spheres. -/
noncomputable def realSpinFourHomeomorphQuaternionSphereProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  realSpinFourContinuousMulEquivQuaternionUnitaryProd.toHomeomorph.trans
    (Quaternion.unitaryHomeomorphSphere.prodCongr Quaternion.unitaryHomeomorphSphere)

/-- First quaternion coordinate of `realSpinFourHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_fst_realSpinFourHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourHomeomorphQuaternionSphereProd s).1 : ℍ[ℝ]) =
      (realSpinFourEquivQuaternionUnitaryProd s).1 := by
  rw [realSpinFourHomeomorphQuaternionSphereProd, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    Prod.map_fst, Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact congrArg (fun p ↦ (p.1 : ℍ[ℝ]))
    (realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply s)

/-- Second quaternion coordinate of `realSpinFourHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_snd_realSpinFourHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourHomeomorphQuaternionSphereProd s).2 : ℍ[ℝ]) =
      (realSpinFourEquivQuaternionUnitaryProd s).2 := by
  rw [realSpinFourHomeomorphQuaternionSphereProd, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    Prod.map_snd, Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact congrArg (fun p ↦ (p.2 : ℍ[ℝ]))
    (realSpinFourContinuousMulEquivQuaternionUnitaryProd_apply s)

/-- Inverse of `realSpinFourHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem realSpinFourHomeomorphQuaternionSphereProd_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :
    realSpinFourHomeomorphQuaternionSphereProd.symm q =
      realSpinFourEquivQuaternionUnitaryProd.symm
        (Quaternion.unitaryHomeomorphSphere.symm q.1,
          Quaternion.unitaryHomeomorphSphere.symm q.2) := by
  rw [realSpinFourHomeomorphQuaternionSphereProd, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.coe_prodCongr,
    ContinuousMulEquiv.toHomeomorph_eq_coe, ContinuousMulEquiv.coe_toHomeomorph_symm]
  exact realSpinFourContinuousMulEquivQuaternionUnitaryProd_symm_apply _

/-- `realSpinFourHomeomorphQuaternionSphereProd` sends `1` to `(1, 1)`. -/
@[simp]
theorem realSpinFourHomeomorphQuaternionSphereProd_one :
    realSpinFourHomeomorphQuaternionSphereProd 1 = 1 := by
  apply Prod.ext <;> apply Subtype.ext
  · rw [coe_fst_realSpinFourHomeomorphQuaternionSphereProd_apply, map_one]
    rfl
  · rw [coe_snd_realSpinFourHomeomorphQuaternionSphereProd_apply, map_one]
    rfl

/-- `realSpinFourHomeomorphQuaternionSphereProd.symm` sends `(1, 1)` to `1`. -/
theorem realSpinFourHomeomorphQuaternionSphereProd_symm_one :
    realSpinFourHomeomorphQuaternionSphereProd.symm 1 = 1 :=
  realSpinFourHomeomorphQuaternionSphereProd.symm_apply_eq.mpr
    realSpinFourHomeomorphQuaternionSphereProd_one.symm

/-- The calibrated `(1, i, j, k)` equivalence from compact `Spin(4)` to pairs of unit Hamilton
quaternions is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd :
    Continuous (realSpinFourCalibratedEquivQuaternionUnitaryProd :
      spinGroup (realCliffordForm 4 0) → unitary ℍ[ℝ] × unitary ℍ[ℝ]) :=
  continuous_spinFourToQuaternionUnitaryProd realCliffordFourZeroCalibratedEvenEquivQuaternionProd
    realSpinFourCalibratedEquivQuaternionUnitaryProd
    coe_realSpinFourCalibratedEquivQuaternionUnitaryProd_apply

/-- **Calibrated topological group isomorphism `Spin(4) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ]`**, aligned
with the standard `(1, i, j, k)` quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  ContinuousMulEquiv.mk realSpinFourCalibratedEquivQuaternionUnitaryProd
    continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd
    (Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := realSpinFourCalibratedEquivQuaternionUnitaryProd.toEquiv)
      continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd)

/-- `realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd` has
`realSpinFourCalibratedEquivQuaternionUnitaryProd` as its forward map. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd s =
      realSpinFourCalibratedEquivQuaternionUnitaryProd s :=
  (rfl)

/-- The inverse of `realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd` is
`realSpinFourCalibratedEquivQuaternionUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_symm_apply
    (q : unitary ℍ[ℝ] × unitary ℍ[ℝ]) :
    realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.symm q =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.symm q :=
  (rfl)

/-- The calibrated algebraic equivalence `Spin(4) ≃* SU(2) × SU(2)` is continuous. -/
@[fun_prop]
theorem continuous_realSpinFourCalibratedEquivSpecialUnitaryProd :
    Continuous (realSpinFourCalibratedEquivSpecialUnitaryProd :
      spinGroup (realCliffordForm 4 0) →
        Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ((Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.continuous.prodMap
    Quaternion.unitaryContinuousMulEquivSpecialUnitaryGroup.continuous).comp
      continuous_realSpinFourCalibratedEquivQuaternionUnitaryProd).congr fun s ↦ ?_
  have h := coe_realSpinFourCalibratedEquivSpecialUnitaryProd_apply s
  apply Prod.ext <;> apply Subtype.ext
  · simpa using (congrArg Prod.fst h).symm
  · simpa using (congrArg Prod.snd h).symm

/-- **Calibrated topological group isomorphism `Spin(4) ≃ₜ* SU(2) × SU(2)`**, aligned with the
standard `(1, i, j, k)` quaternion model of `ℝ⁴`. -/
noncomputable def realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ContinuousMulEquiv.mk realSpinFourCalibratedEquivSpecialUnitaryProd
    continuous_realSpinFourCalibratedEquivSpecialUnitaryProd
    (continuous_realSpinFourCalibratedEquivSpecialUnitaryProd.continuous_symm_of_equiv_compact_to_t2
      (f := realSpinFourCalibratedEquivSpecialUnitaryProd.toEquiv))

/-- `realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd` has
`realSpinFourCalibratedEquivSpecialUnitaryProd` as its forward map. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd s =
      realSpinFourCalibratedEquivSpecialUnitaryProd s :=
  (rfl)

/-- The inverse of `realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd` is
`realSpinFourCalibratedEquivSpecialUnitaryProd.symm`. -/
@[simp]
theorem realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd_symm_apply
    (M : Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    realSpinFourCalibratedContinuousMulEquivSpecialUnitaryProd.symm M =
      realSpinFourCalibratedEquivSpecialUnitaryProd.symm M :=
  (rfl)

/-- **Calibrated homeomorphism `Spin(4) ≃ₜ S³ × S³`** in the standard `(1, i, j, k)` quaternion
coordinates. -/
noncomputable def realSpinFourCalibratedHomeomorphQuaternionSphereProd :
    spinGroup (realCliffordForm 4 0) ≃ₜ sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1 :=
  realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd.toHomeomorph.trans
    (Quaternion.unitaryHomeomorphSphere.prodCongr Quaternion.unitaryHomeomorphSphere)

/-- First quaternion coordinate of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_fst_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourCalibratedHomeomorphQuaternionSphereProd s).1 : ℍ[ℝ]) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).1 := by
  rw [realSpinFourCalibratedHomeomorphQuaternionSphereProd, Homeomorph.trans_apply,
    Homeomorph.coe_prodCongr, Prod.map_fst, Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact congrArg (fun p ↦ (p.1 : ℍ[ℝ]))
    (realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply s)

/-- Second quaternion coordinate of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem coe_snd_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply
    (s : spinGroup (realCliffordForm 4 0)) :
    ((realSpinFourCalibratedHomeomorphQuaternionSphereProd s).2 : ℍ[ℝ]) =
      (realSpinFourCalibratedEquivQuaternionUnitaryProd s).2 := by
  rw [realSpinFourCalibratedHomeomorphQuaternionSphereProd, Homeomorph.trans_apply,
    Homeomorph.coe_prodCongr, Prod.map_snd, Quaternion.coe_unitaryHomeomorphSphere_apply]
  exact congrArg (fun p ↦ (p.2 : ℍ[ℝ]))
    (realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_apply s)

/-- Inverse of `realSpinFourCalibratedHomeomorphQuaternionSphereProd`. -/
@[simp]
theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_apply
    (q : sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm q =
      realSpinFourCalibratedEquivQuaternionUnitaryProd.symm
        (Quaternion.unitaryHomeomorphSphere.symm q.1,
          Quaternion.unitaryHomeomorphSphere.symm q.2) := by
  rw [realSpinFourCalibratedHomeomorphQuaternionSphereProd, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.coe_prodCongr,
    ContinuousMulEquiv.toHomeomorph_eq_coe, ContinuousMulEquiv.coe_toHomeomorph_symm]
  exact realSpinFourCalibratedContinuousMulEquivQuaternionUnitaryProd_symm_apply _

/-- `realSpinFourCalibratedHomeomorphQuaternionSphereProd` sends `1` to `(1, 1)`. -/
@[simp]
theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_one :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd 1 = 1 := by
  apply Prod.ext <;> apply Subtype.ext
  · rw [coe_fst_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply, map_one]
    rfl
  · rw [coe_snd_realSpinFourCalibratedHomeomorphQuaternionSphereProd_apply, map_one]
    rfl

/-- `realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm` sends `(1, 1)` to `1`. -/
theorem realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_one :
    realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm 1 = 1 :=
  realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm_apply_eq.mpr
    realSpinFourCalibratedHomeomorphQuaternionSphereProd_one.symm

end TauCeti

/-! ### Higher homotopy groups and factor-pinning of `Spin(4)` and `SO(4)` -/

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- **`πₖ(Spin(3)) ≅ πₖ(S³)` for `k ≥ 1`.** Compact `Spin(3)` is homeomorphic to the unit
quaternion sphere `S³ ⊆ ℍ` via `TauCeti.realSpinThreeHomeomorphQuaternionSphere`. -/
def realSpinThreeHomotopyGroupMulEquivSphere {N : Type*} [DecidableEq N] [Nonempty N] :
    HomotopyGroup N (realCliffordSpinGroupZero 3) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  HomotopyGroup.homeomorphMulEquivOfEq realSpinThreeHomeomorphQuaternionSphere
    realSpinThreeHomeomorphQuaternionSphere_one

/-- `realSpinThreeHomotopyGroupMulEquivSphere` is the map induced on homotopy groups by
`realSpinThreeHomeomorphQuaternionSphere`. -/
@[simp]
theorem realSpinThreeHomotopyGroupMulEquivSphere_apply {N : Type*} [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup N (realCliffordSpinGroupZero 3) 1) :
    realSpinThreeHomotopyGroupMulEquivSphere a =
      HomotopyGroup.map ⟨realSpinThreeHomeomorphQuaternionSphere,
        realSpinThreeHomeomorphQuaternionSphere.continuous⟩
        realSpinThreeHomeomorphQuaternionSphere_one a :=
  (rfl)

/-- The inverse of `realSpinThreeHomotopyGroupMulEquivSphere` is induced by
`realSpinThreeHomeomorphQuaternionSphere.symm`. -/
theorem realSpinThreeHomotopyGroupMulEquivSphere_symm_apply {N : Type*} [DecidableEq N]
    [Nonempty N] (a : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    realSpinThreeHomotopyGroupMulEquivSphere.symm a =
      HomotopyGroup.map ⟨realSpinThreeHomeomorphQuaternionSphere.symm,
        realSpinThreeHomeomorphQuaternionSphere.symm.continuous⟩
        realSpinThreeHomeomorphQuaternionSphere_symm_one a := by
  rw [realSpinThreeHomotopyGroupMulEquivSphere, HomotopyGroup.homeomorphMulEquivOfEq_symm_apply]

/-- On higher homotopy groups (`k ≥ 2`), `realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere`
agrees with `realSpinThreeHomotopyGroupMulEquivSphere` across the Spin double cover. -/
@[simp]
theorem realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere_spinProjection {N : Type*}
    [DecidableEq N] [Nontrivial N] (a : HomotopyGroup N (realCliffordSpinGroupZero 3) 1) :
    realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere
        (HomotopyGroup.map (realCliffordSpinProjectionZero 3 : C(_, _))
          (map_one (realCliffordSpinProjectionZero 3)) a) =
      realSpinThreeHomotopyGroupMulEquivSphere a := by
  let b := realSpinThreeHomotopyGroupMulEquivSphere a
  have ha : a = realSpinThreeHomotopyGroupMulEquivSphere.symm b :=
    (realSpinThreeHomotopyGroupMulEquivSphere.symm_apply_apply a).symm
  have hproj :
      HomotopyGroup.map (realCliffordSpinProjectionZero 3 : C(_, _))
          (map_one (realCliffordSpinProjectionZero 3)) a =
        realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere.symm b := by
    rw [ha, realSpinThreeHomotopyGroupMulEquivSphere_symm_apply, HomotopyGroup.map_comp_apply,
      realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere_symm_apply]
  rw [hproj, realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere.apply_symm_apply]

/-- **`πₖ(Spin(4)) ≅ πₖ(S³) × πₖ(S³)` for `k ≥ 1` in the calibrated model.** Under
`TauCeti.realSpinFourCalibratedHomeomorphQuaternionSphereProd`, positive-dimensional homotopy
groups of compact `Spin(4)` decompose into two copies of `πₖ(S³, 1)`. -/
def realSpinFourCalibratedHomotopyGroupMulEquivSphereProd {N : Type*} [DecidableEq N]
    [Nonempty N] :
    HomotopyGroup N (realCliffordSpinGroupZero 4) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 ×
        HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (HomotopyGroup.homeomorphMulEquivOfEq
    realSpinFourCalibratedHomeomorphQuaternionSphereProd
    realSpinFourCalibratedHomeomorphQuaternionSphereProd_one).trans
    (HomotopyGroup.prodMulEquiv 1 1)

/-- `realSpinFourCalibratedHomotopyGroupMulEquivSphereProd` pushes homotopy classes forward along
`realSpinFourCalibratedHomeomorphQuaternionSphereProd` and splits coordinates via
`HomotopyGroup.prodMulEquiv`. -/
theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply {N : Type*} [DecidableEq N]
    [Nonempty N] (a : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd a =
      HomotopyGroup.prodMulEquiv 1 1
        (HomotopyGroup.map ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd,
          realSpinFourCalibratedHomeomorphQuaternionSphereProd.continuous⟩
          realSpinFourCalibratedHomeomorphQuaternionSphereProd_one a) :=
  (rfl)

/-- The inverse of `realSpinFourCalibratedHomotopyGroupMulEquivSphereProd` forms the product
homotopy class and pulls back along `realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm`. -/
theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_symm_apply {N : Type*}
    [DecidableEq N] [Nonempty N]
    (ab : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab =
      HomotopyGroup.map ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm,
        realSpinFourCalibratedHomeomorphQuaternionSphereProd.symm.continuous⟩
        realSpinFourCalibratedHomeomorphQuaternionSphereProd_symm_one
        (HomotopyGroup.prod ab.1 ab.2) := by
  rw [realSpinFourCalibratedHomotopyGroupMulEquivSphereProd, MulEquiv.symm_trans_apply,
    HomotopyGroup.prodMulEquiv_symm_apply, HomotopyGroup.homeomorphMulEquivOfEq_symm_apply]

/-- **`πₖ(SO(4)) ≅ πₖ(S³) × πₖ(S³)` for `k ≥ 2` in the calibrated model.** Compact `Spin(4)`
double covers `SO(4)`, transporting `realSpinFourCalibratedHomotopyGroupMulEquivSphereProd` to
higher homotopy groups of `SO(4)`. -/
def realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd {N : Type*} [DecidableEq N]
    [Nontrivial N] :
    HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 ×
        HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).symm.trans
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd

/-- Across the Spin double cover `Spin(4) → SO(4)`,
`realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd` agrees with
`realSpinFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
@[simp]
theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection
    {N : Type*} [DecidableEq N] [Nontrivial N]
    (a : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map (realCliffordSpinProjectionZero 4 : C(_, _))
          (map_one (realCliffordSpinProjectionZero 4)) a) =
      realSpinFourCalibratedHomotopyGroupMulEquivSphereProd a := by
  simp [realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd,
    ← realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply]

/-- Inverse of `realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd`. -/
theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_symm_apply
    {N : Type*} [DecidableEq N] [Nontrivial N]
    (ab : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 × HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab =
      HomotopyGroup.map (realCliffordSpinProjectionZero 4 : C(_, _))
        (map_one (realCliffordSpinProjectionZero 4))
        (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd.symm ab) := by
  rw [realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd,
    MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply]

/-- **Compact `Spin(3)` is `2`-connected at every basepoint**: `πₖ(Spin(3), g) = 0` for
`k = Nat.card N < 3`. -/
theorem subsingleton_homotopyGroup_realSpin_three {N : Type*} (hN : Nat.card N < 3)
    (g : realCliffordSpinGroupZero 3) :
    Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 3) g) := by
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :=
    subsingleton_homotopyGroup_sphere_quaternion hN 1
  have : Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 3) 1) :=
    (HomotopyGroup.homeomorphEquivOfEq realSpinThreeHomeomorphQuaternionSphere
      realSpinThreeHomeomorphQuaternionSphere_one).subsingleton
  exact (HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (mul_one g)).symm.subsingleton

/-- **Compact `Spin(4)` is `2`-connected at every basepoint**: `πₖ(Spin(4), g) = 0` for
`k = Nat.card N < 3`. -/
theorem subsingleton_homotopyGroup_realSpin_four {N : Type*} (hN : Nat.card N < 3)
    (g : realCliffordSpinGroupZero 4) :
    Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 4) g) := by
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :=
    subsingleton_homotopyGroup_sphere_quaternion hN 1
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) (1, 1)) :=
    (HomotopyGroup.prodEquiv (N := N) (1 : sphere (0 : ℍ[ℝ]) 1) 1).subsingleton
  have : Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :=
    (HomotopyGroup.homeomorphEquivOfEq realSpinFourCalibratedHomeomorphQuaternionSphereProd
      realSpinFourCalibratedHomeomorphQuaternionSphereProd_one).subsingleton
  exact (HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (mul_one g)).symm.subsingleton

/-- **`π₂(SO(4)) = 0`.** The second homotopy group of compact `SO(4)` is trivial at every
basepoint. -/
theorem subsingleton_homotopyGroup_realSpecialOrthogonal_four {N : Type*} (hN : Nat.card N = 2)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) :
    Subsingleton
      (HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) g) := by
  classical
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Subsingleton (HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :=
    subsingleton_homotopyGroup_realSpin_four (by omega) 1
  have : Subsingleton
      (HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1) :=
    (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).symm.toEquiv.subsingleton
  exact (HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (mul_one g)).symm.subsingleton

/-- **First-coordinate stabilization `Spin(3) → Spin(4)` induces the diagonal map on homotopy
groups** in the calibrated sphere-product model. -/
theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion {N : Type*}
    [DecidableEq N] [Nonempty N] (a : HomotopyGroup N (realCliffordSpinGroupZero 3) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map (realCliffordSpinFirstInclusionContinuousMonoidHom 3 :
          C(realCliffordSpinGroupZero 3, realCliffordSpinGroupZero 4))
          (map_one (realCliffordSpinFirstInclusionContinuousMonoidHom 3)) a) =
      (realSpinThreeHomotopyGroupMulEquivSphere a,
        realSpinThreeHomotopyGroupMulEquivSphere a) := by
  let f₁ : C(realCliffordSpinGroupZero 3, unitary ℍ[ℝ]) :=
    realSpinThreeContinuousMulEquivQuaternionUnitary
  let f₂ : C(unitary ℍ[ℝ], unitary ℍ[ℝ]) :=
    ⟨MulAut.conj realSpinThreeToFourCalibrationUnitary,
      IsTopologicalGroup.continuous_conj realSpinThreeToFourCalibrationUnitary⟩
  let f₃ : C(unitary ℍ[ℝ], sphere (0 : ℍ[ℝ]) 1) :=
    ⟨Quaternion.unitaryHomeomorphSphere, Quaternion.unitaryHomeomorphSphere.continuous⟩
  have hf₁ : f₁ 1 = 1 := map_one realSpinThreeContinuousMulEquivQuaternionUnitary
  have hf₂ : f₂ 1 = 1 := (MulAut.conj realSpinThreeToFourCalibrationUnitary).map_one
  have hf₂_apply (q : unitary ℍ[ℝ]) :
      f₂ q = MulAut.conj realSpinThreeToFourCalibrationUnitary q := rfl
  have hf₃ : f₃ 1 = 1 := Subtype.ext (Quaternion.coe_unitaryHomeomorphSphere_apply 1)
  have hf₃f₁ : f₃.comp f₁ = ⟨realSpinThreeHomeomorphQuaternionSphere,
      realSpinThreeHomeomorphQuaternionSphere.continuous⟩ := by
    ext s : 1
    apply Subtype.ext
    simp [f₃, f₁]
  have hdiag :
      HomotopyGroup.map ((f₃.comp f₂).comp f₁) (by simp [hf₁, hf₂, hf₃]) a =
        realSpinThreeHomotopyGroupMulEquivSphere a := by
    rw [← HomotopyGroup.map_comp_apply (f₃.comp f₂) (by simp [hf₂, hf₃]) f₁ hf₁,
      ← HomotopyGroup.map_comp_apply f₃ hf₃ f₂ hf₂,
      HomotopyGroup.map_conj_eq_id, HomotopyGroup.map_comp_apply,
      realSpinThreeHomotopyGroupMulEquivSphere_apply]
    exact HomotopyGroup.map_congr hf₃f₁ _ _ a
  rw [realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply, HomotopyGroup.prodMulEquiv_apply,
    HomotopyGroup.prodEquiv_apply, HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply,
    HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply, ← hdiag]
  refine Prod.ext (HomotopyGroup.map_congr ?_ _ _ a) (HomotopyGroup.map_congr ?_ _ _ a)
  · ext s : 1
    apply Subtype.ext
    simp [f₁, hf₂_apply, f₃, realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion]
  · ext s : 1
    apply Subtype.ext
    simp [f₁, hf₂_apply, f₃, realSpinFourCalibratedEquivQuaternionUnitaryProd_firstInclusion]

/-- **First-coordinate stabilization `SO(3) → SO(4)` induces the diagonal map on higher homotopy
groups** (`k ≥ 2`) in the calibrated sphere-product model. -/
theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion
    {N : Type*} [DecidableEq N] [Nontrivial N]
    (b : HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map
          (realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom 3 : C(_, _))
          (map_one (realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom 3)) b) =
      (realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere b,
        realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere b) := by
  obtain ⟨a, rfl⟩ := (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 3).surjective b
  rw [realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply,
    realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere_spinProjection]
  let inc₃ : C(realCliffordSpinGroupZero 3, realCliffordSpinGroupZero 4) :=
    realCliffordSpinFirstInclusionContinuousMonoidHom 3
  let proj₃ : C(realCliffordSpinGroupZero 3,
      QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) :=
    realCliffordSpinProjectionZero 3
  let proj₄ : C(realCliffordSpinGroupZero 4,
      QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) :=
    realCliffordSpinProjectionZero 4
  let incSO₃ : C(QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0),
      QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) :=
    realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom 3
  have hcomm : incSO₃.comp proj₃ = proj₄.comp inc₃ := by
    ext s : 1
    simp [incSO₃, proj₃, proj₄, inc₃]
  have hpush :
      HomotopyGroup.map incSO₃
          (map_one (realCliffordSpecialOrthogonalFirstInclusionContinuousMonoidHom 3))
          (HomotopyGroup.map proj₃ (map_one (realCliffordSpinProjectionZero 3)) a) =
        HomotopyGroup.map proj₄ (map_one (realCliffordSpinProjectionZero 4))
          (HomotopyGroup.map inc₃
            (map_one (realCliffordSpinFirstInclusionContinuousMonoidHom 3)) a) := by
    rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply]
    exact HomotopyGroup.map_congr hcomm _ _ a
  rw [hpush, realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection]
  exact realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstInclusion a

/-- **First-coordinate reflection swaps the two `πₖ(S³)` factors of `πₖ(Spin(4))`** in the
calibrated sphere-product model. -/
theorem realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection {N : Type*}
    [DecidableEq N] [Nonempty N] (a : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
    realSpinFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map ((realCliffordFirstReflectionIsometry 3).spinGroupContinuousMulEquiv :
          C(realCliffordSpinGroupZero 4, realCliffordSpinGroupZero 4))
          (map_one (realCliffordFirstReflectionIsometry 3).spinGroupContinuousMulEquiv) a) =
      Prod.swap (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd a) := by
  let e₄ : C(realCliffordSpinGroupZero 4, sphere (0 : ℍ[ℝ]) 1 × sphere (0 : ℍ[ℝ]) 1) :=
    ⟨realSpinFourCalibratedHomeomorphQuaternionSphereProd,
      realSpinFourCalibratedHomeomorphQuaternionSphereProd.continuous⟩
  have hfst (x : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
      (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd x).1 =
        HomotopyGroup.map ((ContinuousMap.fst : C(_, _)).comp e₄)
          (by simp [e₄]) x :=
    (congrArg Prod.fst ((realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply x).trans
      ((HomotopyGroup.prodMulEquiv_apply 1 1 _).trans
        (HomotopyGroup.prodEquiv_apply 1 1 _)))).trans
      (HomotopyGroup.map_comp_apply _ rfl e₄
        realSpinFourCalibratedHomeomorphQuaternionSphereProd_one x)
  have hsnd (x : HomotopyGroup N (realCliffordSpinGroupZero 4) 1) :
      (realSpinFourCalibratedHomotopyGroupMulEquivSphereProd x).2 =
        HomotopyGroup.map ((ContinuousMap.snd : C(_, _)).comp e₄)
          (by simp [e₄]) x :=
    (congrArg Prod.snd ((realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_apply x).trans
      ((HomotopyGroup.prodMulEquiv_apply 1 1 _).trans
        (HomotopyGroup.prodEquiv_apply 1 1 _)))).trans
      (HomotopyGroup.map_comp_apply _ rfl e₄
        realSpinFourCalibratedHomeomorphQuaternionSphereProd_one x)
  apply Prod.ext
  · rw [Prod.fst_swap, hfst, hsnd, HomotopyGroup.map_comp_apply]
    refine HomotopyGroup.map_congr ?_ _ _ a
    ext s : 1
    apply Subtype.ext
    simp [e₄]
  · rw [Prod.snd_swap, hsnd, hfst, HomotopyGroup.map_comp_apply]
    refine HomotopyGroup.map_congr ?_ _ _ a
    ext s : 1
    apply Subtype.ext
    simp [e₄]

/-- **First-coordinate reflection swaps the two `πₖ(S³)` factors of `πₖ(SO(4))`** (`k ≥ 2`) in the
calibrated sphere-product model. -/
theorem realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection
    {N : Type*} [DecidableEq N] [Nontrivial N]
    (b : HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) 1) :
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map
          (realCliffordFirstReflectionSpecialOrthogonalContinuousMulEquiv 3 : C(_, _))
          (map_one (realCliffordFirstReflectionSpecialOrthogonalContinuousMulEquiv 3)) b) =
      Prod.swap (realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd b) := by
  obtain ⟨a, rfl⟩ := (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 4).surjective b
  rw [realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply,
    realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection]
  let refl₄ : C(realCliffordSpinGroupZero 4, realCliffordSpinGroupZero 4) :=
    (realCliffordFirstReflectionIsometry 3).spinGroupContinuousMulEquiv
  let proj₄ : C(realCliffordSpinGroupZero 4,
      QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) :=
    realCliffordSpinProjectionZero 4
  let reflSO₄ : C(QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0),
      QuadraticMap.specialOrthogonalGroup (realCliffordForm 4 0)) :=
    realCliffordFirstReflectionSpecialOrthogonalContinuousMulEquiv 3
  have hcomm : reflSO₄.comp proj₄ = proj₄.comp refl₄ := by
    ext s : 1
    simp [reflSO₄, proj₄, refl₄]
  have hpush :
      HomotopyGroup.map reflSO₄
          (map_one (realCliffordFirstReflectionSpecialOrthogonalContinuousMulEquiv 3))
          (HomotopyGroup.map proj₄ (map_one (realCliffordSpinProjectionZero 4)) a) =
        HomotopyGroup.map proj₄ (map_one (realCliffordSpinProjectionZero 4))
          (HomotopyGroup.map refl₄
            (map_one (realCliffordFirstReflectionIsometry 3).spinGroupContinuousMulEquiv) a) := by
    rw [HomotopyGroup.map_comp_apply, HomotopyGroup.map_comp_apply]
    exact HomotopyGroup.map_congr hcomm _ _ a
  rw [hpush, realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd_spinProjection]
  exact realSpinFourCalibratedHomotopyGroupMulEquivSphereProd_firstReflection a

end

end CliffordAlgebra

namespace TauCeti

noncomputable section

variable {N : Type*} [DecidableEq N] [Nontrivial N]

/-- **`πₖ(SO(4)) ≅ πₖ(S³) × πₖ(S³)` for `k ≥ 2`, for the matrix group.** Transports
`CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd` along the
topological group isomorphism
`TauCeti.QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4`. -/
def specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd :
    HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 4) ℝ) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 ×
        HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (HomotopyGroup.homeomorphMulEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4).toHomeomorph
    (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4))).trans
    CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd

/-- The matrix-group isomorphism passes through
`QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4`. -/
theorem specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd_apply
    (a : HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 4) ℝ) 1) :
    specialOrthogonalGroupFourCalibratedHomotopyGroupMulEquivSphereProd a =
      CliffordAlgebra.realSpecialOrthogonalFourCalibratedHomotopyGroupMulEquivSphereProd
        (HomotopyGroup.map
          (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4 : C(_, _))
          (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4))
          a) :=
  (rfl)

/-- **`π₂(SO(4)) = 0` for the matrix group.** The second homotopy group of the group of real
special-orthogonal `4 × 4` matrices is trivial at every basepoint. -/
theorem subsingleton_homotopyGroup_specialOrthogonalGroup_four {N : Type*} (hN : Nat.card N = 2)
    (g : Matrix.specialOrthogonalGroup (Fin 4) ℝ) :
    Subsingleton (HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 4) ℝ) g) :=
  have := CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_four hN
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4 g)
  (HomotopyGroup.homeomorphEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 4).toHomeomorph
    rfl).subsingleton

end

end TauCeti
