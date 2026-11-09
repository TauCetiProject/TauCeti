/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Covering
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SimplyConnected
public import TauCeti.Topology.Algebra.QuadraticForm.RealSpecialOrthogonal
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Higher homotopy groups of `SO(n)` through the Spin double cover

The projection `Spin(n) → SO(n)` from the compact real Spin group is a covering map
(`CliffordAlgebra.isCoveringMap_realCliffordSpinProjectionZero`), so it identifies the homotopy
groups of `Spin(n)` and `SO(n)` at the identity in every dimension at least two
(`CliffordAlgebra.realCliffordSpinProjectionZeroHomotopyGroupMulEquiv`). In rank three, compact
`Spin(3)` is the unit quaternion sphere `S³ ⊆ ℍ`
(`TauCeti.realSpinThreeHomeomorphQuaternionSphere`), so `πₖ(SO(3), 1) ≅ πₖ(S³, 1)` for `k ≥ 2`
(`CliffordAlgebra.realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere`). Since `S³` is
`2`-connected, this gives the low-rank value

`π₂(SO(3)) = 0`

at every basepoint (`CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_three`).
This is the case `n = 3` of the torsion of `π_(n - 1)(SO(n))` for odd `n`, which enters the
exact sequence `π_n(SO(n + 1)) → π_n(Sⁿ) → π_(n - 1)(SO(n))` of the fibration
`SO(n) → SO(n + 1) → Sⁿ`. The same statements are transported to the matrix group
`Matrix.specialOrthogonalGroup (Fin 3) ℝ`
(`TauCeti.specialOrthogonalGroupThreeHomotopyGroupMulEquivSphere`,
`TauCeti.subsingleton_homotopyGroup_specialOrthogonalGroup_three`).

## Main definitions

* `CliffordAlgebra.realCliffordSpinProjectionZeroHomotopyGroupMulEquiv`:
  `π_N(Spin(n), 1) ≃* π_N(SO(n), 1)` for `Nat.card N ≥ 2`, induced by the Spin projection.
* `CliffordAlgebra.realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere`:
  `π_N(SO(3), 1) ≃* π_N(S³, 1)` for `Nat.card N ≥ 2`.
* `TauCeti.specialOrthogonalGroupThreeHomotopyGroupMulEquivSphere`: the same isomorphism for the
  matrix group `SO(3)`.

## Main results

* `CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_three`: `π₂(SO(3), g)` is
  trivial for every `g`.
* `TauCeti.subsingleton_homotopyGroup_specialOrthogonalGroup_three`: the same for the matrix group.

## References

* A. Hatcher, *Algebraic Topology* (2002), Proposition 4.1 and Section 4.2 (homotopy groups of
  covering spaces and of Lie groups).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

noncomputable section

open Metric
open scoped Quaternion Topology.Homotopy

namespace CliffordAlgebra

open TauCeti

variable {N : Type*} [DecidableEq N] [Nontrivial N]

/-- **The Spin projection is an isomorphism on higher homotopy groups.** Since
`Spin(n) → SO(n)` is a covering map, it induces `π_N(Spin(n), 1) ≃* π_N(SO(n), 1)` whenever
`N` has at least two elements, that is, in every dimension at least two. -/
def realCliffordSpinProjectionZeroHomotopyGroupMulEquiv (n : ℕ) [NeZero n] :
    HomotopyGroup N (realCliffordSpinGroupZero n) 1 ≃*
      HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)) 1 :=
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (realCliffordSpinProjectionZero n : C(_, _))
      (map_one (realCliffordSpinProjectionZero n)))
    (HomotopyGroup.map_bijective (isCoveringMap_realCliffordSpinProjectionZero n) _)

/-- The isomorphism of higher homotopy groups is the map induced by the Spin projection. -/
@[simp]
theorem realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply (n : ℕ) [NeZero n]
    (a : HomotopyGroup N (realCliffordSpinGroupZero n) 1) :
    realCliffordSpinProjectionZeroHomotopyGroupMulEquiv n a =
      HomotopyGroup.map (realCliffordSpinProjectionZero n : C(_, _))
        (map_one (realCliffordSpinProjectionZero n)) a :=
  (rfl)

/-- **`πₖ(SO(3)) ≅ πₖ(S³)` for `k ≥ 2`.** Compact `Spin(3)` is the unit quaternion sphere and
double covers `SO(3)`, so the higher homotopy groups of `SO(3)` at the identity are those of the
three-sphere `S³ ⊆ ℍ` at `1`. -/
def realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere :
    HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (realCliffordSpinProjectionZeroHomotopyGroupMulEquiv 3).symm.trans
    (HomotopyGroup.homeomorphMulEquivOfEq realSpinThreeHomeomorphQuaternionSphere
      realSpinThreeHomeomorphQuaternionSphere_one)

/-- The inverse of `realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere` is the map induced by
the Spin projection after the quaternion model of compact `Spin(3)`. -/
theorem realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere_symm_apply
    (a : HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :
    realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere.symm a =
      HomotopyGroup.map ((realCliffordSpinProjectionZero 3 : C(_, _)).comp
          ⟨realSpinThreeHomeomorphQuaternionSphere.symm,
            realSpinThreeHomeomorphQuaternionSphere.symm.continuous⟩)
        (by simp [realSpinThreeHomeomorphQuaternionSphere_symm_one,
          -realSpinThreeHomeomorphQuaternionSphere_symm_apply]) a := by
  rw [realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, realCliffordSpinProjectionZeroHomotopyGroupMulEquiv_apply,
    HomotopyGroup.homeomorphMulEquivOfEq_symm_apply]
  exact HomotopyGroup.map_comp_apply _ _ _ _ a

/-- **`π₂(SO(3)) = 0`.** The second homotopy group of the compact rotation group `SO(3)` is
trivial at every basepoint, since `SO(3)` is double covered by the three-sphere. -/
theorem subsingleton_homotopyGroup_realSpecialOrthogonal_three {N : Type*} (hN : Nat.card N = 2)
    (g : QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) :
    Subsingleton
      (HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) g) := by
  classical
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have : Subsingleton (HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1) :=
    subsingleton_homotopyGroup_sphere_of_lt (by rw [Quaternion.finrank_eq_four]) (by omega) 1
  have : Subsingleton
      (HomotopyGroup N (QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0)) 1) :=
    realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere.toEquiv.subsingleton
  exact (HomotopyGroup.homeomorphEquivOfEq (Homeomorph.mulLeft g) (mul_one g)).symm.subsingleton

end CliffordAlgebra

namespace TauCeti

variable {N : Type*} [DecidableEq N] [Nontrivial N]

/-- **`πₖ(SO(3)) ≅ πₖ(S³)` for `k ≥ 2`, for the matrix group.** The real special-orthogonal
`3 × 3` matrices form a topological group isomorphic to the special orthogonal group of
`realCliffordForm 3 0`, whose higher homotopy groups are computed by
`CliffordAlgebra.realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere`. -/
def specialOrthogonalGroupThreeHomotopyGroupMulEquivSphere :
    HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 3) ℝ) 1 ≃*
      HomotopyGroup N (sphere (0 : ℍ[ℝ]) 1) 1 :=
  (HomotopyGroup.homeomorphMulEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 3).toHomeomorph
    (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 3))).trans
    CliffordAlgebra.realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere

/-- The matrix-group isomorphism first passes to the special orthogonal group of
`realCliffordForm 3 0` through the matrix comparison. -/
theorem specialOrthogonalGroupThreeHomotopyGroupMulEquivSphere_apply
    (a : HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 3) ℝ) 1) :
    specialOrthogonalGroupThreeHomotopyGroupMulEquivSphere a =
      CliffordAlgebra.realSpecialOrthogonalThreeHomotopyGroupMulEquivSphere
        (HomotopyGroup.map
          (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 3 : C(_, _))
          (map_one (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 3))
          a) :=
  (rfl)

/-- **`π₂(SO(3)) = 0` for the matrix group.** The second homotopy group of the group of real
special-orthogonal `3 × 3` matrices is trivial at every basepoint. -/
theorem subsingleton_homotopyGroup_specialOrthogonalGroup_three {N : Type*} (hN : Nat.card N = 2)
    (g : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Subsingleton (HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin 3) ℝ) g) :=
  have := CliffordAlgebra.subsingleton_homotopyGroup_realSpecialOrthogonal_three hN
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 3 g)
  (HomotopyGroup.homeomorphEquivOfEq
    (QuadraticMap.matrixSpecialOrthogonalContinuousMulEquivRealCliffordForm 3).toHomeomorph
    rfl).subsingleton

end TauCeti
