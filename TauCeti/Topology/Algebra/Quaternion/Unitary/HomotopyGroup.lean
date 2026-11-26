/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Algebra.Quaternion.Unitary
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# The third homotopy group of `SU(2)`

`SU(2)` is the three-sphere, the unit sphere of the quaternions
(`TauCeti.specialUnitaryGroupTwoHomeomorphSphere`). Transporting `π₃(S³) ≅ ℤ`
(`TauCeti.homotopyGroupSphereQuaternionMulEquiv`) along this homeomorphism gives
`π₃(SU(2)) ≅ ℤ` at every base point, and the homotopy groups of a product give
`π₃(SU(2) × SU(2)) ≅ ℤ²`.

## Main definitions

* `TauCeti.specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt`:
  `π₃(SU(2), g) ≅ ℤ` for every `g`.
* `TauCeti.specialUnitaryGroupTwoProdHomotopyGroupThreeMulEquiv`:
  `π₃(SU(2) × SU(2), (g, h)) ≅ ℤ²` for all `g` and `h`.
-/

public section

open scoped Topology

namespace TauCeti

/-- **`π₃(SU(2)) ≅ ℤ`**, at every base point: `SU(2)` is the three-sphere, the unit sphere of the
quaternions. -/
noncomputable def specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    π_ 3 (Matrix.specialUnitaryGroup (Fin 2) ℂ) g ≃* Multiplicative ℤ :=
  (HomotopyGroup.homeomorphMulEquiv specialUnitaryGroupTwoHomeomorphSphere g).trans
    (homotopyGroupSphereQuaternionMulEquiv _)

/-- **`π₃(SU(2) × SU(2)) ≅ ℤ²`**, at every base point: the homotopy groups of a product are the
products of the homotopy groups of the factors (`HomotopyGroup.prodMulEquiv`), and each factor is
identified with `ℤ` by `TauCeti.specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt`. -/
noncomputable def specialUnitaryGroupTwoProdHomotopyGroupThreeMulEquiv
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    π_ 3 (Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ) (g, h) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (HomotopyGroup.prodMulEquiv g h).trans
    ((specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt g).prodCongr
      (specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt h))

end TauCeti
