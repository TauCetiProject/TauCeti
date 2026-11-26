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

## Main results

* `TauCeti.nonempty_homotopyGroup_three_specialUnitaryGroup_two_mulEquiv_int`:
  `π₃(SU(2), g) ≅ ℤ` for every `g`.
* `TauCeti.nonempty_homotopyGroup_three_prod_specialUnitaryGroup_two_mulEquiv`:
  `π₃(SU(2) × SU(2), (g, h)) ≅ ℤ²` for all `g` and `h`.
-/

public section

open scoped Topology

namespace TauCeti

/-- **`π₃(SU(2)) ≅ ℤ`**, at every base point: `SU(2)` is the three-sphere, the unit sphere of the
quaternions. -/
theorem nonempty_homotopyGroup_three_specialUnitaryGroup_two_mulEquiv_int
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Nonempty (π_ 3 (Matrix.specialUnitaryGroup (Fin 2) ℂ) g ≃* Multiplicative ℤ) :=
  ⟨(HomotopyGroup.homeomorphMulEquiv specialUnitaryGroupTwoHomeomorphSphere g).trans
    (homotopyGroupSphereQuaternionMulEquiv _)⟩

/-- **`π₃(SU(2) × SU(2)) ≅ ℤ²`**, at every base point: the homotopy groups of a product are the
products of the homotopy groups of the factors. -/
theorem nonempty_homotopyGroup_three_prod_specialUnitaryGroup_two_mulEquiv
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Nonempty (π_ 3 (Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (g, h) ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  obtain ⟨e₁⟩ := nonempty_homotopyGroup_three_specialUnitaryGroup_two_mulEquiv_int g
  obtain ⟨e₂⟩ := nonempty_homotopyGroup_three_specialUnitaryGroup_two_mulEquiv_int h
  exact ⟨(HomotopyGroup.prodMulEquiv g h).trans (e₁.prodCongr e₂)⟩

end TauCeti
