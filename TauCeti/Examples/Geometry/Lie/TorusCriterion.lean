/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane
public import TauCeti.RepresentationTheory.SU2.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup
public import TauCeti.Topology.Algebra.Quaternion.Unitary.HomotopyGroup

/-!
# Checks of the torus criterion on tori, `SU(2)` and `SO(3)`

The torus criterion `TauCeti.Lie.isAspherical_iff_exists_continuousMulEquiv_torus` says that a
compact connected Lie group is aspherical exactly when it is isomorphic, as a topological group,
to a torus `(S¹)ʳ`. This file checks it, and the computations of `π₃` it rests on, on tori and
on the groups `SU(2)`, `SU(2) × SU(2)` and `SO(3)`.

* **Tori.** `Fin r → Circle` is aspherical (`Circle.isAspherical_pi`) and is a torus: both sides
  hold. In particular its third homotopy group vanishes.
* **`SU(2)` and `SU(2) × SU(2)`.** `SU(2)` is the three-sphere
  (`TauCeti.specialUnitaryGroupTwoHomeomorphSphere`), so `π₃(SU(2)) ≅ ℤ`
  (`TauCeti.specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt`), and
  `π₃(SU(2) × SU(2)) ≅ ℤ²`
  (`TauCeti.specialUnitaryGroupTwoProdHomotopyGroupThreeMulEquiv`). Both are
  proved in `TauCeti.Topology.Algebra.Quaternion.Unitary.HomotopyGroup`.
* **`SO(3)`.** `SO(3)` is doubly covered by the simply connected group `Spin(3) ≅ S³`, so the
  torus factor of its finite cover is trivial. A covering map is bijective on the homotopy groups
  in degrees at least two, so `π₃(SO(3)) ≅ π₃(S³) ≅ ℤ` at every base point
  (`TauCeti.specialOrthogonalGroupThreeHomotopyGroupThreeMulEquivInt`), while
  `π₂(SO(3)) = 0` (`TauCeti.subsingleton_homotopyGroup_specialOrthogonalGroup_three`). Hence
  `SO(3)` is not aspherical (`TauCeti.not_isAspherical_specialOrthogonalGroup_three`), and it is
  not a torus, since tori are aspherical: both sides fail.
  The computation of `π₃(SO(3))` and the failure of asphericity are proved with the other
  homotopy groups of `SO(3)` in `TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup`.

The Lie group hypothesis of the criterion is checked on the product `ℕ → Circle` of countably
many circles by `Circle.isEmpty_pi_mulEquiv_pi` and `TauCeti.not_lieGroup_pi_circle`: it is
aspherical but not a torus, and it is not a Lie group.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.30 and the proof of
  Proposition 6.31).
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapters I and V.
-/

public section

noncomputable section

open Matrix
open scoped Topology Topology.Homotopy

namespace TauCeti

/-! ### Tori -/

/-- **Tori**: a torus `Fin r → Circle` is aspherical and is a torus, so both sides of the torus
criterion hold. -/
example (r : ℕ) : IsAspherical (Fin r → Circle) 1 ∧
    ∃ s : ℕ, Nonempty ((Fin r → Circle) ≃ₜ* (Fin s → Circle)) :=
  ⟨Circle.isAspherical_pi 1, r, ⟨ContinuousMulEquiv.refl _⟩⟩

/-- **The third homotopy group of a torus vanishes**, so the Cartan three-form, which vanishes on
a torus, has nothing to detect there. -/
example (r : ℕ) : Subsingleton (π_ 3 (Fin r → Circle) 1) :=
  (Circle.isAspherical_pi 1).subsingleton_homotopyGroup 1

/-! ### The groups `SU(2)` and `SU(2) × SU(2)` -/

/-- **`π₃(SU(2)) ≅ ℤ`**, at every base point: `SU(2)` is the three-sphere, the unit sphere of the
quaternions. -/
example (g : SU2) : Nonempty (π_ 3 SU2 g ≃* Multiplicative ℤ) :=
  ⟨specialUnitaryGroupTwoHomotopyGroupThreeMulEquivInt g⟩

/-- **`π₃(SU(2) × SU(2)) ≅ ℤ²`**, at every base point: the homotopy groups of a product are the
products of the homotopy groups of the factors. -/
example (g h : SU2) :
    Nonempty (π_ 3 (SU2 × SU2) (g, h) ≃* Multiplicative ℤ × Multiplicative ℤ) :=
  ⟨specialUnitaryGroupTwoProdHomotopyGroupThreeMulEquiv g h⟩

/-! ### The rotation group `SO(3)` -/

/-- **`SO(3)` is not a torus**: it is not isomorphic, as a topological group, to any torus
`Fin r → Circle`, since tori are aspherical and `SO(3)` is not. With
`TauCeti.not_isAspherical_specialOrthogonalGroup_three`, both sides of the torus criterion fail
for `SO(3)`. -/
example :
    ¬∃ r : ℕ, Nonempty (specialOrthogonalGroup (Fin 3) ℝ ≃ₜ* (Fin r → Circle)) := by
  rintro ⟨r, ⟨e⟩⟩
  exact not_isAspherical_specialOrthogonalGroup_three 1
    ((Circle.isAspherical_pi 1).of_homotopyEquiv e.toHomeomorph.symm.toHomotopyEquiv 1)

end TauCeti
