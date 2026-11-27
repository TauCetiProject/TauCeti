/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# The orthogonal projector of a line in complex projective space

A point `L` of complex projective space `CPⁿ` (`TauCeti.ComplexProjectiveSpace n`) is a complex
line in `ℂⁿ⁺¹`; this file identifies it with the orthogonal projector `Π_L` onto that line, a
Hermitian matrix, by transporting `Projectivization.hermitianProjector` along
`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hermitianProjector`: the orthogonal projector `Π_L` of a line.

## Main results

* `TauCeti.ComplexProjectiveSpace.hermitianProjector_injective`: distinct lines have distinct
  projectors.
* `TauCeti.ComplexProjectiveSpace.coe_hermitianProjector_mk`: for a unit vector `y`,
  `Π_[y] = y y*`.
* `TauCeti.ComplexProjectiveSpace.coe_hermitianProjector_smul`: the projector is unitarily
  equivariant, `Π_(A L) = A Π_L A*`.
-/

public section

noncomputable section

open Function Matrix Metric WithLp

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

variable (n) in
/-- The **orthogonal projector** `Π_L` onto a line `L` of `ℂⁿ⁺¹`, as a Hermitian matrix: the
Hermitian projector `y y* / (y* y)` of any vector `y` spanning `L`
(`Projectivization.hermitianProjector`). -/
def hermitianProjector (x : ComplexProjectiveSpace n) :
    selfAdjoint.submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
  ⟨(homeomorphProjectivization n x).hermitianProjector,
    (mem_hermitianProjectorLocus.mp
      (Projectivization.hermitianProjector_mem_hermitianProjectorLocus _)).1.isSelfAdjoint⟩

theorem coe_hermitianProjector (x : ComplexProjectiveSpace n) :
    (hermitianProjector n x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (homeomorphProjectivization n x).hermitianProjector :=
  (rfl)

/-- Distinct lines have distinct projectors. -/
theorem hermitianProjector_injective : Injective (hermitianProjector n) := fun _ _ h ↦
  (homeomorphProjectivization n).injective
    (Projectivization.hermitianProjector_injective (congrArg Subtype.val h))

/-- Two lines are equal exactly when their projectors are. -/
@[simp]
theorem hermitianProjector_inj {x y : ComplexProjectiveSpace n} :
    hermitianProjector n x = hermitianProjector n y ↔ x = y :=
  hermitianProjector_injective.eq_iff

/-- The projector onto the line spanned by a unit vector `y` is the Hermitian projector of `y`,
the matrix `y y*`. -/
@[simp]
theorem coe_hermitianProjector_mk (y : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (hermitianProjector n (mk n y) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      rankOneHermitianProjector (ofLp (y : EuclideanSpace ℂ (Fin (n + 1)))) := by
  rw [coe_hermitianProjector, homeomorphProjectivization_mk, Projectivization.hermitianProjector_mk]

/-- **The projector is unitarily equivariant**: moving a line by a unitary matrix `A` conjugates
its projector by `A`, `Π_(A L) = A Π_L A*`. -/
theorem coe_hermitianProjector_smul (A : unitaryGroup (Fin (n + 1)) ℂ)
    (x : ComplexProjectiveSpace n) :
    (hermitianProjector n (A • x) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      A * hermitianProjector n x * star (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  induction x using ComplexProjectiveSpace.inductionOn with
  | h y =>
    rw [smul_mk, coe_hermitianProjector_mk, coe_hermitianProjector_mk,
      LinearIsometryEquiv.coe_smul_unitSphere, UnitaryGroup.toLinearIsometryEquiv_apply, ofLp_toLp,
      rankOneHermitianProjector_unitary_mulVec A.property]

end TauCeti.ComplexProjectiveSpace
