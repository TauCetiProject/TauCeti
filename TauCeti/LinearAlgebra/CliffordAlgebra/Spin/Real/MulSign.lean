/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic

/-!
# Multiplication by the central signs of `Spin(n)`

In positive dimension the kernel of the double cover `Spin(n) → SO(n)` is the cyclic group of order
two, embedded by `(CliffordAlgebra.realCliffordSpinDoubleCoverZero n).inl`, which sends the
generator to `-1`. This kernel is central
(`CliffordAlgebra.realCliffordSpinDoubleCoverZero_inl_commute`), so multiplication by it is a
homomorphism

`μ : Spin(n) × ℤ/2 → Spin(n)`, `(g, ε) ↦ g ε`

(`CliffordAlgebra.realCliffordSpinMulSign`), and it does not change the rotation `π(g)` of `g`
(`CliffordAlgebra.spinToSpecialOrthogonal_comp_realCliffordSpinMulSign`). Twisting a Spin
structure by a principal `ℤ/2`-bundle extends its fibre product with the bundle along `μ`
(`TauCeti.SpinStructure.twist`); since every sign squares to one, twisting twice by the same
bundle gives back the Spin structure.

## Main definitions

* `CliffordAlgebra.realCliffordSpinMulSign`: multiplication by the central signs,
  `Spin(n) × ℤ/2 →* Spin(n)`.

## Main results

* `CliffordAlgebra.spinToSpecialOrthogonal_comp_realCliffordSpinMulSign`: multiplying by a sign
  does not change the rotation.
* `CliffordAlgebra.realCliffordSpinMulSign_comp_inl`: multiplying by the trivial sign changes
  nothing.
* `CliffordAlgebra.realCliffordSpinMulSign_realCliffordSpinMulSign`: multiplying by `ε` and then by
  `ε'` is multiplying by `ε ε'`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter I, §2
  and Chapter II, §1.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable (n : ℕ) [NeZero n]

/-- **Multiplication by the central signs** of `Spin(n)`, `Spin(n) × ℤ/2 →* Spin(n)`,
`(g, ε) ↦ g ε`, where `ℤ/2` is embedded as the kernel `{1, -1}` of the double cover
`Spin(n) → SO(n)` (`CliffordAlgebra.realCliffordSpinDoubleCoverZero`). It is a homomorphism because
the signs are central. -/
noncomputable def realCliffordSpinMulSign :
    realCliffordSpinGroupZero n × Multiplicative (ZMod 2) →* realCliffordSpinGroupZero n :=
  (MonoidHom.id _).noncommCoprod (realCliffordSpinDoubleCoverZero n).inl fun g ε ↦
    (realCliffordSpinDoubleCoverZero_inl_commute n ε g).symm

@[simp]
theorem realCliffordSpinMulSign_apply (g : realCliffordSpinGroupZero n)
    (ε : Multiplicative (ZMod 2)) :
    realCliffordSpinMulSign n (g, ε) = g * (realCliffordSpinDoubleCoverZero n).inl ε :=
  (rfl)

/-- **Multiplying by a sign does not change the rotation**: `π(g ε) = π(g)`. -/
@[simp]
theorem spinToSpecialOrthogonal_realCliffordSpinMulSign
    (g : realCliffordSpinGroupZero n × Multiplicative (ZMod 2)) :
    spinToSpecialOrthogonal (realCliffordForm n 0) (realCliffordSpinMulSign n g) =
      spinToSpecialOrthogonal (realCliffordForm n 0) g.1 := by
  rw [realCliffordSpinMulSign_apply, map_mul,
    spinToSpecialOrthogonal_realCliffordSpinDoubleCoverZero_inl, mul_one]

/-- Multiplication by the central signs lifts the first projection along the double cover
`Spin(n) → SO(n)`. -/
theorem spinToSpecialOrthogonal_comp_realCliffordSpinMulSign :
    (spinToSpecialOrthogonal (realCliffordForm n 0)).comp (realCliffordSpinMulSign n) =
      (spinToSpecialOrthogonal (realCliffordForm n 0)).comp (MonoidHom.fst _ _) :=
  MonoidHom.ext (spinToSpecialOrthogonal_realCliffordSpinMulSign n)

/-- Multiplication by the central signs lifts the first projection along the vector action
`Spin(n) → SO(n) ⊆ GL(ℝⁿ)`, along which Spin structures lift the orthonormal frame bundle. -/
theorem subtype_comp_spinToSpecialOrthogonal_comp_realCliffordSpinMulSign :
    (((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype).comp
        (spinToSpecialOrthogonal (realCliffordForm n 0))).comp (realCliffordSpinMulSign n) =
      (((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype).comp
        (spinToSpecialOrthogonal (realCliffordForm n 0))).comp (MonoidHom.fst _ _) := by
  rw [MonoidHom.comp_assoc, spinToSpecialOrthogonal_comp_realCliffordSpinMulSign,
    MonoidHom.comp_assoc]

/-- Multiplying by the trivial sign changes nothing: `μ (g, 1) = g`. -/
@[simp]
theorem realCliffordSpinMulSign_comp_inl :
    (realCliffordSpinMulSign n).comp (MonoidHom.inl _ _) = MonoidHom.id _ :=
  MonoidHom.ext fun g ↦ by simp

/-- Multiplying by the sign `ε` and then by `ε'` is multiplying by `ε ε'`. -/
theorem realCliffordSpinMulSign_realCliffordSpinMulSign (g : realCliffordSpinGroupZero n)
    (ε ε' : Multiplicative (ZMod 2)) :
    realCliffordSpinMulSign n (realCliffordSpinMulSign n (g, ε), ε') =
      realCliffordSpinMulSign n (g, ε * ε') := by
  simp only [realCliffordSpinMulSign_apply, map_mul, mul_assoc]

end CliffordAlgebra
