/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Euclidean

/-!
# Multiplication by the central signs of `Spin(n)`

In positive dimension the kernel of the double cover `Spin(n) → SO(n)` is the cyclic group of order
two, embedded by `(CliffordAlgebra.realCliffordSpinDoubleCoverZero n).inl`, which sends the
generator to `-1`. This kernel is central, so multiplication by it is a homomorphism

`μ : Spin(n) × ℤ/2 → Spin(n)`, `(g, ε) ↦ g ε`

(`CliffordAlgebra.realCliffordSpinMulSign`), and it does not change the rotation `π(g)` of `g`
(`CliffordAlgebra.spinToSpecialOrthogonal_comp_realCliffordSpinMulSign`). Extending a fibre
product of a Spin structure with a principal `ℤ/2`-bundle along `μ` twists the Spin structure by
that bundle (`TauCeti.SpinStructure.twist`); since every sign squares to one, twisting twice by
the same bundle gives back the Spin structure.

## Main definitions

* `CliffordAlgebra.realCliffordSpinMulSign`: multiplication by the central signs,
  `Spin(n) × ℤ/2 →* Spin(n)`.

## Main results

* `CliffordAlgebra.realCliffordSpinDoubleCoverZero_inl_mem_center`: the signs are central.
* `CliffordAlgebra.spinToSpecialOrthogonal_comp_realCliffordSpinMulSign`: multiplying by a sign
  does not change the rotation.
* `CliffordAlgebra.realCliffordSpinMulSign_realCliffordSpinMulSign`: multiplying by `ε` and then by
  `ε'` is multiplying by `ε ε'`.
* `CliffordAlgebra.continuous_realCliffordSpinMulSign`: the multiplication is continuous.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter I, §2
  and Chapter II, §1.
-/

public section

namespace CliffordAlgebra

open TauCeti

variable (n : ℕ) [NeZero n]

/-- **The signs of `Spin(n)` are central**: the image of the kernel `ℤ/2` of the double cover
`Spin(n) → SO(n)`, namely `{1, -1}`, lies in the centre of `Spin(n)`. -/
theorem realCliffordSpinDoubleCoverZero_inl_mem_center (ε : Multiplicative (ZMod 2)) :
    (realCliffordSpinDoubleCoverZero n).inl ε ∈ Subgroup.center (realCliffordSpinGroupZero n) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain rfl | rfl : ε = 1 ∨ ε = Multiplicative.ofAdd 1 := by revert ε; decide
  · rw [map_one, mul_one, one_mul]
  · rw [realCliffordSpinDoubleCoverZero_inl_ofAdd_one, spinGroup.negOne_mul_comm]

/-- The signs of `Spin(n)` act trivially on `ℝⁿ`: they lie in the kernel of `Spin(n) → SO(n)`. -/
@[simp]
theorem spinToSpecialOrthogonal_realCliffordSpinDoubleCoverZero_inl (ε : Multiplicative (ZMod 2)) :
    spinToSpecialOrthogonal (realCliffordForm n 0) ((realCliffordSpinDoubleCoverZero n).inl ε) =
      1 := by
  rw [← realCliffordSpinDoubleCoverZero_rightHom, GroupExtension.rightHom_inl]

/-- **Multiplication by the central signs** of `Spin(n)`, `Spin(n) × ℤ/2 →* Spin(n)`,
`(g, ε) ↦ g ε`, where `ℤ/2` is embedded as the kernel `{1, -1}` of the double cover
`Spin(n) → SO(n)` (`CliffordAlgebra.realCliffordSpinDoubleCoverZero`). It is a homomorphism because
the signs are central. -/
noncomputable def realCliffordSpinMulSign :
    realCliffordSpinGroupZero n × Multiplicative (ZMod 2) →* realCliffordSpinGroupZero n :=
  (MonoidHom.id _).noncommCoprod (realCliffordSpinDoubleCoverZero n).inl fun g ε ↦
    Subgroup.mem_center_iff.1 (realCliffordSpinDoubleCoverZero_inl_mem_center n ε) g

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

/-- Multiplying by the sign `ε` and then by `ε'` is multiplying by `ε ε'`. -/
theorem realCliffordSpinMulSign_realCliffordSpinMulSign (g : realCliffordSpinGroupZero n)
    (ε ε' : Multiplicative (ZMod 2)) :
    realCliffordSpinMulSign n (realCliffordSpinMulSign n (g, ε), ε') =
      realCliffordSpinMulSign n (g, ε * ε') := by
  simp only [realCliffordSpinMulSign_apply, map_mul, mul_assoc]

/-- Multiplication by the central signs is continuous. -/
@[fun_prop]
theorem continuous_realCliffordSpinMulSign : Continuous (realCliffordSpinMulSign n) := by
  have h : Continuous fun g : realCliffordSpinGroupZero n × Multiplicative (ZMod 2) ↦
      g.1 * (realCliffordSpinDoubleCoverZero n).inl g.2 :=
    continuous_fst.mul (continuous_of_discreteTopology.comp continuous_snd)
  exact h.congr fun g ↦ (realCliffordSpinMulSign_apply n g.1 g.2).symm

end CliffordAlgebra
