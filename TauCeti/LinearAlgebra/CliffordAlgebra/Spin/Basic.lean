/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Basic

/-!
# Basic Spin-group carrier facts

This file records the carrier-level criterion that a product of two Clifford vectors with
unit product of norms belongs to the Spin group, identifies membership in the range of
`spinGroup.toUnits` with membership of the underlying Clifford value, and proves that the Spin
group of the zero module is trivial. The action and its orthogonal comparison are defined in
`Spin.Action` and `Pin.Action`.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- A Clifford unit belongs to the range of the canonical map from the Spin group exactly when
its Clifford value belongs to the Spin group. -/
@[simp↓]
theorem mem_spinGroup_toUnits_range_iff (u : (CliffordAlgebra Q)ˣ) :
    u ∈ (spinGroup.toUnits (Q := Q)).range ↔ (u : CliffordAlgebra Q) ∈ spinGroup Q := by
  constructor
  · rintro ⟨s, rfl⟩
    exact s.2
  · intro hu
    refine ⟨⟨(u : CliffordAlgebra Q), hu⟩, ?_⟩
    apply Units.ext
    rfl

/-- The product of two Clifford generators belongs to Spin when their norms multiply to one. -/
theorem ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one (x y : M)
    (hxy : Q x * Q y = 1) :
    ι Q x * ι Q y ∈ spinGroup Q := by
  let _ : Invertible (Q x) := (IsUnit.of_mul_eq_one (Q y) hxy).invertible
  let _ : Invertible (Q y) :=
    (IsUnit.of_mul_eq_one (Q x) (by simpa only [mul_comm] using hxy)).invertible
  let a := unitι Q x * unitι Q y
  have ha : (a : CliffordAlgebra Q) = ι Q x * ι Q y := by simp [a]
  apply spinGroup.mem_iff.mpr
  refine ⟨?_, ?_⟩
  · refine ⟨⟨a, mul_mem (unitι_mem_lipschitzGroup x) (unitι_mem_lipschitzGroup y), ha⟩,
      (ha ▸ a.isUnit).mem_unitary_of_star_mul_self ?_⟩
    rw [star_mul, star_ι, star_ι, neg_mul_neg]
    calc
      (ι Q y * ι Q x) * (ι Q x * ι Q y) =
          ι Q y * (ι Q x * ι Q x) * ι Q y := by noncomm_ring
      _ = ι Q y * algebraMap R _ (Q x) * ι Q y := by rw [ι_sq_scalar]
      _ = algebraMap R _ (Q x) * (ι Q y * ι Q y) := by
        rw [← Algebra.commutes (Q x) (ι Q y), mul_assoc]
      _ = algebraMap R _ (Q x) * algebraMap R _ (Q y) := by rw [ι_sq_scalar]
      _ = 1 := by rw [← map_mul, hxy, map_one]
  · rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero Q x y

/-- The Spin group of a quadratic form on the zero module is trivial, because the Lipschitz group
containing it is (`lipschitzGroup_eq_bot`). -/
instance instSubsingletonSpinGroup [Subsingleton M] : Subsingleton (spinGroup Q) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have h (z : spinGroup Q) : (z : CliffordAlgebra Q) = 1 := by
    obtain ⟨w, hw, hwz⟩ := pinGroup.mem_lipschitzGroup (spinGroup.mem_pin z.2)
    rw [SetLike.mem_coe, Subgroup.mem_toSubmonoid, lipschitzGroup_eq_bot, Subgroup.mem_bot] at hw
    simp [← hwz, hw]
  rw [h x, h y]

end CliffordAlgebra
