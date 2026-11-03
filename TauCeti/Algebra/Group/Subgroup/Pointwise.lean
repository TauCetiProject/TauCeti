/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Conjugating subgroups and joining with a normalizing subgroup

Mathlib writes the conjugate `sHs⁻¹` of a subgroup `H` of a group `G` as the pointwise scalar
action `MulAut.conj s • H`.  This file records the membership criterion for that subgroup and the
two laws making `s ↦ MulAut.conj s • (-)` an action of `G` on the subgroups of `G`.

`Subgroup.mem_pointwise_smul_iff_inv_smul_mem` fixes the orientation: membership of `x` in
`MulAut.conj s • H` is `s⁻¹ * x * s ∈ H`, so `MulAut.conj s • H` is `sHs⁻¹` and not `s⁻¹Hs`.
`TauCeti.mem_conj_smul` pins that reading in the form the conjugate representation
(`TauCeti.RepresentationTheory.Induction.Conjugate`) and the Mackey subgroup
(`TauCeti.RepresentationTheory.Induction.Mackey.Subgroup`) consume, so neither can be silently
orientation-reversed.

When `K` normalizes `H`, Mathlib computes the carrier of the join `H ⊔ K` as the pointwise product
`H * K` (`Subgroup.coe_mul_of_right_le_normalizer_left`). This file also records the elementwise
form of that computation: every element of `H ⊔ K` is a product `x * t` with `x ∈ H` and `t ∈ K`.

## Main statements

* `TauCeti.mem_conj_smul`: membership in `sHs⁻¹` is `s⁻¹ * x * s ∈ H`.
* `TauCeti.conj_one_smul`, `TauCeti.conj_mul_smul`, `TauCeti.conj_inv_smul_smul`: conjugation of
  subgroups is an action of `G`.
* `TauCeti.map_conj_eq_conj_smul`: the image of `H` under the inner automorphism of `s` is
  `MulAut.conj s • H`, which converts Mathlib's statements phrased with `Subgroup.map`, such as
  `MulAction.stabilizer_smul_eq_stabilizer_map_conj` and `Ideal.inertia_smul`, to this convention.
* `Subgroup.mem_sup_of_right_le_normalizer_left`: if `K` normalizes `H`, an element of `H ⊔ K` is
  a product of an element of `H` followed by an element of `K`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- Membership in `sHs⁻¹`, in the conjugation convention `MulAut.conj s • H`. -/
@[simp]
theorem mem_conj_smul (s : G) (H : Subgroup G) (x : G) :
    x ∈ (MulAut.conj s • H : Subgroup G) ↔ s⁻¹ * x * s ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

/-- Conjugating a subgroup by `1` leaves it unchanged. -/
theorem conj_one_smul (H : Subgroup G) : MulAut.conj (1 : G) • H = H := by
  simp

/-- Conjugating a subgroup by `s * t` is conjugating by `t` and then by `s`. -/
theorem conj_mul_smul (s t : G) (H : Subgroup G) :
    MulAut.conj (s * t) • H = MulAut.conj s • (MulAut.conj t • H) := by
  rw [map_mul, mul_smul]

/-- Conjugating a subgroup by `s⁻¹` undoes conjugating it by `s`. -/
theorem conj_inv_smul_smul (s : G) (H : Subgroup G) :
    MulAut.conj s⁻¹ • (MulAut.conj s • H) = H := by
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The image of a subgroup under the inner automorphism of `s` is its conjugate
`MulAut.conj s • H`. -/
theorem map_conj_eq_conj_smul (s : G) (H : Subgroup G) :
    H.map (MulAut.conj s : G →* G) = MulAut.conj s • H :=
  -- The pointwise action of `MulAut G` on subgroups is defined as `Subgroup.map`.
  (rfl)

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G] {H K : Subgroup G}

/-- An element of `H ⊔ K` is a product of an element of `H` followed by an element of `K`, as soon
as `K` normalizes `H`. -/
theorem mem_sup_of_right_le_normalizer_left (hLE : K ≤ normalizer (H : Set G)) {g : G} :
    g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ t ∈ K, x * t = g := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left H K hLE, Set.mem_mul]
  simp only [SetLike.mem_coe]

end Subgroup
