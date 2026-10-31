/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# Basic Spin-group carrier facts

This file records the carrier-level criterion that a product of evenly many Clifford vectors whose
norms multiply to one belongs to the Spin group, identifies membership in the range of
`spinGroup.toUnits` with membership of the underlying Clifford value, includes the Spin group in
the even Clifford subalgebra, writes every Spin element as a product of an even number of vectors
of invertible norm when `2` is invertible, and proves that the Spin group of the zero module is
trivial. The action and its orthogonal comparison are defined in `Spin.Action` and `Pin.Action`.
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

/-- **The inclusion of the Spin group into the even Clifford subalgebra**, the Spin group
consisting of even elements by `spinGroup.mem_even`. -/
def spinGroupToEven (Q : QuadraticForm R M) : spinGroup Q →* even Q :=
  Submonoid.inclusion fun _ hx => spinGroup.mem_even hx

/-- A Spin-group element sits in the even subalgebra as itself. -/
@[simp]
theorem coe_spinGroupToEven_apply (Q : QuadraticForm R M) (x : spinGroup Q) :
    (spinGroupToEven Q x : CliffordAlgebra Q) = x :=
  (rfl)

/-- `spinGroupToEven` on an explicitly packaged Spin element. -/
@[simp]
theorem spinGroupToEven_mk (x : CliffordAlgebra Q) (hx : x ∈ spinGroup Q) :
    spinGroupToEven Q ⟨x, hx⟩ = ⟨x, spinGroup.mem_even hx⟩ :=
  Subtype.ext (coe_spinGroupToEven_apply Q _)

/-- **A product of evenly many vectors whose norms multiply to one lies in the Spin group.** The
norms are then units, so the product is a unit of the Lipschitz group, and its Clifford norm
`star x * x` is `(-1) ^ n * Q v₁ ⋯ Q vₙ = 1`. -/
theorem prod_map_ι_mem_spinGroup {l : List M} (hl : Even l.length) (hQ : (l.map Q).prod = 1) :
    (l.map (ι Q)).prod ∈ spinGroup Q := by
  have hunit : ∀ v ∈ l, IsUnit (Q v) := fun v hv ↦
    List.prod_isUnit_iff.mp (hQ ▸ isUnit_one) (Q v) (List.mem_map_of_mem hv)
  have hP := isUnit_prod_map_ι (Q := Q) (hQ ▸ isUnit_one)
  have hstar : star (l.map (ι Q)).prod * (l.map (ι Q)).prod = 1 := by
    rw [star_prod_map_ι_mul_prod_map_ι, hl.neg_one_pow, hQ, one_mul, map_one]
  refine spinGroup.mem_iff.mpr ⟨⟨⟨hP.unit, mem_lipschitzGroup_of_coe_eq_prod_map_ι l hunit rfl,
    rfl⟩, hP.mem_unitary_of_star_mul_self hstar⟩, ?_⟩
  rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
  exact prod_map_ι_mem_evenOdd_zero_of_even_length hl

/-- The product of two Clifford generators belongs to Spin when their norms multiply to one. -/
theorem ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one (x y : M)
    (hxy : Q x * Q y = 1) :
    ι Q x * ι Q y ∈ spinGroup Q := by
  simpa using prod_map_ι_mem_spinGroup (Q := Q) (l := [x, y]) (by simp) (by simpa using hxy)

/-- When `2` is invertible, every Spin element is a product of an even number of vectors of
invertible norm. -/
theorem exists_even_length_list_of_spinGroup [Invertible (2 : R)] (x : spinGroup Q) :
    ∃ l : List M, (∀ v ∈ l, IsUnit (Q v)) ∧ Even l.length ∧
      (x : CliffordAlgebra Q) = (l.map (ι Q)).prod := by
  obtain ⟨l, hl, hx⟩ := mem_lipschitzGroup_iff_exists_list.mp
    (spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits x) x.2)
  rw [spinGroup.val_toUnits_apply] at hx
  by_cases heven : Even l.length
  · exact ⟨l, hl, heven, hx⟩
  -- An odd product of vectors is negated by the grade involution, while the even element `x` is
  -- fixed by it. So the unit `x` vanishes, the Clifford algebra is trivial, and `[]` works.
  have hinv := involute_prod_map_ι (Q := Q) l
  rw [← hx, spinGroup.involute_eq x.2, (Nat.not_even_iff_odd.mp heven).neg_one_pow,
    neg_one_smul] at hinv
  have hzero : (x : CliffordAlgebra Q) = 0 := by
    have h2 : (2 : R) • (x : CliffordAlgebra Q) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hinv]
      exact neg_add_cancel _
    simpa using congrArg ((⅟2 : R) • ·) h2
  have h01 := spinGroup.coe_mul_star_self x
  rw [hzero, zero_mul] at h01
  have : Subsingleton (CliffordAlgebra Q) := subsingleton_of_zero_eq_one h01
  exact ⟨[], by simp, by simp, Subsingleton.elim _ _⟩

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
