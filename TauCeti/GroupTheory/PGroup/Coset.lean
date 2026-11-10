/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup

/-!
# Prime-power subgroups and cosets

A `p`-subgroup is contained in a conjugate of every subgroup whose index is prime to `p`.
This is the coset-action form of the fixed-point theorem
`IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card`: a fixed coset determines a conjugate
containing the acting subgroup. Neither the ambient group nor the acting subgroup needs to be
finite.
-/

public section

namespace IsPGroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}

/-- A `p`-subgroup lies in a conjugate of any subgroup of index indivisible by `p`. -/
theorem exists_le_map_conj_of_not_dvd_index (hA : IsPGroup p A) (H : Subgroup G)
    (hH : ¬ p ∣ H.index) :
    ∃ g : G, A ≤ H.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ H)
    (by simpa only [H.index_eq_card] using hH)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g, fun a ha => ?_⟩
  have hfix := MulAction.mem_fixedPoints.mp hx (⟨a, ha⟩ : A)
  have hcoset : (g : G ⧸ H) = ((a * g : G) : G ⧸ H) := by
    simpa only [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul] using hfix.symm
  have hmem : g⁻¹ * a * g ∈ H := by
    simpa only [mul_assoc] using QuotientGroup.eq.mp hcoset
  exact ⟨g⁻¹ * a * g, hmem, by simp [MulAut.conj_apply, mul_assoc]⟩

end IsPGroup
