/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Splitting extensions of cyclic groups

An extension of a cyclic group splits if and only if a generator lifts to an element satisfying
its order relation. For a central extension, a root in the kernel can correct an arbitrary lift
to one satisfying that relation.
-/

public section

namespace GroupExtension

variable {N E G : Type*} [Group N] [Group E] [Group G]

/-- An extension of a cyclic group splits exactly when the chosen generator lifts to an element
whose `orderOf g`-th power is `1`. For an infinite cyclic quotient this relation is automatic. -/
theorem nonempty_splitting_iff_exists_lift_pow_eq_one (S : GroupExtension N E G)
    {g : G} (hg : Subgroup.zpowers g = ⊤) :
    Nonempty S.Splitting ↔ ∃ t : E, S.rightHom t = g ∧ t ^ orderOf g = 1 := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s g, s.rightHom_splitting g, by rw [← map_pow, pow_orderOf_eq_one, map_one]⟩
  · rintro ⟨t, ht, hpow⟩
    have hsurj : Function.Surjective (zpowersHom G g) := by
      rw [← MonoidHom.range_eq_top, Subgroup.range_zpowersHom, hg]
    let e := QuotientGroup.quotientKerEquivOfSurjective (zpowersHom G g) hsurj
    let f := QuotientGroup.lift (zpowersHom G g).ker (zpowersHom E t) (by
      rw [zpowersHom_ker_eq, Subgroup.zpowers_le, MonoidHom.mem_ker]
      simpa using hpow)
    have hf : Function.RightInverse (f.comp e.symm.toMonoidHom) S.rightHom := by
      intro q
      obtain ⟨i, rfl⟩ := hsurj q
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply]
      simp [f, ht]
    exact ⟨{ toMonoidHom := f.comp e.symm.toMonoidHom, rightInverse_rightHom := hf }⟩

/-- A central extension of a cyclic group splits if the kernel admits roots of degree the
order of a generator (or if the generator has infinite order). -/
theorem nonempty_splitting_of_zpowers_eq_top (S : GroupExtension N E G)
    {g : G} (hg : Subgroup.zpowers g = ⊤)
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (hroot : 0 < orderOf g → Function.Surjective (fun n : N ↦ n ^ orderOf g)) :
    Nonempty S.Splitting := by
  obtain ⟨t, ht⟩ := S.rightHom_surjective g
  apply (S.nonempty_splitting_iff_exists_lift_pow_eq_one hg).2
  by_cases h : orderOf g = 0
  · exact ⟨t, ht, by simp [h]⟩
  have hmem : (t ^ orderOf g)⁻¹ ∈ S.inl.range := by
    simp [S.range_inl_eq_ker_rightHom, ht, pow_orderOf_eq_one]
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨b, hb : b ^ orderOf g = a⟩ := hroot (Nat.pos_of_ne_zero h) a
  have hc : Commute t (S.inl b) := Subgroup.mem_center_iff.mp (hcentral ⟨b, rfl⟩) t
  exact ⟨t * S.inl b, by simp [ht], by rw [hc.mul_pow, ← map_pow, hb, ha, mul_inv_cancel]⟩

end GroupExtension
