/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Kernels on cyclic subgroups

A group homomorphism cuts out a cyclic subgroup of a given cyclic subgroup: the new
step is the original generator raised to the order of its image.
-/

public section

namespace Subgroup

/-- The powers of `g` in the kernel of `f` are the powers of `g ^ orderOf (f g)`.
The formula also covers an image of infinite order, when only the zeroth power survives. -/
theorem zpowers_inf_ker_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    zpowers g ⊓ f.ker = zpowers (g ^ orderOf (f g)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn, hf⟩ := mem_inf.mp hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hn
    rw [MonoidHom.mem_ker, map_zpow] at hf
    obtain ⟨k, rfl⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hf
    exact mem_zpowers_iff.mpr ⟨k, by rw [← zpow_natCast, ← zpow_mul]⟩
  · intro hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact mem_inf.mpr ⟨(zpowers g).zpow_mem (npow_mem_zpowers g _) _, by
      rw [MonoidHom.mem_ker, map_zpow, map_pow, pow_orderOf_eq_one, one_zpow]⟩

end Subgroup
