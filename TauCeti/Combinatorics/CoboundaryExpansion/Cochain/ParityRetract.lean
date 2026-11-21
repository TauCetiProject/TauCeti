/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Invariance
public import TauCeti.GroupTheory.Perm.ParityRetract
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Parity retraction for transposition-subgroup cochains

Embedding a `Subgroup.zpowers t`-valued `1`-cochain on any finite two-complex `X` into
`Equiv.Perm α` does not change its moved-point gauge distance
(`TauCeti.Cochain.gaugeDist_map_zpowers_subtype`), because `Equiv.Perm.parityRetract` gives a
norm-nonincreasing retraction back onto `Subgroup.zpowers t`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, doi:10.5281/zenodo.23245792, Corollary 7.
-/

public section

namespace TauCeti

namespace Cochain

/-- **Parity-retraction subgroup gauge equality**: for any `Subgroup.zpowers t`-valued `1`-cochain
`γ` on a two-complex `X`, embedding `γ` into `Equiv.Perm α` does not change its moved-point gauge
distance (Beasley, Corollary 7). -/
theorem gaugeDist_map_zpowers_subtype {V α : Type*} [Fintype V] [LinearOrder V]
    [Fintype α] [DecidableEq α] {X : TwoComplex V} {t : Equiv.Perm α} (ht : t.IsSwap)
    (γ : Cochain X (Subgroup.zpowers t)) :
    (γ.map (Subgroup.zpowers t).subtype).gaugeDist (Equiv.Perm.movedNorm α) =
      γ.gaugeDist ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) := by
  let ρ : Equiv.Perm α →* Subgroup.zpowers t :=
    (Equiv.Perm.parityRetract ht).codRestrict (Subgroup.zpowers t) fun σ ↦ by
      rw [Equiv.Perm.parityRetract_apply]
      split_ifs
      · exact one_mem _
      · exact Subgroup.mem_zpowers t
  have hρ_id : ρ.comp (Subgroup.zpowers t).subtype = MonoidHom.id (Subgroup.zpowers t) := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (sq t ▸ ht.mul_self)).mp x.property with
      hx | hx <;>
      simp [ρ, hx]
  have hmap : (γ.map (Subgroup.zpowers t).subtype).map ρ = γ := by
    rw [map_map, hρ_id, map_id]
  have hle := (γ.map (Subgroup.zpowers t).subtype).gaugeDist_map_le
    (ℓ_G := Equiv.Perm.movedNorm α)
    (ℓ_H := (Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective)
    (φ := ρ)
    fun g ↦ by
      rw [GroupNorm.comp_apply, Subgroup.coe_subtype]
      exact Equiv.Perm.movedNorm_parityRetract_le ht g
  rw [hmap] at hle
  exact le_antisymm (γ.gaugeDist_map_subtype_le (Equiv.Perm.movedNorm α) (Subgroup.zpowers t)) hle

end Cochain

end TauCeti
