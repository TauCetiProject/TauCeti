/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Jumps of the ramification filtrations

An upper jump is an index at which the upper ramification group is strictly larger than at every
later index, including the possible jump at `-1` from the full Galois group to inertia. The
Herbrand order isomorphism carries the lower jumps exactly to the upper jumps. The lower-jump
definition and its integer criterion are in `RamificationGroup`.

In prime degree, an upper break at a natural number `t` implies that the lower ramification
group `G_t` is the full Galois group and that `G_{t+1}` is trivial. The natural inverse Herbrand
function fixes every depth up to `t`.

These statements identify the breaks used by the norm filtration and Hasse–Arf theory.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- An upper break: the upper ramification group at `u` is strictly larger than the group at
every later index. -/
def UpperJump (u : RamificationIndexDomain) : Prop :=
  ∀ v : RamificationIndexDomain, u < v →
    upperRamificationGroup K L v < upperRamificationGroup K L u

/-- An upper break is a strict drop of the upper ramification group at every later index. -/
theorem upperJump_iff (u : RamificationIndexDomain) :
    UpperJump K L u ↔ ∀ v : RamificationIndexDomain, u < v →
      upperRamificationGroup K L v < upperRamificationGroup K L u := Iff.rfl

/-- The Herbrand function takes lower breaks precisely to upper breaks. -/
@[simp]
theorem upperJump_herbrand_iff (u : RamificationIndexDomain) :
    UpperJump K L (herbrand K L u) ↔ LowerJump K L u := by
  constructor
  · intro h
    apply (lowerJump_iff K L u).mpr
    intro v huv
    have h' := (upperJump_iff K L _).mp h (herbrand K L v)
      ((herbrand_strictMono K L) huv)
    simpa only [upperRamificationGroup_herbrand] using h'
  · intro h
    apply (upperJump_iff K L _).mpr
    intro v huv
    have h' : u < inverseHerbrand K L v := by
      have hv := (inverseHerbrand_strictMono K L) huv
      rwa [inverseHerbrand_herbrand] at hv
    simpa only [upperRamificationGroup_def, inverseHerbrand_herbrand] using
      (lowerJump_iff K L u).mp h (inverseHerbrand K L v) h'

/-- The inverse Herbrand function takes upper breaks precisely to lower breaks. -/
@[simp]
theorem lowerJump_inverseHerbrand_iff (u : RamificationIndexDomain) :
    LowerJump K L (inverseHerbrand K L u) ↔ UpperJump K L u := by
  simpa only [herbrand_inverseHerbrand] using
    (upperJump_herbrand_iff K L (inverseHerbrand K L u)).symm

/-- In prime degree, an upper break at a natural number `t` has `G_t = Gal(L/K)`: the group
`G^t = G_{ψ(t)}` strictly contains every later upper group, so it is nontrivial, hence the whole
Galois group, and `t ≤ ψ(t)`. -/
theorem lowerRamificationGroup_natCast_eq_top_of_upperJump (hℓ : (Module.finrank K L).Prime)
    {t : ℕ} (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    lowerRamificationGroup K L t = ⊤ := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime := ⟨IsGalois.card_aut_eq_finrank K L ▸ hℓ⟩
  have hlt := (upperJump_iff K L _).1 ht ⟨(t + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (t + 1)⟩
    (Subtype.mk_lt_mk.2 (by push_cast; linarith))
  have hne := (bot_le.trans_lt hlt).ne'
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast,
    lowerRamificationGroupReal_intCast] at hne
  have hψ : lowerRamificationGroup K L (psiNat K L t) = ⊤ :=
    ((lowerRamificationGroup K L _).eq_bot_or_eq_top_of_prime_card).resolve_left hne
  have htψ : (t : ℤ) ≤ psiNat K L t := by exact_mod_cast self_le_psiNat K L t
  exact top_le_iff.1 <| hψ ▸ lowerRamificationGroup_antitone K L htψ

/-- In prime degree, the natural inverse Herbrand function fixes every depth at or below a
natural upper break. -/
theorem psiNat_eq_self_of_le_break (hℓ : (Module.finrank K L).Prime)
    {v t : ℕ} (hvt : v ≤ t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    psiNat K L v = v := by
  have hGi (i : ℕ) (hi : i ≤ t) : lowerRamificationGroup K L i = ⊤ :=
    top_le_iff.1 <| lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht ▸
      lowerRamificationGroup_antitone K L (by exact_mod_cast hi)
  exact (psiNat_eq_self_iff K L).2 (by rw [hGi v hvt, ← Nat.cast_zero, hGi 0 (Nat.zero_le t)])

/-- In prime degree, an upper break at a natural number `t` has `G_{t+1} = 1`. Together with
`G_t = Gal(L/K)` (`lowerRamificationGroup_natCast_eq_top_of_upperJump`), this says that the lower
filtration drops from the whole Galois group to the trivial group exactly between `t` and `t + 1`.
-/
theorem lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump
    (hℓ : (Module.finrank K L).Prime) {t : ℕ}
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    lowerRamificationGroup K L (t + 1) = ⊥ := by
  have : Fact (Nat.card (L ≃ₐ[K] L)).Prime := ⟨IsGalois.card_aut_eq_finrank K L ▸ hℓ⟩
  refine ((lowerRamificationGroup K L _).eq_bot_or_eq_top_of_prime_card).resolve_right
    fun htop ↦ ?_
  have hlt := (upperJump_iff K L _).1 ht ⟨(t + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (t + 1)⟩
    (Subtype.mk_lt_mk.2 (by push_cast; linarith))
  have hne := (hlt.trans_le le_top).ne
  have hG0 : lowerRamificationGroup K L 0 = ⊤ :=
    top_le_iff.1 (htop ▸ lowerRamificationGroup_antitone K L (by positivity))
  have hψ : psiNat K L (t + 1) = t + 1 :=
    (psiNat_eq_self_iff K L).2 (by push_cast; rw [htop, hG0])
  rw [upperRamificationGroup_def, ← coe_psiNat, ← Int.cast_natCast,
    lowerRamificationGroupReal_intCast, hψ] at hne
  push_cast at hne
  exact hne htop

end TauCeti.LocalFieldsRamification
