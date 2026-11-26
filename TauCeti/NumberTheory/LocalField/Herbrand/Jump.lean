/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# Jumps of the ramification filtrations

An upper jump is an index at which the upper ramification group is strictly larger than at every
later index, including the possible jump at `-1` from the full Galois group to inertia. The
Herbrand order isomorphism carries the lower jumps exactly to the upper jumps. The lower-jump
definition and its integer criterion are in `RamificationGroup`.

In prime degree, an upper break at a natural number `t` implies that the lower ramification
group `G_t` is the full Galois group and that `G_{t+1}` is trivial. The natural inverse Herbrand
function fixes every depth up to `t`.

These statements identify the breaks used by the norm filtration and Hasse–Arf theory; all proofs
specialize the local-ring results of `TauCeti.RingTheory.LocalRing.Herbrand` to `Gal(L/K)` acting
on `𝒪[L]`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

open ValuativeRel

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

/-- The local-field upper breaks are the upper breaks of `Gal(L/K)` acting on `𝒪[L]`. -/
theorem upperJump_iff_isLocalRing_upperJump (u : RamificationIndexDomain) :
    UpperJump K L u ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [upperJump_iff, TauCeti.IsLocalRing.upperJump_iff]
  refine ⟨fun h v huv ↦ ?_, fun h v huv ↦ ?_⟩
  · have hv := h ⟨v, u.property.trans huv.le⟩ huv
    rwa [upperRamificationGroup_eq_isLocalRing_upperRamificationGroup,
      upperRamificationGroup_eq_isLocalRing_upperRamificationGroup, Subtype.coe_mk] at hv
  · simpa only [upperRamificationGroup_eq_isLocalRing_upperRamificationGroup] using h v huv

/-- An upper break requires a nontrivial Galois group. -/
theorem UpperJump.nontrivial {u : RamificationIndexDomain} (hu : UpperJump K L u) :
    Nontrivial (L ≃ₐ[K] L) :=
  ((upperJump_iff_isLocalRing_upperJump K L u).1 hu).nontrivial

/-- The Herbrand function takes lower breaks precisely to upper breaks. -/
@[simp]
theorem upperJump_herbrand_iff (u : RamificationIndexDomain) :
    UpperJump K L (herbrand K L u) ↔ LowerJump K L u := by
  rw [upperJump_iff_isLocalRing_upperJump, lowerJump_iff_isLocalRing_lowerJump,
    coe_herbrand_eq_herbrandFun, TauCeti.IsLocalRing.upperJump_herbrandFun_iff]

/-- The inverse Herbrand function takes upper breaks precisely to lower breaks. -/
@[simp]
theorem lowerJump_inverseHerbrand_iff (u : RamificationIndexDomain) :
    LowerJump K L (inverseHerbrand K L u) ↔ UpperJump K L u := by
  rw [lowerJump_iff_isLocalRing_lowerJump, upperJump_iff_isLocalRing_upperJump,
    coe_inverseHerbrand_eq_inverseHerbrandFun, TauCeti.IsLocalRing.lowerJump_inverseHerbrandFun_iff]

/-- In prime degree, an upper break at a natural number `t` has `G_t = Gal(L/K)`: the group
`G^t = G_{ψ(t)}` strictly contains every later upper group, so it is nontrivial, hence the whole
Galois group, and `t ≤ ψ(t)`. -/
theorem lowerRamificationGroup_natCast_eq_top_of_upperJump (hℓ : (Module.finrank K L).Prime)
    {t : ℕ} (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    lowerRamificationGroup K L t = ⊤ := by
  rw [lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.ramificationGroup_natCast_eq_top_of_upperJump (L ≃ₐ[K] L) 𝒪[L]
    (IsGalois.card_aut_eq_finrank K L ▸ hℓ)
    ((upperJump_iff_isLocalRing_upperJump K L _).1 ht)

/-- In prime degree, the natural inverse Herbrand function fixes every depth at or below a
natural upper break. -/
theorem psiNat_eq_self_of_le_break (hℓ : (Module.finrank K L).Prime)
    {v t : ℕ} (hvt : v ≤ t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    psiNat K L v = v := by
  rw [psiNat_eq_isLocalRing_psiNat]
  exact TauCeti.IsLocalRing.psiNat_eq_self_of_le_upperJump (L ≃ₐ[K] L) 𝒪[L]
    (IsGalois.card_aut_eq_finrank K L ▸ hℓ) hvt
    ((upperJump_iff_isLocalRing_upperJump K L _).1 ht)

/-- In prime degree, an upper break at a natural number `t` has `G_{t+1} = 1`. Together with
`G_t = Gal(L/K)` (`lowerRamificationGroup_natCast_eq_top_of_upperJump`), this says that the lower
filtration drops from the whole Galois group to the trivial group exactly between `t` and `t + 1`.
-/
theorem lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump
    (hℓ : (Module.finrank K L).Prime) {t : ℕ}
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    lowerRamificationGroup K L (t + 1) = ⊥ := by
  rw [lowerRamificationGroup_def]
  exact TauCeti.IsLocalRing.ramificationGroup_natCast_add_one_eq_bot_of_upperJump (L ≃ₐ[K] L) 𝒪[L]
    (IsGalois.card_aut_eq_finrank K L ▸ hℓ)
    ((upperJump_iff_isLocalRing_upperJump K L _).1 ht)

end TauCeti.LocalFieldsRamification
