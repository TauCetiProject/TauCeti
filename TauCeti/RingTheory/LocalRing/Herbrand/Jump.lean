/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Herbrand.Basic

/-!
# Upper ramification jumps of a group acting on a local ring

This module extends `TauCeti.RingTheory.LocalRing.Herbrand.Basic` with
`TauCeti.IsLocalRing.UpperJump` for a group acting on a local ring, its correspondence with
`LowerJump` under the Herbrand functions, and transport along bijective action-compatible or
filtration-preserving homomorphisms.

Adapts `NumberTheory/LocalField/Herbrand/Jump.lean`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1, 3.
-/

public section
noncomputable section
namespace TauCeti.IsLocalRing

section Defs
variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- An **upper break** of the ramification filtration of a finite group `G`: `G^v < G^u` for every
`v > u`. -/
def UpperJump (u : ℝ) : Prop :=
  ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u

theorem upperJump_iff (u : ℝ) : UpperJump G S u ↔
    ∀ v : ℝ, u < v → upperRamificationGroup G S v < upperRamificationGroup G S u := Iff.rfl

end Defs

section Finite
variable (G : Type*) [Group G] [Finite G] (S : Type*) [CommRing S] [IsLocalRing S]
  [MulSemiringAction G S]

/-- `herbrandFun G S u` is an upper break if and only if `u` is a lower break. -/
@[simp] theorem upperJump_herbrandFun_iff (u : ℝ) :
    UpperJump G S (herbrandFun G S u) ↔ LowerJump G S u := by
  rw [upperJump_iff, lowerJump_iff]
  refine ⟨fun h v huv ↦ ?_, fun h _ huv ↦ ?_⟩
  · simpa using h (herbrandFun G S v) (herbrandFun_strictMono G S huv)
  · rw [upperRamificationGroup_herbrandFun, upperRamificationGroup_def]
    exact h _ (lt_inverseHerbrandFun_iff.2 huv)

/-- `inverseHerbrandFun G S v` is a lower break if and only if `v` is an upper break. -/
@[simp] theorem lowerJump_inverseHerbrandFun_iff (v : ℝ) :
    LowerJump G S (inverseHerbrandFun G S v) ↔ UpperJump G S v := by
  simpa using (upperJump_herbrandFun_iff G S (inverseHerbrandFun G S v)).symm

variable {G S} in
/-- Every upper break of a finite group action is at least `-1`. -/
theorem UpperJump.neg_one_le {v : ℝ} (hv : UpperJump G S v) : -1 ≤ v :=
  neg_one_le_inverseHerbrandFun_iff.1
    ((lowerJump_inverseHerbrandFun_iff G S v).2 hv).neg_one_le

end Finite

section Transport
section Actions
variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  {H : Type*} [Group H]

section Comap
variable {T : Type*} [CommRing T] [IsLocalRing T] [MulSemiringAction H T] {φ : G →* H}
  (hφ : Function.Bijective φ)
  (he : ∀ i : ℤ, ramificationGroup G S i = (ramificationGroup H T i).comap φ)
include hφ he

/-- A bijective `φ : G →* H` pulling back lower groups preserves `UpperJump`. -/
theorem upperJump_iff_of_ramificationGroup_eq_comap (u : ℝ) :
    UpperJump G S u ↔ UpperJump H T u := by
  simp_rw [upperJump_iff, upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap hφ he,
    Subgroup.comap_lt_comap_of_surjective hφ.2]

end Comap

section SMul
variable {φ : G →* H} (hφ : Function.Bijective φ) [MulSemiringAction H S]
  (he : ∀ (g : G) (x : S), g • x = φ g • x)
include hφ he

/-- Two groups linked by a bijective action-compatible homomorphism share `UpperJump`. -/
theorem upperJump_iff_of_smul_eq (u : ℝ) :
    UpperJump G S u ↔ UpperJump H S u :=
  upperJump_iff_of_ramificationGroup_eq_comap hφ (ramificationGroup_eq_comap_of_smul_eq he) u

end SMul
end Actions
end Transport

end TauCeti.IsLocalRing
