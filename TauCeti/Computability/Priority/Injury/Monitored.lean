/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Injury.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Labelled injury events for multi-oracle priority constructions

For an indexed family of finite-stage enumerations `A : κ → ℕ → Finset ℕ` and a target map
`target : ℕ → κ` assigning the oracle monitored by requirement `e`, `monitoredInjuryEvents A target
r e : Set (κ × ℕ × ℕ)` pairs `target e` with `injuryEvents (A (target e)) r e`. Retaining the label
`target e` separates injuries across distinct oracles when combining events across priorities.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.2.
-/

public section

open Set

namespace TauCeti.Priority

variable {κ : Type*} (A : κ → ℕ → Finset ℕ) (target : ℕ → κ) (r : ℕ → ℕ → Option ℕ) (e : ℕ)

/-- The labelled injury events `(k, s, x)` of requirement `e`, with `k = target e` and
`(s, x) ∈ injuryEvents (A (target e)) r e`. -/
def monitoredInjuryEvents : Set (κ × ℕ × ℕ) :=
  {p | p.1 = target e ∧ p.2 ∈ injuryEvents (A (target e)) r e}

variable {A target r e}

/-- Membership in `monitoredInjuryEvents`. -/
@[simp] theorem mem_monitoredInjuryEvents {p : κ × ℕ × ℕ} :
    p ∈ monitoredInjuryEvents A target r e ↔
      p.1 = target e ∧ p.2.2 ∈ injuriesAt (A (target e)) r e p.2.1 := by
  rw [monitoredInjuryEvents, mem_ofPred_eq, mem_injuryEvents]

/-- Explicit triple membership in `monitoredInjuryEvents`. -/
theorem mk_mem_monitoredInjuryEvents {k : κ} {s x : ℕ} :
    (k, s, x) ∈ monitoredInjuryEvents A target r e ↔
      k = target e ∧ x ∈ injuriesAt (A (target e)) r e s := mem_monitoredInjuryEvents

/-- **Label separation.** An event on `k ≠ target e` never belongs to `monitoredInjuryEvents`. -/
theorem notMem_monitoredInjuryEvents_of_ne {k : κ} {s x : ℕ} (hk : k ≠ target e) :
    (k, s, x) ∉ monitoredInjuryEvents A target r e := fun h => hk h.1

/-- Requirements monitoring distinct oracle labels have disjoint labelled injury-event sets. -/
theorem disjoint_monitoredInjuryEvents_of_target_ne {A' : κ → ℕ → Finset ℕ} {target' : ℕ → κ}
    {r' : ℕ → ℕ → Option ℕ} {d : ℕ} (h : target d ≠ target' e) :
    Disjoint (monitoredInjuryEvents A target r d) (monitoredInjuryEvents A' target' r' e) :=
  disjoint_left.mpr fun _ h₁ h₂ => h (h₁.1.symm.trans h₂.1)

/-- Changing the target map away from `e` leaves `monitoredInjuryEvents` at `e` unchanged. -/
theorem monitoredInjuryEvents_congr_target {target' : ℕ → κ} (h : target e = target' e) :
    monitoredInjuryEvents A target r e = monitoredInjuryEvents A target' r e := by
  ext ⟨k, s, x⟩; simp [h]

/-- `monitoredInjuryEvents A target r e` is the `target e`-labelled image of `injuryEvents`. -/
theorem monitoredInjuryEvents_eq_image :
    monitoredInjuryEvents A target r e = Prod.mk (target e) '' injuryEvents (A (target e)) r e := by
  ext ⟨k, s, x⟩; simp [eq_comm, and_comm]

/-- Projecting away the oracle label recovers `injuryEvents (A (target e)) r e`. -/
@[simp] theorem image_snd_monitoredInjuryEvents :
    Prod.snd '' monitoredInjuryEvents A target r e = injuryEvents (A (target e)) r e := by
  rw [monitoredInjuryEvents_eq_image, image_image]; simp

/-- Projecting `monitoredInjuryEvents` to the injuring number recovers `injurySet`. -/
theorem image_number_monitoredInjuryEvents :
    (fun p : κ × ℕ × ℕ => p.2.2) '' monitoredInjuryEvents A target r e =
      injurySet (A (target e)) r e := by
  rw [injurySet_eq_image, ← image_snd_monitoredInjuryEvents, image_image]

/-- Projecting `monitoredInjuryEvents` to the transition stage `s + 1` recovers `injuryStages`. -/
theorem image_stage_monitoredInjuryEvents :
    (fun p : κ × ℕ × ℕ => p.2.1 + 1) '' monitoredInjuryEvents A target r e =
      injuryStages (A (target e)) r e := by
  rw [injuryStages_eq_image, ← image_snd_monitoredInjuryEvents, image_image]

/-- The fibre of `monitoredInjuryEvents` over `target e` is `injuryEvents (A (target e)) r e`. -/
@[simp] theorem preimage_mk_monitoredInjuryEvents_self :
    Prod.mk (target e) ⁻¹' monitoredInjuryEvents A target r e =
      injuryEvents (A (target e)) r e := by ext ⟨s, x⟩; simp

/-- The fibre of `monitoredInjuryEvents` over any label `k ≠ target e` is empty. -/
theorem preimage_mk_monitoredInjuryEvents_of_ne {k : κ} (hk : k ≠ target e) :
    Prod.mk k ⁻¹' monitoredInjuryEvents A target r e = ∅ := by ext ⟨s, x⟩; simp [hk]

/-- Restricting combined events of `e < N` to label `k` retains those `e < N` monitoring `k`. -/
theorem preimage_mk_biUnion_monitoredInjuryEvents (k : κ) (N : ℕ) :
    Prod.mk k ⁻¹' (⋃ e < N, monitoredInjuryEvents A target r e) =
      ⋃ (e < N) (_ : target e = k), injuryEvents (A k) r e := by
  ext ⟨s, x⟩
  simp only [mem_preimage, mem_iUnion, mk_mem_monitoredInjuryEvents, mem_injuryEvents]
  exact ⟨fun ⟨e, heN, hke, hx⟩ => ⟨e, heN, hke.symm, hke ▸ hx⟩,
    fun ⟨e, heN, hke, hx⟩ => ⟨e, heN, hke.symm, hke.symm ▸ hx⟩⟩

/-- Finiteness of `monitoredInjuryEvents` at `e` is equivalent to finiteness of `injuryStages`. -/
theorem finite_monitoredInjuryEvents_iff_finite_injuryStages :
    (monitoredInjuryEvents A target r e).Finite ↔ (injuryStages (A (target e)) r e).Finite := by
  refine ⟨fun h => image_stage_monitoredInjuryEvents ▸ h.image _, fun h => ?_⟩
  rw [monitoredInjuryEvents_eq_image]
  refine Finite.image _ (((h.image Nat.pred).biUnion fun s _ =>
    (finite_singleton s).prod (injuriesAt (A (target e)) r e s).finite_toSet).subset ?_)
  rintro ⟨s, x⟩ hx
  exact mem_biUnion ⟨s + 1, succ_mem_injuryStages.mpr ⟨x, mem_injuryEvents.mp hx⟩, rfl⟩
    ⟨rfl, mem_injuryEvents.mp hx⟩

/-- Combined labelled injury events on `e < N` are finite when each `e < N` has finite
`injuryStages`. -/
theorem finite_biUnion_monitoredInjuryEvents {N : ℕ}
    (h : ∀ e < N, (injuryStages (A (target e)) r e).Finite) :
    (⋃ e < N, monitoredInjuryEvents A target r e).Finite :=
  (finite_Iio N).biUnion fun e he =>
    finite_monitoredInjuryEvents_iff_finite_injuryStages.mpr (h e he)

end TauCeti.Priority
