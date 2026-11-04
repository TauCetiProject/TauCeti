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

When a priority construction builds an indexed family of finite-stage enumerations
`A : κ → ℕ → Finset ℕ` — such as the two sets `A` and `B` of the Friedberg–Muchnik theorem, where
each requirement enumerates into one set and protects the other — a target map `target : ℕ → κ`
specifies which oracle sequence requirement `e` monitors. The unlabelled injury predicates of
`TauCeti.Computability.Priority.Injury.Basic` instantiate directly on `A (target e)`.

When combining events across requirements that monitor different oracles, retaining the oracle
label `target e` in `monitoredInjuryEvents A target r e : Set (κ × ℕ × ℕ)` keeps an entry of `x`
into `A k₁` distinct from an entry of the same number `x` into `A k₂` (`k₁ ≠ k₂`). In particular,
an injury event on one oracle label never belongs to `monitoredInjuryEvents` for a requirement
monitoring a different label, and replacing `target` by `target'` requires agreeing at `e`.

## Main definitions

* `TauCeti.Priority.monitoredInjuryEvents`: the labelled triples `(k, s, x)` recording that
  `k = target e` and `x ∈ injuriesAt (A (target e)) r e s`.

## Main results

* `TauCeti.Priority.monitoredInjuryEvents_eq_image`,
  `TauCeti.Priority.image_snd_monitoredInjuryEvents`,
  `TauCeti.Priority.image_number_monitoredInjuryEvents`,
  `TauCeti.Priority.image_stage_monitoredInjuryEvents`: exact projections between
  `monitoredInjuryEvents A target r e` and the unlabelled events, injuring numbers, and injury
  stages of `A (target e)`.
* `TauCeti.Priority.notMem_monitoredInjuryEvents_of_ne`,
  `TauCeti.Priority.disjoint_monitoredInjuryEvents_of_target_ne`: label separation and
  non-interchangeability of distinct monitored oracles.
* `TauCeti.Priority.preimage_mk_biUnion_monitoredInjuryEvents`,
  `TauCeti.Priority.biUnion_monitoredInjuryEvents_mono`,
  `TauCeti.Priority.finite_biUnion_monitoredInjuryEvents`: fibres, monotonicity, and finiteness on
  initial priority segments `e < N`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.2.
-/

public section

open Set

namespace TauCeti.Priority

variable {κ : Type*} (A : κ → ℕ → Finset ℕ) (target : ℕ → κ) (r : ℕ → ℕ → Option ℕ) (e : ℕ)

/-- The labelled injury events of requirement `e`: the triples `(k, s, x)` where `k = target e` is
the oracle label monitored by `e` and `(s, x) ∈ injuryEvents (A (target e)) r e`. -/
def monitoredInjuryEvents : Set (κ × ℕ × ℕ) :=
  {p | p.1 = target e ∧ p.2 ∈ injuryEvents (A (target e)) r e}

variable {A target r e}

/-- Membership in `monitoredInjuryEvents`. -/
@[simp]
theorem mem_monitoredInjuryEvents {p : κ × ℕ × ℕ} :
    p ∈ monitoredInjuryEvents A target r e ↔
      p.1 = target e ∧ p.2.2 ∈ injuriesAt (A (target e)) r e p.2.1 := by
  rw [monitoredInjuryEvents, mem_ofPred_eq, mem_injuryEvents]

/-- Explicit triple membership in `monitoredInjuryEvents`. -/
theorem mk_mem_monitoredInjuryEvents {k : κ} {s x : ℕ} :
    (k, s, x) ∈ monitoredInjuryEvents A target r e ↔
      k = target e ∧ x ∈ injuriesAt (A (target e)) r e s :=
  mem_monitoredInjuryEvents

/-- Every event in `monitoredInjuryEvents A target r e` carries the oracle label `target e`. -/
theorem fst_eq_of_mem_monitoredInjuryEvents {p : κ × ℕ × ℕ}
    (hp : p ∈ monitoredInjuryEvents A target r e) : p.1 = target e :=
  hp.1

/-- **Label separation.** An event recorded on an oracle `k ≠ target e` cannot satisfy
`monitoredInjuryEvents A target r e`, even if the same number enters `A k` below `r e s`. -/
theorem notMem_monitoredInjuryEvents_of_ne {k : κ} {s x : ℕ} (hk : k ≠ target e) :
    (k, s, x) ∉ monitoredInjuryEvents A target r e :=
  fun h => hk h.1

/-- Requirements monitoring distinct oracle labels have disjoint labelled injury-event sets. -/
theorem disjoint_monitoredInjuryEvents_of_target_ne {A' : κ → ℕ → Finset ℕ} {target' : ℕ → κ}
    {r' : ℕ → ℕ → Option ℕ} {d : ℕ} (h : target d ≠ target' e) :
    Disjoint (monitoredInjuryEvents A target r d) (monitoredInjuryEvents A' target' r' e) :=
  disjoint_left.mpr fun _ h₁ h₂ => h (h₁.1.symm.trans h₂.1)

/-- Changing the target map away from `e` leaves `monitoredInjuryEvents` at `e` unchanged. -/
theorem monitoredInjuryEvents_congr_target {target' : ℕ → κ} (h : target e = target' e) :
    monitoredInjuryEvents A target r e = monitoredInjuryEvents A target' r e := by
  ext ⟨k, s, x⟩
  simp [h]

/-- `monitoredInjuryEvents A target r e` is the `target e`-labelled image of
`injuryEvents (A (target e)) r e`. -/
theorem monitoredInjuryEvents_eq_image :
    monitoredInjuryEvents A target r e = Prod.mk (target e) '' injuryEvents (A (target e)) r e := by
  ext ⟨k, s, x⟩
  simp [eq_comm, and_comm]

/-- Projecting away the oracle label recovers `injuryEvents (A (target e)) r e`. -/
@[simp]
theorem image_snd_monitoredInjuryEvents :
    Prod.snd '' monitoredInjuryEvents A target r e = injuryEvents (A (target e)) r e := by
  rw [monitoredInjuryEvents_eq_image, image_image]
  simp

/-- Projecting `monitoredInjuryEvents` to the injuring number recovers `injurySet` on the monitored
oracle. -/
theorem image_number_monitoredInjuryEvents :
    (fun p : κ × ℕ × ℕ => p.2.2) '' monitoredInjuryEvents A target r e =
      injurySet (A (target e)) r e := by
  rw [injurySet_eq_image, ← image_snd_monitoredInjuryEvents, image_image]

/-- Projecting `monitoredInjuryEvents` to the transition stage `s + 1` recovers `injuryStages` on
the monitored oracle. -/
theorem image_stage_monitoredInjuryEvents :
    (fun p : κ × ℕ × ℕ => p.2.1 + 1) '' monitoredInjuryEvents A target r e =
      injuryStages (A (target e)) r e := by
  rw [injuryStages_eq_image, ← image_snd_monitoredInjuryEvents, image_image]

/-- The fibre of `monitoredInjuryEvents A target r e` over `target e` is
`injuryEvents (A (target e)) r e`. -/
@[simp]
theorem preimage_mk_monitoredInjuryEvents_self :
    Prod.mk (target e) ⁻¹' monitoredInjuryEvents A target r e =
      injuryEvents (A (target e)) r e := by
  ext ⟨s, x⟩
  simp

/-- The fibre of `monitoredInjuryEvents A target r e` over any other label `k ≠ target e` is
empty. -/
theorem preimage_mk_monitoredInjuryEvents_of_ne {k : κ} (hk : k ≠ target e) :
    Prod.mk k ⁻¹' monitoredInjuryEvents A target r e = ∅ := by
  ext ⟨s, x⟩
  simp [hk]

/-! ### Initial priority segments -/

/-- Monotonicity of combined labelled injury events in the priority cutoff `N`. -/
theorem biUnion_monitoredInjuryEvents_mono {M N : ℕ} (hMN : M ≤ N) :
    (⋃ e < M, monitoredInjuryEvents A target r e) ⊆
      ⋃ e < N, monitoredInjuryEvents A target r e := by
  intro p hp
  simp only [mem_iUnion] at hp ⊢
  obtain ⟨e, he, hp⟩ := hp
  exact ⟨e, lt_of_lt_of_le he hMN, hp⟩

/-- Restricting the combined events of priorities `e < N` to a single oracle label `k` retains
precisely the injury events of those `e < N` that monitor `k`. -/
theorem preimage_mk_biUnion_monitoredInjuryEvents (k : κ) (N : ℕ) :
    Prod.mk k ⁻¹' (⋃ e < N, monitoredInjuryEvents A target r e) =
      ⋃ (e < N) (_ : target e = k), injuryEvents (A k) r e := by
  ext ⟨s, x⟩
  simp only [mem_preimage, mem_iUnion, mk_mem_monitoredInjuryEvents, mem_injuryEvents]
  constructor
  · rintro ⟨e, heN, rfl, hx⟩
    exact ⟨e, heN, rfl, hx⟩
  · rintro ⟨e, heN, rfl, hx⟩
    exact ⟨e, heN, rfl, hx⟩

/-- Finiteness of `monitoredInjuryEvents` at `e` is equivalent to finiteness of `injuryStages` on
the monitored sequence `A (target e)`. -/
theorem finite_monitoredInjuryEvents_iff_finite_injuryStages :
    (monitoredInjuryEvents A target r e).Finite ↔ (injuryStages (A (target e)) r e).Finite := by
  constructor
  · intro h
    rw [← image_stage_monitoredInjuryEvents]
    exact h.image _
  · intro h
    rw [monitoredInjuryEvents_eq_image]
    refine Finite.image _ ?_
    refine ((h.image Nat.pred).biUnion fun s _ =>
      (finite_singleton s).prod (injuriesAt (A (target e)) r e s).finite_toSet).subset ?_
    rintro ⟨s, x⟩ hx
    have hx' := mem_injuryEvents.mp hx
    exact mem_biUnion ⟨s + 1, succ_mem_injuryStages.mpr ⟨x, hx'⟩, rfl⟩ ⟨rfl, hx'⟩

/-- On an initial priority segment `e < N`, the combined labelled injury events are finite whenever
each requirement `e < N` has finitely many injury stages on its monitored oracle. -/
theorem finite_biUnion_monitoredInjuryEvents {N : ℕ}
    (h : ∀ e < N, (injuryStages (A (target e)) r e).Finite) :
    (⋃ e < N, monitoredInjuryEvents A target r e).Finite :=
  (finite_Iio N).biUnion fun e he =>
    finite_monitoredInjuryEvents_iff_finite_injuryStages.mpr (h e he)

end TauCeti.Priority
