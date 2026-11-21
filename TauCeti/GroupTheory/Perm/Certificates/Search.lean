/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.GroupTheory.Perm.Certificates.Encoding.Basic
public import TauCeti.Probability.FiniteSeed.Amplification

/-!
# A bounded search for verified certificates

The runner stops at the first successful check. Soundness is unconditional;
the probability bound separately assumes a lower bound on the fraction of
seeds producing accepted certificates. `calls` counts the attempts actually
made, including the successful one.
-/

@[expose] public section

namespace TauCeti.BoundedRunner

variable {S V : Type*}

/-- Return the first successful attempt in a finite list of seeds. -/
def firstSuccess (attempt : S → Option V) : List S → Option V
  | [] => none
  | seed :: rest =>
      match attempt seed with
      | some value => some value
      | none => firstSuccess attempt rest

/-- Count the attempted seeds, stopping at the first success. -/
def calls (attempt : S → Option V) : List S → ℕ
  | [] => 0
  | seed :: rest =>
      match attempt seed with
      | some _ => 1
      | none => 1 + calls attempt rest

theorem firstSuccess_eq_none_iff (attempt : S → Option V) (seeds : List S) :
    firstSuccess attempt seeds = none ↔ ∀ seed ∈ seeds, attempt seed = none := by
  induction seeds with
  | nil => simp [firstSuccess]
  | cons seed rest ih =>
      cases h : attempt seed <;> simp [firstSuccess, h, ih]

theorem firstSuccess_eq_some_mem (attempt : S → Option V) (seeds : List S)
    (value : V) (h : firstSuccess attempt seeds = some value) :
    ∃ seed ∈ seeds, attempt seed = some value := by
  induction seeds with
  | nil => simp [firstSuccess] at h
  | cons seed rest ih =>
      cases hs : attempt seed with
      | none =>
          obtain ⟨s, hm, hv⟩ := ih (by simpa [firstSuccess, hs] using h)
          exact ⟨s, List.mem_cons_of_mem _ hm, hv⟩
      | some v =>
          have hv : v = value := by simpa [firstSuccess, hs] using h
          exact ⟨seed, List.mem_cons_self, hv ▸ hs⟩

theorem firstSuccess_sound (attempt : S → Option V) (sound : V → Prop)
    (hcheck : ∀ seed value, attempt seed = some value → sound value)
    (seeds : List S) (value : V) (h : firstSuccess attempt seeds = some value) :
    sound value := by
  obtain ⟨seed, _, hs⟩ := firstSuccess_eq_some_mem attempt seeds value h
  exact hcheck seed value hs

theorem calls_le_length (attempt : S → Option V) (seeds : List S) :
    calls attempt seeds ≤ seeds.length := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      cases h : attempt seed with
      | none =>
          simpa [calls, h, Nat.add_comm] using Nat.add_le_add_left ih 1
      | some _ => simp [calls, h]

/-- Search a fixed number of trials in increasing seed-index order. -/
def run {trials : ℕ} (attempt : S → Option V) (seeds : Fin trials → S) : Option V :=
  firstSuccess attempt (List.ofFn seeds)

theorem run_eq_none_iff {trials : ℕ} (attempt : S → Option V)
    (seeds : Fin trials → S) :
    run attempt seeds = none ↔ ∀ i, attempt (seeds i) = none := by
  simp [run, firstSuccess_eq_none_iff, List.mem_ofFn]

theorem run_sound {trials : ℕ} (attempt : S → Option V) (sound : V → Prop)
    (hcheck : ∀ seed value, attempt seed = some value → sound value)
    (seeds : Fin trials → S) (value : V) (h : run attempt seeds = some value) :
    sound value :=
  firstSuccess_sound attempt sound hcheck _ _ h

theorem run_calls_le {trials : ℕ} (attempt : S → Option V) (seeds : Fin trials → S) :
    calls attempt (List.ofFn seeds) ≤ trials := by
  simpa using calls_le_length attempt (List.ofFn seeds)

theorem run_zero (attempt : S → Option V) (seeds : Fin 0 → S) :
    run attempt seeds = none := by
  simp [run, firstSuccess]

theorem run_isSome_of_all_success {trials : ℕ} (attempt : S → Option V)
    (seeds : Fin trials → S) (htrials : 0 < trials)
    (hsuccess : ∀ seed, (attempt seed).isSome = true) :
    (run attempt seeds).isSome = true := by
  cases hrun : run attempt seeds with
  | none =>
      have hfailure := (run_eq_none_iff attempt seeds).mp hrun
      have h := hsuccess (seeds ⟨0, htrials⟩)
      rw [hfailure] at h
      cases h
  | some value => rfl

theorem run_unknown_probability [Fintype S] [Nonempty S]
    (attempt : S → Option V) (trials : ℕ) :
    FiniteSeeds.uniformProbability (Fin trials → S)
      (fun seeds => run attempt seeds = none) =
      (1 - FiniteSeeds.uniformProbability S (fun seed => (attempt seed).isSome = true)) ^
        trials := by
  have hevent :
      (fun seeds : Fin trials → S => run attempt seeds = none) =
        (fun seeds => ∀ i, ¬(attempt (seeds i)).isSome = true) := by
    funext seeds
    simp [run_eq_none_iff, Option.isSome_eq_false_iff]
  rw [hevent]
  exact FiniteSeeds.uniformProbability_all_fail S
    (fun seed => (attempt seed).isSome = true) trials

theorem run_unknown_le_half_pow [Fintype S] [Nonempty S]
    (attempt : S → Option V) (R k : ℕ) (hR : 0 < R)
    (haccepts : 1 / (R : ℝ) ≤
      FiniteSeeds.uniformProbability S (fun seed => (attempt seed).isSome = true)) :
    FiniteSeeds.uniformProbability (Fin (k * R) → S)
      (fun seeds => run attempt seeds = none) ≤ (1 / 2 : ℝ) ^ k := by
  rw [run_unknown_probability]
  exact TauCeti.failure_pow_mul_le_half_pow
    (FiniteSeeds.uniformProbability_le_one S _) R k hR haccepts

/-- Abstract execution cost: initialization, each actual trial, and finalization. -/
def executionBudget {trials : ℕ} (attempt : S → Option V) (seeds : Fin trials → S)
    (initial trial final : ℕ) : ℕ :=
  initial + calls attempt (List.ofFn seeds) * trial + final

theorem executionBudget_le {trials : ℕ} (attempt : S → Option V)
    (seeds : Fin trials → S) (initial trial final : ℕ) :
    executionBudget attempt seeds initial trial final ≤ initial + trials * trial + final := by
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_right trial (run_calls_le attempt seeds)) initial) final

/-- Concatenate fixed-length seed vectors in increasing trial-index order. -/
def seedBits {B trials : ℕ} (seeds : Fin trials → (Fin B → Bool)) : List Bool :=
  BinaryCodec.writeVector (fun seed => List.ofFn seed) seeds

theorem seedBits_length {B trials : ℕ} (seeds : Fin trials → (Fin B → Bool)) :
    (seedBits seeds).length = trials * B := by
  induction trials with
  | zero => simp [seedBits, BinaryCodec.writeVector]
  | succ trials ih =>
      change (List.ofFn (seeds 0) ++
        BinaryCodec.writeVector (fun seed => List.ofFn seed) (Fin.tail seeds)).length =
          (trials + 1) * B
      rw [List.length_append, List.length_ofFn]
      change B + (seedBits (Fin.tail seeds)).length = _
      rw [ih, Nat.succ_mul, Nat.add_comm]

open Equiv CertifiedPermutation CertificateWire

/-- Generate and verify certificates for the supplied permutation generators. -/
def search {degree trials : ℕ} (gs : List (Perm (Fin degree)))
    (candidate : S → List Bool) (seeds : Fin trials → S) : Option (VerifiedCertificate gs) :=
  run (fun seed => verifyRaw gs (candidate seed)) seeds

theorem search_sound {degree trials : ℕ} (gs : List (Perm (Fin degree)))
    (candidate : S → List Bool) (seeds : Fin trials → S) (result : VerifiedCertificate gs)
    (_h : search gs candidate seeds = some result) :
    ClaimHolds result.certificate :=
  result.sound gs

theorem search_unknown_le_half_pow [Fintype S] [Nonempty S]
    {degree : ℕ} (gs : List (Perm (Fin degree))) (candidate : S → List Bool)
    (R k : ℕ) (hR : 0 < R)
    (haccepts : 1 / (R : ℝ) ≤ FiniteSeeds.uniformProbability S
      (fun seed => (verifyRaw gs (candidate seed)).isSome = true)) :
    FiniteSeeds.uniformProbability (Fin (k * R) → S)
      (fun seeds => search gs candidate seeds = none) ≤ (1 / 2 : ℝ) ^ k :=
  run_unknown_le_half_pow _ R k hR haccepts

/-- Generate and verify certificates against the supplied raw group encoding. -/
def searchInput {trials : ℕ} (input : List Bool)
    (candidate : S → List Bool) (seeds : Fin trials → S) : Option VerifiedInput :=
  run (fun seed => verify input (candidate seed)) seeds

theorem searchInput_sound {trials : ℕ} (input : List Bool)
    (candidate : S → List Bool) (seeds : Fin trials → S) (result : VerifiedInput)
    (_h : searchInput input candidate seeds = some result) :
    ClaimHolds result.result.certificate :=
  result.sound

theorem searchInput_matches {trials : ℕ} (input : List Bool)
    (candidate : S → List Bool) (seeds : Fin trials → S) (result : VerifiedInput)
    (h : searchInput input candidate seeds = some result) :
    BinaryCodec.readAll readGroup input = some ⟨result.degree, result.generators⟩ := by
  obtain ⟨seed, _, hs⟩ := firstSuccess_eq_some_mem
    (fun seed => verify input (candidate seed)) (List.ofFn seeds) result h
  exact verify_input_matches input (candidate seed) result hs

theorem searchInput_unknown_le_half_pow [Fintype S] [Nonempty S]
    (input : List Bool) (candidate : S → List Bool) (R k : ℕ) (hR : 0 < R)
    (haccepts : 1 / (R : ℝ) ≤ FiniteSeeds.uniformProbability S
      (fun seed => (verify input (candidate seed)).isSome = true)) :
    FiniteSeeds.uniformProbability (Fin (k * R) → S)
      (fun seeds => searchInput input candidate seeds = none) ≤ (1 / 2 : ℝ) ^ k :=
  run_unknown_le_half_pow _ R k hR haccepts


end TauCeti.BoundedRunner
