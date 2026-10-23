/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Hilbert
public import TauCeti.NumberTheory.LocalField.Different.Trace
public import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# The trace below the Herbrand shift

Let `L/K` be a finite Galois extension of nonarchimedean local fields. Hilbert's formula
`d(L/K) = ∑_{i ≥ 0} (#G_i - 1)`, truncated at `m = ψℕ_{L/K}(n)`, together with the defining
identity `#G_1 + ⋯ + #G_m = n · #G_0`, gives

`e(L/K) (n + 1) ≤ ψℕ_{L/K}(n) + 1 + d(L/K)`.

The trace formula for powers of the maximal ideal then bounds the integral trace below the
Herbrand shift. This is the trace input to the Herbrand-shifted norm inclusion in
`TauCeti.NumberTheory.LocalField.Norm.Herbrand`.

## Main results

* `TauCeti.intTrace_mem_maximalIdeal_pow_succ_of_mem_psiNat`: the integral trace carries
  `𝓂[L] ^ (ψℕ_{L/K}(n) + 1)` into `𝓂[K] ^ (n + 1)`.
* `TauCeti.trace_mem_maximalIdeal_pow_succ`: when `[L : K] ≥ 2` and `G_{v+1} = Gal(L/K)`,
  the trace carries `𝓂[L] ^ v` into `𝓂[K] ^ (v + 1)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3 (Lemmas 4 and 5) and §6
  (Proposition 8).
-/

public section

open ValuativeRel IsLocalRing TauCeti.LocalFieldsRamification

namespace TauCeti

section Trace

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- `e(L/K) (n + 1) ≤ ψℕ_{L/K}(n) + 1 + d(L/K)`: Hilbert's formula, truncated at `ψℕ_{L/K}(n)`,
together with `#G_1 + ⋯ + #G_m = n · #G_0` for `m = ψℕ_{L/K}(n)`. -/
private theorem ramificationIndex_mul_succ_le (n : ℕ) :
    ramificationIndex K L * (n + 1) ≤ psiNat K L n + 1 + differentExponent K L := by
  set m := psiNat K L n
  set g : ℕ → ℕ := fun i ↦ Nat.card (lowerRamificationGroup K L i)
  have hg : ∀ i, 1 ≤ g i := fun i ↦ Nat.card_pos
  -- `#G_0 + #G_1 + ⋯ + #G_m = (n + 1) e(L/K)`.
  have hsum : ∑ i ∈ Finset.range (m + 1), g i = ramificationIndex K L * (n + 1) := by
    have h : ∑ i ∈ Finset.range m, g (i + 1) = n * g 0 := by
      have h₀ := (psiNat_eq_iff K L).1 (rfl : psiNat K L n = m)
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
        at h₀
      simp only [g, Nat.cast_zero, ← h₀]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_comm i 1]
    rw [Finset.sum_range_succ', h, ← natCard_lowerRamificationGroup_zero K L]
    simp only [g, Nat.cast_zero]
    ring
  -- Hilbert's formula, truncated at `m`: `∑_{i ≤ m} (#G_i - 1) ≤ d(L/K)`.
  have htrunc : ∑ i ∈ Finset.range (m + 1), (g i - 1) ≤ differentExponent K L :=
    sum_range_card_lowerRamificationGroup_sub_one_le_differentExponent K L (m + 1)
  have hsub : ∑ i ∈ Finset.range (m + 1), (g i - 1) + (m + 1) =
      ∑ i ∈ Finset.range (m + 1), g i := by
    calc ∑ i ∈ Finset.range (m + 1), (g i - 1) + (m + 1)
        = ∑ i ∈ Finset.range (m + 1), (g i - 1 + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      _ = ∑ i ∈ Finset.range (m + 1), g i :=
          Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hg i)
  omega

/-- **The trace below the Herbrand shift.** In a finite Galois extension `L/K` of nonarchimedean
local fields, the integral trace carries `𝓂[L] ^ (ψℕ_{L/K}(n) + 1)` into `𝓂[K] ^ (n + 1)`. -/
theorem intTrace_mem_maximalIdeal_pow_succ_of_mem_psiNat {n : ℕ} {x : 𝒪[L]}
    (hx : x ∈ 𝓂[L] ^ (psiNat K L n + 1)) :
    Algebra.intTrace 𝒪[K] 𝒪[L] x ∈ 𝓂[K] ^ (n + 1) :=
  intTrace_mem_maximalIdeal_pow_of_mem hx (ramificationIndex_mul_succ_le n)

/-- If `[L : K] ≥ 2` and `G_{v+1} = Gal(L/K)`, the trace carries `𝓂[L] ^ v` into
`𝓂[K] ^ (v + 1)`: Hilbert's formula, truncated at `v + 1`, gives
`d(L/K) ≥ (v + 2) ([L : K] - 1)`. -/
theorem trace_mem_maximalIdeal_pow_succ (h2 : 2 ≤ Module.finrank K L) {v : ℕ}
    (hG : lowerRamificationGroup K L (v + 1) = ⊤) {w : 𝒪[L]} (hw : w ∈ 𝓂[L] ^ v) :
    Algebra.trace 𝒪[K] 𝒪[L] w ∈ 𝓂[K] ^ (v + 1) := by
  have hGi (i : ℕ) (hi : i ≤ v + 1) : lowerRamificationGroup K L i = ⊤ :=
    top_le_iff.1 (hG ▸ lowerRamificationGroup_antitone K L (by omega))
  have he : ramificationIndex K L = Module.finrank K L :=
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).1 <|
      (lowerRamificationGroup_zero_eq_top_iff K L).1 (by simpa using hGi 0 (by omega))
  have hd : (v + 2) * (Module.finrank K L - 1) ≤ differentExponent K L := by
    have hsum := sum_range_card_lowerRamificationGroup_sub_one_le_differentExponent K L (v + 2)
    rwa [Finset.sum_congr rfl fun i hi ↦ by
        rw [hGi i (by simp only [Finset.mem_range] at hi; omega), Subgroup.card_top,
          IsGalois.card_aut_eq_finrank],
      Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  rw [← Algebra.intTrace_eq_trace]
  refine intTrace_mem_maximalIdeal_pow_of_mem hw ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
  have hm1 : 2 + m - 1 = m + 1 := by omega
  rw [he, hm]
  rw [hm, hm1] at hd
  nlinarith

end Trace

end TauCeti
