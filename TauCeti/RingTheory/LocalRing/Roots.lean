/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Filtration
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# Roots of units in a finite extension with trivial residue extension

Let `R → S` be a local homomorphism of local rings with `R` Noetherian and `S` finite over `R`,
and suppose the residue field extension is trivial. If `n` is invertible in `R`, then every
`n`-th root in `S` of a unit of `R` already lies in `R`.

For instance, a totally ramified finite extension of a discrete valuation ring contains no roots
of unity of order prime to the residue characteristic beyond those of the base.

## Main results

* `TauCeti.IsLocalRing.algebraMap_sub_pow_dvd_sub_algebraMap_of_pow_eq`: if `c ∈ R` is congruent
  modulo `𝔪(S)` to an `n`-th root `s` of a unit `u` of `R`, then `u - cⁿ` divides `s - c`.
* `TauCeti.IsLocalRing.mem_range_algebraMap_of_pow_eq_of_isUnit`: an `n`-th root of a unit of
  `R`, with `n` invertible in `R`, lies in the image of `R`.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

omit [IsLocalRing R] [IsLocalHom (algebraMap R S)] in
/-- **Approximating roots of units in a local algebra.** Let `S` be a local `R`-algebra, `n` be
invertible in `R`, and `s ∈ S` be an `n`-th root of a unit `u` of `R`. If `c ∈ R` is congruent to
`s` modulo `𝔪(S)`, then `u - cⁿ` divides `s - c` in `S`. -/
theorem algebraMap_sub_pow_dvd_sub_algebraMap_of_pow_eq {n : ℕ} (hn : IsUnit (n : R)) {u : R}
    (hu : IsUnit u) {s : S} (hs : s ^ n = algebraMap R S u) {c : R}
    (hc : s - algebraMap R S c ∈ maximalIdeal S) :
    algebraMap R S (u - c ^ n) ∣ s - algebraMap R S c := by
  have hn0 : n ≠ 0 := by rintro rfl; simpa using hn.map (algebraMap R S)
  set Q := ∑ i ∈ Finset.range n, s ^ i * algebraMap R S c ^ (n - 1 - i)
  have hQ : Q * (s - algebraMap R S c) = algebraMap R S (u - c ^ n) := by
    rw [geom_sum₂_mul, hs, map_sub, map_pow]
  -- Modulo `𝔪(S)`, `Q` is `n cⁿ⁻¹`, and `c` is a unit because `s` is.
  have hres : residue S s = residue S (algebraMap R S c) := by
    rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  have hsu : IsUnit s := (isUnit_pow_iff hn0).mp (hs ▸ hu.map _)
  have hQu : IsUnit Q := by
    rw [← isUnit_map_iff (residue S), map_sum]
    simp_rw [map_mul, map_pow, ← hres, geom_sum₂_self]
    exact (by simpa using (hn.map (algebraMap R S)).map (residue S) : IsUnit _).mul
      ((hsu.map _).pow _)
  exact ⟨↑hQu.unit⁻¹, by rw [← hQ, mul_comm Q, mul_assoc, hQu.mul_val_inv, mul_one]⟩

/-- **Roots of units descend along a finite extension with trivial residue extension.** Let
`R → S` be a local homomorphism of local rings, with `R` Noetherian, `S` finite over `R`, and
trivial residue field extension. If `n` is invertible in `R`, then every `n`-th root in `S` of a
unit of `R` lies in the image of `R`. -/
theorem mem_range_algebraMap_of_pow_eq_of_isUnit [IsNoetherianRing R] [Module.Finite R S]
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S))) {n : ℕ}
    (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u) {s : S} (hs : s ^ n = algebraMap R S u) :
    s ∈ Set.range (algebraMap R S) := by
  -- This is a Hensel-type approximation without any completeness assumption. Correcting an
  -- approximation `c` of `s` by a multiple of `u - cⁿ` improves it by one power of `𝔪(S)`. Some
  -- power of `𝔪(S)` lies in `𝔪(R) S` (`TauCeti.IsLocalRing.exists_maximalIdeal_pow_le_map`), so
  -- the class of `s` in the finite `R`-module `S ⧸ R` lies in every `𝔪(R)ᵏ (S ⧸ R)`, which is
  -- zero by Krull's intersection theorem.
  have hlift (b : S) : ∃ a : R, b - algebraMap R S a ∈ maximalIdeal S := by
    obtain ⟨x, hx⟩ := hres (residue S b)
    obtain ⟨a, rfl⟩ := residue_surjective x
    refine ⟨a, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, ← ResidueField.algebraMap_residue, hx, sub_self]
  -- Successive approximations of `s` by elements of `R`, modulo powers of `𝔪(S)`.
  have happrox (k : ℕ) : ∃ c : R, s - algebraMap R S c ∈ maximalIdeal S ^ (k + 1) := by
    induction k with
    | zero => simpa using hlift s
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨w, hw⟩ := algebraMap_sub_pow_dvd_sub_algebraMap_of_pow_eq hn hu hs
        (Ideal.pow_le_self k.succ_ne_zero hc)
      obtain ⟨c₁, hc₁⟩ := hlift w
      have ht : algebraMap R S (u - c ^ n) ∈ maximalIdeal S ^ (k + 1) := by
        rw [map_sub, map_pow, ← hs]
        exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ n) hc
      refine ⟨c + (u - c ^ n) * c₁, ?_⟩
      have : s - algebraMap R S (c + (u - c ^ n) * c₁) =
          algebraMap R S (u - c ^ n) * (w - algebraMap R S c₁) := by
        rw [map_add, map_mul]
        linear_combination hw
      rw [this, pow_succ]
      exact Ideal.mul_mem_mul ht hc₁
  -- The class of `s` in `S ⧸ R` lies in every `𝔪(R)ᵏ (S ⧸ R)`, so it vanishes by Krull.
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map (R := R) (S := S)
  set P := LinearMap.range (Algebra.linearMap R S)
  have hmem : P.mkQ s ∈ (⨅ k : ℕ, maximalIdeal R ^ k • ⊤ : Submodule R (S ⧸ P)) := by
    refine Submodule.mem_iInf _ |>.mpr fun k ↦ ?_
    obtain ⟨c, hc⟩ := happrox (N * k)
    have hck : s - algebraMap R S c ∈ (maximalIdeal R ^ k • ⊤ : Submodule R S) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
      refine Ideal.pow_right_mono hN k ?_
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (Nat.le_succ _) hc
    have hle : (maximalIdeal R ^ k • ⊤ : Submodule R S).map P.mkQ ≤ maximalIdeal R ^ k • ⊤ := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    have hsc : P.mkQ s = P.mkQ (s - algebraMap R S c) := by
      have hc0 : P.mkQ (algebraMap R S c) = 0 :=
        (Submodule.Quotient.mk_eq_zero P).mpr ⟨c, rfl⟩
      rw [map_sub, hc0, sub_zero]
    exact hsc ▸ hle (Submodule.mem_map_of_mem hck)
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

end TauCeti.IsLocalRing
