/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Ideal

import TauCeti.Algebra.CharP.Lemmas
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import TauCeti.RingTheory.WittVector.Frobenius

/-!
# The Artin–Schreier sequence modulo a Witt ideal

Let `K` be a perfect ring of characteristic `p`, `O ⊆ K` a subring and `𝔪` an ideal of `O`.
Inside `W(K)` we consider the additive subgroup `W(𝔪) + p^n W(K)`
(`TauCeti.WittVector.idealModPow p 𝔪 n`, defined in `TauCeti.RingTheory.WittVector.Ideal`): the
Witt vectors that are congruent modulo `p^n` to a Witt vector all of whose coordinates lie in `𝔪`.
Since `K` is perfect, these are exactly the Witt vectors whose first `n` coordinates lie in `𝔪`
(`TauCeti.WittVector.mem_idealModPow_iff`).

For `K = C♭` the fraction field of the tilt of `𝒪_{ℂ_p}`, `O = O♭` and `𝔪` its maximal ideal,
this is the subgroup `W(𝔪♭) + p^n W(C♭)` modulo which the Artin–Schreier step `φ - 1` on
`W(C♭)/p^n` is studied. Over an algebraically closed field `φ - 1` is onto `W(K)/p^n`
(`TauCeti.WittVector.artinSchreierMod_surjective`); here we show that modulo `W(𝔪)` its kernel is
still exactly the finite constants:

* `TauCeti.WittVector.exists_sub_intCast_mem_idealModPow`: if `O` is closed under the roots of
  the Artin–Schreier equations `z ^ p - z = a` with `a ∈ O` (for instance if `O` is integrally
  closed in `K`) and `𝔪` is prime, then `φ(x) - x ∈ W(𝔪) + p^n W(K)` forces
  `x - c ∈ W(𝔪) + p^n W(K)` for an integer `c`;
* `TauCeti.WittVector.intCast_mem_idealModPow_iff`: an integer `c` lies in `W(𝔪) + p^n W(K)`
  only when `p^n ∣ c`, for any proper ideal `𝔪`.

The proof works one coordinate at a time: modulo `W(𝔪) + p^n W(K)` the `n`-th coordinate `z` of
`x - c` satisfies `z ^ p - z ∈ 𝔪`, so `z` lies in `O` and its residue modulo `𝔪` is a root of
`X ^ p - X`, hence lies in `𝔽_p`.

## References

* L. Herr, *Sur la cohomologie galoisienne des corps p-adiques*, Bull. Soc. Math. France 126
  (1998), on Artin–Schreier–Witt sequences over the tilt of `ℂ_p`.
-/

public section

noncomputable section

namespace TauCeti.WittVector

open _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {K : Type*} [CommRing K] [CharP K p] [PerfectRing K p]
  {O : Subring K} {𝔪 : Ideal O}

local notation "𝕎" => _root_.WittVector p

/-- **The constants modulo `W(𝔪)`.** For a proper ideal `𝔪`, an integer `c` lies in
`W(𝔪) + p^n W(K)` exactly when `p^n ∣ c`. -/
theorem intCast_mem_idealModPow_iff (h𝔪 : 𝔪 ≠ ⊤) {n : ℕ} {c : ℤ} :
    (c : 𝕎 K) ∈ idealModPow p 𝔪 n ↔ (p : ℤ) ^ n ∣ c := by
  refine ⟨fun hc ↦ ?_, fun ⟨d, hd⟩ ↦ mem_idealModPow_of_mem_span
    (Ideal.mem_span_singleton'.mpr ⟨d, by simp [hd, mul_comm]⟩)⟩
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    -- the zeroth coordinate `c` lies in `𝔪`, so `p ∣ c` since `O ⧸ 𝔪` has characteristic `p`
    have hpc : (p : ℤ) ∣ c := by
      obtain ⟨a, ha, hac⟩ := mem_idealModPow_one_iff.mp (idealModPow_antitone (by omega) hc)
      have hac : a = (c : O) := Subtype.ext <| by
        rw [Subring.coe_intCast, hac, ← constantCoeff_apply, map_intCast]
      have := Ideal.Quotient.nontrivial_iff.mpr h𝔪
      have := O.subtype.charP O.subtype_injective p
      have := charP_of_ringHom_of_prime (Ideal.Quotient.mk 𝔪) p
      rwa [← CharP.intCast_eq_zero_iff (O ⧸ 𝔪) p, ← map_intCast (Ideal.Quotient.mk 𝔪),
        Ideal.Quotient.eq_zero_iff_mem, ← hac]
    obtain ⟨d, rfl⟩ := hpc
    -- `p * d = V d`, so `d` lies in `W(𝔪) + p^n W(K)`
    rw [← pow_one (p : ℤ), intCast_pow_mul_eq_iterate_verschiebung, Function.iterate_one,
      verschiebung_mem_idealModPow_succ_iff] at hc
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih hc)

/-- **The Artin–Schreier sequence modulo `W(𝔪)`.** Let `K` be a perfect ring of characteristic
`p`, `O ⊆ K` a subring that contains every root `z ∈ K` of an equation `z ^ p - z = a` with
`a ∈ O` (for instance a subring integrally closed in `K`), and `𝔪` a prime ideal of `O`. If
`φ(x) - x ∈ W(𝔪) + p^n W(K)`, then `x` is congruent to an integer modulo `W(𝔪) + p^n W(K)`. -/
theorem exists_sub_intCast_mem_idealModPow [𝔪.IsPrime] (hO : ∀ z : K, z ^ p - z ∈ O → z ∈ O)
    {n : ℕ} {x : 𝕎 K} (hx : frobenius x - x ∈ idealModPow p 𝔪 n) :
    ∃ c : ℤ, x - c ∈ idealModPow p 𝔪 n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (idealModPow_antitone (Nat.le_succ n) hx)
    -- write `x - c = u + V^n z` with `u ∈ W(𝔪)`
    obtain ⟨w, hw, y, hy, hxy⟩ := mem_idealModPow.mp hc
    set z := y.shift n
    have hyz : y = verschiebung^[n] z :=
      eq_iterate_verschiebung ((mem_span_p_pow_iff_le_coeff_eq_zero y n).mp hy)
    have hu := map_mem_idealModPow hw (n + 1)
    -- since `φ` fixes `c` and commutes with `V`, `V^n (φ z - z)` lies in `W(𝔪) + p^(n+1) W(K)`
    have hVz : verschiebung^[n] (frobenius z - z) ∈ idealModPow p 𝔪 (1 + n) := by
      have hφ : frobenius x - x = (frobenius (map O.subtype w) - map O.subtype w) +
          verschiebung^[n] (frobenius z - z) := by
        have hx' : x = (c : 𝕎 K) + (map O.subtype w + verschiebung^[n] z) := by
          rw [← hyz, hxy, add_sub_cancel]
        rw [hx', map_add, map_add, map_intCast, ← verschiebung_frobenius_comm.iterate_left n,
          iterate_map_sub]
        abel
      have := sub_mem hx (sub_mem (frobenius_mem_idealModPow hu) hu)
      rwa [hφ, add_sub_cancel_left, add_comm] at this
    rw [iterate_verschiebung_mem_idealModPow_add_iff, mem_idealModPow_one_iff] at hVz
    obtain ⟨a, ha, haz⟩ := hVz
    -- the residue step: `z₀ ^ p - z₀ ∈ 𝔪`, so `z₀ ∈ O` is congruent modulo `𝔪` to some `d : ℕ`
    have haz : (a : K) = z.coeff 0 ^ p - z.coeff 0 := by
      simpa [coeff_frobenius_charP] using haz.trans (map_sub constantCoeff (frobenius z) z)
    have hz : z.coeff 0 ∈ O := hO _ (haz ▸ a.property)
    have := O.subtype.charP O.subtype_injective p
    have := charP_of_ringHom_of_prime (Ideal.Quotient.mk 𝔪) p
    have hza : (⟨z.coeff 0, hz⟩ : O) ^ p - ⟨z.coeff 0, hz⟩ = a :=
      Subtype.ext (by simpa using haz.symm)
    obtain ⟨d, hd⟩ := Ideal.exists_natCast_sub_mem_of_pow_sub_self_mem (p := p) (hza ▸ ha)
    obtain ⟨b, hb, hbz⟩ : ∃ b ∈ 𝔪, (b : K) = z.coeff 0 - d := ⟨_, hd, by simp⟩
    refine ⟨c + p ^ n * d, ?_⟩
    -- `p^n d = V^n d`, so `x - (c + p^n d) = u + V^n (z - d)`
    have hpd := intCast_pow_mul_eq_iterate_verschiebung (k := K) n d
    rw [Int.cast_natCast] at hpd
    have hx' : x - ((c + p ^ n * d : ℤ) : 𝕎 K) =
        map O.subtype w + verschiebung^[n] (z - (d : 𝕎 K)) := by
      rw [Int.cast_add, iterate_map_sub, ← hyz, ← hpd]
      linear_combination -hxy
    rw [hx']
    refine add_mem hu ?_
    rw [add_comm n, iterate_verschiebung_mem_idealModPow_add_iff, mem_idealModPow_one_iff]
    exact ⟨b, hb, by simpa [hbz] using (map_sub constantCoeff z (d : 𝕎 K)).symm⟩

end TauCeti.WittVector
