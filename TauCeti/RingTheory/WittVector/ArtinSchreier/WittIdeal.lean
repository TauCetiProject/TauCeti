/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Complete
public import TauCeti.RingTheory.WittVector.Ideal

import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The Artin–Schreier sequence modulo a Witt ideal

Let `K` be a perfect ring of characteristic `p`, `O ⊆ K` a subring and `𝔪` an ideal of `O`.
Inside `W(K)` we consider the additive subgroup `W(𝔪) + p^n W(K)`
(`TauCeti.WittVector.idealModPow p 𝔪 n`): the Witt vectors that are congruent modulo `p^n` to a
Witt vector all of whose coordinates lie in `𝔪`. Since `K` is perfect, these are exactly the
Witt vectors whose first `n` coordinates lie in `𝔪` (`TauCeti.WittVector.mem_idealModPow_iff`).

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

variable (p : ℕ) [hp : Fact p.Prime] {K : Type*} [CommRing K]

local notation "𝕎" => _root_.WittVector p

/-- For an ideal `𝔪` of a subring `O ⊆ K`, the additive subgroup `W(𝔪) + p^n W(K)` of `W(K)`:
the Witt vectors over `K` congruent modulo `p^n` to the image of a Witt vector all of whose
coordinates lie in `𝔪`. Over a perfect ring of characteristic `p` these are the Witt vectors
whose first `n` coordinates lie in `𝔪` (`TauCeti.WittVector.mem_idealModPow_iff`). -/
def idealModPow {O : Subring K} (𝔪 : Ideal O) (n : ℕ) : AddSubgroup (𝕎 K) :=
  (ideal p 𝔪).toAddSubgroup.map (map O.subtype).toAddMonoidHom ⊔
    (Ideal.span {(p : 𝕎 K) ^ n}).toAddSubgroup

variable {p} {O : Subring K} {𝔪 : Ideal O}

/-- `idealModPow p 𝔪 n` is the sum of the image of `W(𝔪)` and the ideal `p^n W(K)`. -/
theorem idealModPow_def (n : ℕ) : idealModPow p 𝔪 n =
    (ideal p 𝔪).toAddSubgroup.map (map O.subtype).toAddMonoidHom ⊔
      (Ideal.span {(p : 𝕎 K) ^ n}).toAddSubgroup :=
  (rfl)

/-- A Witt vector lies in `W(𝔪) + p^n W(K)` exactly when it is the sum of the image of an element
of `W(𝔪)` and a multiple of `p^n`. -/
theorem mem_idealModPow {n : ℕ} {x : 𝕎 K} : x ∈ idealModPow p 𝔪 n ↔
    ∃ w ∈ ideal p 𝔪, ∃ y ∈ Ideal.span {(p : 𝕎 K) ^ n}, map O.subtype w + y = x := by
  simp [idealModPow, AddSubgroup.mem_sup]

/-- The image of the Witt ideal `W(𝔪)` lies in `W(𝔪) + p^n W(K)`. -/
theorem map_mem_idealModPow {w : 𝕎 O} (hw : w ∈ ideal p 𝔪) (n : ℕ) :
    map O.subtype w ∈ idealModPow p 𝔪 n :=
  AddSubgroup.mem_sup_left ⟨w, hw, rfl⟩

/-- The multiples of `p^n` lie in `W(𝔪) + p^n W(K)`. -/
theorem mem_idealModPow_of_mem_span {n : ℕ} {x : 𝕎 K}
    (hx : x ∈ Ideal.span {(p : 𝕎 K) ^ n}) : x ∈ idealModPow p 𝔪 n :=
  AddSubgroup.mem_sup_right hx

/-- Every Witt vector lies in `W(𝔪) + p^0 W(K)`. -/
@[simp]
theorem idealModPow_zero : idealModPow p 𝔪 0 = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_idealModPow_of_mem_span (by simp)

/-- The subgroups `W(𝔪) + p^n W(K)` decrease as `n` grows. -/
theorem idealModPow_antitone : Antitone (idealModPow p 𝔪) := fun _ _ h ↦
  sup_le_sup_left (Submodule.toAddSubgroup_mono
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ h))) _

/-- `W(𝔪) + p^n W(K)` is stable under the Witt vector Frobenius. -/
theorem frobenius_mem_idealModPow {n : ℕ} {x : 𝕎 K} (hx : x ∈ idealModPow p 𝔪 n) :
    frobenius x ∈ idealModPow p 𝔪 n := by
  obtain ⟨w, hw, y, hy, rfl⟩ := mem_idealModPow.mp hx
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [map_add, ← (frobenius_isPoly p).map]
  refine add_mem (map_mem_idealModPow (frobenius_mem_ideal hw) n)
    (mem_idealModPow_of_mem_span (Ideal.mem_span_singleton'.mpr ⟨frobenius t, ?_⟩))
  simp

variable [CharP K p] [PerfectRing K p]

/-- Over a perfect ring of characteristic `p`, a Witt vector lies in `W(𝔪) + p^n W(K)` exactly
when its first `n` coordinates lie in `𝔪`. -/
theorem mem_idealModPow_iff {n : ℕ} {x : 𝕎 K} :
    x ∈ idealModPow p 𝔪 n ↔ ∀ i < n, ∃ a ∈ 𝔪, (a : K) = x.coeff i := by
  constructor
  · intro hx i hi
    obtain ⟨w, hw, y, hy, rfl⟩ := mem_idealModPow.mp hx
    have hy : ∀ j < n, y.coeff j = 0 :=
      (mem_span_p_pow_iff_le_coeff_eq_zero y n).mp hy
    -- adding `y`, whose first `n` coordinates vanish, does not change the first `n` coordinates
    have hcoeff : ∀ j < n, (map O.subtype w + y).coeff j = (map O.subtype w).coeff j :=
      le_coeff_eq_iff_le_sub_coeff_eq_zero.mpr (by simpa only [add_sub_cancel_left] using hy)
    exact ⟨w.coeff i, mem_ideal_iff.mp hw i, by
      rw [hcoeff i hi, map_coeff, Subring.coe_subtype]⟩
  · intro h
    classical
    let w : 𝕎 O := mk p fun i ↦ if hi : i < n then (h i hi).choose else 0
    have hw : w ∈ ideal p 𝔪 := mem_ideal_iff.mpr fun i ↦ by
      by_cases hi : i < n
      · simpa [w, hi] using (h i hi).choose_spec.1
      · simp [w, hi]
    have hsub : x - map O.subtype w ∈ Ideal.span {(p : 𝕎 K) ^ n} := by
      refine (mem_span_p_pow_iff_le_coeff_eq_zero _ n).mpr
        (le_coeff_eq_iff_le_sub_coeff_eq_zero.mp fun i hi ↦ ?_)
      simpa [w, hi] using (h i hi).choose_spec.2.symm
    simpa using add_mem (map_mem_idealModPow hw n) (mem_idealModPow_of_mem_span hsub)

/-- A Witt vector lies in `W(𝔪) + p W(K)` exactly when its zeroth coordinate lies in `𝔪`. -/
theorem mem_idealModPow_one_iff {x : 𝕎 K} :
    x ∈ idealModPow p 𝔪 1 ↔ ∃ a ∈ 𝔪, (a : K) = x.coeff 0 := by
  simp [mem_idealModPow_iff]

/-- A Verschiebung `V x` lies in `W(𝔪) + p^(n+1) W(K)` exactly when `x` lies in
`W(𝔪) + p^n W(K)`. -/
@[simp]
theorem verschiebung_mem_idealModPow_succ_iff {n : ℕ} {x : 𝕎 K} :
    verschiebung x ∈ idealModPow p 𝔪 (n + 1) ↔ x ∈ idealModPow p 𝔪 n := by
  simp only [mem_idealModPow_iff]
  constructor
  · intro h i hi
    simpa only [verschiebung_coeff_succ] using h (i + 1) (Nat.succ_lt_succ hi)
  · rintro h (_ | i) hi
    · exact ⟨0, 𝔪.zero_mem, by simp⟩
    · simpa only [verschiebung_coeff_succ] using h i (Nat.succ_lt_succ_iff.mp hi)

/-- An iterated Verschiebung `V^k x` lies in `W(𝔪) + p^(n+k) W(K)` exactly when `x` lies in
`W(𝔪) + p^n W(K)`. -/
@[simp]
theorem iterate_verschiebung_mem_idealModPow_add_iff {n k : ℕ} {x : 𝕎 K} :
    verschiebung^[k] x ∈ idealModPow p 𝔪 (n + k) ↔ x ∈ idealModPow p 𝔪 n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← add_assoc, verschiebung_mem_idealModPow_succ_iff, ih]

omit [PerfectRing K p] in
/-- Over a ring of characteristic `p`, the integer `p^n d` is the iterated Verschiebung
`V^n d = V^n (F^n d)` of `d`. -/
theorem intCast_pow_mul_eq_iterate_verschiebung (n : ℕ) (d : ℤ) :
    ((p ^ n * d : ℤ) : 𝕎 K) = verschiebung^[n] (d : 𝕎 K) := by
  rw [← Function.iterate_fixed (map_intCast (_root_.WittVector.frobenius : 𝕎 K →+* 𝕎 K) d) n,
    iterate_verschiebung_iterate_frobenius]
  push_cast
  ring

omit [PerfectRing K p] in
/-- For a proper ideal `𝔪` of a subring `O` of a ring of characteristic `p`, the quotient
`O ⧸ 𝔪` has characteristic `p`. -/
private theorem charP_quotient (h𝔪 : 𝔪 ≠ ⊤) : CharP (O ⧸ 𝔪) p :=
  have := Ideal.Quotient.nontrivial_iff.mpr h𝔪
  (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
    exact (Subtype.ext (by simp) : (p : O) = 0) ▸ 𝔪.zero_mem

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
      have := charP_quotient h𝔪
      rwa [← CharP.intCast_eq_zero_iff (O ⧸ 𝔪) p, ← map_intCast (Ideal.Quotient.mk 𝔪),
        Ideal.Quotient.eq_zero_iff_mem, ← hac]
    obtain ⟨d, rfl⟩ := hpc
    -- `p * d = V d`, so `d` lies in `W(𝔪) + p^n W(K)`
    rw [← pow_one (p : ℤ), intCast_pow_mul_eq_iterate_verschiebung, Function.iterate_one,
      verschiebung_mem_idealModPow_succ_iff] at hc
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih hc)

omit [PerfectRing K p] in
/-- The residue step: if `z ^ p - z ∈ 𝔪` with `O` closed under Artin–Schreier roots and `𝔪`
prime, then `z` is congruent modulo `𝔪` to a natural number. -/
private theorem exists_natCast_sub_mem [𝔪.IsPrime] (hO : ∀ z : K, z ^ p - z ∈ O → z ∈ O)
    {z : K} {a : O} (ha : a ∈ 𝔪) (haz : (a : K) = z ^ p - z) :
    ∃ d : ℕ, ∃ b ∈ 𝔪, (b : K) = z - d := by
  have hz : z ∈ O := hO z (haz ▸ a.property)
  have := charP_quotient (p := p) (Ideal.IsPrime.ne_top ‹_›)
  have hza : (⟨z, hz⟩ : O) ^ p - ⟨z, hz⟩ = a := Subtype.ext (by simpa using haz.symm)
  obtain ⟨d, hd⟩ := Ideal.exists_natCast_sub_mem_of_pow_sub_self_mem (p := p) (hza ▸ ha)
  exact ⟨d, _, hd, by simp⟩

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
    obtain ⟨d, b, hb, hbz⟩ := exists_natCast_sub_mem hO ha (by
      simpa [coeff_frobenius_charP] using haz.trans (map_sub constantCoeff (frobenius z) z))
    refine ⟨c + p ^ n * d, ?_⟩
    -- `p^n d = V^n d`, so `x - (c + p^n d) = u + V^n (z - d)`
    have hpd := intCast_pow_mul_eq_iterate_verschiebung (K := K) n d
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
