/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import TauCeti.Combinatorics.NoncrossingPartition.Interval
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import TauCeti.Combinatorics.NoncrossingPartition.PowerSeries

/-!
# The Möbius function of the lattice of noncrossing partitions

The Möbius function `μ` of the lattice `NC(s)` of noncrossing partitions of a finite set `s` of
positions in a linear order is computed on the lower intervals:
`μ(0_s, π) = ∏_{B ∈ π} (-1)^(|B| - 1) catalan(|B| - 1)`. In particular
`μ(0_n, 1_n) = (-1)^(n - 1) catalan(n - 1)` for `n ≥ 1`, and `μ(0_s, π)` is multiplicative over
the parts of `π`: `μ(0_s, π) = ∏_{B ∈ π} μ(0_B, 1_B)`. The value `μ(0_n, 1_n)` is the coefficient
of the product of the first moments in the formula `κ_n = ∑_{π ∈ NC(n)} μ(π, 1_n) φ_π` for free
cumulants, and the products `∏_B (-1)^(|B| - 1) catalan(|B| - 1)` are the leading coefficients of
the asymptotics of the unitary Weingarten function.

The lower interval `[0_s, π]` is the product of the lattices `NC(B)` over the parts `B` of `π`, so
the function `π ↦ ∏_{B ∈ π} w_{|B|}` with `w_k = (-1)^(k - 1) catalan(k - 1)` has lower sums
`∏_{B ∈ π} ∑_{τ ∈ NC(B)} ∏_{C ∈ τ} w_{|C|}`. The generating function
`W(z) = ∑_{k ≥ 1} w_k z^k = z c(-z)`, where `c` is the Catalan generating function, satisfies
`W + W² = z` by the Catalan recurrence; hence `W(z + z²) = z`, and the moment–cumulant functional
equation (`TauCeti.NoncrossingPartition.sum_prod_coeff_eq_coeff_of_subst_eq`) with
`C = 1 + W` and `M = 1 + z` shows that `∑_{τ ∈ NC(B)} ∏_{C ∈ τ} w_{|C|}` is `1` for a single
position and `0` for two or more. The lower sums are therefore those of the Möbius function
`σ ↦ μ(0_s, σ)`, and Möbius inversion identifies the two.

## Main results

* `TauCeti.NoncrossingPartition.mu_bot_eq_prod` —
  `μ(0_s, π) = ∏_{B ∈ π} (-1)^(|B| - 1) catalan(|B| - 1)`.
* `TauCeti.NoncrossingPartition.mu_bot_top` — `μ(0_s, 1_s) = (-1)^(|s| - 1) catalan(|s| - 1)`
  for nonempty `s`, and `TauCeti.NoncrossingPartition.mu_bot_top_fin` — the same for the
  positions of `Fin n`, `n ≥ 1`.
* `TauCeti.NoncrossingPartition.mu_bot_eq_prod_mu_bot_top` — `μ(0_s, π) = ∏_{B ∈ π} μ(0_B, 1_B)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 10 (the
  Möbius function of the lattice of noncrossing partitions).
* G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1 (1972), 333–350.
-/

public section

open Finset IncidenceAlgebra PowerSeries

namespace TauCeti.NoncrossingPartition

variable {R α : Type*} [CommRing R] [LinearOrder α] {s : Finset α}

/-- The series `1 + z c(-z) = 1 + ∑_{k ≥ 1} (-1)^(k - 1) catalan(k - 1) z^k`, where `c` is the
Catalan generating function. -/
private noncomputable def moebiusSeries (R : Type*) [CommRing R] : R⟦X⟧ :=
  1 + X * rescale (-1) (map (Nat.castRingHom R) catalanSeries)

private theorem coeff_succ_moebiusSeries (k : ℕ) :
    coeff (k + 1) (moebiusSeries R) = (-1) ^ k * catalan k := by
  simp [moebiusSeries, coeff_one, coeff_rescale]

private theorem constantCoeff_moebiusSeries : constantCoeff (moebiusSeries R) = 1 := by
  simp [moebiusSeries]

/-- The series `1 + W(z)` with `W(z) = z c(-z)` satisfies `1 + W(z (1 + z)) = 1 + z`. -/
private theorem moebiusSeries_subst :
    (moebiusSeries R).subst (X * (1 + X) : R⟦X⟧) = (1 + X : R⟦X⟧) := by
  set c' : R⟦X⟧ := rescale (-1) (map (Nat.castRingHom R) catalanSeries)
  have hP : HasSubst (X * (1 + X) : R⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  -- The Catalan recurrence `c = 1 + z c²` at `-z` gives `W + W² = z`.
  have hc : c' ^ 2 * -X + 1 = c' := by
    have h := congrArg (fun f => rescale (-1) (map (Nat.castRingHom R) f))
      catalanSeries_sq_mul_X_add_one
    simpa [rescale_X] using h
  have hW : X * c' + (X * c') ^ 2 = X := by linear_combination (-X) * hc
  set H : R⟦X⟧ := (X * c').subst (X * (1 + X) : R⟦X⟧)
  have hH : H + H ^ 2 = X * (1 + X) := by
    have h := congrArg (subst (X * (1 + X) : R⟦X⟧)) hW
    rwa [subst_add hP, subst_pow hP, subst_X hP] at h
  -- `W(z (1 + z))` and `z` both solve `F + F² = z (1 + z)` with `F(0) = 0`.
  have hH0 : constantCoeff H = 0 := by simp [H, subst_mul hP, subst_X hP]
  have hu : IsUnit (H + X + 1) := isUnit_iff_constantCoeff.2 (by simp [hH0])
  have hHX : H = X := sub_eq_zero.1 <| hu.mul_left_eq_zero.1 (by linear_combination hH)
  have h1 : (1 : R⟦X⟧).subst (X * (1 + X) : R⟦X⟧) = 1 := by
    simpa [coe_substAlgHom] using map_one (substAlgHom hP (R := R))
  rw [moebiusSeries, subst_add hP, h1]
  exact congrArg (1 + ·) hHX

/-- The total weight of the noncrossing partitions of a nonempty set `s` when a part of size `k`
has weight `(-1)^(k - 1) catalan(k - 1)` is `1` if `s` is a single position and `0` otherwise. -/
private theorem sum_prod_neg_one_pow_mul_catalan (hs : s.Nonempty) :
    ∑ π : NoncrossingPartition s, ∏ B ∈ π.1.parts, ((-1) ^ (#B - 1) * catalan (#B - 1) : R) =
      if #s = 1 then 1 else 0 := by
  have h := sum_prod_coeff_eq_coeff_of_subst_eq constantCoeff_moebiusSeries
    (moebiusSeries_subst (R := R)) s
  rw [map_add, coeff_one, ite_eq_right_iff.2 fun h => absurd h hs.card_pos.ne', zero_add,
    coeff_X] at h
  rw [← h]
  refine sum_congr rfl fun π _ => prod_congr rfl fun B hB => ?_
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (π.1.nonempty_of_mem_parts hB).card_pos.ne'
  rw [hk, coeff_succ_moebiusSeries, Nat.add_sub_cancel]

/-- The Möbius function of the lattice of noncrossing partitions on a lower interval:
`μ(0_s, π) = ∏_{B ∈ π} (-1)^(|B| - 1) catalan(|B| - 1)`. -/
theorem mu_bot_eq_prod (π : NoncrossingPartition s) :
    mu R ⊥ π = ∏ B ∈ π.1.parts, (-1) ^ (#B - 1) * (catalan (#B - 1) : R) := by
  refine ((moebius_inversion_bot (𝕜 := R)
    (fun σ : NoncrossingPartition s => ∏ B ∈ σ.1.parts, (-1) ^ (#B - 1) * (catalan (#B - 1) : R))
    (fun σ => if σ = ⊥ then 1 else 0) (fun σ => ?_) π).trans ?_).symm
  · rw [sum_Iic_prod_parts_eq_prod_sum σ fun B => (-1) ^ (#B - 1) * (catalan (#B - 1) : R),
      prod_congr rfl fun B hB => sum_prod_neg_one_pow_mul_catalan (σ.1.nonempty_of_mem_parts hB),
      prod_boole]
    exact if_congr (by rw [← Subtype.coe_inj, coe_bot, Finpartition.eq_bot_iff_forall_card_eq_one])
      rfl rfl
  · simp

/-- The Möbius function of the lattice of noncrossing partitions of a nonempty set `s`:
`μ(0_s, 1_s) = (-1)^(|s| - 1) catalan(|s| - 1)`. -/
theorem mu_bot_top (hs : s.Nonempty) :
    mu R (⊥ : NoncrossingPartition s) ⊤ = (-1) ^ (#s - 1) * catalan (#s - 1) := by
  rw [mu_bot_eq_prod, coe_top, Finpartition.parts_top hs.ne_empty, prod_singleton]

/-- The Möbius function of the lattice `NC(n)` of noncrossing partitions of `n ≥ 1` ordered
positions: `μ(0_n, 1_n) = (-1)^(n - 1) catalan(n - 1)`. -/
theorem mu_bot_top_fin {n : ℕ} (hn : n ≠ 0) :
    mu R (⊥ : NoncrossingPartition (univ : Finset (Fin n))) ⊤ =
      (-1) ^ (n - 1) * catalan (n - 1) := by
  rw [mu_bot_top (univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero hn))), card_univ,
    Fintype.card_fin]

/-- The Möbius function of the lattice of noncrossing partitions is multiplicative on lower
intervals: `μ(0_s, π) = ∏_{B ∈ π} μ(0_B, 1_B)`. -/
theorem mu_bot_eq_prod_mu_bot_top (π : NoncrossingPartition s) :
    mu R ⊥ π = ∏ B ∈ π.1.parts, mu R (⊥ : NoncrossingPartition B) ⊤ := by
  rw [mu_bot_eq_prod]
  exact prod_congr rfl fun B hB => (mu_bot_top (π.1.nonempty_of_mem_parts hB)).symm

end TauCeti.NoncrossingPartition
