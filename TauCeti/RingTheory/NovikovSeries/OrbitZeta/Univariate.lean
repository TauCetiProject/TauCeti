/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic

/-!
# Orbit zeta functions with integer periods

When the period map `N` of a Novikov ring `Nov(K, H, N)` takes integer values `N h = n h` for an
additive map `n : H →+ ℤ`, the pushforward along `n` (`TauCeti.NovikovSeries.mapRingHom`) lands
in `Nov(K, ℤ, ℤ ↪ ℝ)`, the ring of Laurent series `K⸨t⸩`
(`TauCeti.NovikovSeries.toLaurentSeries`). By the naturality of the orbit zeta function
(`TauCeti.NovikovSeries.mapRingHom_orbitZeta`), it sends the orbit zeta function of the classes
`γ i` to the orbit zeta function of their periods `d i = n (γ i)`: the classes of the orbits are
forgotten, and only their periods remain. For the suspension flow of a mapping torus, `n` is the
time period and this is the classical univariate dynamical zeta function.

This file computes the coefficients of the logarithm of that univariate orbit zeta function. For
orbits of positive integer periods `d i`, only finitely many below each bound, the `m`-th
coefficient of the orbit logarithm

`L = ∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · t^((k + 1) d i)`

collects the iterates of period `m`, one for each orbit whose period divides `m`
(`TauCeti.NovikovSeries.coeff_orbitLog_natCast`):

`[t^m] L = ∑_{d i ∣ m} ε i (m / d i) / (m / d i)`.

Multiplied by `m`, it is the integer `∑_{d i ∣ m} d i ε i (m / d i)`
(`TauCeti.NovikovSeries.natCast_mul_coeff_orbitLog_natCast`). For the periodic orbits of a map
`f`, when the points `x i` represent distinct periodic orbits, `d i` is the minimal period of
`x i`, and `ε i k` is the Lefschetz sign of `x i` as a fixed point of `f^(k d i)`, the `d i`
points of the `i`-th orbit are fixed points of `f^m` exactly when `d i ∣ m`, each with the same
sign, so this integer is the signed count of the fixed points of `f^m`. Hence, under these
conditions, the univariate orbit zeta function is `exp (∑_m a_m t^m / m)` with these integers
`a_m`, the form in which it is compared with the Lefschetz numbers of the iterates of `f`. The
results of this file are the purely algebraic identities and assume none of these conditions.

## Main results

* `TauCeti.NovikovSeries.coeff_orbitLog_natCast`: the coefficients of the univariate orbit
  logarithm.
* `TauCeti.NovikovSeries.natCast_mul_coeff_orbitLog_natCast`: `m` times the `m`-th coefficient is
  the integer `∑_{d i ∣ m} d i ε i (m / d i)`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* M. Artin and B. Mazur, *On periodic points*, Ann. of Math. (2) 81 (1965), 82--99.
-/

public section

noncomputable section

open Filter

namespace TauCeti.NovikovSeries

variable {ι K : Type*} [CommRing K] [Algebra ℚ K] {d : ι → ℕ}

/-- The positive natural periods `d i`, read as integer exponents, have positive periods. -/
private theorem intCast_pos (hd : ∀ i, 0 < d i) (i : ι) : 0 < Int.castAddHom ℝ (d i : ℤ) := by
  simpa using hd i

/-- Positive natural periods tending to infinity, read as integer exponents, have periods tending
to infinity. -/
private theorem tendsto_intCast (hfin : Tendsto d cofinite atTop) :
    Tendsto (fun i => Int.castAddHom ℝ (d i : ℤ)) cofinite atTop := by
  refine (tendsto_natCast_atTop_atTop.comp hfin).congr fun i => ?_
  simp

/-- The sum over the iterates of one orbit of period `p > 0` of the terms of total period `m`:
only the `(m / p)`-fold iterate contributes, when `p ∣ m`. -/
private theorem finsum_succ_mul_eq (p m : ℕ) (hp : 0 < p) (e : ℕ → ℤ) :
    (∑ᶠ k : ℕ, if (k + 1) * p = m then (e (k + 1) : ℚ) / (k + 1 : ℕ) else 0) =
      if p ∣ m then (e (m / p) : ℚ) / (m / p : ℕ) else 0 := by
  split_ifs with hdvd
  · obtain ⟨j, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left j hp]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    -- For `m = 0` no iterate has period `0`, and the right side divides by `0`.
    · refine (finsum_eq_zero_of_forall_eq_zero fun k => ite_eq_right ?_).trans (by simp)
      simp [hp.ne']
    · refine (finsum_eq_single _ (j - 1) fun k hk => ite_eq_right ?_).trans ?_
      · rw [mul_comm p j, Nat.mul_left_inj hp.ne']
        omega
      · rw [Nat.sub_add_cancel hj, ite_eq_left (mul_comm j p)]
  · refine finsum_eq_zero_of_forall_eq_zero fun k => ite_eq_right fun h => hdvd ⟨k + 1, ?_⟩
    rw [← h, mul_comm]

/-- **Coefficients of the univariate orbit logarithm.** For orbits of positive integer periods
`d i`, only finitely many below each bound, the coefficient of `t^m` in the orbit logarithm
`∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · t^((k + 1) d i)` is `∑_{d i ∣ m} ε i (m / d i) / (m / d i)`. -/
theorem coeff_orbitLog_natCast (hd : ∀ i, 0 < d i) (hfin : Tendsto d cofinite atTop)
    (ε : ι → ℕ → ℤ) (m : ℕ) :
    (orbitLog K (Int.castAddHom ℝ) (fun i => (d i : ℤ)) ε).coeff (m : ℤ) =
      algebraMap ℚ K (∑ᶠ i, if d i ∣ m then (ε i (m / d i) : ℚ) / (m / d i : ℕ) else 0) := by
  have hcast (i : ι) (k : ℕ) : (k + 1) • (d i : ℤ) = (m : ℤ) ↔ (k + 1) * d i = m := by
    rw [nsmul_eq_mul]
    norm_cast
  rw [coeff_orbitLog (intCast_pos hd) (tendsto_intCast hfin), finsum_curry _
    (finite_support_ite_succ_nsmul_eq (intCast_pos hd) (tendsto_intCast hfin) _ _)]
  congr 1
  exact finsum_congr fun i => by
    simp only [hcast]
    exact finsum_succ_mul_eq (d i) m (hd i) (ε i)

/-- **The univariate orbit logarithm has integral numerators.** For `m ≠ 0`, `m` times the
coefficient of `t^m` in the orbit logarithm of orbits of positive integer periods `d i` is the
integer `∑_{d i ∣ m} d i ε i (m / d i)`. For the periodic orbits of a map, when the `i`-th
orbit has minimal period `d i`, distinct indices give distinct orbits, and `ε i k` is the
Lefschetz sign of the `k`-th iterate of the `i`-th orbit, this is the signed count of the fixed
points of the `m`-th iterate. -/
theorem natCast_mul_coeff_orbitLog_natCast (hd : ∀ i, 0 < d i) (hfin : Tendsto d cofinite atTop)
    (ε : ι → ℕ → ℤ) {m : ℕ} (hm : m ≠ 0) :
    (m : K) * (orbitLog K (Int.castAddHom ℝ) (fun i => (d i : ℤ)) ε).coeff (m : ℤ) =
      ((∑ᶠ i, if d i ∣ m then (d i : ℤ) * ε i (m / d i) else 0 : ℤ) : K) := by
  -- Only the finitely many orbits of period at most `m` contribute.
  have hfin' : {i | d i ≤ m}.Finite := by
    simpa using eventually_cofinite.1 (hfin.eventually_gt_atTop m)
  have hsupp :
      (Function.support fun i => if d i ∣ m then (d i : ℤ) * ε i (m / d i) else 0).Finite :=
    hfin'.subset (Function.support_subset_iff'.2 fun _ hi =>
      ite_eq_right fun h => hi (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h))
  have hcast := map_finsum (Int.castRingHom ℚ) hsupp
  simp only [eq_intCast] at hcast
  rw [coeff_orbitLog_natCast hd hfin, ← map_natCast (algebraMap ℚ K), ← _root_.map_mul,
    mul_finsum, ← map_intCast (algebraMap ℚ K), hcast]
  congr 1
  refine finsum_congr fun i => ?_
  split_ifs with hdvd
  · obtain ⟨j, rfl⟩ := hdvd
    have hj : (j : ℚ) ≠ 0 := by
      rintro h
      exact hm (by simp [Nat.cast_eq_zero.1 h])
    rw [Nat.mul_div_cancel_left j (hd i)]
    push_cast
    field_simp
  · simp

end TauCeti.NovikovSeries
