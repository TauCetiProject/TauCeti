/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Typical

/-!
# Leading terms of typical curves

Monomial curves in prime-power degrees on a typical formal group are typical. Conversely,
over a ring in which all other primes are units, a typical curve cannot have its first
nonzero coefficient in a degree outside the prime powers. These facts support recursive
expansions of typical curves, including the Araki expansion of the multiplication series.
-/

public section

namespace FormalGroup

variable {R : Type*} [CommRing R]

private theorem monomialCurve_eq_verschiebungCurve_homothetyCurve (F : FormalGroup R)
    (n : ℕ) (hn : n ≠ 0) (c : R) :
    F.monomialCurve n hn c =
      F.verschiebungCurve n hn (F.homothetyCurve c F.tautologicalCurve) := by
  apply Curve.ext
  simp [PowerSeries.rescale_X, PowerSeries.expand_C, PowerSeries.smul_eq_C_mul]

/-- A monomial curve of prime-power degree on a `p`-typical law is `p`-typical. -/
theorem IsPTypical.monomialCurve_pow {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) (hp : p.Prime) (n : ℕ) (c : R) :
    (F.monomialCurve (p ^ n) (pow_ne_zero n hp.ne_zero) c).IsPTypical p := by
  rw [monomialCurve_eq_verschiebungCurve_homothetyCurve]
  exact (hF.tautologicalCurve.homothetyCurve c).verschiebungCurve_pow hp n

/-- If a typical curve vanishes below a degree which is not a power of `p`, it
also vanishes in that degree, provided every other prime is invertible. -/
theorem Curve.IsPTypical.coeff_eq_zero_of_forall_lt {F : FormalGroup R} [F.IsComm]
    {p : ℕ} {γ : F.Curve} (hγ : γ.IsPTypical p)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {k : ℕ}
    (hpow : ∀ n, k ≠ p ^ n) (hzero : ∀ i < k, PowerSeries.coeff i γ.toPowerSeries = 0) :
    PowerSeries.coeff k γ.toPowerSeries = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact γ.coeff_zero_toPowerSeries
  have h := F.coeff_pTypicalProjectorCurve_congr p hunit (k := k)
    (γ₁ := γ) (γ₂ := F.monomialCurve k hk (PowerSeries.coeff k γ.toPowerSeries))
    (fun i hi ↦ by
      rcases hi.eq_or_lt with rfl | hi
      · simp
      · simp [hzero i hi, PowerSeries.coeff_X_pow, hi.ne])
  rw [F.pTypicalProjectorCurve_eq_self p hunit hγ,
    monomialCurve_eq_verschiebungCurve_homothetyCurve,
    F.pTypicalProjectorCurve_verschiebungCurve_eq_zero_of_forall_ne_pow p hunit hk hpow] at h
  simpa using h

end FormalGroup
