/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.LargeDegree
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.CycleBounds

/-!
# Large degree at marked primes of a theta chain

For a Frobenius cycle at a marked prime, the chain length supplies a lower bound on the
logarithm of the residue size. The upper bounds on the cycle length and on the step exponent
keep the defect budget small. Together the bounds give the `IsLargeDegree` hypothesis for
the edge Hecke operator at the jet order `x * b`.

The scale comparison is that of `New.Data.isLargeDegree_of_le_card` in
`grh/src/New/UpperBound/Divisibility/MarkOperator.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) (`72fead1`).
-/

public section

open Real

namespace TauCeti.FrobeniusCycle

/-- The cutoff, chain length, rank and cycle size at a marked prime satisfy the large-degree
condition with parabolic rank `Nat.clog T.p m` and tolerance `1 / (m² f)`. The hypothesis
`m ≤ T.e * N` bounds the logarithmic residue size from below; `N ≤ f` caps the number of letters
by the number of infinite places. -/
theorem isLargeDegree_of_chain_scales {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R]
    {N : ℕ} (T : FrobeniusCycle W R N) {x x₁ b m k f : ℕ}
    (hcut : x ^ 235 ≤ x₁) (hsmall : log (x₁ : ℝ) ^ 6 ≤ log b) (hlarge : log (b : ℝ) ^ 8 ≤ x)
    (hm : x ≤ m ^ 2) (hm' : m ^ 2 ≤ 4 * x) (hk : x ^ 3 ≤ k) (hk' : k ≤ x ^ 6)
    (hf : f ≤ x ^ 12) (hN : N ≤ f) (hp : 3 ≤ T.p) (hp' : T.p ≤ x₁)
    (he : T.e ≤ Nat.clog T.p m) (hlen : m ≤ T.e * N) :
    T.IsLargeDegree k (x * b) (Nat.clog T.p m) (1 / ((m : ℝ) ^ 2 * f)) := by
  have hb : 0 < (b : ℝ) := by
    have hlog := log_pos (show 1 < (x₁ : ℝ) by exact_mod_cast (show 1 < x₁ by omega))
    have hb₀ : 0 < log (b : ℝ) := (pow_pos hlog 6).trans_le hsmall
    exact_mod_cast (show 0 < b by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hb₀)
  obtain ⟨hr, hrk, hθ, hn, hbound⟩ := OneSidedBound.frobenius_cycle_degree_bounds
    (by exact_mod_cast hcut) hb hsmall hlarge (by exact_mod_cast hm) (by exact_mod_cast hm')
    (by exact_mod_cast hk) (by exact_mod_cast hk') (by exact_mod_cast hf) hN hp
    (by exact_mod_cast hp') he hlen
  have hq : (T.q : ℝ) = (T.p : ℝ) ^ (T.e * N) := by
    rw [q_def, P_def, ← pow_mul, Nat.cast_pow]
  refine ⟨hr, hrk, hθ.1, hθ.2, ?_, ?_⟩
  · exact_mod_cast (show ((x : ℝ) * b) ^ 4 ≤ T.q by rwa [hq])
  · simpa only [hq, P_def, Nat.cast_pow, Nat.cast_mul] using hbound

end TauCeti.FrobeniusCycle
