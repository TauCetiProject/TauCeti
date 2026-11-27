/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroFree
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic

/-!
# Reduction to the moduli of the one-sided prime sum bound

At each positive multiple `q₀` of `18480`, the designated class `q₀ / 2 - 1` is reduced
(`coprime_div_two_sub_one_of_dvd`) and congruent to `7` modulo `8` (`div_two_sub_one_modEq_seven`).
Dirichlet's theorem gives arbitrarily large primes in this class, so the possible parameter moduli
are exactly the positive multiples of `18480`.

The reduction `forall_zeroFreeRightOf_LFunction_iff_forall_parameters` shows that it is enough
to establish pointwise nonvanishing off `s = 1` at these moduli, for every open half-plane with
threshold strictly greater than `1/2`. The proof uses level change without losing information
about zeros in the right half-plane.

The choice of moduli follows `New.grh` in `New/Reduction/OneSidedBound.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

namespace TauCeti.OneSidedBound

open DirichletCharacter

/-- Every positive multiple of `18480` occurs as the modulus of parameters with prime `d`
larger than any specified bound. -/
theorem Parameters.exists_q₀_eq_and_lt_d {q₀ : ℕ} (hq₀ : q₀ ≠ 0) (hq : 18480 ∣ q₀) (B : ℕ) :
    ∃ P : Parameters, P.q₀ = q₀ ∧ B < P.d := by
  obtain ⟨d, hd, hprime, hmod⟩ := Filter.frequently_atTop'.mp
    (Nat.frequently_atTop_prime_and_modEq hq₀ (coprime_div_two_sub_one_of_dvd hq₀ hq)) B
  exact ⟨Parameters.ofModEq hq hprime hmod, Parameters.ofModEq_q₀ hq hprime hmod,
    (Parameters.ofModEq_d hq hprime hmod).symm ▸ hd⟩

/-- To exclude zeros right of `1/2` for all Dirichlet characters, it suffices to prove
nonvanishing away from `1` on `Re s > β` for every `β > 1/2` and every parameter modulus.
The statement on the left concerns meromorphic orders, so the principal pole at `1` is allowed. -/
theorem forall_zeroFreeRightOf_LFunction_iff_forall_parameters :
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ZeroFreeRightOf (1 / 2) χ.LFunction) ↔
      ∀ (P : Parameters) (β : ℝ), 1 / 2 < β → ∀ (χ : DirichletCharacter ℂ P.q₀) {s : ℂ},
        β < s.re → s ≠ 1 → χ.LFunction s ≠ 0 := by
  constructor
  · intro h P β hβ χ s hs hs₁ hz
    exact (zeroFreeRightOf_iff.mp (h P.q₀ χ) s (hβ.trans hs)).not_gt
      (χ.meromorphicOrderAt_LFunction_pos_iff.mpr ⟨hz, .inl hs₁⟩)
  · intro h N _ χ
    obtain ⟨P, hP, _⟩ := Parameters.exists_q₀_eq_and_lt_d (q₀ := 18480 * N)
      (Nat.mul_ne_zero (by decide) (NeZero.ne N)) (dvd_mul_right _ _) 0
    have hd : N ∣ P.q₀ := hP.symm ▸ dvd_mul_left _ _
    apply zeroFreeRightOf_iff_forall_gt.mpr
    intro β hβ
    have hβ₀ : 0 ≤ β := by linarith
    apply (χ.zeroFreeRightOf_LFunction_changeLevel_iff hd hβ₀).mp
    rw [zeroFreeRightOf_iff]
    intro s hs
    refine not_lt.mp fun hpos ↦ ?_
    let χ' := χ.changeLevel hd
    obtain ⟨hz, hguard⟩ := χ'.meromorphicOrderAt_LFunction_pos_iff.mp hpos
    have hs₁ : s ≠ 1 := fun heq ↦
      (χ'.LFunction_ne_zero_of_one_le_re hguard.symm (by simp [heq])) hz
    exact h P β hβ χ' hs hs₁ hz

end TauCeti.OneSidedBound
