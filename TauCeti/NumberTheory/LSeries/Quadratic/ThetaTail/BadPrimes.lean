/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic
public import TauCeti.NumberTheory.LSeries.Quadratic.TwistSelection
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive
import TauCeti.NumberTheory.LSeries.Quadratic.TailComparison
import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.ZeroDetection

/-!
# Detecting primes with a zero of a quadratic twist

A prime in a residue class with a twist zero can be detected by a large Jacobi theta tail,
using the primitive character inducing the original base character. The uniform detection
threshold applies to the same set of primes as the density-to-selection theorem. A bound on
summed tails can then be used to count these primes.

This is the zero-detection step of `New.zero_density_quadTwist` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
(revision `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open Filter DirichletCharacter
open scoped Nat

namespace TauCeti

/-- At sufficiently large scale `T`, every prime `d` in the class with a quadratic twist zero
in the box, and with `q * d ≤ T²`, has a Jacobi theta tail larger than `T^(2δ)` for one of the
primitive characters inducing a character modulo `q`, and one of the two parities. -/
theorem eventually_exists_lt_thetaTail_of_mem_quadraticTwistBadPrimes
    {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : ∀ d : ℕ, d.Prime → (d : ZMod q) = a → d % 8 = 7 ∧ q.Coprime d)
    (H : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ d ∈ quadraticTwistBadPrimes a (1 / 2 + 9 * δ) H,
      (q : ℝ) * d ≤ T ^ 2 → ∃ (χ : DirichletCharacter ℂ q) (j : Fin 2),
        T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j
          (fun n ↦ χ.primitiveCharacter n * (jacobiSym (-(d : ℤ)) (ordCompl[2] n) : ℂ)) T := by
  have h := Filter.eventually_all.mpr fun j : Fin 2 ↦
    eventually_rpow_lt_quadraticTwistGaussianThetaTailIntegral j H hδ
  filter_upwards [h] with T hT d hd hqd
  obtain ⟨hda, hp, χ, s, hs, hH, hz⟩ := mem_quadraticTwistBadPrimes_iff.mp hd
  obtain ⟨hmod, hcop⟩ := ha d hp hda
  let : Fact d.Prime := ⟨hp⟩
  let : NeZero d := ⟨hp.ne_zero⟩
  let : NeZero (χ.conductor.lcm d) := ⟨Nat.lcm_ne_zero χ.conductor_ne_zero hp.ne_zero⟩
  let : NeZero (χ.conductor * d) := ⟨mul_ne_zero χ.conductor_ne_zero hp.ne_zero⟩
  have hodd : d ≠ 2 := by omega
  have hcop' := hcop.coprime_dvd_left χ.conductor_dvd_level
  have hψ := χ.primitiveCharacter.legendreTwist_ne_one d hodd hcop'
  have hn : χ.primitiveCharacter.mul (jacobiChar ℂ d) ≠ 1 := by
    intro he
    exact hψ (by rw [legendreTwist_eq_changeLevel_mul_jacobiChar, he, map_one])
  have hre : s.re ≠ 0 := by linarith
  have hz' : (χ.primitiveCharacter.legendreTwist d).LFunction s = 0 := by
    rw [legendreTwist_eq_changeLevel_mul_jacobiChar,
      LFunction_changeLevel_eq_zero_iff _ _ hre (.inl hn)]
    exact (χ.LFunction_mul_primitiveCharacter_eq_zero_iff _ hre (.inl hn)).mp hz
  have hlevel : ((χ.conductor * d : ℕ) : ℝ) ≤ T ^ 2 := by
    rw [Nat.cast_mul]
    exact hqd.trans' (mul_le_mul_of_nonneg_right (by exact_mod_cast χ.conductor_le_level)
      (by positivity))
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, χ.primitiveCharacter.legendreTwist d (-1) = (-1) ^ j.val := by
    rcases (χ.primitiveCharacter.legendreTwist d).even_or_odd with heven | hodd'
    · exact ⟨0, by simpa [DirichletCharacter.Even] using heven⟩
    · exact ⟨1, by simpa [DirichletCharacter.Odd] using hodd'⟩
  have hj' := hT j (χ.primitiveCharacter_isPrimitive.legendreTwist hodd hcop')
    hψ hj hlevel hs hH hz'
  exact ⟨χ, j, (χ.primitiveCharacter.quadraticTwistGaussianThetaTailIntegral_legendreTwist
    hmod j T) ▸ hj'⟩

end TauCeti
