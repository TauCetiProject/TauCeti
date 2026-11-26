/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LegendreTwist
public import TauCeti.NumberTheory.LSeries.Quadratic.TwistSelection

/-!
# Bad-prime counts for Legendre twists

A prime in a reduced residue class is coprime to the progression modulus. Consequently, the
bad-prime set defined using least-common-multiple products of Jacobi characters contains exactly
the primes of that class for which a Legendre twist at the product level has a zero in the box.
This connects the count used to select primes to the twists used in signed sums of Dirichlet
logarithmic derivatives.

The box and its use in selecting an auxiliary prime follow `New.zero_density_quadTwist` and
`New.exists_entireL_quadTwist_ne_zero` in `grh/src/Lib/Analytic/QuadraticTwist.lean` of
lsernau/grh-lean (revision `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open DirichletCharacter Filter Asymptotics

namespace TauCeti

/-- In a reduced residue class the bad-prime set can be tested using the Legendre twist at
level `q * d`. This form gives the same count as the Jacobi-character definition. -/
theorem mem_quadraticTwistBadPrimes_iff_legendreTwist {q d : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) {β H : ℝ} :
    d ∈ quadraticTwistBadPrimes a β H ↔ (d : ZMod q) = a ∧ ∃ hd : d.Prime,
      letI : Fact d.Prime := ⟨hd⟩
      ∃ (χ : DirichletCharacter ℂ q) (s : ℂ),
        β ≤ s.re ∧ |s.im| ≤ H ∧ (χ.legendreTwist d).LFunction s = 0 := by
  rw [mem_quadraticTwistBadPrimes_iff]
  apply and_congr_right
  intro heq
  have hqd : q.Coprime d := ((ZMod.isUnit_iff_coprime d q).mp (heq ▸ ha)).symm
  refine exists_congr fun hd ↦ ?_
  let _ : Fact d.Prime := ⟨hd⟩
  simp only [LFunction_mul_jacobiChar_eq_legendreTwist _ hqd]

/-- If the bad-prime count in a reduced residue class has a power saving, then above any
cutoff there is an odd prime in that class for which all pole-removed Legendre-twisted
L-functions are nonzero in the box. In particular their logarithmic derivatives are analytic
at every point of the box. -/
theorem exists_prime_entireLFunction_legendreTwist_ne_zero_of_density
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {β H B : ℝ} (hB : B < 1)
    (hcount : (fun x : ℝ ↦ ({d ∈ quadraticTwistBadPrimes a β H | (d : ℝ) ≤ x}.ncard : ℝ))
      =O[atTop] (· ^ B)) (N : ℕ) :
    ∃ d > N, ∃ hd : d.Prime, (d : ZMod q) = a ∧ Odd d ∧
      letI : Fact d.Prime := ⟨hd⟩
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
        β ≤ s.re → |s.im| ≤ H → (χ.legendreTwist d).entireLFunction s ≠ 0 := by
  obtain ⟨d, hdN, hd, hda, hfree⟩ :=
    exists_prime_quad_twist_zero_free_of_density ha hB hcount (max N 2)
  have hd₂ : 2 < d := lt_of_le_of_lt (le_max_right N 2) hdN
  have hqd : q.Coprime d := ((ZMod.isUnit_iff_coprime d q).mp (hda ▸ ha)).symm
  let _ : Fact d.Prime := ⟨hd⟩
  refine ⟨d, lt_of_le_of_lt (le_max_left N 2) hdN, hd, hda, hd.odd_of_ne_two hd₂.ne', ?_⟩
  intro χ s hs him
  have h := hfree χ s hs him
  rw [LFunction_mul_jacobiChar_eq_legendreTwist χ hqd] at h
  simpa only [entireLFunction_of_ne_one (χ.legendreTwist_ne_one d hd₂.ne' hqd)] using h

end TauCeti
