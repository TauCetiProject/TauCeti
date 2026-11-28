/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FrobeniusRiesz.SplitRamification

/-!
# Comparing Frobenius Riesz sums with local gains

In a chain of theta lifts, each top and lift contributes a capped Riesz sum. Subtracting
local divisibility gains from their total gives a sum of primewise deficits. The prime
ramified in the quadratic subfield contributes its full Riesz term, with the single
logarithmic weight from the split-ramification formula.

The capped prime-power contributions are those of L. Alpöge's
`Formalism.LFunctionChainParameters.characterSumData.ASK`, used in
`Formalism.RankGapBounds.WeightedMeanData.Data.LoP` in the
[published formalization of the Riemann hypothesis][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Finset

namespace MonoidHom

open scoped Classical in
/-- Under split ramification, the total doubled off-kernel Riesz sum minus the logarithmic
net gain is the sum of deficits at unramified inert primes, plus the exceptional contribution
at `d`. The finite index set `s` can be the product of the tops and the lift steps; `a i`
and `w i` are their sizes and caps, with any partner translation included in `w i`.
The common cutoff `M` includes all nonzero Riesz terms. The comparison subtracts the net
local gains for primes up to `M`, with `gain p` denoting the gain after subtracting local
colength and before multiplying by `2 * log p`. -/
theorem sum_frobeniusRieszSum_sub_netGain_eq
    {N : ℕ} [NeZero N] {G K ι : Type*} [Group G] [Fintype G] [CommRing K] [IsDomain K]
    (f : (ZMod N)ˣ →* G) (q : G →* Kˣ) (hq : q * q = 1) {M d : ℕ} (hd : d.Prime)
    (g : ℕ → G) (hg : ∀ {p} (hp : p.Prime), p ≤ M → g p ∈ f.frobeniusCoset hp 1)
    {σ : G} (hI : (f.cyclotomicInertia d : Set G) = {1, σ}) (hσ : q σ ≠ 1)
    (hsplit : ∀ p ∈ Nat.primesLE M, p ≠ d → f.cyclotomicInertia p ≠ ⊥ →
      f.cyclotomicInertia p ≤ q.ker ∧ q (g p) = 1)
    (s : Finset ι) (w : ι → G → ℝ) (a : ι → ℝ)
    (hw : ∀ i ∈ s, ∀ t, q t ≠ 1 → 0 < w i t)
    (hM : ∀ i ∈ s, ∀ t, q t ≠ 1 → ⌊a i / w i t⌋₊ ≤ M)
    (gain : ℕ → ℝ)
    (hgain : ∀ p ∈ Nat.primesLE M, ¬ (f.cyclotomicInertia p = ⊥ ∧ q (g p) ≠ 1) → gain p = 0) :
    (∑ i ∈ s, 2 * f.frobeniusRieszSum (univ.filter fun t ↦ q t ≠ 1) (w i) (a i)) -
        (∑ p ∈ Nat.primesLE M, (2 * Real.log p) * gain p) =
      (∑ p ∈ Nat.primesLE M with f.cyclotomicInertia p = ⊥ ∧ q (g p) ≠ 1,
        (2 * Real.log p) * ((∑ i ∈ s, ∑ k ∈ Icc 1 (p.log M) with Odd k,
          max (a i / ((p ^ k : ℕ) : ℝ) - w i (g p ^ k)) 0) - gain p)) +
      Real.log d * ∑ i ∈ s, ∑ k ∈ Icc 1 (d.log M),
        max (a i / ((d ^ k : ℕ) : ℝ) -
          w i (if q (g d ^ k) = 1 then g d ^ k * σ else g d ^ k)) 0 := by
  have hgainSum :
      (∑ p ∈ (Nat.primesLE M).filter (fun p ↦ f.cyclotomicInertia p = ⊥ ∧ q (g p) ≠ 1),
        (2 * Real.log p) * gain p) = ∑ p ∈ Nat.primesLE M, (2 * Real.log p) * gain p :=
    sum_subset (filter_subset _ _) fun p hp hp' ↦
      mul_eq_zero_of_right _ (hgain p hp fun h ↦ hp' (mem_filter.mpr ⟨hp, h⟩))
  have hterm (i : ι) (hi : i ∈ s) :=
    f.two_mul_frobeniusRieszSum_eq_sum_of_split_ramification
      q hq hd g hg hI hσ hsplit (w i) (a i) (hw i hi) (hM i hi)
  -- Switch the order of summation before subtracting the gains prime by prime.
  rw [sum_congr rfl hterm, sum_add_distrib, sum_comm (s := s), ← mul_sum]
  rw [← hgainSum, add_sub_right_comm, ← sum_sub_distrib]
  simp only [mul_sum, mul_sub]

end MonoidHom
