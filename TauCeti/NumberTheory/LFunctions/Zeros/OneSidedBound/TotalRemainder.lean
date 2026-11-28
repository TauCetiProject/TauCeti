/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Place.OfInt
import TauCeti.Data.ZMod.ReductionFiber
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.PlaceAverage
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TwoCutoffs

/-!
# The signed prime remainder from two cutoffs

Sum the capped prime weights over the cyclotomic places of base class `1`. The cutoff is
`x₁` unless a prime-power translate lands in the exceptional set of base class `-1`, where
it is `x`. Subtracting the logarithmic main term leaves the signed prime remainder at `x₁`
and a difference of signed remainders in the progression `1 mod q₀`. This converts a bound
on the aggregate from the covolume comparison into a bound at the short cutoff `x`.

The normalizations are those of `New.Data.totalRemainder_eq` and `New.Data.primeRemainder_le`
in `grh/src/New/Reduction/PrimeSums.lean` and `grh/src/New/Reduction/OneSidedBound.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`, respectively.
-/

public section

open Finset
open Real (log)

namespace TauCeti.OneSidedBound.Parameters

/-- The excess of the capped prime sums over their logarithmic main term, summed over
cyclotomic labels of base class `1`. The weight is `a / x` on `B` and `a / x₁` elsewhere;
the sum uses indices up to `N` and order `a`. -/
noncomputable def totalRemainder (P : Parameters) (s : ℕ) (B : Finset (ZMod (P.q₁ s))ˣ)
    (N : ℕ) (a x x₁ : ℝ) : ℝ :=
  let π := ZMod.unitsMap (P.q₀_dvd_q₁ s)
  let κ := fun τ ↦ if τ ∈ B then a / x else a / x₁
  ∑ τ ∈ univ.filter (fun τ ↦ π τ = 1),
    ((∑ n ∈ Icc 1 N, primeWeight P.d 1 n * max (a / n - κ (P.placeOfInt s (-(n : ℤ)) * τ)) 0) -
      a * (log a - (∑ σ, log (κ σ)) / Fintype.card (ZMod (P.q₁ s))ˣ + (logDerivMean P.d 1 1).re))

/-- Expand the total remainder as the place sum with the two cutoff weights and the
modulus-one logarithmic constant. -/
theorem totalRemainder_def (P : Parameters) (s : ℕ) (B : Finset (ZMod (P.q₁ s))ˣ)
    (N : ℕ) (a x x₁ : ℝ) :
    let π := ZMod.unitsMap (P.q₀_dvd_q₁ s)
    let κ := fun τ ↦ if τ ∈ B then a / x else a / x₁
    P.totalRemainder s B N a x x₁ = ∑ τ ∈ univ.filter (fun τ ↦ π τ = 1),
      ((∑ n ∈ Icc 1 N,
        primeWeight P.d 1 n * max (a / n - κ (P.placeOfInt s (-(n : ℤ)) * τ)) 0) -
        a * (log a - (∑ σ, log (κ σ)) / Fintype.card (ZMod (P.q₁ s))ˣ +
          (logDerivMean P.d 1 1).re)) := (rfl)

/-- The aggregate is a sum of the modulus-one remainder at `x₁` and the difference of
base-progression remainders at the two cutoffs, with multiplicities determined by the
identity fiber and the exceptional set. -/
theorem totalRemainder_eq_primeRemainder (P : Parameters) {s N : ℕ}
    {B : Finset (ZMod (P.q₁ s))ˣ} {a x x₁ : ℝ}
    (hB : ∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1)
    (ha : 0 ≤ a) (hx : 0 < x) (hx₁ : 0 < x₁) (hN : ⌊max x x₁⌋₊ ≤ N) :
    let A := univ.filter fun τ ↦ ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1
    P.totalRemainder s B N a x x₁ =
      a * ((B.card : ℝ) * (primeRemainder P.d P.q₀ x - primeRemainder P.d P.q₀ x₁) +
        (A.card : ℝ) * primeRemainder P.d 1 x₁) := by
  dsimp only
  have hre (q : ℕ) [NeZero q] (y : ℝ) := congrArg Complex.re
    (ofReal_primeRemainder_eq (d := P.d) (q := q) y)
  simp only [Complex.ofReal_re, Complex.sub_re, ← Complex.ofReal_natCast,
    Complex.div_ofReal_re] at hre
  have hre₁ (y : ℝ) := by simpa only [Nat.totient_one, Nat.cast_one, div_one] using hre 1 y
  have hweight (n : ℕ) :
      (if ZMod.unitsMap (P.q₀_dvd_q₁ s) (P.placeOfInt s (-(n : ℤ))) = -1 then
        (primeWeight P.d 1 n : ℂ) else 0) = (primeWeight P.d P.q₀ n : ℂ) := by
    rw [P.primeWeight_eq_ite_unitsMap_placeOfInt s n, apply_ite Complex.ofReal, Complex.ofReal_zero]
  have h := (ZMod.unitsMap (P.q₀_dvd_q₁ s)).sum_sub_log_eq_rieszSum_sub_log
    (ZMod.unitsMap_surjective _) B hB (fun n ↦ P.placeOfInt s (-(n : ℤ))) (primeWeight P.d 1)
    (logDerivMean P.d 1 1).re (logDerivMean P.d P.q₀ 1).re ha hx hx₁ hN
  simpa only [totalRemainder_def, hweight, ZMod.card_units_eq_totient, ← hre, ← hre₁] using h

/-- An upper bound on the scaled total remainder gives a bound at the short cutoff.
The cardinality inequality is the only sparsity input: it pays for the ratio of the
base-class-one labels to the exceptional labels. -/
theorem primeRemainder_le_of_totalRemainder_bound (P : Parameters) {s N : ℕ}
    {B : Finset (ZMod (P.q₁ s))ˣ} {a x x₁ m L : ℝ}
    (hB : ∀ τ ∈ B, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1)
    (ha : 0 < a) (hx : 0 < x) (hx₁ : 0 < x₁) (hN : ⌊max x x₁⌋₊ ≤ N) (hm : 0 < m)
    (hsize : ((univ.filter fun τ ↦ ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1).card : ℝ) ≤ B.card * L)
    (hmain : m * P.totalRemainder s B N a x x₁ ≤ (Fintype.card (ZMod (P.q₁ s))ˣ : ℝ) * a * L ^ 5) :
    primeRemainder P.d P.q₀ x ≤ (P.q₀.totient : ℝ) * L ^ 6 / m +
      |primeRemainder P.d P.q₀ x₁| + L * |primeRemainder P.d 1 x₁| := by
  let π := ZMod.unitsMap (P.q₀_dvd_q₁ s)
  let A := univ.filter fun τ ↦ π τ = 1
  have hA : 0 < A.card := Finset.card_pos.mpr ⟨1, by simp [A]⟩
  have hBpos : 0 < (B.card : ℝ) := by
    by_contra! h
    have hz : (B.card : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    have hp : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA
    rw [hz, zero_mul] at hsize
    exact hp.not_ge hsize
  have hker : Nat.card π.ker = A.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr fun u _ ↦ π.mem_ker)
  have hcard := ZMod.card_ker_unitsMap_mul_totient (P.q₀_dvd_q₁ s)
  rw [hker, ← ZMod.card_units_eq_totient (P.q₁ s), Nat.mul_comm] at hcard
  have hcard' : (Fintype.card (ZMod (P.q₁ s))ˣ : ℝ) = (P.q₀.totient : ℝ) * A.card := by
    exact_mod_cast hcard.symm
  rw [hcard'] at hmain
  exact primeRemainder_le_of_two_cutoff_identity ha hm (Nat.cast_nonneg A.card) hBpos
    (Nat.cast_nonneg P.q₀.totient) hsize
    (P.totalRemainder_eq_primeRemainder hB ha.le hx hx₁ hN) hmain

end TauCeti.OneSidedBound.Parameters
