/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Primes of good reduction of a rational Weierstrass curve

For a Weierstrass curve `E` over `ℚ` and a prime `p`, `E` has good reduction at `p` when the
minimal equation of `E` over `ℚ_p` reduces to a nonsingular curve over `𝔽_p`. This file defines
that predicate and the finite sets of primes `p ≤ x` at which it holds, the ranges over which
prime-indexed averages such as those of the Sato–Tate theorem are taken.

The minimal equation is the one chosen by Mathlib (`WeierstrassCurve.minimal`); good reduction
does not depend on that choice, nor on the Weierstrass presentation of `E` over `ℚ`.

## Main definitions

* `WeierstrassCurve.HasGoodReductionAt E p`: the minimal equation of `E` over `ℚ_p` has good
  reduction.
* `WeierstrassCurve.goodReductionPrimes E x`: the finite set of primes `p ≤ x` of good reduction.

## Main results

* `WeierstrassCurve.mem_goodReductionPrimes`: membership is `p ≤ x` together with good reduction.
* `WeierstrassCurve.goodReductionPrimes_mono`, `WeierstrassCurve.goodReductionPrimes_inter` and
  `WeierstrassCurve.iUnion_goodReductionPrimes`: the sets increase with the bound, meet at the
  minimum of the bounds, and exhaust the good primes.
* `WeierstrassCurve.hasGoodReductionAt_smul` and `WeierstrassCurve.goodReductionPrimes_smul`:
  good reduction depends only on the isomorphism class over `ℚ`.
* `WeierstrassCurve.hasGoodReductionAt_baseChange_iff_not_dvd`: for an integral equation whose
  discriminant is not divisible by `p ^ 12` (hence minimal at `p`), good reduction at `p` means
  that `p` does not divide the discriminant.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1.
-/

public section

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ)

/-- A Weierstrass curve `E` over `ℚ` **has good reduction at the prime `p`** when the minimal
equation of `E` over `ℚ_p` reduces to a nonsingular curve over `𝔽_p`. This tests the minimal
equation, not the given one: a nonminimal equation may have singular reduction at a prime of
good reduction. -/
def HasGoodReductionAt (p : Nat.Primes) : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]

/-- The defining property of `HasGoodReductionAt`. -/
theorem hasGoodReductionAt_iff {p : Nat.Primes} :
    E.HasGoodReductionAt p ↔ ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p] :=
  Iff.rfl

/-- **Good reduction is a property of the curve**: isomorphic equations over `ℚ` have good
reduction at the same primes. No ellipticity is needed. -/
@[simp]
theorem hasGoodReductionAt_smul (C : VariableChange ℚ) {p : Nat.Primes} :
    (C • E).HasGoodReductionAt p ↔ E.HasGoodReductionAt p := by
  rw [hasGoodReductionAt_iff, hasGoodReductionAt_iff, ← baseChange_smul_baseChange,
    hasGoodReduction_minimal_smul_iff]

/-- The finite set of **primes `p ≤ x` at which `E` has good reduction**, the range over which
the Frobenius angles of `E` are averaged in the Sato–Tate theorem. -/
noncomputable def goodReductionPrimes (x : ℕ) : Finset Nat.Primes := by
  classical
  exact ((Finset.range (x + 1)).subtype Nat.Prime).filter E.HasGoodReductionAt

/-- A prime lies in `goodReductionPrimes E x` exactly when it is at most `x` and `E` has good
reduction there. -/
@[simp]
theorem mem_goodReductionPrimes {x : ℕ} {p : Nat.Primes} :
    p ∈ E.goodReductionPrimes x ↔ (p : ℕ) ≤ x ∧ E.HasGoodReductionAt p := by
  classical
  exact Finset.mem_filter.trans
    (and_congr_left' (Finset.mem_subtype.trans (Finset.mem_range.trans Nat.lt_succ_iff)))

/-- The sets of good primes grow with the bound. -/
theorem goodReductionPrimes_mono : Monotone E.goodReductionPrimes := fun _ _ hxy _ hp ↦ by
  rw [mem_goodReductionPrimes] at hp ⊢
  exact ⟨hp.1.trans hxy, hp.2⟩

/-- The good primes up to `x` and up to `y` have in common the good primes up to `min x y`. -/
@[simp]
theorem goodReductionPrimes_inter (x y : ℕ) :
    E.goodReductionPrimes x ∩ E.goodReductionPrimes y = E.goodReductionPrimes (min x y) := by
  ext p
  simp only [Finset.mem_inter, mem_goodReductionPrimes, le_min_iff]
  tauto

/-- Below `2` there are no primes, so no good primes. -/
@[simp]
theorem goodReductionPrimes_eq_empty {x : ℕ} (hx : x < 2) : E.goodReductionPrimes x = ∅ := by
  ext p
  simp only [mem_goodReductionPrimes, Finset.notMem_empty, iff_false, not_and]
  exact fun hpx ↦ absurd (hpx.trans_lt hx) p.prop.two_le.not_gt

/-- **Removing the bound recovers the good primes**: the sets `goodReductionPrimes E x` exhaust
the primes of good reduction of `E`. -/
theorem iUnion_goodReductionPrimes :
    ⋃ x, (E.goodReductionPrimes x : Set Nat.Primes) = {p | E.HasGoodReductionAt p} := by
  ext p
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_goodReductionPrimes, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, h⟩ ↦ h.2, fun h ↦ ⟨p, le_rfl, h⟩⟩

/-- **The sets of good primes depend only on the isomorphism class of `E` over `ℚ`.** -/
@[simp]
theorem goodReductionPrimes_smul (C : VariableChange ℚ) (x : ℕ) :
    (C • E).goodReductionPrimes x = E.goodReductionPrimes x := by
  ext p
  simp

/-! ### Good reduction of an integral equation -/

section Integral

variable (W : WeierstrassCurve ℤ) (p : Nat.Primes)

/-- **An integral equation, read over `ℚ_p`, has good reduction over `ℤ_p` exactly when `p` does
not divide its discriminant.** -/
theorem hasGoodReduction_baseChange_padic_iff :
    (W.baseChange ℚ_[p]).HasGoodReduction ℤ_[p] ↔ ¬ (p : ℤ) ∣ W.Δ := by
  rw [hasGoodReduction_baseChange_iff_isUnit_algebraMap_Δ, algebraMap_int_eq, eq_intCast,
    PadicInt.isUnit_intCast_iff]

/-- **An integral equation has good reduction at every prime not dividing its discriminant.** -/
theorem hasGoodReductionAt_baseChange_of_not_dvd (h : ¬ (p : ℤ) ∣ W.Δ) :
    (W.baseChange ℚ).HasGoodReductionAt p := by
  rw [hasGoodReductionAt_iff, baseChange_baseChange]
  exact HasGoodReduction.hasGoodReduction_minimal ℤ_[p]
    ((W.hasGoodReduction_baseChange_padic_iff p).2 h)

/-- **For an integral equation whose discriminant is not divisible by `p ^ 12` (hence minimal at
`p`), good reduction at `p` means that `p` does not divide the discriminant.** The hypothesis
`¬ p ^ 12 ∣ Δ` is a sufficient condition for minimality at `p`; without some such condition, an
equation such as `y² = x³ - p⁴ x + p⁶` can have good reduction at `p` while `p` divides its
discriminant. -/
theorem hasGoodReductionAt_baseChange_iff_not_dvd (h12 : ¬ (p : ℤ) ^ 12 ∣ W.Δ) :
    (W.baseChange ℚ).HasGoodReductionAt p ↔ ¬ (p : ℤ) ∣ W.Δ := by
  refine ⟨fun h ↦ ?_, W.hasGoodReductionAt_baseChange_of_not_dvd p⟩
  rw [hasGoodReductionAt_iff, baseChange_baseChange] at h
  have : IsMinimal ℤ_[p] (W.baseChange ℚ_[p]) := by
    rw [← W.baseChange_baseChange (A := ℤ_[p]) ℚ_[p]]
    exact isMinimal_baseChange_of_not_pow_twelve_dvd_Δ ℤ_[p] _ PadicInt.irreducible_p (by
      rwa [baseChange, map_Δ, algebraMap_int_eq, eq_intCast, PadicInt.pow_p_dvd_int_iff])
  obtain ⟨C, hC⟩ := (W.baseChange ℚ_[p]).exists_smul_eq_minimal ℤ_[p]
  exact (W.hasGoodReduction_baseChange_padic_iff p).1
    ⟨(valuation_Δ_eq_of_isMinimal_smul ℤ_[p] C hC).symm.trans h.goodReduction⟩

/-! The curve `y² = x³ - x + 1`, with discriminant `-368 = -2⁴ · 23`, has good reduction at `5`
but not at `23`, where its equation is minimal since `23¹²` does not divide `-368`. -/

example : ((⟨0, 0, 0, -1, 1⟩ : WeierstrassCurve ℤ).baseChange ℚ).HasGoodReductionAt
    ⟨5, by norm_num⟩ :=
  hasGoodReductionAt_baseChange_of_not_dvd _ _ (by norm_num [Δ, b₂, b₄, b₆, b₈])

example : ⟨5, by norm_num⟩ ∈
    ((⟨0, 0, 0, -1, 1⟩ : WeierstrassCurve ℤ).baseChange ℚ).goodReductionPrimes 5 :=
  mem_goodReductionPrimes _ |>.2
    ⟨le_rfl, hasGoodReductionAt_baseChange_of_not_dvd _ _ (by norm_num [Δ, b₂, b₄, b₆, b₈])⟩

example : ¬ ((⟨0, 0, 0, -1, 1⟩ : WeierstrassCurve ℤ).baseChange ℚ).HasGoodReductionAt
    ⟨23, by norm_num⟩ :=
  (hasGoodReductionAt_baseChange_iff_not_dvd _ _ (by norm_num [Δ, b₂, b₄, b₆, b₈])).not.2
    (by norm_num [Δ, b₂, b₄, b₆, b₈])

end Integral

end WeierstrassCurve
