/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Supernatural
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The supernatural invariant of a sequence of matrix sizes

A UHF algebra is presented as an inductive limit of matrix algebras `M_{d₀} → M_{d₁} → ⋯`
with unital connecting maps, so that each size `dₙ` divides the next. Its supernatural invariant
is the supremum of the sizes in the divisibility order, `supernaturalOfSizes d = ⨆ₙ ofNat dₙ`
(Glimm, Definition 1.3). This file defines it and computes it in the standard examples.

## Main definitions

* `TauCeti.Supernatural.supernaturalOfSizes d`: the supremum `⨆ₙ ofNat (d n)`.

## Main statements

* `TauCeti.Supernatural.supernaturalOfSizes_le_iff`: `supernaturalOfSizes d ≤ ν` exactly when
  every size divides `ν`.
* `TauCeti.Supernatural.supernaturalOfSizes_const`, `supernaturalOfSizes_prime_pow` and
  `supernaturalOfSizes_factorial`: constant sizes `d` give `ofNat d`, sizes `pⁿ` give `p^∞`, and
  sizes `n!` give `⊤`.

## References

* J. G. Glimm, *On a certain class of operator algebras*, Trans. Amer. Math. Soc. 95 (1960),
  318–340, Definition 1.3.
-/

public section

namespace TauCeti

namespace Supernatural

/-- The supernatural invariant of a sequence of matrix sizes: the supremum, in the divisibility
order, of the sizes. -/
noncomputable def supernaturalOfSizes (d : ℕ → ℕ+) : Supernatural :=
  ⨆ n, ofNat (d n)

/-- The supernatural invariant is the supremum of the sizes. -/
theorem supernaturalOfSizes_def (d : ℕ → ℕ+) : supernaturalOfSizes d = ⨆ n, ofNat (d n) :=
  (rfl)

/-- The exponent of `p` in the supernatural invariant is the supremum of its exponents in the
sizes. -/
@[simp]
theorem supernaturalOfSizes_apply (d : ℕ → ℕ+) (p : Nat.Primes) :
    supernaturalOfSizes d p = ⨆ n, ofNat (d n) p :=
  iSup_apply _ p

/-- Every size divides the supernatural invariant. -/
theorem ofNat_le_supernaturalOfSizes (d : ℕ → ℕ+) (n : ℕ) :
    ofNat (d n) ≤ supernaturalOfSizes d :=
  le_iSup (fun n ↦ ofNat (d n)) n

/-- The supernatural invariant divides `ν` exactly when every size does. -/
@[simp]
theorem supernaturalOfSizes_le_iff {d : ℕ → ℕ+} {ν : Supernatural} :
    supernaturalOfSizes d ≤ ν ↔ ∀ n, ofNat (d n) ≤ ν :=
  iSup_le_iff

/-- **Check.** Constant sizes `d` have invariant `ofNat d`. -/
@[simp]
theorem supernaturalOfSizes_const (d : ℕ+) : supernaturalOfSizes (fun _ ↦ d) = ofNat d :=
  iSup_const

/-- **Check.** Sizes `pⁿ` have invariant `p^∞`. -/
theorem supernaturalOfSizes_prime_pow (p : Nat.Primes) :
    supernaturalOfSizes (fun n ↦ (p : ℕ+) ^ n) = primePower p ⊤ := by
  refine (supernaturalOfSizes_def _).trans ?_
  simp only [ofNat_prime_pow]
  ext q
  rw [iSup_apply]
  by_cases hq : q = p
  · subst hq
    simp only [primePower_apply_self]
    exact ENat.iSup_natCast_eq_top.2 (fun ⟨b, hb⟩ ↦ by
      have := hb ⟨b + 1, rfl⟩
      simp at this)
  · simp [primePower_apply_of_ne hq]

/-- **Check.** Sizes `n!` have invariant `⊤`, the invariant of the universal UHF algebra. -/
theorem supernaturalOfSizes_factorial :
    supernaturalOfSizes (fun n ↦ ⟨n.factorial, n.factorial_pos⟩) = ⊤ := by
  refine (supernaturalOfSizes_def _).trans ?_
  refine eq_top_iff.2 (le_iff.2 fun p ↦ ?_)
  rw [top_apply, iSup_apply]
  -- `p ^ k ∣ (p ^ k)!`, so the exponent of `p` in `(p ^ k)!` is at least `k`.
  refine ENat.forall_natCast_le_iff_le.1 fun k _ ↦ le_iSup_of_le ((p : ℕ+) ^ k : ℕ+) ?_
  exact (ofNat_prime_pow_le_iff p k _).1
    (ofNat_le_ofNat_iff.2 (PNat.dvd_iff.2 (Nat.dvd_factorial ((p : ℕ+) ^ k).pos le_rfl)))

end Supernatural

end TauCeti
