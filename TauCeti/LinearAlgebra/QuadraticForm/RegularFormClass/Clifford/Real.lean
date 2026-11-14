/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Clifford.Basic
import TauCeti.Algebra.BrauerGroup.Quaternion
import TauCeti.Data.Nat.Choose.Lucas

/-!
# The Clifford invariant of a real sum of squares

Over any field in which two is invertible, the sum of `n` squares `n⟨1⟩ = ⟨1, …, 1⟩` has Clifford
invariant `[(-1,-1)]^C(n+1,4)` (`TauCeti.RegularFormClass.cliffordInvariant_natCast`). Over `ℝ`
the class `[(-1,-1)]` of Hamilton's quaternions has order two in the Brauer group, so the
invariant is trivial exactly when `C(n+1,4)` is even. By Lucas' theorem `C(n+1,4)` has the parity
of `⌊(n+1)/4⌋`, so the invariant is periodic of period eight in `n`: it is trivial for
`n ≡ 0, 1, 2, 7 (mod 8)` and is the class of `ℍ` for `n ≡ 3, 4, 5, 6 (mod 8)`.

For `n = 1, …, 8` this is the list `1, 1, [ℍ], [ℍ], [ℍ], [ℍ], 1, 1` of Brauer classes of the
algebras `ℝ`, `M₂(ℝ)`, `ℍ`, `M₂(ℍ)`, `M₂(ℍ)`, `M₄(ℍ)`, `M₈(ℝ)`, `M₁₆(ℝ)`: the even Clifford
algebra of `n⟨1⟩` in odd rank and its Clifford algebra in even rank. Since the Hasse invariant and
the discriminant of `n⟨1⟩` are trivial, these values test only the second correction exponent
`C(n+1,4)` of Lam's comparison of the Clifford and Hasse invariants. The worked example at the end
of the file tests the first one on `⟨-1,-1,-1⟩`.

## Main results

* `TauCeti.RegularFormClass.cliffordInvariant_natCast_eq_one_iff_real`: over `ℝ`, `c(n⟨1⟩)` is
  trivial exactly when `n ≡ 0, 1, 2, 7 (mod 8)`.
* `TauCeti.RegularFormClass.cliffordInvariant_natCast_eq_quaternionClass_iff_real`: over `ℝ`,
  `c(n⟨1⟩) = [(-1,-1)]` exactly when `n ≡ 3, 4, 5, 6 (mod 8)`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, Theorem 2.4, Definition 3.12 and Theorem 3.20.
-/

public section

namespace TauCeti

namespace RegularFormClass

open BrauerGroup

/-- Over `ℝ`, `c(n⟨1⟩) = [(-1,-1)]^k` exactly when `⌊(n+1)/4⌋ ≡ k (mod 2)`: the class of `ℍ` has
order two, and by Lucas' theorem at the prime `2` the exponent `C(n+1,4)` of
`TauCeti.RegularFormClass.cliffordInvariant_natCast` has the parity of `⌊(n+1)/4⌋`. -/
private theorem cliffordInvariant_natCast_eq_pow_iff_real (n k : ℕ) :
    cliffordInvariant (n : RegularFormClass ℝ) = quaternionClass (-1) (-1) ^ k ↔
      (n + 1) / 4 ≡ k [MOD 2] := by
  have h2 : orderOf (quaternionClass (-1 : ℝˣ) (-1)) = 2 := by
    simpa [quaternionClass_def] using Quaternion.orderOf_mk_eq_two
  have hc : (n + 1).choose 4 ≡ (n + 1) / 4 [MOD 2] := by
    simpa using Choose.choose_pow_modEq_div_nat (p := 2) (n + 1) 2
  rw [cliffordInvariant_natCast, pow_eq_pow_iff_modEq, h2]
  exact ⟨hc.symm.trans, hc.trans⟩

/-- **The Clifford invariant of a real sum of squares is trivial exactly when
`n ≡ 0, 1, 2, 7 (mod 8)`.** -/
theorem cliffordInvariant_natCast_eq_one_iff_real (n : ℕ) :
    cliffordInvariant (n : RegularFormClass ℝ) = 1 ↔ n % 8 ∈ ({0, 1, 2, 7} : Finset ℕ) := by
  rw [← pow_zero (quaternionClass (-1 : ℝˣ) (-1)), cliffordInvariant_natCast_eq_pow_iff_real,
    Nat.ModEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **The Clifford invariant of a real sum of squares is the class of `ℍ` exactly when
`n ≡ 3, 4, 5, 6 (mod 8)`.** -/
theorem cliffordInvariant_natCast_eq_quaternionClass_iff_real (n : ℕ) :
    cliffordInvariant (n : RegularFormClass ℝ) = quaternionClass (-1) (-1) ↔
      n % 8 ∈ ({3, 4, 5, 6} : Finset ℕ) := by
  rw [← pow_one (quaternionClass (-1 : ℝˣ) (-1)), cliffordInvariant_natCast_eq_pow_iff_real,
    Nat.ModEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ### Worked examples -/

/-- `⟨1,1,1⟩` has Clifford invariant `[ℍ]`: its even Clifford algebra is `ℍ`. -/
example : cliffordInvariant ((3 : ℕ) : RegularFormClass ℝ) = quaternionClass (-1) (-1) :=
  (cliffordInvariant_natCast_eq_quaternionClass_iff_real 3).2 (by decide)

/-- `8⟨1⟩` has trivial Clifford invariant: its Clifford algebra is `M₁₆(ℝ)`. -/
example : cliffordInvariant ((8 : ℕ) : RegularFormClass ℝ) = 1 :=
  (cliffordInvariant_natCast_eq_one_iff_real 8).2 (by decide)

/-- **The first correction exponent of Lam's comparison.** The even Clifford algebra of
`⟨-1,-1,-1⟩` over `ℝ` is `ℍ`, so its Clifford invariant is `[ℍ]`. Its Hasse invariant is
`[ℍ]³ = [ℍ]` and its discriminant is `[-1]`, so Lam's formula
`c = s · [(-1, d)]^C(2,2) · [(-1,-1)]^C(4,4)` gives `[ℍ] · [ℍ] · [ℍ] = [ℍ]`; with the factor
`[(-1, d)]` dropped it would give the trivial class instead. -/
example :
    cliffordInvariant (Quotient.mk (regularFormSetoid ℝ) ⟨3, ![-1, -1, -1]⟩) ≠
      hasseInvariant (Quotient.mk (regularFormSetoid ℝ) ⟨3, ![-1, -1, -1]⟩) *
        quaternionClass (-1) (-1) ^ Nat.choose 4 4 := by
  have hne : quaternionClass (-1 : ℝˣ) (-1) ≠ 1 := by
    simpa [quaternionClass_def] using Quaternion.mk_ne_one
  have hs : hasseInvariant (Quotient.mk (regularFormSetoid ℝ) ⟨3, ![-1, -1, -1]⟩) =
      quaternionClass (-1 : ℝˣ) (-1) := by
    simp [Fin.prod_univ_succ, ← sq]
  rw [hs, Nat.choose_self, pow_one, ← sq, quaternionClass_sq, cliffordInvariant_mk_ternary]
  simpa using hne

end RegularFormClass

end TauCeti
