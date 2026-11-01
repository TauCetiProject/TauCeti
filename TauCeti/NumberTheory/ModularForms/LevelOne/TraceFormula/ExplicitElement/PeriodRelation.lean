/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.CosetCriterion
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.CosetSum

/-!
# Popa–Zagier's explicit element satisfies the period relation

Popa and Zagier's explicit element `Tₙ` of `ℛₙ = k[ℳₙ]` (written with a tilde in their paper,
their eq. (15)) satisfies the exchange relations (B) (their Theorem 4(a)), and its coefficients sum
to `-1` over every right coset of `PSL(2, ℤ)` in `ℳₙ` (Theorem 4(b), first part). By their §3
Theorem 2(b), these two properties together are equivalent to the period relation

  (A)  `(1 - S) Tₙ - Tₙ^∞ (1 - S) ∈ (1 - T) ℛₙ`

for a solution of (B). So `Tₙ` satisfies both (A) and (B): it is an explicit solution of the two
relations, whose existence
`TauCeti.TraceFormulaMatrixModule.exists_periodRelation_and_exchangeRelations` proves abstractly.
Popa and Zagier prove the Eichler–Selberg trace formula by computing the trace of this element on
period polynomials.

## Main results

* `TauCeti.TraceFormulaMatrixModule.periodRelation_popaZagierElement`: Popa–Zagier's explicit
  element satisfies the period relation (A), for `n > 0` over a field in which `12 ≠ 0`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §3 Theorem 2 and §4
  Theorem 4.
-/

public section

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} [Field k] {n : ℤ}

/-- **Popa–Zagier's explicit element satisfies the period relation (A)**: for `n > 0`,
`(1 - S) Tₙ - Tₙ^∞ (1 - S) ∈ (1 - T) k[ℳₙ]`. It follows from the exchange relations (B) and the
coset identity `⟨Tₙ, K⟩ = -1` by Popa–Zagier's §3 Theorem 2(b). This needs `12 ≠ 0` in `k`, as
`Tₙ` is defined with denominators dividing `12`. -/
theorem periodRelation_popaZagierElement (h12 : (12 : k) ≠ 0) (hn : 0 < n) :
    PeriodRelation k n (popaZagierElement k n) := by
  have h2 : (2 : k) ≠ 0 := fun h ↦ h12 (by rw [show (12 : k) = 6 * 2 by norm_num, h, mul_zero])
  have h3 : (3 : k) ≠ 0 := fun h ↦ h12 (by rw [show (12 : k) = 4 * 3 by norm_num, h, mul_zero])
  let : Invertible (2 : k) := invertibleOfNonzero h2
  let : Invertible (3 : k) := invertibleOfNonzero h3
  exact (ExchangeRelations.periodRelation_iff_mapDomain_orbitRel_mk_coeff_eq_neg_one
    (exchangeRelations_popaZagierElement k n) hn).2
    (mapDomain_orbitRel_mk_coeff_popaZagierElement h12 hn)

end TauCeti.TraceFormulaMatrixModule
