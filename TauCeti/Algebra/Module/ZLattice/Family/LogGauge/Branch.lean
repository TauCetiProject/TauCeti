/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Branch independence for logarithmic translations on a family of tori

Two complex logarithms `a` and `b` of the same nonzero number (`Complex.exp a = Complex.exp b`)
differ by `2πi k` for an integer `k`, so translating the fibre coordinate of a family of tori
`(Y × E)/Λ` by `(a / 2πi) • P y l` and by `(b / 2πi) • P y l` yields the same quotient class
(`TauCeti.torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq`).

## Main results

* `TauCeti.torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq`: two logarithms of the same number
  give the same quotient point when used as translation coefficients of a period.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- Two logarithms of the same number give the same point in `(Y × E)/Λ` when used as translation
coefficients of a period `P y l`, since they differ by `2πi k`. -/
theorem torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq {Y Λ E : Type*} [AddCommGroup Λ]
    [AddCommGroup E] [Module ℂ E] (P : Y → Λ →ₗ[ℤ] E) (l : Λ) {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) (y : Y) (e : E) :
    letI := periodAddAction P
    (Quotient.mk _ (y, e + (a / (2 * π * I)) • P y l) :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      Quotient.mk _ (y, e + (b / (2 * π * I)) • P y l) := by
  let _ := periodAddAction P
  obtain ⟨k, hk⟩ := Complex.exists_div_two_pi_I_smul_eq_add_zsmul h (P y l)
  rw [hk, ← map_zsmul, ← add_assoc, ← periodAddAction_vadd P (k • l) (y, _)]
  exact AddAction.orbitRel.Quotient.quotient_vadd_eq (g := k • l)
    (a := (y, e + (b / (2 * π * I)) • P y l))

end TauCeti
