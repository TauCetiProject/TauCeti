/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Cotrace

/-!
# The Hurwitz genus formula

Let `F' / k'` be a finite separable extension of the algebraic function field `F / k`, with exact
constant fields and `k' / k` finite separable, and write `g` and `g'` for the genera of `F` and
`F'`.  The **Hurwitz genus formula** (Stichtenoth, Theorem 3.4.13) relates the two genera through
the degree of the different divisor `Diff(F'/F)`:

`[k' : k] · (2g' - 2) = [F' : F] · (2g - 2) + [k' : k] · deg Diff(F'/F)`.

It is the degree of the divisor identity `(Cotr ω) = Con (ω) + Diff(F'/F)`
(`TauCeti.weilDifferentialDivisor_weilDifferentialCotrace`) for any nonzero Weil differential `ω`
of `F`: the divisor of a nonzero Weil differential has degree `2g - 2`, and the conorm multiplies
degrees by `[F' : F] / [k' : k]` (`TauCeti.Divisor.finrank_mul_degree_conorm`).  Since `k' / k`
is separable and `k` is the exact constant field of `F`, `[k' : k]` divides `[F' : F]`, and
dividing through gives the familiar form

`2g' - 2 = n(F'/F) · (2g - 2) + deg Diff(F'/F)`

with the geometric degree `n(F'/F) = [F' : F k']`; when `k' = k` this is `[F' : F]`.

## Main results

* `TauCeti.hurwitz_genus_formula`: **the Hurwitz genus formula**, cross-multiplied
  (Stichtenoth, Theorem 3.4.13).
* `TauCeti.hurwitz_genus_formula_geometricDegree`: the Hurwitz genus formula through the
  geometric degree.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.4.13.
-/

public section

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
variable [Algebra.IsSeparable F F'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']

/-- **The Hurwitz genus formula** (Stichtenoth, Theorem 3.4.13): for a finite separable extension
`F' / k'` of the function field `F / k`, both with exact constants and with `k' / k` finite
separable, `[k' : k] · (2g' - 2) = [F' : F] · (2g - 2) + [k' : k] · deg Diff(F'/F)`. -/
theorem hurwitz_genus_formula (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (hex : IsIntegrallyClosedIn k F)
    (hex' : IsIntegrallyClosedIn k' F') :
    (Module.finrank k k' : ℤ) * (2 * genus k' F' - 2) =
      Module.finrank F F' * (2 * genus k F - 2) +
        Module.finrank k k' * Divisor.degree (Divisor.different k' F' hF) := by
  obtain ⟨ω, hωmem, hω0⟩ := (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  have hω : (⟨ω, hωmem⟩ : ↥(weilDifferentialSpace k F)) ≠ 0 := by simpa using hω0
  have h := congrArg Divisor.degree
    (weilDifferentialDivisor_weilDifferentialCotrace hF hF' hex hex' _ hω)
  rw [degree_weilDifferentialDivisor, map_add] at h
  rw [h, mul_add, Divisor.finrank_mul_degree_conorm, degree_weilDifferentialDivisor]

/-- **The Hurwitz genus formula through the geometric degree** (Stichtenoth, Theorem 3.4.13): under
the hypotheses of `TauCeti.hurwitz_genus_formula`,
`2g' - 2 = n(F'/F) · (2g - 2) + deg Diff(F'/F)`, where `n(F'/F) = [F' : F k']` is the geometric
degree. -/
theorem hurwitz_genus_formula_geometricDegree (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (hex : IsIntegrallyClosedIn k F)
    (hex' : IsIntegrallyClosedIn k' F') :
    2 * (genus k' F' : ℤ) - 2 =
      geometricDegree F k' F' * (2 * genus k F - 2) +
        Divisor.degree (Divisor.different k' F' hF) := by
  have hpos : (0 : ℤ) < Module.finrank k k' := by exact_mod_cast Module.finrank_pos
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [hurwitz_genus_formula hF hF' hex hex',
    finrank_eq_geometricDegree_mul_finrank_of_finrank_constantCompositum_eq F k' F'
      (finrank_constantCompositum_eq_finrank_of_isSeparable F k' F' hex)]
  push_cast
  ring

end TauCeti
