/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Cotrace
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc

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
* `TauCeti.geometricDegree_mul_add_degree_tameDifferent_le` and
  `TauCeti.two_mul_genus_sub_two_eq_iff_forall_isTame`: the tame lower bound
  `2g' - 2 ≥ n(F'/F) · (2g - 2) + ∑_{P'} (e(P' ∣ P) - 1) · deg P'`, with equality exactly when
  every place of `F'` is tame (Stichtenoth, Corollary 3.5.6).
* `TauCeti.genus_le_genus`: `g ≤ g'` (Stichtenoth, Corollary 3.5.7).
* `TauCeti.hurwitz_genus_formula_ratFunc`: `2g - 2 = -2 [F : k(x)] + deg Diff(F / k(x))` for a
  finite separable extension of the rational function field (Stichtenoth, Corollary 3.4.14).
* `TauCeti.different_ne_zero_of_one_lt_finrank`: a finite separable extension of `k(x)` of degree
  greater than one has nonzero different (Stichtenoth, Corollary 3.5.8).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.4.13, Corollaries 3.4.14, 3.5.6, 3.5.7 and 3.5.8.
-/

public section

namespace TauCeti

universe u u' v v'

section Extension

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

/-- **The Hurwitz genus formula, tame lower bound** (Stichtenoth, Corollary 3.5.6(a)): under the
hypotheses of `TauCeti.hurwitz_genus_formula`,
`n(F'/F) · (2g - 2) + ∑_{P'} (e(P' ∣ P) - 1) · deg P' ≤ 2g' - 2`, the sum being the degree of the
tame different. -/
theorem geometricDegree_mul_add_degree_tameDifferent_le (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (hex : IsIntegrallyClosedIn k F)
    (hex' : IsIntegrallyClosedIn k' F') :
    geometricDegree F k' F' * (2 * genus k F - 2) +
        Divisor.degree (Divisor.tameDifferent k' F' hF) ≤ 2 * (genus k' F' : ℤ) - 2 := by
  rw [hurwitz_genus_formula_geometricDegree hF hF' hex hex']
  exact (add_le_add_iff_left _).mpr
    (Divisor.degree_le_of_le (Divisor.tameDifferent_le_different k' F' hF))

/-- **The Hurwitz genus formula, tame case** (Stichtenoth, Corollary 3.5.6(b)): under the
hypotheses of `TauCeti.hurwitz_genus_formula`, the tame lower bound
`2g' - 2 = n(F'/F) · (2g - 2) + ∑_{P'} (e(P' ∣ P) - 1) · deg P'` is an equality exactly when every
place of `F'` is tame over `F`. -/
theorem two_mul_genus_sub_two_eq_iff_forall_isTame (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (hex : IsIntegrallyClosedIn k F)
    (hex' : IsIntegrallyClosedIn k' F') :
    2 * (genus k' F' : ℤ) - 2 =
        geometricDegree F k' F' * (2 * genus k F - 2) +
          Divisor.degree (Divisor.tameDifferent k' F' hF) ↔
      ∀ P' : Place k' F', Place.IsTame k F P' := by
  rw [hurwitz_genus_formula_geometricDegree hF hF' hex hex', add_right_inj,
    ← Divisor.tameDifferent_eq_different_iff k' F' hF]
  exact ⟨fun h ↦ Divisor.eq_of_le_of_degree_eq hF'
    (Divisor.tameDifferent_le_different k' F' hF) h.symm, fun h ↦ by rw [h]⟩

/-- **The genus does not decrease in a finite separable extension** (Stichtenoth,
Corollary 3.5.7): under the hypotheses of `TauCeti.hurwitz_genus_formula`, `g ≤ g'`. -/
theorem genus_le_genus (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k' F') :
    genus k F ≤ genus k' F' := by
  have h := hurwitz_genus_formula_geometricDegree hF hF' hex hex'
  have hn : (1 : ℤ) ≤ geometricDegree F k' F' := by
    exact_mod_cast geometricDegree_pos F k' F'
  have hd := Divisor.zero_le_degree_different k' F' hF
  rcases Nat.eq_zero_or_pos (genus k F) with hg | hg
  · simp [hg]
  · have hg' : (0 : ℤ) ≤ 2 * genus k F - 2 := by omega
    have := mul_le_mul_of_nonneg_right hn hg'
    omega

end Extension

/-! ### Separable extensions of the rational function field -/

section RatFunc

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]

/-- **The Hurwitz genus formula over a rational subfield** (Stichtenoth, Corollary 3.4.14): for a
finite separable extension `F` of the rational function field `k(x)` with exact constant field
`k`, `2g - 2 = -2 [F : k(x)] + deg Diff(F / k(x))`. -/
theorem hurwitz_genus_formula_ratFunc (hex : IsIntegrallyClosedIn k F) :
    2 * (genus k F : ℤ) - 2 =
      -2 * Module.finrank (RatFunc k) F +
        Divisor.degree (Divisor.different k F (IsFunctionField.ratFunc k)) := by
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  rw [hurwitz_genus_formula_geometricDegree (IsFunctionField.ratFunc k) hF inferInstance hex,
    geometricDegree_eq_finrank, genus_ratFunc]
  ring

/-- **A separable extension of the rational function field of degree greater than one has nonzero
different** (Stichtenoth, Corollary 3.5.8): if `F / k(x)` is finite separable of degree `> 1` and
`k` is the exact constant field of `F`, some place of `F` has positive different exponent over
`k(x)`. -/
theorem different_ne_zero_of_one_lt_finrank (hex : IsIntegrallyClosedIn k F)
    (h : 1 < Module.finrank (RatFunc k) F) :
    Divisor.different k F (IsFunctionField.ratFunc k) ≠ 0 := by
  intro hD
  have hg := hurwitz_genus_formula_ratFunc hex
  rw [hD, map_zero] at hg
  have : (1 : ℤ) < Module.finrank (RatFunc k) F := by exact_mod_cast h
  omega

end RatFunc

end TauCeti
