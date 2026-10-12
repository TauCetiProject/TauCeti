/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum
public import TauCeti.FieldTheory.ArtinSchreier.Additive
public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.FunctionField.ArtinSchreier.Additive.Basic
import TauCeti.FieldTheory.FunctionField.Different.ArtinSchreier.Additive
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz

/-!
# The genus of elementary abelian Artin–Schreier extensions of function fields

Let `F / k` be an algebraic function field, `V` a finite additive subgroup of `F` consisting of
constants, with additive polynomial `a_V = ∏_{c ∈ V} (X - c)`, and `F' = F(y)` with
`a_V (y) = u`. Suppose that reduced representatives are supplied at every place: at the places of
a finite set `S` some `u - a_V (w)` has a pole of order `m P` prime to `|V|`, and at every other
place some `u - a_V (w)` is regular. The local different exponents
(`TauCeti.FieldTheory.FunctionField.Different.ArtinSchreier.Additive`) give the different divisor

`|V| • Diff(F' / F) = (|V| - 1) • Con (∑ P ∈ S, (m P + 1) P)`,

and when `k` is the exact constant field of `F` and `S` is nonempty, the Hurwitz genus formula
becomes the genus formula of Stichtenoth's Proposition 3.7.10(e):

`2 g' - 2 = |V| (2 g - 2) + (|V| - 1) ∑ P ∈ S, (m P + 1) deg P`.

As in `TauCeti.FieldTheory.FunctionField.ArtinSchreier.Additive.Basic`, finiteness, separability
and exactness of the constants of `F'` are derived from the equation and one pole, not assumed.

## Main results

* `TauCeti.Divisor.nsmul_different_eq_zsmul_conorm_of_aeval_additivePolynomial_eq`: the different
  divisor of `F' / F`.
* `TauCeti.two_mul_genus_sub_two_eq_of_exists_reduced_additivePolynomial_poles`: the genus
  formula.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.10.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {k : Type*} {F : Type*} {F' : Type*} [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (V : AddSubgroup F) [Fintype V]

/-- **The different divisor of an elementary abelian Artin–Schreier extension.** Let `V` consist
of constants and `a_V (y) = u`. Suppose that at each place `P` of a finite set `S` some
representative `u - a_V (w)` has a pole of order `m P` prime to `|V|`, and that at every other place
some representative is regular. Then `|V| • Diff(F' / F) = (|V| - 1) • Con (∑ P ∈ S, (m P + 1) P)`
(Stichtenoth, Proposition 3.7.10(c) and (d)). -/
theorem Divisor.nsmul_different_eq_zsmul_conorm_of_aeval_additivePolynomial_eq
    {k' : Type*} [Field k'] [Algebra k k'] [Algebra k' F'] [IsScalarTower k k' F']
    (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (hV : ∀ c ∈ V, IsAlgebraic k c)
    {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤) (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (S : Finset (Place k F)) (m : Place k F → ℕ)
    (hpole : ∀ P ∈ S, ∃ w : F, P.ord (u - aeval w V.additivePolynomial) = -(m P : ℤ) ∧
      0 < m P ∧ (Fintype.card V).Coprime (m P))
    (hreg : ∀ P ∉ S, ∃ w : F, u - aeval w V.additivePolynomial ∈ P.integers) :
    letI := V.finiteDimensional_of_aeval_additivePolynomial_eq hy hgen
    letI := V.isGalois_of_aeval_additivePolynomial_eq hy hgen
    Fintype.card V • Divisor.different k' F' hF = (Fintype.card V - 1 : ℤ) •
      Divisor.conorm k' F' (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1) := by
  classical
  let _ := V.finiteDimensional_of_aeval_additivePolynomial_eq hy hgen
  let _ := V.isGalois_of_aeval_additivePolynomial_eq hy hgen
  refine WeilDivisor.ext fun P' ↦ ?_
  rw [WeilDivisor.coeff_nsmul, Divisor.coeff_different, WeilDivisor.coeff_zsmul,
    Divisor.coeff_conorm, WeilDivisor.coeff_ofFinsetWithMultiplicity]
  by_cases hP : P'.restrict k F ∈ S
  · obtain ⟨w, hw, hm, hcop⟩ := hpole _ hP
    have hgcd : Int.gcd (Fintype.card V) ((P'.restrict k F).ord (u - aeval w V.additivePolynomial))
        = 1 := by
      rwa [hw, Int.gcd_neg, Int.gcd_natCast_natCast]
    rw [ite_eq_left hP,
      Place.differentExponent_eq_of_sub_aeval_additivePolynomial_ord_eq_neg k F V hF hF' hV _ hgen
        hy hw hm hcop,
      Place.ramificationIdx_eq_card_of_exists_reduced_additivePolynomial_pole k F V hV hgen hy
        ⟨w, by omega, hgcd⟩]
    push_cast [Nat.cast_sub Fintype.card_pos]
    ring
  · rw [ite_eq_right hP,
      Place.differentExponent_eq_zero_of_exists_sub_aeval_additivePolynomial_mem_integers k F V hV
        hgen hy (hreg _ hP)]
    simp

/-- **The genus of an elementary abelian Artin–Schreier extension** (Stichtenoth,
Proposition 3.7.10(e)). Let `k` be the exact constant field of `F`, `V` a finite group of constants,
and `F' = F(y)` with `a_V (y) = u`. Suppose that at each place `P` of a finite nonempty set `S` some
representative `u - a_V (w)` has a pole of order `m P` prime to `|V|`, and that at every other place
some representative is regular. Then

`2 g' - 2 = |V| (2 g - 2) + (|V| - 1) ∑ P ∈ S, (m P + 1) deg P`.

The representatives may vary with the place; finiteness, separability and exactness of the
constants of `F'` follow from the equation and a pole. -/
theorem two_mul_genus_sub_two_eq_of_exists_reduced_additivePolynomial_poles
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hV : ∀ c ∈ V, IsAlgebraic k c)
    {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤) (hy : aeval y V.additivePolynomial = algebraMap F F' u)
    (S : Finset (Place k F)) (m : Place k F → ℕ) (hS : S.Nonempty)
    (hpole : ∀ P ∈ S, ∃ w : F, P.ord (u - aeval w V.additivePolynomial) = -(m P : ℤ) ∧
      0 < m P ∧ (Fintype.card V).Coprime (m P))
    (hreg : ∀ P ∉ S, ∃ w : F, u - aeval w V.additivePolynomial ∈ P.integers) :
    2 * (genus k F' : ℤ) - 2 = Fintype.card V * (2 * genus k F - 2) +
      (Fintype.card V - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  let _ := V.finiteDimensional_of_aeval_additivePolynomial_eq hy hgen
  let _ := V.isGalois_of_aeval_additivePolynomial_eq hy hgen
  have hF' : IsFunctionField k F' := hF.finite_extension
  -- One reduced pole gives the degree `|V|` and the exactness of the constants of `F'`.
  obtain ⟨P, hP⟩ := hS
  obtain ⟨w, hw, hm, hcop⟩ := hpole P hP
  have hpole' : ∃ w : F, P.ord (u - aeval w V.additivePolynomial) < 0 ∧
      Int.gcd (Fintype.card V) (P.ord (u - aeval w V.additivePolynomial)) = 1 :=
    ⟨w, by omega, by rwa [hw, Int.gcd_neg, Int.gcd_natCast_natCast]⟩
  have hfin := finrank_eq_card_of_exists_reduced_additivePolynomial_pole V hF hV hgen hy P hpole'
  have hex' :=
    isIntegrallyClosedIn_of_exists_reduced_additivePolynomial_pole V hF hex hV hgen hy P hpole'
  -- Taking degrees in the divisor identity gives
  -- `deg Diff(F' / F) = (|V| - 1) ∑ P ∈ S, (m P + 1) deg P`.
  have hdiff := congrArg Divisor.degree
    (Divisor.nsmul_different_eq_zsmul_conorm_of_aeval_additivePolynomial_eq (k' := k) V hF hF' hV
      hgen hy S m hpole hreg)
  rw [map_nsmul, Divisor.degree_zsmul, nsmul_eq_mul] at hdiff
  have hcon := Divisor.finrank_mul_degree_conorm_of_isSeparable (k' := k) (F' := F')
    (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1)
  rw [Divisor.degree_eq_weightedDegree (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1),
    WeilDivisor.weightedDegree_ofFinsetWithMultiplicity, hfin, Module.finrank_self] at hcon
  have hq : (0 : ℤ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdeg : Divisor.degree (Divisor.different k F' hF) =
      (Fintype.card V - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
    push_cast at hcon
    refine mul_left_cancel₀ hq.ne' ?_
    linear_combination hdiff + (Fintype.card V - 1 : ℤ) * hcon
  have hH := hurwitz_genus_formula hF hF' hex hex'
  rw [Module.finrank_self, hfin, hdeg] at hH
  linear_combination hH

end TauCeti
