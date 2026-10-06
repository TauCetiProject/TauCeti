/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum
-- Supplies splitting-field and Galois instances in the public theorem statements.
public import TauCeti.FieldTheory.ArtinSchreier.Basic

import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.Different.ArtinSchreier
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified

/-!
# The genus formula for Artin--Schreier extensions

For `F' = F(y)` with `y ^ p - y = u`, supply reduced representatives of the class of `u`
at every place of `F`. On a finite set `S`, these representatives have pole orders `m P`
prime to `p`; outside `S`, they are regular. The conductor divisor on `F` has coefficient
`m P + 1` on `S` and zero elsewhere. Total ramification and the local different formula give

`p • Diff(F'/F) = (p - 1) • Con (∑ P ∈ S, (m P + 1) P)`.

Taking degrees gives `[k' : k] deg Diff = (p - 1) ∑ P ∈ S, (m P + 1) deg P`.
For a nontrivial Artin--Schreier class, Hurwitz then computes the genus:

`[k' : k] (2g' - 2) = p (2g - 2) + (p - 1) ∑ P ∈ S, (m P + 1) deg P`.

The hypotheses supply the representatives, not their ramification data. No perfectness of
constants or residue fields is assumed. Over imperfect residue fields such representatives
need not exist. The genus formula uses exact constants and the finite separable constant-field
extension required by the Hurwitz theorem.

`isIntegrallyClosedIn_of_exists_reduced_artinSchreier_pole` proves exactness of the
extension's constants from a single supplied reduced pole.
For a finite nonempty set of reduced poles,
`two_mul_genus_sub_two_eq_of_exists_reduced_artinSchreier_poles` derives nontriviality and
exactness of the constants over any function field with exact constants. For an extension of `k(x)`,
`two_mul_genus_eq_of_exists_reduced_artinSchreier_poles_ratFunc` specialises this to
`2g = (p - 1) (∑ P ∈ S, (m P + 1) deg P - 2)`. Finiteness, separability,
nontriviality, and exactness of the constants are derived from the equation and a pole.
For a single pole, `two_mul_genus_eq_of_exists_reduced_artinSchreier_pole_ratFunc`
gives `2g = (p - 1) ((m + 1) deg P - 2)` directly.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8 and Theorem 3.4.13.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

private theorem ord_neg_of_ord_eq_neg_of_not_dvd
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    {P : Place k F} {a : F} {m p : ℕ}
    (hw : P.ord a = -(m : ℤ)) (hprime : ¬ (p : ℤ) ∣ P.ord a) :
    P.ord a < 0 := by
  have hm : m ≠ 0 := by
    intro hm
    apply hprime
    simp [hw, hm]
  rw [hw]
  omega

section Extension

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')
variable (p : ℕ) [Fact p.Prime] [CharP F p]
variable {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤) (hy : y ^ p - y = algebraMap F F' u)
variable (S : Finset (Place k F)) (m : Place k F → ℕ)
variable (hpole : ∀ P ∈ S, ∃ w : F, P.ord (u - (w ^ p - w)) = -(m P : ℤ) ∧
  ¬ (p : ℤ) ∣ P.ord (u - (w ^ p - w)))
variable (hreg : ∀ P ∉ S, ∃ w : F, u - (w ^ p - w) ∈ P.integers)

include hF hF' hgen hy hpole hreg

/-- The different of an Artin--Schreier extension is computed by the conorm of its reduced
conductor divisor. This is a divisor identity, before taking degrees or imposing exact constants.
The supplied pole orders are necessarily positive because they are not divisible by `p`. -/
theorem Divisor.nsmul_different_eq_zsmul_conorm_of_pow_sub_self_eq :
    letI := ArtinSchreier.isSplittingField hy hgen
    letI := Polynomial.IsSplittingField.finiteDimensional F'
      (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
    letI := ArtinSchreier.isGalois hy hgen
    p • Divisor.different k' F' hF = (p - 1 : ℤ) • Divisor.conorm k' F'
      (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1) := by
  classical
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F'
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  refine WeilDivisor.ext fun P' ↦ ?_
  rw [WeilDivisor.coeff_nsmul, Divisor.coeff_different, WeilDivisor.coeff_zsmul,
    Divisor.coeff_conorm, WeilDivisor.coeff_ofFinsetWithMultiplicity]
  by_cases hP : P'.restrict k F ∈ S
  · obtain ⟨w, hw, hprime⟩ := hpole _ hP
    have hneg := ord_neg_of_ord_eq_neg_of_not_dvd hw hprime
    rw [ite_eq_left hP,
      Place.differentExponent_eq_of_sub_pow_sub_self_ord_eq_neg k F hF hF' p _ hgen hy
        hw hprime,
      Place.ramificationIdx_eq_of_exists_reduced_artinSchreier_pole k F p hgen hy
        ⟨w, hneg, hprime⟩]
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    push_cast
    rw [Nat.cast_sub hp]
    ring
  · rw [ite_eq_right hP,
      Place.differentExponent_eq_zero_of_exists_sub_pow_sub_self_mem_integers k F p hgen hy
        (hreg _ hP)]
    simp

/-- The weighted degree of the Artin--Schreier different, for supplied reduced representatives.
A reduced pole forces the extension degree to be `p`; when there are no reduced poles, the
different is zero. The factor `[k' : k]` accounts for a possible enlargement of the constant
field. No exactness or constant-field separability is needed for this degree identity. -/
theorem Divisor.finrank_mul_degree_different_of_pow_sub_self_eq :
    letI := ArtinSchreier.isSplittingField hy hgen
    letI := Polynomial.IsSplittingField.finiteDimensional F'
      (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
    letI := ArtinSchreier.isGalois hy hgen
    (Module.finrank k k' : ℤ) * Divisor.degree (Divisor.different k' F' hF) =
      (p - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F'
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  let _ : Algebra.IsIntegral k k' := Algebra.IsIntegral.of_finite k k'
  have h := congrArg Divisor.degree
    (Divisor.nsmul_different_eq_zsmul_conorm_of_pow_sub_self_eq
      hF hF' p hgen hy S m hpole hreg)
  rw [map_nsmul, Divisor.degree_zsmul, nsmul_eq_mul] at h
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hd : Divisor.degree (Divisor.different k' F' hF) = 0 := by
      simpa [hS, (Fact.out : p.Prime).ne_zero] using h
    simp [hS, hd]
  -- A reduced pole forces degree `p`; the empty case above needs no degree assumption.
  obtain ⟨P, hP⟩ := hS
  obtain ⟨P', hP'⟩ := Place.restrict_surjective (k := k) (F := F) hF' P
  obtain ⟨w, hw, hprime⟩ := hpole P hP
  have hneg := ord_neg_of_ord_eq_neg_of_not_dvd hw hprime
  have hfin := Place.finrank_eq_of_exists_reduced_artinSchreier_pole k F (P' := P')
    p hgen hy ⟨w, by simpa [hP'] using hneg, by simpa [hP'] using hprime⟩
  have hcon := Divisor.finrank_mul_degree_conorm_of_isSeparable (k' := k') (F' := F')
    (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1)
  rw [Divisor.degree_eq_weightedDegree
      (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1),
    WeilDivisor.weightedDegree_ofFinsetWithMultiplicity,
    hfin] at hcon
  apply mul_left_cancel₀ hp
  calc
    (p : ℤ) * ((Module.finrank k k' : ℤ) *
        Divisor.degree (Divisor.different k' F' hF)) =
        (Module.finrank k k' : ℤ) * ((p - 1 : ℤ) *
          Divisor.degree (Divisor.conorm k' F'
            (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1))) := by
              linear_combination (Module.finrank k k' : ℤ) * h
    _ = (p : ℤ) * ((p - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree) := by
      push_cast at hcon
      linear_combination (p - 1 : ℤ) * hcon

/-- **The Artin--Schreier genus formula**, cross-multiplied for a possible constant-field
extension. The representatives may vary with the place. Pole orders are weighted by residue
field degrees, not by the number of poles. -/
theorem artinSchreier_genus_formula [Algebra.IsSeparable k k']
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k' F')
    (hu : ∀ w : F, w ^ p - w ≠ u) :
    (Module.finrank k k' : ℤ) * (2 * genus k' F' - 2) =
      (p : ℤ) * (2 * genus k F - 2) +
        (p - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F'
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  rw [hurwitz_genus_formula hF hF' hex hex', ArtinSchreier.finrank_eq hy hgen hu,
    Divisor.finrank_mul_degree_different_of_pow_sub_self_eq hF hF' p hgen hy S m hpole hreg]

end Extension

section Poles

variable {k : Type u} {F : Type v} {F' : Type v'} [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

/-- An Artin--Schreier extension of a function field with exact constants acquires no new
constants if one supplied representative has a pole of order prime to `p`.
Finiteness and separability follow from the equation and the generator hypothesis. -/
theorem isIntegrallyClosedIn_of_exists_reduced_artinSchreier_pole
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ p - y = algebraMap F F' u) (P : Place k F)
    (hpole : ∃ w : F, P.ord (u - (w ^ p - w)) < 0 ∧
      ¬ (p : ℤ) ∣ P.ord (u - (w ^ p - w))) :
    IsIntegrallyClosedIn k F' := by
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F'
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  have hF' : IsFunctionField k F' := hF.finite_extension
  obtain ⟨P', hP'⟩ := Place.restrict_surjective_of_finiteDimensional
    (k' := k) hF hF' P
  have hpole' : ∃ w : F, (P'.restrict k F).ord (u - (w ^ p - w)) < 0 ∧
      ¬ (p : ℤ) ∣ (P'.restrict k F).ord (u - (w ^ p - w)) := by
    simpa only [hP'] using hpole
  have he := Place.ramificationIdx_eq_of_exists_reduced_artinSchreier_pole
    k F p hgen hy hpole'
  refine isIntegrallyClosedIn_of_finrank_prime_of_ramificationIdx_ne_one hex ?_
    (P' := P') (he.trans_ne (Fact.out : p.Prime).ne_one)
  rw [Place.finrank_eq_of_exists_reduced_artinSchreier_pole k F p hgen hy hpole']
  exact Fact.out

/-- An Artin--Schreier extension of a function field with exact constants and a finite
nonempty set of supplied reduced poles has no new constants. Its genus is determined by
`2g' - 2 = p (2g - 2) + (p - 1) ∑ P ∈ S, (m P + 1) deg P`.
Finiteness, separability, nontriviality, and exactness of the extension's constants follow
from the equation and a pole. The representatives may vary with the place. -/
theorem two_mul_genus_sub_two_eq_of_exists_reduced_artinSchreier_poles
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {y : F'} {u : F} (hgen : F⟮y⟯ = ⊤)
    (hy : y ^ p - y = algebraMap F F' u)
    (S : Finset (Place k F)) (m : Place k F → ℕ) (hS : S.Nonempty)
    (hord : ∀ P ∈ S, ∃ w : F, P.ord (u - (w ^ p - w)) = -(m P : ℤ))
    (hprime : ∀ P ∈ S, ¬ p ∣ m P)
    (hreg : ∀ Q : Place k F, Q ∉ S → ∃ w : F, u - (w ^ p - w) ∈ Q.integers) :
    2 * (genus k F' : ℤ) - 2 =
      (p : ℤ) * (2 * genus k F - 2) +
        (p - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  classical
  have hpole : ∀ Q ∈ S, ∃ w : F, Q.ord (u - (w ^ p - w)) = -(m Q : ℤ) ∧
      ¬ (p : ℤ) ∣ Q.ord (u - (w ^ p - w)) := by
    intro Q hQ
    obtain ⟨w, hw⟩ := hord Q hQ
    have hprime' : ¬ (p : ℤ) ∣ (m Q : ℤ) := by exact_mod_cast hprime Q hQ
    exact ⟨w, hw, by simpa [hw] using hprime'⟩
  obtain ⟨P, hP⟩ := hS
  obtain ⟨w₀, hw₀, hdiv⟩ := hpole P hP
  have hneg := ord_neg_of_ord_eq_neg_of_not_dvd hw₀ hdiv
  have hu := ne_pow_sub_self_of_exists_reduced_artinSchreier_pole (v := P.valuation) p
    (Fact.out : p.Prime).one_lt
    ⟨w₀, by simpa only [Valuation.ord_def, ← P.ord_def] using hneg,
      by simpa only [Valuation.ord_def, ← P.ord_def] using hdiv⟩
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F'
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  have hF' : IsFunctionField k F' := hF.finite_extension
  have hex' := isIntegrallyClosedIn_of_exists_reduced_artinSchreier_pole
    hF hex p hgen hy P ⟨w₀, hneg, hdiv⟩
  simpa only [Module.finrank_self, Nat.cast_one, one_mul] using
    artinSchreier_genus_formula hF hF' p hgen hy S m hpole hreg hex hex' hu

end Poles

section RatFunc

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- An Artin--Schreier extension of `k(x)` with supplied reduced representatives and a finite
nonempty set of poles of orders prime to `p` has genus determined by
`2g = (p - 1) (∑ P ∈ S, (m P + 1) deg P - 2)`. The representatives may vary with the place.
For one rational pole of order `m`, this is `2g = (p - 1) (m - 1)`. Finiteness, separability,
nontriviality, and exactness of the constants follow from the equation and a pole. -/
theorem two_mul_genus_eq_of_exists_reduced_artinSchreier_poles_ratFunc
    (p : ℕ) [Fact p.Prime] [CharP (RatFunc k) p]
    {y : F} {u : RatFunc k} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ p - y = algebraMap (RatFunc k) F u)
    (S : Finset (Place k (RatFunc k))) (m : Place k (RatFunc k) → ℕ) (hS : S.Nonempty)
    (hord : ∀ P ∈ S, ∃ w : RatFunc k, P.ord (u - (w ^ p - w)) = -(m P : ℤ))
    (hprime : ∀ P ∈ S, ¬ p ∣ m P)
    (hreg : ∀ Q : Place k (RatFunc k), Q ∉ S → ∃ w : RatFunc k,
      u - (w ^ p - w) ∈ Q.integers) :
    2 * (genus k F : ℤ) =
      (p - 1 : ℤ) * (∑ P ∈ S, (m P + 1 : ℤ) * P.degree - 2) := by
  have hg := two_mul_genus_sub_two_eq_of_exists_reduced_artinSchreier_poles
    (IsFunctionField.ratFunc k) inferInstance p hgen hy S m hS hord hprime hreg
  simp only [genus_ratFunc, Nat.cast_zero, mul_zero, zero_sub] at hg
  linear_combination hg

/-- An Artin--Schreier extension of `k(x)` with a single supplied reduced pole of order
`m` prime to `p` has genus determined by `2g = (p - 1) ((m + 1) deg P - 2)`.
Representatives may vary with the place; finiteness, separability, nontriviality, and
exactness of the constants follow from the equation and the pole. -/
theorem two_mul_genus_eq_of_exists_reduced_artinSchreier_pole_ratFunc
    (p : ℕ) [Fact p.Prime] [CharP (RatFunc k) p]
    {y : F} {u : RatFunc k} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ p - y = algebraMap (RatFunc k) F u)
    (P : Place k (RatFunc k)) (m : ℕ)
    (hord : ∃ w : RatFunc k, P.ord (u - (w ^ p - w)) = -(m : ℤ))
    (hprime : ¬ p ∣ m)
    (hreg : ∀ Q : Place k (RatFunc k), Q ≠ P → ∃ w : RatFunc k,
      u - (w ^ p - w) ∈ Q.integers) :
    2 * (genus k F : ℤ) = (p - 1 : ℤ) * ((m + 1 : ℤ) * P.degree - 2) := by
  classical
  simpa only [Finset.sum_singleton] using
    two_mul_genus_eq_of_exists_reduced_artinSchreier_poles_ratFunc p hgen hy {P}
      (fun _ ↦ m) (Finset.singleton_nonempty P)
      (by simpa only [Finset.mem_singleton, forall_eq] using hord)
      (by simpa only [Finset.mem_singleton, forall_eq] using hprime)
      (by simpa only [Finset.mem_singleton] using hreg)

end RatFunc

end TauCeti
