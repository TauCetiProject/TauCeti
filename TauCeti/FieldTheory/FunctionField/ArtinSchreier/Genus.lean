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

import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.Different.ArtinSchreier
import TauCeti.FieldTheory.ArtinSchreier.Basic
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

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8 and Theorem 3.4.13.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

section Extension

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']
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
    p • Divisor.different k' F' hF = (p - 1 : ℤ) • Divisor.conorm k' F'
      (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1) := by
  classical
  let _ : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  refine WeilDivisor.ext fun P' ↦ ?_
  rw [WeilDivisor.coeff_nsmul, Divisor.coeff_different, WeilDivisor.coeff_zsmul,
    Divisor.coeff_conorm, WeilDivisor.coeff_ofFinsetWithMultiplicity]
  by_cases hP : P'.restrict k F ∈ S
  · obtain ⟨w, hw, hprime⟩ := hpole _ hP
    have hm : 0 < m (P'.restrict k F) := by
      by_contra h
      have hm0 : m (P'.restrict k F) = 0 := by omega
      apply hprime
      rw [hw, hm0]
      simp
    have hneg : (P'.restrict k F).ord (u - (w ^ p - w)) < 0 := by
      rw [hw]
      exact neg_neg_of_pos (by exact_mod_cast hm)
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
The class is nontrivial, so the extension degree is `p`. The factor `[k' : k]` accounts for a
possible enlargement of the constant field. No exactness or constant-field separability is
needed for this degree identity. -/
theorem finrank_mul_degree_different_of_pow_sub_self_eq
    (hu : ∀ w : F, w ^ p - w ≠ u) :
    (Module.finrank k k' : ℤ) * Divisor.degree (Divisor.different k' F' hF) =
      (p - 1 : ℤ) * ∑ P ∈ S, (m P + 1 : ℤ) * P.degree := by
  let _ : FiniteDimensional k k' := hF.finiteDimensional_baseExtension hF'
  let _ : Algebra.IsIntegral k k' := Algebra.IsIntegral.of_finite k k'
  have h := congrArg Divisor.degree
    (Divisor.nsmul_different_eq_zsmul_conorm_of_pow_sub_self_eq
      hF hF' p hgen hy S m hpole hreg)
  have hcon := Divisor.finrank_mul_degree_conorm_of_isSeparable (k' := k') (F' := F')
    (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1)
  rw [Divisor.degree_eq_weightedDegree
      (WeilDivisor.ofFinsetWithMultiplicity S fun P ↦ m P + 1),
    WeilDivisor.weightedDegree_ofFinsetWithMultiplicity,
    ArtinSchreier.finrank_eq hy hgen hu] at hcon
  rw [map_nsmul, Divisor.degree_zsmul, nsmul_eq_mul] at h
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
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

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
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
    finrank_mul_degree_different_of_pow_sub_self_eq hF hF' p hgen hy S m hpole hreg hu]

end Extension

section SinglePole

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]

/-- An Artin--Schreier extension of `k(x)` with just one pole of order `m` prime to `p`
has genus determined by `2g = (p - 1) ((m + 1) deg P - 2)`. In particular, at a rational pole
this is `2g = (p - 1) (m - 1)`. Finiteness, separability, nontriviality, and exactness of the
constants follow from the equation and the pole, rather than being assumed. -/
theorem two_mul_genus_eq_of_artinSchreier_single_pole
    (p m : ℕ) [Fact p.Prime] [CharP (RatFunc k) p]
    {y : F} {u : RatFunc k} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ p - y = algebraMap (RatFunc k) F u) (P : Place k (RatFunc k))
    (hord : P.ord u = -(m : ℤ)) (hprime : ¬ (p : ℤ) ∣ (m : ℤ))
    (hreg : ∀ Q : Place k (RatFunc k), Q ≠ P → u ∈ Q.integers) :
    2 * (genus k F : ℤ) = (p - 1 : ℤ) * ((m + 1 : ℤ) * P.degree - 2) := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    exact hprime (hm0 ▸ dvd_zero _)
  have hneg : P.ord u < 0 := by rw [hord]; omega
  have hdiv : ¬ (p : ℤ) ∣ P.ord u := by simpa [hord] using hprime
  have hu : ∀ w : RatFunc k, w ^ p - w ≠ u := by
    intro w
    -- The valuation order and the place order use the same multiplicative-to-additive convention.
    exact (P.valuation.ne_pow_sub_self_of_ord_neg_of_not_dvd
      (Fact.out : p.Prime).one_lt
      (by simpa only [Valuation.ord_def, ← P.ord_def] using hneg)
      (by simpa only [Valuation.ord_def, ← P.ord_def] using hdiv) w).symm
  let _ := ArtinSchreier.isSplittingField hy hgen
  let _ := Polynomial.IsSplittingField.finiteDimensional F
    (Polynomial.X ^ p - Polynomial.X - Polynomial.C u)
  let _ := ArtinSchreier.isGalois hy hgen
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  obtain ⟨P', hP'⟩ := Place.restrict_surjective_of_finiteDimensional
    (k' := k) (IsFunctionField.ratFunc k) hF P
  have he : Place.ramificationIdx (RatFunc k) P' = p := by
    apply Place.ramificationIdx_eq_of_exists_reduced_artinSchreier_pole
      k (RatFunc k) p hgen hy
    exact ⟨0, by simpa [hP', hp0] using hneg, by simpa [hP', hp0] using hdiv⟩
  have hex : IsIntegrallyClosedIn k F :=
    isIntegrallyClosedIn_of_finrank_prime_of_ramificationIdx_ne_one inferInstance
      (by rw [ArtinSchreier.finrank_eq hy hgen hu]; exact Fact.out)
      (P' := P') (he.trans_ne (Fact.out : p.Prime).ne_one)
  have hg := artinSchreier_genus_formula (IsFunctionField.ratFunc k) hF p hgen hy
    {P} (fun _ ↦ m)
    (by simpa using ⟨(0 : RatFunc k), by simpa [hp0] using hord,
      by simpa [hp0] using hdiv⟩)
    (fun Q hQ ↦ ⟨0, by simpa [hp0] using hreg Q (by simpa using hQ)⟩)
    inferInstance hex hu
  simp only [Module.finrank_self, Nat.cast_one, one_mul, genus_ratFunc, Nat.cast_zero,
    mul_zero, zero_sub, Finset.sum_singleton] at hg
  linear_combination hg

end SinglePole

end TauCeti
