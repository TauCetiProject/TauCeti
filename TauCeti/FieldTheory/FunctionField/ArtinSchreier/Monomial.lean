/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ArtinSchreier.Genus
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import TauCeti.FieldTheory.FunctionField.Different.ArtinSchreier.Basic
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence

/-!
# The Artin–Schreier curves `y ^ p - y = x ^ m`

Let `k` be a field of characteristic `p` and `m` a natural number not divisible by `p`. This file
constructs the function field `F = k(x, y)` of the curve `y ^ p - y = x ^ m` and computes its
ramification over `k(x)` completely. It is the standard example of **wild** ramification, which
the tame theory gets wrong:

* `F / k(x)` is an Artin–Schreier extension of degree `p`, and `k` is the exact constant field
  of `F`;
* the place at infinity of `k(x)` is totally ramified in `F`, with a unique place `P_∞` above it,
  of degree one; every other place of `k(x)` is unramified;
* `P_∞` is wild: its ramification index `e = p` vanishes in the residue field, and its different
  exponent is `d = (p - 1) (m + 1)`, so `d ≥ e`, whereas a tame place has `d = e - 1`
  (Dedekind's different theorem);
* the different of `F / k(x)` is `(p - 1) (m + 1) P_∞`, while the tame count `e - 1` gives only
  `(p - 1) P_∞`; the Hurwitz genus formula with the true different gives
  `2 g = (p - 1) (m - 1)`.

For instance `y ^ 2 - y = x ^ 3` in characteristic two has genus one and different `4 P_∞`, and
`y ^ p - y = x ^ 2` for odd `p` has genus `(p - 1) / 2` and different `3 (p - 1) P_∞`. Fed the
tame different instead, the Hurwitz formula would give `2 g - 2 = -2 p + (p - 1)`, a negative
genus.

## Main declarations

* `TauCeti.ArtinSchreierMonomial.FunctionField k p m`: the function field, with coordinates
  `genX` and `genY`; it is a field by
  `TauCeti.ArtinSchreierMonomial.irreducible_equationPolynomial`.
* `TauCeti.ArtinSchreierMonomial.existsUnique_restrict_eq_infty`: the unique place `P_∞` over
  infinity, of degree one.
* `TauCeti.ArtinSchreierMonomial.differentExponent_eq_of_restrict_eq_infty` and
  `TauCeti.ArtinSchreierMonomial.isWild_of_restrict_eq_infty`: `d(P_∞) = (p - 1) (m + 1)`, and
  `P_∞` is wild.
* `TauCeti.ArtinSchreierMonomial.ramificationIdx_eq_one_of_restrict_ne_infty`: no other place
  ramifies.
* `TauCeti.ArtinSchreierMonomial.different_eq` and
  `TauCeti.ArtinSchreierMonomial.tameDifferent_eq`: the different and the tame different.
* `TauCeti.ArtinSchreierMonomial.two_mul_genus`: `2 g = (p - 1) (m - 1)`.
* `TauCeti.ArtinSchreierMonomial.genus_functionField_two_three` and
  `TauCeti.ArtinSchreierMonomial.two_mul_genus_functionField_two`: the two classical
  instances.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.1 and Proposition 3.7.8.
-/

public section

noncomputable section

namespace TauCeti.ArtinSchreierMonomial

open _root_.Polynomial
open scoped _root_.IntermediateField
open AlgebraicGeometry

variable (k : Type*) [Field k] (p m : ℕ)

/-- The Artin–Schreier equation `Y ^ p - Y - x ^ m` over `k(x)`. -/
def equationPolynomial : (RatFunc k)[X] :=
  X ^ p - X - C (RatFunc.X ^ m)

/-- The defining polynomial, for computation without unfolding its body. -/
theorem equationPolynomial_def :
    equationPolynomial k p m = X ^ p - X - C (RatFunc.X ^ m) := (rfl)

/-- The function field of the affine curve `y ^ p - y = x ^ m`, obtained by adjoining a root of
the Artin–Schreier equation to `k(x)`. It is a field when `p` is a prime not dividing `m` and
`k` has characteristic `p`. -/
abbrev FunctionField := AdjoinRoot (equationPolynomial k p m)

/-- The `y`-coordinate: the root of the Artin–Schreier equation. -/
def genY : FunctionField k p m := AdjoinRoot.root (equationPolynomial k p m)

/-- The `y`-coordinate is the root in the defining root algebra. -/
theorem genY_def : genY k p m = AdjoinRoot.root (equationPolynomial k p m) := (rfl)

/-- The `x`-coordinate: the image of the variable of `k(x)`. -/
def genX : FunctionField k p m := algebraMap (RatFunc k) (FunctionField k p m) RatFunc.X

/-- The `x`-coordinate is the image of the variable of `k(x)`. -/
theorem genX_def : genX k p m = algebraMap (RatFunc k) (FunctionField k p m) RatFunc.X := (rfl)

/-- The coordinate `y` satisfies the Artin–Schreier equation over `k(x)`. -/
theorem genY_pow_sub_genY :
    genY k p m ^ p - genY k p m =
      algebraMap (RatFunc k) (FunctionField k p m) (RatFunc.X ^ m) :=
  ArtinSchreier.root_pow_sub_root_of_dvd (dvd_of_eq (equationPolynomial_def k p m))

/-- **The equation of the curve**: `y ^ p - y = x ^ m`. -/
theorem genY_pow_sub_genY_eq : genY k p m ^ p - genY k p m = genX k p m ^ m := by
  rw [genY_pow_sub_genY, map_pow, genX_def]

variable {p m} in
/-- An exponent not divisible by `p` is nonzero. -/
private theorem ne_zero_of_not_dvd (hm : ¬ p ∣ m) : m ≠ 0 := by
  rintro rfl
  exact hm (dvd_zero p)

variable [Fact p.Prime]

/-- At infinity, `x ^ m` is its own reduced representative: it has a pole of order `m`. -/
private theorem ord_infty_sub :
    (Place.infty k).ord ((RatFunc.X : RatFunc k) ^ m - ((0 : RatFunc k) ^ p - 0)) =
      -(m : ℤ) := by
  rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero, sub_zero, Place.ord_pow,
    Place.ord_infty, RatFunc.intDegree_X]
  ring

/-- At every finite place, `x ^ m` is regular. -/
private theorem pow_mem_integers {Q : Place k (RatFunc k)} (hQ : Q ≠ Place.infty k) :
    (RatFunc.X : RatFunc k) ^ m - ((0 : RatFunc k) ^ p - 0) ∈ Q.integers := by
  rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero, sub_zero]
  exact pow_mem (not_not.mp (Place.X_notMem_integers_iff_eq_infty.not.mpr hQ)) m

variable {m} in
/-- At infinity, `x ^ m` is a reduced Artin–Schreier representative: its pole has order `m`,
prime to `p`. -/
private theorem reduced_pole (hm : ¬ p ∣ m) :
    (Place.infty k).ord ((RatFunc.X : RatFunc k) ^ m - ((0 : RatFunc k) ^ p - 0)) < 0 ∧
      ¬ (p : ℤ) ∣
        (Place.infty k).ord ((RatFunc.X : RatFunc k) ^ m - ((0 : RatFunc k) ^ p - 0)) := by
  rw [ord_infty_sub k p m]
  refine ⟨?_, fun h ↦ hm (Int.natCast_dvd_natCast.mp (dvd_neg.mp h))⟩
  have := ne_zero_of_not_dvd hm
  omega

variable [CharP k p]

variable {m} in
/-- When `p ∤ m`, `x ^ m` is not of the form `w ^ p - w`: it has a pole of order prime to `p` at
infinity. -/
private theorem ne_pow_sub_self (hm : ¬ p ∣ m) :
    ∀ w : RatFunc k, w ^ p - w ≠ RatFunc.X ^ m := by
  obtain ⟨hneg, hdvd⟩ := reduced_pole k p hm
  exact ne_pow_sub_self_of_exists_reduced_artinSchreier_pole (v := (Place.infty k).valuation) p
    (Fact.out : p.Prime).one_lt
    ⟨0, by simpa only [Valuation.ord_def, ← Place.ord_def] using hneg,
      by simpa only [Valuation.ord_def, ← Place.ord_def] using hdvd⟩

variable {m} in
/-- The Artin–Schreier equation of `y ^ p - y = x ^ m` is irreducible over `k(x)` when `p ∤ m`. -/
theorem irreducible_equationPolynomial (hm : ¬ p ∣ m) :
    Irreducible (equationPolynomial k p m) :=
  ArtinSchreier.irreducible_X_pow_sub_X_sub_C p (ne_pow_sub_self k p hm)

variable [hm : Fact (¬ p ∣ m)]

/-- Irreducibility supplies the field structure on the root algebra. -/
instance : Fact (Irreducible (equationPolynomial k p m)) :=
  ⟨irreducible_equationPolynomial k p hm.out⟩

/-- The function field is generated by `y` over `k(x)`. -/
theorem adjoin_genY_eq_top : (RatFunc k)⟮genY k p m⟯ = ⊤ :=
  IntermediateField.adjoin_root_eq_top (equationPolynomial k p m)

/-- The function field has degree `p` over `k(x)`. -/
theorem finrank_eq : Module.finrank (RatFunc k) (FunctionField k p m) = p :=
  ArtinSchreier.finrank_eq (genY_pow_sub_genY k p m) (adjoin_genY_eq_top k p m)
    (ne_pow_sub_self k p hm.out)

/-- The function field is finite over `k(x)`. -/
instance : FiniteDimensional (RatFunc k) (FunctionField k p m) :=
  Module.finite_of_finrank_pos (by rw [finrank_eq]; exact (Fact.out : p.Prime).pos)

/-- The function field is a Galois extension of `k(x)`, as every Artin–Schreier extension is. -/
instance : IsGalois (RatFunc k) (FunctionField k p m) :=
  ArtinSchreier.isGalois (genY_pow_sub_genY k p m) (adjoin_genY_eq_top k p m)

/-- The curve `y ^ p - y = x ^ m` has an algebraic function field over `k`. -/
theorem isFunctionField : IsFunctionField k (FunctionField k p m) :=
  isFunctionField_iff_functionField.mpr inferInstance

/-- **The constants of `y ^ p - y = x ^ m` are exactly `k`**: the pole at infinity is totally
ramified. -/
theorem isIntegrallyClosedIn : IsIntegrallyClosedIn k (FunctionField k p m) :=
  isIntegrallyClosedIn_of_exists_reduced_artinSchreier_pole
    (IsFunctionField.ratFunc k) inferInstance p (adjoin_genY_eq_top k p m)
    (genY_pow_sub_genY k p m) (Place.infty k) ⟨0, reduced_pole k p hm.out⟩

/-! ### The place at infinity -/

section Infinity

variable {k p m} {P : Place k (FunctionField k p m)}

/-- **The place at infinity is totally ramified**: a place over it has ramification index `p`. -/
theorem ramificationIdx_eq_of_restrict_eq_infty (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Place.ramificationIdx (RatFunc k) P = p :=
  Place.ramificationIdx_eq_of_exists_reduced_artinSchreier_pole k (RatFunc k) p
    (adjoin_genY_eq_top k p m) (genY_pow_sub_genY k p m)
    (by rw [hP]; exact ⟨0, reduced_pole k p hm.out⟩)

/-- **The place at infinity is wild**: its ramification index `p` vanishes in its residue
field. -/
theorem isWild_of_restrict_eq_infty (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Place.IsWild k (RatFunc k) P :=
  Place.isWild_of_exists_reduced_artinSchreier_pole k (RatFunc k) p
    (adjoin_genY_eq_top k p m) (genY_pow_sub_genY k p m)
    (by rw [hP]; exact ⟨0, reduced_pole k p hm.out⟩)

/-- **The different exponent at infinity is `(p - 1) (m + 1)`**, the conductor computation for a
reduced pole of order `m`. -/
theorem differentExponent_eq_of_restrict_eq_infty
    (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Place.differentExponent k (RatFunc k) P = (p - 1) * (m + 1) :=
  Place.differentExponent_eq_of_sub_pow_sub_self_ord_eq_neg k (RatFunc k)
    (IsFunctionField.ratFunc k) (isFunctionField k p m) p m (adjoin_genY_eq_top k p m)
    (genY_pow_sub_genY k p m) (w := 0) (by rw [hP]; exact ord_infty_sub k p m)
    (by rw [hP]; exact (reduced_pole k p hm.out).2)

/-- **The tame different theorem fails at infinity**: the different exponent `d` is at least the
ramification index `e`, so `e ≠ d + 1`, unlike at every tame place. -/
theorem ramificationIdx_le_differentExponent_of_restrict_eq_infty
    (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Place.ramificationIdx (RatFunc k) P ≤ Place.differentExponent k (RatFunc k) P :=
  (Place.ramificationIdx_le_differentExponent_iff k (RatFunc k) P).mpr
    (isWild_of_restrict_eq_infty hP)

variable (k p m) in
/-- **There is exactly one place over infinity, and it has degree one.** -/
theorem existsUnique_restrict_eq_infty :
    ∃ P : Place k (FunctionField k p m), P.restrict k (RatFunc k) = Place.infty k ∧
      P.degree = 1 ∧ ∀ Q : Place k (FunctionField k p m),
        Q.restrict k (RatFunc k) = Place.infty k → Q = P := by
  obtain ⟨P, hP⟩ := Place.restrict_surjective_of_finiteDimensional
    (IsFunctionField.ratFunc k) (isFunctionField k p m) (Place.infty k)
  -- Eliminate the lambda in the surjectivity statement before rewriting the restriction.
  have hP : P.restrict k (RatFunc k) = Place.infty k := hP
  have htot : Place.IsTotallyRamified (RatFunc k) P := by
    rw [Place.isTotallyRamified_iff, ramificationIdx_eq_of_restrict_eq_infty hP, finrank_eq]
  refine ⟨P, hP, ?_, fun Q hQ ↦ Place.eq_of_isTotallyRamified k (RatFunc k) htot
    (hQ.trans hP.symm)⟩
  rw [Place.degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k), hP,
    Place.degree_infty, Place.relativeDegree_eq_one_of_isTotallyRamified k (RatFunc k) htot]

end Infinity

/-! ### The finite places -/

section Finite

variable {k p m} {P : Place k (FunctionField k p m)}

/-- **The finite places are unramified**: away from infinity `x ^ m` is regular. -/
theorem ramificationIdx_eq_one_of_restrict_ne_infty
    (hP : P.restrict k (RatFunc k) ≠ Place.infty k) :
    Place.ramificationIdx (RatFunc k) P = 1 :=
  Place.ramificationIdx_eq_one_of_exists_sub_pow_sub_self_mem_integers k (RatFunc k) p
    (adjoin_genY_eq_top k p m) (genY_pow_sub_genY k p m) ⟨0, pow_mem_integers k p m hP⟩

/-- The different exponent vanishes at the finite places. -/
theorem differentExponent_eq_zero_of_restrict_ne_infty
    (hP : P.restrict k (RatFunc k) ≠ Place.infty k) :
    Place.differentExponent k (RatFunc k) P = 0 :=
  Place.differentExponent_eq_zero_of_exists_sub_pow_sub_self_mem_integers k (RatFunc k) p
    (adjoin_genY_eq_top k p m) (genY_pow_sub_genY k p m) ⟨0, pow_mem_integers k p m hP⟩

end Finite

/-! ### The different and the genus -/

/-- **The different of `F / k(x)` is `(p - 1) (m + 1) P_∞`**, concentrated at the unique place
over infinity. -/
theorem different_eq {P : Place k (FunctionField k p m)}
    (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Divisor.different k (FunctionField k p m) (IsFunctionField.ratFunc k) =
      (((p - 1) * (m + 1) : ℕ) : ℤ) • WeilDivisor.ofPoint P := by
  obtain ⟨Q, -, -, huniq⟩ := existsUnique_restrict_eq_infty k p m
  refine WeilDivisor.ext fun R ↦ ?_
  rw [Divisor.coeff_different, WeilDivisor.coeff_zsmul]
  by_cases hR : R.restrict k (RatFunc k) = Place.infty k
  · rw [huniq R hR, ← huniq P hP, WeilDivisor.coeff_ofPoint_self,
      differentExponent_eq_of_restrict_eq_infty hP, mul_one]
  · rw [differentExponent_eq_zero_of_restrict_ne_infty hR,
      WeilDivisor.coeff_ofPoint_of_ne (fun h : R = P ↦ hR (h ▸ hP)), mul_zero, Nat.cast_zero]

/-- **The tame different of `F / k(x)` is only `(p - 1) P_∞`**: the tame count `e - 1` misses the
wild part of the different. -/
theorem tameDifferent_eq {P : Place k (FunctionField k p m)}
    (hP : P.restrict k (RatFunc k) = Place.infty k) :
    Divisor.tameDifferent k (FunctionField k p m) (IsFunctionField.ratFunc k) =
      ((p - 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P := by
  obtain ⟨Q, -, -, huniq⟩ := existsUnique_restrict_eq_infty k p m
  refine WeilDivisor.ext fun R ↦ ?_
  rw [Divisor.coeff_tameDifferent, WeilDivisor.coeff_zsmul]
  have hp := (Fact.out : p.Prime).one_lt
  by_cases hR : R.restrict k (RatFunc k) = Place.infty k
  · rw [huniq R hR, ← huniq P hP, WeilDivisor.coeff_ofPoint_self,
      ramificationIdx_eq_of_restrict_eq_infty hP]
    push_cast [hp.le]
    ring
  · rw [ramificationIdx_eq_one_of_restrict_ne_infty hR,
      WeilDivisor.coeff_ofPoint_of_ne (fun h : R = P ↦ hR (h ▸ hP))]
    simp

/-- The different of `F / k(x)` has degree `(p - 1) (m + 1)`. -/
theorem degree_different :
    Divisor.degree (Divisor.different k (FunctionField k p m) (IsFunctionField.ratFunc k)) =
      (p - 1 : ℤ) * (m + 1) := by
  obtain ⟨P, hP, hdeg, -⟩ := existsUnique_restrict_eq_infty k p m
  rw [different_eq k p m hP, map_zsmul, Divisor.degree_ofPoint, hdeg]
  push_cast [(Fact.out : p.Prime).one_le]
  ring

/-- **The genus of `y ^ p - y = x ^ m` is `(p - 1) (m - 1) / 2`**: the Hurwitz genus formula over
`k(x)` with the different `(p - 1) (m + 1) P_∞`. -/
theorem two_mul_genus :
    2 * genus k (FunctionField k p m) = (p - 1) * (m - 1) := by
  have h := two_mul_genus_eq_of_exists_reduced_artinSchreier_pole_ratFunc p
    (adjoin_genY_eq_top k p m) (genY_pow_sub_genY k p m) (Place.infty k) m
    ⟨0, ord_infty_sub k p m⟩ hm.out fun Q hQ ↦ ⟨0, pow_mem_integers k p m hQ⟩
  rw [Place.degree_infty] at h
  have hp := (Fact.out : p.Prime).one_le
  zify [hp, Nat.one_le_iff_ne_zero.mpr (ne_zero_of_not_dvd hm.out)]
  linear_combination h

/-! ### The two classical instances -/

/-- **`y ^ 2 - y = x ^ 3` in characteristic two has genus one.** Its different `4 P_∞` is wild:
with the tame count `P_∞` instead, the Hurwitz formula would read `2 g - 2 = -3`. -/
theorem genus_functionField_two_three [CharP k 2] :
    haveI : Fact (¬ 2 ∣ 3) := ⟨by decide⟩
    genus k (FunctionField k 2 3) = 1 := by
  have : Fact (¬ 2 ∣ 3) := ⟨by decide⟩
  have h := two_mul_genus k 2 3
  omega

/-- **`y ^ p - y = x ^ 2` has genus `(p - 1) / 2`** for an odd prime `p`. -/
theorem two_mul_genus_functionField_two (hp : p ≠ 2) :
    haveI : Fact (¬ p ∣ 2) :=
      ⟨fun h ↦ hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)⟩
    2 * genus k (FunctionField k p 2) = p - 1 := by
  have : Fact (¬ p ∣ 2) :=
    ⟨fun h ↦ hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)⟩
  simpa using two_mul_genus k p 2

end TauCeti.ArtinSchreierMonomial
