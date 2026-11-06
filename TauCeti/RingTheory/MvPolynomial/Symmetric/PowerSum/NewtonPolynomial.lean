/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import Mathlib.Data.Multiset.Fintype
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Newton polynomials

The power sum `pₖ = x₁ᵏ + ⋯ + xₙᵏ` is a symmetric polynomial in `n` variables, so by the
fundamental theorem of symmetric polynomials it is a unique polynomial `sₖ(e₁, …, eₙ)` in the
elementary symmetric polynomials `eⱼ`. Following Milnor and Stasheff (§16), `sₖ` is the *Newton
polynomial*. It is defined over every commutative ring, and changing the coefficients along a ring
homomorphism carries the Newton polynomial to the Newton polynomial, so it always has integer
coefficients. For `n` formal roots `x₁, …, xₙ` in any commutative algebra, `sₖ` evaluated at the
elementary symmetric functions of the roots is their `k`-th power sum. It is called
`TauCeti.newtonMvPolynomial` to distinguish it from `TauCeti.newtonPolynomial`, the monic
univariate polynomial with prescribed power sums, which goes in the opposite direction.

In characteristic class theory the `eⱼ` are the Chern classes of a complex vector bundle of rank
`n` and the `xᵢ` its Chern roots; `sₖ(c₁, …, cₙ) / k!` is then the degree-`2k` component of the
Chern character, `TauCeti.chernCharacterPolynomial`. Replacing a bundle by its dual changes `cⱼ`
into `(-1)ʲ cⱼ`, and the Newton polynomial changes by the sign `(-1)ᵏ`.

## Main definitions

* `TauCeti.newtonMvPolynomial R n k`: the polynomial `sₖ` in `n` variables over `R`, where the
  variable `j : Fin n` stands for the elementary symmetric polynomial `e_{j+1}`, following
  `MvPolynomial.esymmAlgHom`.

## Main results

* `TauCeti.aeval_esymm_newtonMvPolynomial`, `TauCeti.eq_newtonMvPolynomial_iff`: `sₖ` is the unique
  polynomial whose value at `e₁, …, eₙ` is the power sum `pₖ`.
* `TauCeti.map_newtonMvPolynomial`: the Newton polynomial is compatible with every change of
  coefficients; in particular it is the image of the integral Newton polynomial.
* `Multiset.aeval_esymm_newtonMvPolynomial`: for a multiset `s` of `n` roots,
  `sₖ(e₁(s), …, eₙ(s)) = ∑_{x ∈ s} xᵏ`.
* `TauCeti.aeval_neg_one_pow_mul_newtonMvPolynomial`: replacing each `eⱼ` by `(-1)ʲ eⱼ`
  multiplies `sₖ` by `(-1)ᵏ`.
* `TauCeti.aeval_snoc_zero_newtonMvPolynomial`: in positive degree the Newton polynomial is
  unchanged by setting `eₙ₊₁ = 0` in the polynomial for `n + 1` variables.
* `TauCeti.newtonMvPolynomial_zero_right`, `TauCeti.newtonMvPolynomial_one_right`,
  `TauCeti.newtonMvPolynomial_two_right`, `TauCeti.newtonMvPolynomial_three_right`: `s₀ = n`,
  `s₁ = e₁`, `s₂ = e₁² - 2e₂` and `s₃ = e₁³ - 3e₁e₂ + 3e₃`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §16 and Problem 16-A.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable (R : Type*) [CommRing R] (n k : ℕ)

/-- The **Newton polynomial** `sₖ` in `n` variables: the unique polynomial such that
substituting the elementary symmetric polynomials `e₁, …, eₙ` of `x₁, …, xₙ` gives the power sum
`x₁ᵏ + ⋯ + xₙᵏ`. The variable `j : Fin n` stands for `e_{j+1}`, following
`MvPolynomial.esymmAlgHom`. -/
noncomputable def newtonMvPolynomial : MvPolynomial (Fin n) R :=
  (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).symm
    ⟨psum (Fin n) R k, psum_isSymmetric (Fin n) R k⟩

/-- The defining property of `TauCeti.newtonMvPolynomial`: its value at the elementary symmetric
polynomials `e₁, …, eₙ` is the power sum `pₖ`. -/
theorem aeval_esymm_newtonMvPolynomial :
    aeval (fun j : Fin n => esymm (Fin n) R (j + 1)) (newtonMvPolynomial R n k) =
      psum (Fin n) R k := by
  rw [← esymmAlgHom_apply, ← esymmAlgEquiv_apply (Fin n) R (Fintype.card_fin n),
    newtonMvPolynomial, AlgEquiv.apply_symm_apply]

variable {R n k} in
/-- `TauCeti.newtonMvPolynomial` is characterized by its value at the elementary symmetric
polynomials. -/
theorem eq_newtonMvPolynomial_iff {p : MvPolynomial (Fin n) R} :
    p = newtonMvPolynomial R n k ↔
      aeval (fun j : Fin n => esymm (Fin n) R (j + 1)) p = psum (Fin n) R k := by
  refine ⟨fun h => h ▸ aeval_esymm_newtonMvPolynomial R n k, fun h => ?_⟩
  refine esymmAlgHom_injective R (Fintype.card_fin n).ge (Subtype.ext ?_)
  rw [esymmAlgHom_apply, esymmAlgHom_apply, aeval_esymm_newtonMvPolynomial, h]

/-- **Integrality of the Newton polynomial**: changing the coefficients along a ring homomorphism
carries the Newton polynomial to the Newton polynomial. Applied to `Int.castRingHom R`, this says
that the Newton polynomial over `R` is the image of the integral one. -/
@[simp]
theorem map_newtonMvPolynomial {S : Type*} [CommRing S] (f : R →+* S) :
    map f (newtonMvPolynomial R n k) = newtonMvPolynomial S n k := by
  refine eq_newtonMvPolynomial_iff.2 ?_
  have h : (aeval fun j : Fin n => esymm (Fin n) S (j + 1)).toRingHom.comp (map f) =
      (map f).comp (aeval fun j : Fin n => esymm (Fin n) R (j + 1)).toRingHom := by
    ext <;> simp [map_esymm]
  have h' := congrArg (fun φ => φ (newtonMvPolynomial R n k)) h
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h'
  rw [h', aeval_esymm_newtonMvPolynomial]
  simp [psum]

section Roots

variable {R n k} {S : Type*} [CommSemiring S] [Algebra R S]

/-- **Root description of the Newton polynomial**: for a multiset `s` of `n` roots in a
commutative `R`-algebra, `sₖ(e₁(s), …, eₙ(s)) = ∑_{x ∈ s} xᵏ`. -/
theorem _root_.Multiset.aeval_esymm_newtonMvPolynomial (s : Multiset S) (hs : s.card = n) :
    aeval (fun j : Fin n => s.esymm (j + 1)) (newtonMvPolynomial R n k) = (s.map (· ^ k)).sum := by
  classical
  let e : Fin n ≃ s.ToType := Fintype.equivOfCardEq (by simp [hs])
  have hx : (univ.val.map fun i => (e i : S)) = s := by
    conv_rhs => rw [← Multiset.map_univ_coe s, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
    rw [Function.comp_def]
  have h : (fun j : Fin n => (univ.val.map fun i => (e i : S)).esymm (j + 1)) =
      fun j : Fin n => aeval (fun i => (e i : S)) (esymm (Fin n) R (j + 1)) := by
    simp [aeval_esymm_eq_multiset_esymm]
  rw [← hx, h, ← comp_aeval_apply, TauCeti.aeval_esymm_newtonMvPolynomial, psum, map_sum,
    Finset.sum_eq_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def, map_pow, aeval_X]

end Roots

variable {R n k}

/-- A polynomial whose value at the elementary symmetric functions of the variables is their
power sum `pₖ` is the Newton polynomial. -/
private theorem eq_newtonMvPolynomial_of_aeval {p : MvPolynomial (Fin n) R}
    (h : aeval (fun j : Fin n => (univ.val.map (X (R := R) (σ := Fin n))).esymm (j + 1)) p =
      ((univ.val.map (X (R := R) (σ := Fin n))).map (· ^ k)).sum) :
    p = newtonMvPolynomial R n k :=
  aeval_multiset_esymm_X_injective R (Fintype.card_fin n).ge <| by
    rw [h, Multiset.aeval_esymm_newtonMvPolynomial _ (by simp)]

/-- **The Newton polynomial of the dual**: replacing each `eⱼ` by `(-1)ʲ eⱼ` multiplies the
Newton polynomial `sₖ` by `(-1)ᵏ`. For the Chern classes of a complex vector bundle, this is the
effect of passing to the dual bundle, whose Chern roots are the negatives of the original ones. -/
theorem aeval_neg_one_pow_mul_newtonMvPolynomial {S : Type*} [CommRing S] [Algebra R S]
    (c : Fin n → S) :
    aeval (fun j : Fin n => (-1) ^ (j.val + 1) * c j) (newtonMvPolynomial R n k) =
      (-1) ^ k * aeval c (newtonMvPolynomial R n k) := by
  set s := univ.val.map (X (R := R) (σ := Fin n))
  have hs : s.card = n := by simp [s]
  -- The identity holds universally, with the variables in place of `c`.
  have hX : aeval (fun j : Fin n => (-1) ^ (j.val + 1) * X j) (newtonMvPolynomial R n k) =
      (-1) ^ k * newtonMvPolynomial R n k := by
    refine aeval_multiset_esymm_X_injective R (Fintype.card_fin n).ge ?_
    rw [comp_aeval_apply]
    simp only [map_mul, map_pow, map_neg, map_one, aeval_X]
    simp_rw [← Multiset.esymm_neg]
    rw [Multiset.aeval_esymm_newtonMvPolynomial _ (by simp),
      Multiset.aeval_esymm_newtonMvPolynomial _ hs, Multiset.map_map, ← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => neg_pow x k)
  simpa [comp_aeval_apply] using congrArg (aeval c) hX

/-- **Stability of the Newton polynomial**: in positive degree, setting `eₙ₊₁ = 0` in the
Newton polynomial for `n + 1` variables gives the Newton polynomial for `n` variables. -/
@[simp]
theorem aeval_snoc_zero_newtonMvPolynomial {S : Type*} [CommSemiring S] [Algebra R S]
    (hk : k ≠ 0) (c : Fin n → S) :
    aeval (Fin.snoc c 0) (newtonMvPolynomial R (n + 1) k) = aeval c (newtonMvPolynomial R n k) := by
  -- The identity holds universally, with the variables in place of `c`.
  have hX : aeval (Fin.snoc X 0 : Fin (n + 1) → MvPolynomial (Fin n) R)
      (newtonMvPolynomial R (n + 1) k) = newtonMvPolynomial R n k := by
    refine eq_newtonMvPolynomial_of_aeval ?_
    -- The elementary symmetric polynomials of `x₁, …, xₙ, 0` are those of `x₁, …, xₙ`, then `0`.
    have h : (fun j : Fin (n + 1) => aeval
        (fun j : Fin n => (univ.val.map (X (R := R) (σ := Fin n))).esymm (j + 1))
        (Fin.snoc (α := fun _ => MvPolynomial (Fin n) R) X 0 j)) =
        fun j : Fin (n + 1) =>
          (0 ::ₘ univ.val.map (X : Fin n → MvPolynomial (Fin n) R)).esymm (j + 1) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last, map_zero, Fin.val_last, Multiset.esymm_cons_zero,
          Multiset.esymm_of_card_lt (by simp)]
      · rw [Fin.snoc_castSucc, aeval_X, Fin.val_castSucc, Multiset.esymm_cons_zero]
    rw [comp_aeval_apply, h, Multiset.aeval_esymm_newtonMvPolynomial _ (by simp)]
    simp [zero_pow hk]
  rw [← hX, comp_aeval_apply]
  refine congrArg (fun f => aeval f _) (funext fun j => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

variable (R n)

/-- The Newton polynomial of degree zero is the constant `n`, the number of roots. -/
@[simp]
theorem newtonMvPolynomial_zero_right : newtonMvPolynomial R n 0 = n :=
  (eq_newtonMvPolynomial_iff.2 (by simp [psum_zero])).symm

/-- **The linear Newton polynomial**: `s₁ = e₁`. -/
theorem newtonMvPolynomial_one_right : newtonMvPolynomial R (n + 1) 1 = X 0 := by
  refine (eq_newtonMvPolynomial_of_aeval ?_).symm
  rw [Multiset.sum_map_pow_one_eq_esymm, aeval_X, Fin.val_zero]

/-- **The quadratic Newton polynomial**: in at least two variables, `s₂ = e₁² - 2e₂`. -/
theorem newtonMvPolynomial_two_right :
    newtonMvPolynomial R (n + 2) 2 = X 0 ^ 2 - 2 * X 1 := by
  refine (eq_newtonMvPolynomial_of_aeval ?_).symm
  rw [Multiset.sum_map_pow_two_eq_esymm]
  simp only [map_sub, map_mul, map_pow, map_ofNat, aeval_X, Fin.val_zero, Fin.val_one]

/-- **The cubic Newton polynomial**: in at least three variables,
`s₃ = e₁³ - 3e₁e₂ + 3e₃`. -/
theorem newtonMvPolynomial_three_right :
    newtonMvPolynomial R (n + 3) 3 = X 0 ^ 3 - 3 * X 0 * X 1 + 3 * X 2 := by
  refine (eq_newtonMvPolynomial_of_aeval ?_).symm
  have h2 : (2 : Fin (n + 3)).val = 2 := Nat.mod_eq_of_lt (by omega : 2 < n + 3)
  rw [Multiset.sum_map_pow_three_eq_esymm]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_X, Fin.val_zero, Fin.val_one,
    h2]

end TauCeti
