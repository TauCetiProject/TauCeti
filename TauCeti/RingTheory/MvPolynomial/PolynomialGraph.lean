/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import TauCeti.RingTheory.MvPolynomial.Kronecker
public import TauCeti.RingTheory.MvPolynomial.PowerSubstitution

import TauCeti.Data.Finsupp.Weight

/-!
# The base-`B` Kronecker substitution

For natural numbers `m` and `B`, `MvPolynomial.polynomialGraph R m B` is the ring homomorphism
`R[X_0, …, X_{m-1}] → R[T]` which is the identity on coefficients and sends `X_i` to `T ^ (B ^ i)`.
Its spectrum is the graph `𝔸¹ → 𝔸^m`, `T ↦ (T, T ^ B, T ^ (B ^ 2), …, T ^ (B ^ (m - 1)))`, a
curve defined over the coefficient ring, passing through the origin when `B ≠ 0`
(`MvPolynomial.constantCoeff_comp_polynomialGraph`), whose first coordinate is `T`.

It is the Kronecker substitution of `TauCeti.RingTheory.MvPolynomial.Kronecker` for the weight `i ↦
B ^ i` (`MvPolynomial.polynomialGraph_apply`); for `m = 2` it is the power substitution
`MvPolynomial.powerSubstitution B` (`MvPolynomial.polynomialGraph_fin_two`). The weight `i ↦ B ^ i`
sends the exponent vector `d` to its base-`B` value `∑ i, d i * B ^ i`. By uniqueness of base-`B`
digits this weight is injective on the box of exponent vectors with entries `< B`
(`Finsupp.injOn_weight_pow` in `TauCeti.Data.Finsupp.Weight`). Hence a base `B` exceeding every
exponent of `h` preserves every coefficient of `h` (`MvPolynomial.coeff_polynomialGraph`), and a
nonzero `h` stays nonzero. Since `B` may be chosen after `h`, this produces for every hypersurface
`V(h)` of affine space a curve through the origin, defined over the base ring, that is not contained
in `V(h)`. Straight lines do not suffice: over `𝔽₂` the polynomial `X₀² X₁ - X₀ X₁²` vanishes on
all three rational lines through the origin, but pulls back to `T⁵ + T⁷` along `T ↦ (T, T³)`.

For `m ≠ 0` the substitution is surjective, as `X_0 ↦ T`
(`MvPolynomial.polynomialGraph_surjective`), so the graph is a closed immersion; for `m ≥ 2` it is
not injective, since `X_1 - X_0 ^ B` lies in its kernel
(`MvPolynomial.not_injective_polynomialGraph`).

## Main definitions

* `MvPolynomial.polynomialGraph R m B`: the substitution `X_i ↦ T ^ (B ^ i)`.

## Main results

* `MvPolynomial.coeff_polynomialGraph`: if every exponent of `h` is `< B`, the coefficient of
  `T ^ (∑ i, e i * B ^ i)` in the image of `h` is the coefficient of `X ^ e` in `h`, for every `e`
  with entries `< B`.
* `MvPolynomial.injOn_polynomialGraph`, `MvPolynomial.polynomialGraph_eq_zero_iff`: the
  substitution is injective on the polynomials all of whose exponents are `< B`.
* `MvPolynomial.polynomialGraph_surjective`: the substitution is surjective when `m ≠ 0`.

## References

* L. Kronecker, *Grundzüge einer arithmetischen Theorie der algebraischen Grössen*, J. Reine
  Angew. Math. 92 (1882), for the substitution `X_i ↦ T ^ (B ^ i)`.
* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 and Proposition 5.3.5, where a curve
  through a rational point meeting a dense open set is needed.
-/

public section

noncomputable section

namespace MvPolynomial

open Finsupp

section CommSemiring

variable (R : Type*) [CommSemiring R] (m B : ℕ)

/-- The **base-`B` Kronecker substitution** `R[X_0, …, X_{m-1}] → R[T]`, the identity on
coefficients and `X_i ↦ T ^ (B ^ i)`. Variables are numbered from zero, so `X_0 ↦ T`. Its spectrum
is the graph `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))` from the affine line to affine `m`-space. -/
def polynomialGraph : MvPolynomial (Fin m) R →+* Polynomial R :=
  eval₂Hom Polynomial.C fun i ↦ Polynomial.X ^ (B ^ (i : ℕ))

variable {R m B}

@[simp]
theorem polynomialGraph_C (a : R) : polynomialGraph R m B (C a) = Polynomial.C a :=
  eval₂Hom_C _ _ _

@[simp]
theorem polynomialGraph_X (i : Fin m) :
    polynomialGraph R m B (X i) = Polynomial.X ^ (B ^ (i : ℕ)) :=
  eval₂Hom_X' _ _ _

/-- The substitution is `R`-linear: composed with the coefficient inclusion it is
`Polynomial.C`. -/
theorem polynomialGraph_comp_C : (polynomialGraph R m B).comp C = Polynomial.C :=
  RingHom.ext polynomialGraph_C

/-- The substitution is the Kronecker substitution `aeval (fun i ↦ T ^ (B ^ i))` for the weight
`i ↦ B ^ i`. -/
theorem polynomialGraph_apply (h : MvPolynomial (Fin m) R) :
    polynomialGraph R m B h =
      aeval (fun i : Fin m ↦ (Polynomial.X : Polynomial R) ^ (B ^ (i : ℕ))) h := by
  rw [aeval_def, Polynomial.algebraMap_eq, polynomialGraph, coe_eval₂Hom]

/-- The monomial `a X ^ d` is sent to `a T ^ (∑ i, d i * B ^ i)`. -/
@[simp]
theorem polynomialGraph_monomial (d : Fin m →₀ ℕ) (a : R) :
    polynomialGraph R m B (monomial d a) =
      Polynomial.monomial (weight (fun i : Fin m ↦ B ^ (i : ℕ)) d) a := by
  rw [polynomialGraph_apply, aeval_X_pow_left_monomial]

/-- Evaluating the image of `h` at `a` evaluates `h` at the point `(a, a ^ B, …, a ^ (B ^ (m - 1)))`
of the graph. -/
@[simp]
theorem aeval_polynomialGraph {S : Type*} [CommSemiring S] [Algebra R S] (a : S)
    (h : MvPolynomial (Fin m) R) :
    Polynomial.aeval a (polynomialGraph R m B h) = aeval (fun i : Fin m ↦ a ^ (B ^ (i : ℕ))) h := by
  rw [polynomialGraph_apply, ← AlgHom.comp_apply, comp_aeval]
  simp

/-- Evaluating the image of `h` at `a` evaluates `h` at `(a, a ^ B, …, a ^ (B ^ (m - 1)))`. -/
@[simp]
theorem eval_polynomialGraph (a : R) (h : MvPolynomial (Fin m) R) :
    (polynomialGraph R m B h).eval a = eval (fun i : Fin m ↦ a ^ (B ^ (i : ℕ))) h := by
  rw [← Polynomial.coe_aeval_eq_eval, ← aeval_eq_eval, aeval_polynomialGraph]

/-- For `B ≠ 0` the graph passes through the origin: the constant coefficient of the image of
`h` is the constant coefficient of `h`. For `B = 0` and `m ≥ 2` this fails, since then
`X_1 ↦ 1`. -/
theorem constantCoeff_comp_polynomialGraph (hB : B ≠ 0) :
    Polynomial.constantCoeff.comp (polynomialGraph R m B) = constantCoeff :=
  ringHom_ext (fun a ↦ by simp) fun i ↦ by simp [(pow_ne_zero _ hB).symm]

/-- For `B ≠ 0` the constant coefficient of the image of `h` is the constant coefficient of `h`. -/
@[simp]
theorem coeff_zero_polynomialGraph (hB : B ≠ 0) (h : MvPolynomial (Fin m) R) :
    (polynomialGraph R m B h).coeff 0 = h.coeff 0 :=
  RingHom.congr_fun (constantCoeff_comp_polynomialGraph hB) h

/-- In one variable the substitution is the identification `R[X_0] ≃ R[T]`, `X_0 ↦ T`, for every
base `B`. -/
theorem polynomialGraph_fin_one (h : MvPolynomial (Fin 1) R) :
    polynomialGraph R 1 B h = uniqueAlgEquiv R (Fin 1) h := by
  rw [uniqueAlgEquiv_apply, polynomialGraph, coe_eval₂Hom]
  congr 1
  funext i
  simp [Fin.fin_one_eq_zero i]

/-- In two variables the substitution is the power substitution `Z ↦ T`, `W ↦ T ^ B`, for every
base `B`. -/
theorem polynomialGraph_fin_two (h : MvPolynomial (Fin 2) R) :
    polynomialGraph R 2 B h = powerSubstitution B h := by
  rw [polynomialGraph_apply, powerSubstitution_eq_aeval_X_pow]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The substitution commutes with a ring map applied to the coefficients. -/
@[simp]
theorem polynomialGraph_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (h : MvPolynomial (Fin m) R) :
    polynomialGraph S m B (map f h) = Polynomial.map f (polynomialGraph R m B h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d a => simp
  | add p q hp hq => simp [hp, hq, Polynomial.map_add]

/-- For `m ≥ 2` the substitution is not injective over a nontrivial ring: `X_1` and `X_0 ^ B` both
map to `T ^ B`. -/
theorem not_injective_polynomialGraph [Nontrivial R] (hm : 2 ≤ m) :
    ¬ Function.Injective (polynomialGraph R m B) := by
  intro hinj
  have h := @hinj (X ⟨1, hm⟩) (X ⟨0, by omega⟩ ^ B) (by simp)
  have hc := congrArg (fun p : MvPolynomial (Fin m) R ↦ p.coeff (Finsupp.single ⟨1, hm⟩ 1)) h
  simp [coeff_X_pow, Finsupp.single_eq_single_iff, Fin.ext_iff] at hc

/-- **Coefficients survive bounded Kronecker substitution.** If every exponent of every monomial
of `h` is `< B`, then for every exponent vector `e` with entries `< B` the coefficient of
`T ^ (∑ i, e i * B ^ i)` in the image of `h` is the coefficient of `X ^ e` in `h`. -/
theorem coeff_polynomialGraph {h : MvPolynomial (Fin m) R} (hh : ∀ d ∈ h.support, ∀ i, d i < B)
    {e : Fin m →₀ ℕ} (he : ∀ i, e i < B) :
    (polynomialGraph R m B h).coeff (weight (fun i : Fin m ↦ B ^ (i : ℕ)) e) = h.coeff e := by
  rw [polynomialGraph_apply]
  exact coeff_aeval_X_pow_weight (injOn_weight_pow m B) (fun d hd ↦ hh d hd) he

/-- The substitution is injective on the polynomials all of whose exponents are `< B`. -/
theorem injOn_polynomialGraph :
    Set.InjOn (polynomialGraph R m B) (restrictSupport R {d : Fin m →₀ ℕ | ∀ i, d i < B}) := by
  have : ⇑(polynomialGraph R m B) =
      aeval fun i : Fin m ↦ (Polynomial.X : Polynomial R) ^ (B ^ (i : ℕ)) :=
    funext polynomialGraph_apply
  rw [this]
  exact injOn_aeval_X_pow (injOn_weight_pow m B)

/-- If every exponent of `h` is `< B`, then the image of `h` vanishes only if `h` does. -/
theorem polynomialGraph_eq_zero_iff {h : MvPolynomial (Fin m) R}
    (hh : ∀ d ∈ h.support, ∀ i, d i < B) : polynomialGraph R m B h = 0 ↔ h = 0 := by
  refine ⟨fun h0 ↦ injOn_polynomialGraph ((mem_restrictSupport_iff (R := R)).mpr fun d hd ↦ hh d hd)
    (Submodule.zero_mem _) (by rw [h0, map_zero]), fun h0 ↦ by rw [h0, map_zero]⟩

/-- For `m ≠ 0` the substitution is surjective, for every base `B`: the polynomial `∑ a_j T ^ j`
is the image of `∑ a_j X_0 ^ j`. -/
theorem polynomialGraph_surjective [NeZero m] : Function.Surjective (polynomialGraph R m B) :=
  fun p ↦ ⟨p.eval₂ C (X 0), by
    rw [Polynomial.hom_eval₂, polynomialGraph_comp_C]
    simp⟩

end CommSemiring

end MvPolynomial
