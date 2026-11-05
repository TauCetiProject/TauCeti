/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The cyclic normal-coordinate quotient

For a primitive `e`-th root of unity `ζ`, with `e > 0`, the polynomials fixed by
`z ↦ ζ z` are exactly the polynomials in `z ^ e`. Thus the quotient in the normal
coordinate to a reflecting hyperplane is the power map. The coefficient ring can itself
be a polynomial ring in coordinates along the hyperplane: only the integral-domain
hypothesis and the specified primitive root are needed.

The fixed algebra is Mathlib's `AlgHom.equalizer`, rather than a new invariant-ring
construction. `Polynomial.cyclicInvariantsEquiv` identifies it with a polynomial algebra;
its inclusion is `Polynomial.expand`. Its inverse is `Polynomial.contract`, with an
explicit coefficient formula. The final theorem gives the factor `z ^ (e - 1)` in the
derivative of every invariant, the normal-coordinate contribution to Jacobian divisibility.
No claim about the global Jacobian or general quotient ramification is made here.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §3.5.

The construction uses Mathlib's `Polynomial.expand`, `Polynomial.contract`, and
`AlgHom.equalizer`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommSemiring R] [IsDomain R] {e : ℕ} {ζ : R}

/-- A polynomial is fixed by scalar substitution by a primitive `e`-th root precisely when
all its nonzero coefficients have exponent divisible by `e`. -/
theorem comp_C_mul_X_eq_self_iff (p : R[X]) (hζ : IsPrimitiveRoot ζ e) :
    p.comp (C ζ * X) = p ↔ ∀ n, ¬ e ∣ n → p.coeff n = 0 := by
  constructor
  · intro hp n hn
    have hc := congrArg (fun q : R[X] ↦ q.coeff n) hp
    rw [comp_C_mul_X_coeff] at hc
    have hz : ζ ^ n ≠ 1 := fun h ↦ hn ((hζ.pow_eq_one_iff_dvd n).1 h)
    by_contra hcoeff
    exact hz ((mul_eq_left₀ hcoeff).1 hc)
  · intro hp
    ext n
    rw [comp_C_mul_X_coeff]
    by_cases hn : e ∣ n
    · rw [(hζ.pow_eq_one_iff_dvd n).2 hn, mul_one]
    · rw [hp n hn, zero_mul]

/-- Contracting a scalar-invariant polynomial and then substituting `X ^ e` recovers it. -/
theorem expand_contract_of_comp_C_mul_X_eq_self (p : R[X]) (he : 0 < e)
    (hζ : IsPrimitiveRoot ζ e) (hp : p.comp (C ζ * X) = p) :
    expand R e (contract e p) = p := by
  ext n
  rw [coeff_expand he]
  split_ifs with hn
  · rw [coeff_contract he.ne', Nat.div_mul_cancel hn]
  · exact ((p.comp_C_mul_X_eq_self_iff hζ).1 hp n hn).symm

/-- The normal-coordinate invariants are exactly the image of the power substitution.
The polynomial downstairs is unique, including for the trivial group `e = 1`. -/
theorem comp_C_mul_X_eq_self_iff_existsUnique (p : R[X]) (he : 0 < e)
    (hζ : IsPrimitiveRoot ζ e) :
    p.comp (C ζ * X) = p ↔ ∃! q : R[X], expand R e q = p := by
  constructor
  · intro hp
    exact ⟨contract e p, p.expand_contract_of_comp_C_mul_X_eq_self he hζ hp,
      fun q hq ↦ expand_injective he
        (hq.trans (p.expand_contract_of_comp_C_mul_X_eq_self he hζ hp).symm)⟩
  · rintro ⟨q, rfl, -⟩
    apply (comp_C_mul_X_eq_self_iff _ hζ).2
    intro n hn
    simp [coeff_expand he, hn]

/-- The invariant algebra of a cyclic scalar action is a polynomial algebra. Its inclusion
into the original polynomial ring is the normal-coordinate power map `X ↦ X ^ e`. -/
noncomputable def cyclicInvariantsEquiv (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) :
    R[X] ≃ₐ[R] AlgHom.equalizer (aeval (C ζ * X)) (AlgHom.id R R[X]) :=
  AlgEquiv.ofBijective
    ((expand R e).codRestrict
      (AlgHom.equalizer (aeval (C ζ * X)) (AlgHom.id R R[X]))
      (fun q ↦ (comp_C_mul_X_eq_self_iff_existsUnique _ he hζ).2
        ⟨q, rfl, fun q' hq' ↦ expand_injective he hq'⟩))
    ⟨fun _ _ h ↦ expand_injective he (congrArg Subtype.val h), fun p ↦ by
      obtain ⟨q, hq, -⟩ := (comp_C_mul_X_eq_self_iff_existsUnique _ he hζ).1 p.property
      exact ⟨q, Subtype.ext hq⟩⟩

/-- The quotient inclusion is substitution by the power of the normal coordinate. -/
@[simp]
theorem coe_cyclicInvariantsEquiv (he : 0 < e) (hζ : IsPrimitiveRoot ζ e) (q : R[X]) :
    (cyclicInvariantsEquiv he hζ q : R[X]) = expand R e q := (rfl)

/-- The inverse of the quotient presentation discards the zero coefficients between
successive multiples of `e`. -/
theorem cyclicInvariantsEquiv_symm_apply (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (p : AlgHom.equalizer (aeval (C ζ * X)) (AlgHom.id R R[X])) :
    (cyclicInvariantsEquiv he hζ).symm p = contract e (p : R[X]) := by
  apply expand_injective he
  rw [← coe_cyclicInvariantsEquiv he hζ, AlgEquiv.apply_symm_apply]
  exact (expand_contract_of_comp_C_mul_X_eq_self _ he hζ p.property).symm

/-- The coefficients downstairs are the coefficients at multiples of `e` upstairs. -/
@[simp]
theorem coeff_cyclicInvariantsEquiv_symm (he : 0 < e) (hζ : IsPrimitiveRoot ζ e)
    (p : AlgHom.equalizer (aeval (C ζ * X)) (AlgHom.id R R[X])) (n : ℕ) :
    ((cyclicInvariantsEquiv he hζ).symm p).coeff n = (p : R[X]).coeff (n * e) := by
  rw [cyclicInvariantsEquiv_symm_apply, coeff_contract he.ne']

/-- In the cyclic normal-coordinate model, every invariant derivative is divisible by
`X ^ (e - 1)`. The factorization retains the polynomial downstairs and its derivative,
so the scalar ramification factor is explicit, even in positive characteristic. -/
theorem derivative_of_comp_C_mul_X_eq_self (p : R[X]) (he : 0 < e)
    (hζ : IsPrimitiveRoot ζ e) (hp : p.comp (C ζ * X) = p) :
    derivative p = expand R e (derivative (contract e p)) * ((e : R[X]) * X ^ (e - 1)) := by
  conv_lhs => rw [← p.expand_contract_of_comp_C_mul_X_eq_self he hζ hp]
  exact derivative_expand e _

end Polynomial
