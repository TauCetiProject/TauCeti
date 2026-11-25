/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.CharP.Invertible
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Derivative identities for power series

For a power series `v` over a commutative semiring and `e, n : ℕ` with `e ≠ 0`,

`e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * v')`,

and for all `e, n : ℕ` (including `e = 0`),

`e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * v'))`.

Over a ring in which `n + 1` is not a zero divisor this is the coefficient of
`X ^ (e * (n + 1) - 1)` in `(v ^ (n + 1))' = (n + 1) v ^ n v'`, divided by `n + 1`. The identity
holds over every commutative semiring because both sides are polynomials with natural-number
coefficients in the coefficients of `v`; the proof specializes the generic power series with
coefficients the variables of `MvPolynomial ℕ ℕ`.

In positive characteristic `p` the division by `n + 1` is unavailable when `p ∣ n + 1`, and this
identity is what replaces it. Applied to the inverse of a unit `u ∈ R⟦X⟧ˣ` over a commutative ring,
since `(u⁻¹)' = -(u⁻¹)² u'`, it yields the universal coefficient identity

`(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`

for `e, k ≥ 1`, which governs the behaviour of residues under a substitution `X ↦ φ` of order `e`.

Substitution by a series satisfying `a' = w(a)` intertwines the weighted derivative
`w d/dX` to the ordinary derivative. The iterated chain rule then reads the constant coefficient
of an iterated weighted derivative as a factorial-scaled coefficient after substitution.

## Main results

* `PowerSeries.derivative_subst_of_derivative_eq_subst`: the weighted chain rule for a
  substitution satisfying `a' = w(a)`.
* `PowerSeries.iterate_derivative_subst`,
  `PowerSeries.constantCoeff_iterate_of_derivative_subst`: iteration and coefficient extraction
  for an operator intertwined with the derivative by substitution.
* `PowerSeries.derivative_map`: the derivative commutes with change of coefficients.
* `PowerSeries.derivative_rescale`: the chain rule `(f(a X))' = a f'(a X)` for rescaling.
* `PowerSeries.rescale_X_mul_derivative`, `PowerSeries.evalNegHom_X_mul_derivative`: rescaling
  and negating the variable commute with the Euler operator `X * d⁄dX`.
* `PowerSeries.X_mul_derivative_multiset_prod_rescale`: if `Q G = X Q'`, the logarithmic
  derivative of `∏_{x ∈ s} Q(x t)` is `∑ₘ gₘ pₘ(s) tᵐ`, with `pₘ(s)` the power sums of `s`.
* `PowerSeries.X_mul_derivative_expand`: the Euler operator `X * d⁄dX` commutes with `X ↦ Xᵖ` up to
  the factor `p`.
* `PowerSeries.iterate_derivative_coe`: iterated derivatives of a polynomial are computed as
  polynomials.
* `PowerSeries.coeff_iterate_derivative_eq_descFactorial`: the `M`-th coefficient of `f⁽ⁱ⁾` is
  `(M + i) (M + i - 1) ⋯ (M + 1)` times the `(M + i)`-th coefficient of `f`.
* `PowerSeries.coeff_X_pow_mul_iterate_derivative`, `PowerSeries.coeff_X_mul_derivative`,
  `PowerSeries.coeff_sub_smul_X_mul_derivative`, `PowerSeries.sub_smul_X_mul_derivative_eq_iff`:
  coefficient action of `Xⁱ f⁽ⁱ⁾`, `X * d⁄dX`, and `f ↦ f - c • (X * d⁄dX f)`, and explicit
  characterization of formal solutions to `f - c • (X * d⁄dX f) = u` over a field.
* `PowerSeries.derivative_algebraMap_polynomial`, `PowerSeries.derivative_polynomial_smul`: the
  derivative of the image of a polynomial, and the Leibniz rule for the action of `R[X]` on
  `A⟦X⟧`.
* `PowerSeries.polynomial_map_algebraMap_smul`: the actions of `R[X]` and `S[X]` on `A⟦X⟧` agree
  along a scalar tower `R → S → A`.
* `PowerSeries.polynomial_C_smul`, `PowerSeries.polynomial_X_smul`,
  `PowerSeries.polynomial_X_pow_smul`, `PowerSeries.polynomial_monomial_smul`: under the action
  of `R[X]` on `A⟦X⟧`, constants act as scalars, `Xʲ` as multiplication by `Xʲ`, and `a Xʲ` as
  `a` times multiplication by `Xʲ`.
* `PowerSeries.smul_derivative_mem`: a submodule over `R[X]` stable under `p • d⁄dX` contains
  `(p * r ^ 2) • x'` whenever it contains `r • x`.
* `PowerSeries.coeff_eq_zero_of_derivative_eq_zero`: in prime characteristic `p`, a series
  with zero derivative is supported on degrees divisible by `p`.
* `PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative`,
  `PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative`:
  `e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * v')` for `e ≠ 0`, and
  its `X *`-shifted form for all `e`.
* `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`: the `e = 1` case
  `coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.
* `PowerSeries.eq_of_X_mul_derivative_eq_mul`: with unique division by positive integers, a series
  with prescribed logarithmic derivative `X f' / f` is determined by its constant coefficient.
* `PowerSeries.X_mul_derivative_mk_eq_mul_C_mul_X_iff`: `X f' = f · u X` for `f = ∑ γₖ Xᵏ` exactly
  when `(k + 1) γ_{k+1} = u γ_k`.
* `PowerSeries.mul_coeff_val_zpow_neg_add_coeff_val_zpow_neg_sub_one_mul_derivative_eq_zero`:
  for a unit `u : R⟦X⟧ˣ` over a commutative ring and `e, k ≥ 1`,
  `(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`.
* `PowerSeries.X_pow_dvd_X_mul_derivative_sub`: `X * d⁄dX` preserves congruence modulo
  `X ^ (n + 1)`.
* `PowerSeries.xLogDeriv`, `PowerSeries.toAdd_xLogDeriv`: `X` times the logarithmic derivative,
  `u ↦ X * u' * u⁻¹`, as a homomorphism from the units of `R⟦X⟧` to the additive group of `R⟦X⟧`,
  over any commutative ring.
* `PowerSeries.eq_of_mul_derivative_eq_mul`: over a commutative ring with `HasUniqueDiv`, a series
  `P` solving `u * d⁄dX P = w * P` for `u` with non-zero-divisor constant coefficient is uniquely
  determined by `constantCoeff P`.
-/

public section

namespace PowerSeries

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The derivative of power series commutes with change of coefficients. -/
@[simp]
theorem derivative_map (φ : R⟦X⟧) (f : R →+* S) : d⁄dX (map f φ) = map f (d⁄dX φ) := by
  ext n
  simp [coeff_derivative]

/-- **The chain rule for rescaling**: the derivative of `f(a X)` is `a f'(a X)`. -/
theorem derivative_rescale (φ : R⟦X⟧) (a : R) : d⁄dX (rescale a φ) = C a * rescale a (d⁄dX φ) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul]
  ring

/-- Iterated derivatives of a polynomial, viewed as a power series, are computed as
polynomials. -/
theorem iterate_derivative_coe (p : Polynomial R) (m : ℕ) :
    (d⁄dX)^[m] (p : R⟦X⟧) = ((Polynomial.derivative^[m] p : Polynomial R) : R⟦X⟧) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, derivative_coe,
      Function.iterate_succ_apply']

/-- The `M`-th coefficient of the `i`-th derivative is the falling factorial
`(M + i) (M + i - 1) ⋯ (M + 1)` times the `(M + i)`-th coefficient. -/
theorem coeff_iterate_derivative_eq_descFactorial (f : R⟦X⟧) (i M : ℕ) :
    coeff M ((d⁄dX)^[i] f) = (M + i).descFactorial i * coeff (M + i) f := by
  rw [coeff_iterate_derivative, Nat.add_descFactorial_eq_ascFactorial]

/-- Multiplying the `i`-th derivative by `Xⁱ` multiplies the `M`-th coefficient by the falling
factorial `M (M - 1) ⋯ (M - i + 1)`. -/
theorem coeff_X_pow_mul_iterate_derivative (f : R⟦X⟧) (i M : ℕ) :
    coeff M (X ^ i * (d⁄dX)^[i] f) = M.descFactorial i * coeff M f := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_eq_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp h), Nat.cast_zero, zero_mul]

/-- Multiplying the derivative by `X` multiplies the `n`-th coefficient by `n`. -/
theorem coeff_X_mul_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX f) = n * coeff n f := by
  have h := coeff_X_pow_mul_iterate_derivative f 1 n
  rwa [pow_one, Function.iterate_one, Nat.descFactorial_one] at h

/-- Rescaling commutes with the Euler operator `X * d⁄dX`. -/
theorem rescale_X_mul_derivative (a : R) (φ : R⟦X⟧) :
    rescale a (X * d⁄dX φ) = X * d⁄dX (rescale a φ) := by
  ext n
  rw [coeff_rescale, coeff_X_mul_derivative, coeff_X_mul_derivative, coeff_rescale]
  ring

/-- The shifted coefficient identity when `n + 1` can be cancelled. -/
private theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative_of_hasUniqueDiv
    [HasUniqueDiv R] (v : R⟦X⟧)
    (e n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * d⁄dX v)) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [coeff_zero_X_mul]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
    rw [hm, coeff_succ_X_mul]
    have h := coeff_derivative (v ^ (n + 1)) m
    rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, ← map_natCast (C (R := R)), coeff_C_mul,
      ← Nat.cast_add_one, ← hm] at h
    apply nsmul_right_injective (Nat.succ_ne_zero n)
    simp only [nsmul_eq_mul]
    rw [← hm, Nat.succ_eq_add_one, h]
    push_cast
    ring

/-- For a power series `v` over any commutative semiring and `e, n : ℕ`, `e` times the coefficient
of `X ^ (e * (n + 1))` in `v ^ (n + 1)` is the coefficient of `X ^ (e * (n + 1))` in
`X * (v ^ n * v')`. -/
theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative
    (v : R⟦X⟧) (e n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * d⁄dX v)) := by
  -- Specialize the identity for the generic power series over `MvPolynomial ℕ ℕ`, which has
  -- no additive torsion.
  let V : (MvPolynomial ℕ ℕ)⟦X⟧ := mk fun i ↦ MvPolynomial.X i
  let f : MvPolynomial ℕ ℕ →+* R := MvPolynomial.eval₂Hom (Nat.castRingHom R) fun i ↦ coeff i v
  have hV : map f V = v := by
    ext i
    simp [V, f]
  have h := congrArg f
    (nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative_of_hasUniqueDiv V e n)
  rwa [map_nsmul, ← coeff_map, ← coeff_map, (map f).map_pow, (map f).map_mul, map_X,
    (map f).map_mul, (map f).map_pow, ← derivative_map, hV] at h

/-- For `e ≠ 0`, `e` times the coefficient of `X ^ (e * (n + 1))` in `v ^ (n + 1)` is the
coefficient of `X ^ (e * (n + 1) - 1)` in `v ^ n * v'`, over any commutative semiring. -/
theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) {e : ℕ} (he : e ≠ 0)
    (n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * d⁄dX v) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
  rw [nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative, hm, coeff_succ_X_mul,
    Nat.add_sub_cancel]

/-- The coefficient of `X ^ (n + 1)` in `v ^ (n + 1)` is the coefficient of `X ^ n` in
`v ^ n * v'`, over any commutative semiring. -/
theorem coeff_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  simpa using nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative v one_ne_zero n

/-- **Uniqueness of a series with prescribed logarithmic derivative.** Over a commutative
semiring with unique division by positive integers, a power series `f` with `X f' = f P`, for a
series `P` without constant term, is determined by `P` and its constant coefficient: comparing
`k`-th coefficients gives `k f_k = ∑_{i + j = k, j ≥ 1} f_i P_j`. -/
theorem eq_of_X_mul_derivative_eq_mul [HasUniqueDiv R] {f g P : R⟦X⟧} (hP : constantCoeff P = 0)
    (hf : X * d⁄dX f = f * P) (hg : X * d⁄dX g = g * P) (h₀ : constantCoeff f = constantCoeff g) :
    f = g := by
  ext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simpa using h₀
    have hsum : ∀ h : R⟦X⟧, (∀ i < k + 1, coeff i h = coeff i f) →
        coeff (k + 1) (h * P) = coeff (k + 1) (f * P) := fun h hh => by
      rw [coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rcases Nat.eq_zero_or_pos p.2 with h2 | h2
      · simp [h2, hP]
      · rw [hh p.1 (by have := Finset.mem_antidiagonal.1 hp; omega)]
    refine (nsmul_right_injective (M := R) (Nat.succ_ne_zero k) ?_).symm
    simp only [nsmul_eq_mul]
    rw [← coeff_X_mul_derivative, ← coeff_X_mul_derivative, hf, hg,
      hsum g fun i hi => (ih i hi).symm]

/-- A power series `∑ γₖ Xᵏ` satisfies `X f' = f · u X` exactly when its coefficients satisfy
`(k + 1) γ_{k+1} = u γ_k`, the recursion of the divided powers `uᵏ / k!`. -/
theorem X_mul_derivative_mk_eq_mul_C_mul_X_iff {γ : ℕ → R} {u : R} :
    X * d⁄dX (mk γ) = mk γ * (C u * X) ↔ ∀ k, (k + 1) • γ (k + 1) = u * γ k := by
  have hc : ∀ k, coeff (k + 1) (mk γ * (C u * X)) = u * γ k := fun k => by
    rw [← mul_assoc, coeff_succ_mul_X, mul_comm, coeff_C_mul, coeff_mk]
  rw [PowerSeries.ext_iff]
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · rw [← hc, ← h, coeff_X_mul_derivative, coeff_mk, nsmul_eq_mul]
  · rcases k with _ | k
    · simp
    · rw [hc, ← h, coeff_X_mul_derivative, coeff_mk, nsmul_eq_mul]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Negating the variable commutes with the Euler operator `X * d⁄dX`. -/
theorem evalNegHom_X_mul_derivative (φ : R⟦X⟧) :
    evalNegHom (X * d⁄dX φ) = X * d⁄dX (evalNegHom φ) :=
  rescale_X_mul_derivative (-1) φ

/-- The Euler operator `X * d⁄dX` commutes with the expansion `X ↦ Xᵖ` up to the factor `p`. -/
theorem X_mul_derivative_expand (p : ℕ) (hp : p ≠ 0) (f : R⟦X⟧) :
    X * d⁄dX (expand p hp f) = (p : R⟦X⟧) * expand p hp (X * d⁄dX f) := by
  ext m
  rw [coeff_X_mul_derivative, ← map_natCast C p, coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero hp), coeff_X_mul_derivative]
    push_cast
    ring
  · rw [mul_zero, mul_zero]

/-- An operator intertwined with the derivative by substitution satisfies the iterated chain
rule. -/
theorem iterate_derivative_subst {a : R⟦X⟧} {D : R⟦X⟧ → R⟦X⟧}
    (hD : ∀ f, d⁄dX (subst a f) = subst a (D f)) (f : R⟦X⟧) (n : ℕ) :
    d⁄dX^[n] (subst a f) = subst a (D^[n] f) := by
  have h : Function.Semiconj (subst a) D derivative := fun f ↦ (hD f).symm
  exact (h.iterate_right n f).symm

/-- If substitution by a series with zero constant coefficient intertwines an operator with the
ordinary derivative, the constant coefficient of its `n`-th iterate is `n !` times the `n`-th
coefficient after substitution. -/
theorem constantCoeff_iterate_of_derivative_subst {a : R⟦X⟧} {D : R⟦X⟧ → R⟦X⟧}
    (ha : constantCoeff a = 0) (hD : ∀ f, d⁄dX (subst a f) = subst a (D f))
    (f : R⟦X⟧) (n : ℕ) :
    constantCoeff (D^[n] f) = n.factorial * coeff n (subst a f) := by
  have hconst : constantCoeff (subst a (D^[n] f)) = constantCoeff (D^[n] f) := by
    rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero ha,
      Algebra.algebraMap_self, RingHom.id_apply]
  rw [← hconst, ← iterate_derivative_subst hD, constantCoeff_iterate_derivative]

/-- If `a' = w(a)`, substitution by `a` intertwines the weighted derivative `w d/dX` with the
ordinary derivative. -/
theorem derivative_subst_of_derivative_eq_subst {a w : R⟦X⟧} (ha : HasSubst a)
    (ha' : d⁄dX a = subst a w) (f : R⟦X⟧) :
    d⁄dX (subst a f) = subst a (w * d⁄dX f) := by
  rw [derivative_subst ha, ha', subst_mul ha, mul_comm]

/-- Universal coefficient identity for a unit `u : R⟦X⟧ˣ` over a commutative ring, in shifted form
for all `e, n : ℕ`:
`e • coeff (e * (n + 1)) (u⁻¹ ^ (n + 1)) + coeff (e * (n + 1)) (X * (u⁻¹ ^ (n + 2) * u')) = 0`. -/
theorem nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
    (u : R⟦X⟧ˣ) (e n : ℕ) :
    e • coeff (e * (n + 1)) ((↑u⁻¹ : R⟦X⟧) ^ (n + 1)) +
      coeff (e * (n + 1)) (X * ((↑u⁻¹ : R⟦X⟧) ^ (n + 2) * d⁄dX (u : R⟦X⟧))) = 0 := by
  have hd : (↑u⁻¹ : R⟦X⟧) ^ (n + 2) * d⁄dX (u : R⟦X⟧) =
      -((↑u⁻¹ : R⟦X⟧) ^ n * d⁄dX (↑u⁻¹ : R⟦X⟧)) := by
    rw [(d⁄dX).leibniz_of_mul_eq_one (Units.inv_mul u), smul_eq_mul]
    ring
  rw [hd, mul_neg, map_neg, nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative,
    add_neg_cancel]

/-- **Universal coefficient identity for negative powers of a unit power series.** For a commutative
ring `R`, a unit `u : R⟦X⟧ˣ`, and `e, k ≥ 1`,
`(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`. -/
theorem mul_coeff_val_zpow_neg_add_coeff_val_zpow_neg_sub_one_mul_derivative_eq_zero
    (u : R⟦X⟧ˣ) {e k : ℕ}
    (he : e ≠ 0) (hk : k ≠ 0) :
    (e : R) * coeff (e * k) (↑(u ^ (-(k : ℤ))) : R⟦X⟧) +
      coeff (e * k - 1) ((↑(u ^ (-(k : ℤ) - 1)) : R⟦X⟧) * d⁄dX (u : R⟦X⟧)) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  have hk1 : (↑(u ^ (-((n + 1 : ℕ) : ℤ))) : R⟦X⟧) = (↑u⁻¹ : R⟦X⟧) ^ (n + 1) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hk2 : (↑(u ^ (-((n + 1 : ℕ) : ℤ) - 1)) : R⟦X⟧) = (↑u⁻¹ : R⟦X⟧) ^ (n + 2) := by
    rw [show -((n + 1 : ℕ) : ℤ) - 1 = -((n + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  rw [hk1, hk2]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
  simpa [nsmul_eq_mul, hm, coeff_succ_X_mul] using
    nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
      u e n

/-- Congruence modulo `X ^ (n + 1)` is preserved by `X * d⁄dX`. -/
theorem X_pow_dvd_X_mul_derivative_sub {a b : R⟦X⟧} {n : ℕ} (h : X ^ (n + 1) ∣ a - b) :
    X ^ (n + 1) ∣ X * d⁄dX a - X * d⁄dX b := by
  obtain ⟨c, hc⟩ := h
  refine ⟨C ((n : R) + 1) * c + X * d⁄dX c, ?_⟩
  rw [← mul_sub, ← map_sub, hc, Derivation.leibniz, derivative_X_pow, smul_eq_mul, smul_eq_mul,
    Nat.add_sub_cancel]
  push_cast
  ring

/-- `X` times the logarithmic derivative, `u ↦ X * u' * u⁻¹`, turns products of units into
sums. Unlike the logarithmic derivative over a `ℚ`-algebra it is defined over every commutative
ring. -/
noncomputable def xLogDeriv : R⟦X⟧ˣ →* Multiplicative R⟦X⟧ where
  toFun u := Multiplicative.ofAdd (X * d⁄dX (u : R⟦X⟧) * ↑u⁻¹)
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add, Units.val_mul, mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
    congr 1
    linear_combination (X * d⁄dX (v : R⟦X⟧) * ↑v⁻¹) * u.mul_inv +
      (X * d⁄dX (u : R⟦X⟧) * ↑u⁻¹) * v.mul_inv

/-- The defining equation of `xLogDeriv`: `xLogDeriv u = X * u' * u⁻¹`. -/
@[simp]
theorem toAdd_xLogDeriv (u : R⟦X⟧ˣ) :
    (xLogDeriv u).toAdd = X * d⁄dX (u : R⟦X⟧) * (↑u⁻¹ : R⟦X⟧) := by
  simp only [xLogDeriv, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]

/-- Over a commutative ring with unique division by positive integers, a formal power series `P`
solving `u * d⁄dX P = w * P`, where `constantCoeff u` is not a zero divisor, is uniquely
determined by its constant coefficient. -/
theorem eq_of_mul_derivative_eq_mul [HasUniqueDiv R] {u P Q w : R⟦X⟧}
    (hu : constantCoeff u ∈ nonZeroDivisors R)
    (hc : constantCoeff P = constantCoeff Q) (hP : u * d⁄dX P = w * P)
    (hQ : u * d⁄dX Q = w * Q) : P = Q := by
  suffices hD : P - Q = 0 from sub_eq_zero.mp hD
  set D := P - Q
  have hD₀ : constantCoeff D = 0 := by rw [map_sub, hc, sub_self]
  have hdeq : u * d⁄dX D = w * D := by rw [map_sub, mul_sub, mul_sub, hP, hQ]
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simpa [coeff_zero_eq_constantCoeff_apply] using hD₀
    · have hm := congrArg (coeff m) hdeq
      have hrhs : coeff m (w * D) = 0 :=
        (coeff_mul m w D).trans <| Finset.sum_eq_zero fun p hp => by
          rw [Finset.mem_antidiagonal] at hp; rw [ih p.2 (by omega), mul_zero]
      have hlhs : coeff m (u * d⁄dX D) = (m + 1) • (constantCoeff u * coeff (m + 1) D) := by
        rw [coeff_mul, Finset.sum_eq_single (0, m)]
        · simp only [coeff_zero_eq_constantCoeff_apply, coeff_derivative, nsmul_eq_mul]
          push_cast; ring
        · intro p hp hne
          rw [Finset.mem_antidiagonal] at hp
          have hp0 : p.1 ≠ 0 ∨ p.2 ≠ m := not_and_or.mp (by simpa [Prod.ext_iff] using hne)
          rw [coeff_derivative, ih (p.2 + 1) (by omega), zero_mul, mul_zero]
        · simp
      rw [hlhs, hrhs] at hm
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hu).mp
        (nsmul_right_injective m.succ_ne_zero (hm.trans (smul_zero _).symm))

end CommRing

/-- The `n`-th coefficient of `f - c • (X * d⁄dX f)` is `(1 - c * n) • coeff n f`. -/
theorem coeff_sub_smul_X_mul_derivative {R A : Type*} [Ring R] [CommRing A] [Module R A]
    (c : R) (f : A⟦X⟧) (n : ℕ) :
    coeff n (f - c • (X * d⁄dX f)) = (1 - c * n) • coeff n f := by
  rw [map_sub, coeff_smul, coeff_X_mul_derivative, ← nsmul_eq_mul, sub_smul, one_smul,
    mul_smul, Nat.cast_smul_eq_nsmul]

/-- For a field `K` and `c : K` such that `1 - c * k ≠ 0` for all `k : ℕ`, a series `f : A⟦X⟧`
solves `f - c • (X * d⁄dX f) = u` if and only if its `k`-th coefficient is
`(1 - c * k)⁻¹ • coeff k u`. -/
theorem sub_smul_X_mul_derivative_eq_iff {K A : Type*} [Field K] [CommRing A] [Module K A]
    {f u : A⟦X⟧} {c : K} (hc : ∀ k : ℕ, (1 : K) - c * k ≠ 0) :
    f - c • (X * d⁄dX f) = u ↔ f = mk fun k => (1 - c * k)⁻¹ • coeff k u := by
  simp only [PowerSeries.ext_iff, coeff_sub_smul_X_mul_derivative, coeff_mk]
  exact forall_congr' fun k => (eq_inv_smul_iff₀ (hc k)).symm

section Algebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The image of a polynomial under `PowerSeries.algebraPolynomial` is differentiated as a
polynomial. -/
@[simp]
theorem derivative_algebraMap_polynomial (p : Polynomial R) :
    d⁄dX (algebraMap (Polynomial R) A⟦X⟧ p) =
      algebraMap (Polynomial R) A⟦X⟧ (Polynomial.derivative p) := by
  rw [algebraMap_apply', algebraMap_apply', derivative_map, derivative_coe]

/-- Iterated derivatives of the image of a polynomial under `PowerSeries.algebraPolynomial`. -/
theorem iterate_derivative_algebraMap_polynomial (p : Polynomial R) (m : ℕ) :
    (d⁄dX)^[m] (algebraMap (Polynomial R) A⟦X⟧ p) =
      algebraMap (Polynomial R) A⟦X⟧ (Polynomial.derivative^[m] p) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, derivative_algebraMap_polynomial,
      Function.iterate_succ_apply']

/-- The Leibniz rule for the action of `R[X]` on `A⟦X⟧` given by
`PowerSeries.algebraPolynomial`. -/
theorem derivative_polynomial_smul (p : Polynomial R) (f : A⟦X⟧) :
    d⁄dX (p • f) = Polynomial.derivative p • f + p • d⁄dX f := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Derivation.leibniz,
    derivative_algebraMap_polynomial, smul_eq_mul, smul_eq_mul, mul_comm f, add_comm]

/-- A constant polynomial acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as the
corresponding scalar. -/
@[simp]
theorem polynomial_C_smul (a : R) (f : A⟦X⟧) : (Polynomial.C a : Polynomial R) • f = a • f := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_apply', Polynomial.coe_C, map_C,
    algebraMap_apply]

/-- The polynomial `Xʲ` acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as multiplication
by the power series `Xʲ`. -/
@[simp]
theorem polynomial_X_pow_smul (j : ℕ) (f : A⟦X⟧) :
    (Polynomial.X ^ j : Polynomial R) • f = X ^ j * f := by
  rw [Algebra.smul_def, algebraMap_apply', Polynomial.coe_pow, Polynomial.coe_X, map_pow, map_X]

/-- The polynomial `X` acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as multiplication
by the power series `X`. -/
@[simp]
theorem polynomial_X_smul (f : A⟦X⟧) : (Polynomial.X : Polynomial R) • f = X * f := by
  simpa using polynomial_X_pow_smul (R := R) 1 f

/-- The monomial `a Xʲ` acts on `A⟦X⟧` through `PowerSeries.algebraPolynomial` as the scalar `a`
times multiplication by the power series `Xʲ`. -/
@[simp]
theorem polynomial_monomial_smul (j : ℕ) (a : R) (f : A⟦X⟧) :
    (Polynomial.monomial j a : Polynomial R) • f = a • (X ^ j * f) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_smul, polynomial_X_pow_smul, polynomial_C_smul]

/-- Along a scalar tower `R → S → A`, a polynomial over `R` acts on `A⟦X⟧` as its image in
`S[X]` does. -/
theorem polynomial_map_algebraMap_smul {S : Type*} [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] (q : Polynomial R) (f : A⟦X⟧) :
    q.map (algebraMap R S) • f = q • f := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_apply', algebraMap_apply',
    ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- Nonzero polynomials over the base field act injectively on power series over any
commutative algebra. -/
instance {k K : Type*} [Field k] [CommRing K] [Algebra k K] :
    Module.IsTorsionFree (Polynomial k) K⟦X⟧ where
  isSMulRegular p hp := by
    have hp' : (p : k⟦X⟧) ≠ 0 := by simpa using hp.ne_zero
    have hu := (isUnit_divided_by_X_pow_order hp').map (map (algebraMap k K))
    intro f g hfg
    simp only [Algebra.smul_def, algebraMap_apply'] at hfg
    rw [← X_pow_order_mul_divXPowOrder (f := (p : k⟦X⟧))] at hfg
    simp only [map_mul, map_pow, map_X, mul_assoc] at hfg
    exact hu.mul_right_injective (X_pow_mul_injective hfg)

end Algebra

section AlgebraCommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If a submodule `S` over `R[X]` is stable under `p • d⁄dX` and contains `r • x`, then it
contains `(p * r ^ 2) • x'`. This is the induction step showing that nonzero multiples of all
derivatives of a series lie in a fixed submodule. -/
theorem smul_derivative_mem {S : Submodule (Polynomial R) A⟦X⟧} {p : Polynomial R}
    (hS : ∀ y ∈ S, p • d⁄dX y ∈ S) {r : Polynomial R} {x : A⟦X⟧} (hx : r • x ∈ S) :
    (p * r ^ 2) • d⁄dX x ∈ S := by
  have key : (p * r ^ 2) • d⁄dX x =
      r • (p • d⁄dX (r • x)) - (p * Polynomial.derivative r) • (r • x) := by
    rw [derivative_polynomial_smul]
    module
  rw [key]
  exact S.sub_mem (S.smul_mem _ (hS _ hx)) (S.smul_mem _ hx)

/-- **Logarithmic derivative of `∏ Q(x t)`**: if `Q G = X Q'`, then for a multiset `s` of roots,
`t F' = F · ∑ₘ gₘ pₘ(s) tᵐ` for `F = ∏_{x ∈ s} Q(x t)`, where `pₘ(s)` is the `m`-th power sum. -/
theorem X_mul_derivative_multiset_prod_rescale {Q G : R⟦X⟧}
    (hG : Q * G = X * d⁄dX Q) (s : Multiset A) :
    X * d⁄dX (s.map fun x => rescale x (Q.map (algebraMap R A))).prod =
      (s.map fun x => rescale x (Q.map (algebraMap R A))).prod *
        mk fun m => algebraMap R A (coeff m G) * (s.map (· ^ m)).sum := by
  induction s using Multiset.induction_on with
  | empty => ext m; simp
  | cons x s ih =>
    have h₁ : X * d⁄dX (Q.map (algebraMap R A)) =
        Q.map (algebraMap R A) * G.map (algebraMap R A) := by
      simpa [derivative_map] using (congrArg (map (algebraMap R A)) hG).symm
    have hx : X * d⁄dX (rescale x (Q.map (algebraMap R A))) =
        rescale x (Q.map (algebraMap R A)) * rescale x (G.map (algebraMap R A)) := by
      rw [derivative_rescale, ← mul_assoc, mul_comm X, ← rescale_X, ← map_mul, h₁, map_mul]
    have hH : (mk fun m => algebraMap R A (coeff m G) * ((x ::ₘ s).map (· ^ m)).sum) =
        rescale x (G.map (algebraMap R A)) +
          mk fun m => algebraMap R A (coeff m G) * (s.map (· ^ m)).sum := by
      ext m
      simp only [Multiset.map_cons, Multiset.sum_cons, coeff_mk, map_add, coeff_rescale, coeff_map]
      ring
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hH]
    linear_combination rescale x (Q.map (algebraMap R A)) * ih +
      (s.map fun x => rescale x (Q.map (algebraMap R A))).prod * hx

end AlgebraCommRing

/-- In prime characteristic, a series with zero derivative has no coefficients outside the
multiples of the characteristic. -/
theorem coeff_eq_zero_of_derivative_eq_zero {R : Type*} [CommRing R] {p : ℕ}
    [Fact p.Prime] [CharP R p] {f : PowerSeries R}
    (hf : derivative f = 0) {n : ℕ} (hn : ¬ p ∣ n) : coeff n f = 0 := by
  have hn0 : n ≠ 0 := fun h ↦ hn (h ▸ dvd_zero p)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
  have h := congrArg (coeff m) hf
  simp only [coeff_derivative, map_zero] at h
  exact (CharP.isUnit_natCast_iff (R := R) (Fact.out : p.Prime)).mpr hn |>.mul_right_eq_zero.mp
    (by simpa [Nat.cast_add, Nat.cast_one, mul_comm] using h)

end PowerSeries
