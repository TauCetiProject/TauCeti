/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Uniqueness of polynomial one-parameter subgroups

Over a characteristic-zero domain, a polynomial one-parameter submonoid of an affine monoid
is determined by its value at parameter one. Indeed, its values at positive natural-number
parameters are powers of that point, and polynomial functions agreeing at these parameters agree
identically. The conclusion is equality of coordinate maps, not just agreement on rational
points, so it also identifies their evaluations in arbitrary, possibly nonreduced, algebras.

The additive parameter law is stated on base-valued points. No finite-type, smoothness or
connectedness hypothesis on the affine monoid is needed. The characteristic-zero and domain
hypotheses are essential for the polynomial identity argument.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
-/

public section

open Polynomial WithConv

namespace AlgHom

variable {R H : Type*} [CommRing R] [CommRing H] [Bialgebra R H]

/-- A polynomial curve satisfying the additive parameter law evaluates at a positive natural
number to the corresponding power of its value at one. -/
theorem aeval_natCast_add_one_comp_of_add (γ : H →ₐ[R] R[X])
    (hγ : ∀ s t : R, toConv ((aeval (s + t)).comp γ) =
      toConv ((aeval s).comp γ) * toConv ((aeval t).comp γ)) (n : ℕ) :
    toConv ((aeval ((n + 1 : ℕ) : R)).comp γ) =
      toConv ((aeval (1 : R)).comp γ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, hγ, ih, ← pow_succ]

/-- Polynomial one-parameter submonoids of an affine monoid over a characteristic-zero domain
are determined by their value at one. Equality here is equality of regular coordinate maps. -/
theorem eq_of_aeval_one_comp_eq [IsDomain R] [CharZero R]
    (γ δ : H →ₐ[R] R[X])
    (hγ : ∀ s t : R, toConv ((aeval (s + t)).comp γ) =
      toConv ((aeval s).comp γ) * toConv ((aeval t).comp γ))
    (hδ : ∀ s t : R, toConv ((aeval (s + t)).comp δ) =
      toConv ((aeval s).comp δ) * toConv ((aeval t).comp δ))
    (h : (aeval (1 : R)).comp γ = (aeval (1 : R)).comp δ) : γ = δ := by
  apply AlgHom.ext
  intro x
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    ((Nat.cast_injective (R := R)).comp Nat.succ_injective)).mono
  rintro _ ⟨n, rfl⟩
  have hn : (aeval ((n + 1 : ℕ) : R)).comp γ =
      (aeval ((n + 1 : ℕ) : R)).comp δ := by
    apply toConv_injective
    rw [aeval_natCast_add_one_comp_of_add γ hγ,
      aeval_natCast_add_one_comp_of_add δ hδ, h]
  simpa using AlgHom.congr_fun hn x

end AlgHom
