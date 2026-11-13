/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Bialgebra
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Primitive
import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Omega

/-!
# The Hopf algebra of symmetric functions

The bialgebra `Λ_R` of symmetric functions over a commutative ring (`Δ(e_n) = ∑_{i + j = n}
e_i ⊗ e_j`, counit the constant term) is a Hopf algebra. Since `Λ_R` is the polynomial ring on the
elementary symmetric functions `e₁, e₂, …`, the antipode may be prescribed as the algebra
endomorphism with `S(e_n) = (-1)ⁿ h_n`. Both antipode laws are then identities between algebra
homomorphisms out of `Λ_R`, so it suffices to check them on each `e_n`, where they become the
relation `H(t) E(-t) = 1` between the generating functions of the complete homogeneous and the
elementary symmetric functions.

Comparing the antipode law for `h_n`, whose coproduct is `∑_{i + j = n} h_i ⊗ h_j`, with the same
relation shows by induction that also `S(h_n) = (-1)ⁿ e_n`. Hence `S` is an involution. The power
sums `p_n` (`n ≥ 1`) are primitive, so `S(p_n) = -p_n`.

## Main definitions

* `TauCeti.SymmetricFunction.instHopfAlgebra`: the Hopf algebra structure on `Λ_R`.

## Main results

* `TauCeti.SymmetricFunction.antipode_of_stableEsymm`: `S(e_n) = (-1)ⁿ h_n`.
* `TauCeti.SymmetricFunction.antipode_of_stableHsymm`: `S(h_n) = (-1)ⁿ e_n`.
* `TauCeti.SymmetricFunction.antipode_antipode`: `S² = id`.
* `TauCeti.SymmetricFunction.antipode_of_stablePsum`: `S(p_n) = -p_n` for `n ≠ 0`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, Example 25: the antipode of `Λ` and its values on `e_n`, `h_n` and `p_n`.
* The Hopf algebra instance is built with Mathlib's `HopfAlgebra.ofAlgHom` for commutative
  bialgebras.
-/

public section

open Finset MvPolynomial TensorProduct HopfAlgebra

namespace TauCeti

namespace SymmetricFunction

variable (R : Type*) [CommRing R]

/- The antipode is the algebra endomorphism prescribed on the free generators by
`e_(r + 1) ↦ (-1)^(r + 1) h_(r + 1)`. It is written out in the statements below, rather than
named by a private definition, because the Hopf algebra instance must not refer to private
declarations. -/

private theorem antipode_aux_of_stableEsymm (n : ℕ) :
    ((aeval fun r => (-1 : SymmetricFunction R) ^ (r + 1) *
        DirectSum.of _ (r + 1) (stableHsymm R (r + 1))).comp (esymmAlgEquiv R).symm.toAlgHom)
      (DirectSum.of _ n (stableEsymm R n)) =
        (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n) := by
  cases n with
  | zero => simp
  | succ r => simp

/-- The relation `H(t) E(-t) = 1`, with the sign carried by the complete homogeneous factor:
`∑_{i + j = m} (-1)ⁱ hᵢ eⱼ = δ_{m0}`. -/
private theorem sum_antidiagonal_neg_one_pow_mul_of_stableHsymm_mul_of_stableEsymm (m : ℕ) :
    ∑ p ∈ antidiagonal m, (-1 : SymmetricFunction R) ^ p.1 *
        DirectSum.of _ p.1 (stableHsymm R p.1) * DirectSum.of _ p.2 (stableEsymm R p.2) =
      if m = 0 then 1 else 0 := by
  rw [← sum_antidiagonal_of_stableEsymm_mul_neg_one_pow_mul_of_stableHsymm R m,
    ← Nat.sum_antidiagonal_swap]
  exact sum_congr rfl fun p _ => by simp only [Prod.fst_swap, Prod.snd_swap]; ring

section Laws

variable {R} {S : SymmetricFunction R →ₐ[R] SymmetricFunction R}

/-- The left antipode law for an algebra endomorphism with `S(e_n) = (-1)ⁿ h_n`. -/
private theorem lift_comp_comulAlgHom_of_stableEsymm
    (hS : ∀ n, S (DirectSum.of _ n (stableEsymm R n)) =
      (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n)) :
    (Algebra.TensorProduct.lift S (.id R _) fun _ _ ↦ Commute.all _ _).comp
        (Bialgebra.comulAlgHom R (SymmetricFunction R)) =
      (Algebra.ofId R _).comp (Bialgebra.counitAlgHom R (SymmetricFunction R)) :=
  algHom_ext fun n => by
    simp [hS, sum_antidiagonal_neg_one_pow_mul_of_stableHsymm_mul_of_stableEsymm]

/-- The right antipode law for an algebra endomorphism with `S(e_n) = (-1)ⁿ h_n`. -/
private theorem lift_id_comp_comulAlgHom_of_stableEsymm
    (hS : ∀ n, S (DirectSum.of _ n (stableEsymm R n)) =
      (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n)) :
    (Algebra.TensorProduct.lift (.id R _) S fun _ _ ↦ Commute.all _ _).comp
        (Bialgebra.comulAlgHom R (SymmetricFunction R)) =
      (Algebra.ofId R _).comp (Bialgebra.counitAlgHom R (SymmetricFunction R)) :=
  algHom_ext fun n => by
    simp [hS, sum_antidiagonal_of_stableEsymm_mul_neg_one_pow_mul_of_stableHsymm]

end Laws

/-- **The Hopf algebra of symmetric functions**: the antipode is the algebra endomorphism sending
the elementary symmetric function `e_n` to `(-1)ⁿ h_n`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (SymmetricFunction R) :=
  .ofAlgHom
    ((aeval fun r => (-1 : SymmetricFunction R) ^ (r + 1) *
      DirectSum.of _ (r + 1) (stableHsymm R (r + 1))).comp (esymmAlgEquiv R).symm.toAlgHom)
    (by exact lift_comp_comulAlgHom_of_stableEsymm (antipode_aux_of_stableEsymm R))
    (by exact lift_id_comp_comulAlgHom_of_stableEsymm (antipode_aux_of_stableEsymm R))

/-- **The antipode of an elementary symmetric function**: `S(e_n) = (-1)ⁿ h_n`. -/
@[simp]
theorem antipode_of_stableEsymm (n : ℕ) :
    antipode R (DirectSum.of _ n (stableEsymm R n) : SymmetricFunction R) =
      (-1) ^ n * DirectSum.of _ n (stableHsymm R n) :=
  antipode_aux_of_stableEsymm R n

/-- **The antipode of a complete homogeneous symmetric function**: `S(h_n) = (-1)ⁿ e_n`. -/
@[simp]
theorem antipode_of_stableHsymm (n : ℕ) :
    antipode R (DirectSum.of _ n (stableHsymm R n) : SymmetricFunction R) =
      (-1) ^ n * DirectSum.of _ n (stableEsymm R n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain _ | k := n
  · simp
  -- The antipode law `∑ hᵢ S(hⱼ) = ε(h_(k + 1)) = 0` and the relation `∑ hᵢ (-1)ʲ eⱼ = 0` agree
  -- term by term for `j ≤ k`, by induction, so their terms at `j = k + 1` agree.
  have h1 := mul_antipode_lTensor_comul_apply (R := R)
    (DirectSum.of _ (k + 1) (stableHsymm R (k + 1)) : SymmetricFunction R)
  have h2 := sum_antidiagonal_of_stableHsymm_mul_neg_one_pow_mul_of_stableEsymm R (k + 1)
  simp only [comul_of_stableHsymm, Nat.sum_antidiagonal_succ, map_add, map_sum,
    LinearMap.lTensor_tmul, LinearMap.mul'_apply, counit_of_ne_zero R k.succ_ne_zero, map_zero,
    Nat.add_one_ne_zero, ↓reduceIte, stableHsymm_zero, of_stableSymmetricOne, one_mul] at h1 h2
  rw [← h2] at h1
  refine add_right_cancel (h1.trans ?_)
  congr 1
  refine sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [ih p.2 (by omega)]

/-- **The antipode of the symmetric functions is an involution**: `S(S(x)) = x`. -/
@[simp]
theorem antipode_antipode (x : SymmetricFunction R) :
    antipode R (antipode R x) = x := by
  have h : (antipodeAlgHom R (SymmetricFunction R)).comp (antipodeAlgHom R _) = .id R _ :=
    algHom_ext fun n => by
      simp only [AlgHom.comp_apply, antipodeAlgHom_apply, antipode_of_stableEsymm, map_mul,
        map_pow, map_neg, map_one, antipode_of_stableHsymm, AlgHom.id_apply, ← mul_assoc,
        ← mul_pow, neg_mul_neg, mul_one, one_pow, one_mul]
  exact DFunLike.congr_fun h x

/-- **The antipode of a power sum**: `S(p_n) = -p_n` for `n ≠ 0`, since the power sums are
primitive. -/
@[simp]
theorem antipode_of_stablePsum {n : ℕ} (hn : n ≠ 0) :
    antipode R (DirectSum.of _ n (stablePsum R hn) : SymmetricFunction R) =
      -DirectSum.of _ n (stablePsum R hn) :=
  (isPrimitiveElem_of_stablePsum R hn).antipode_eq_neg

end SymmetricFunction

end TauCeti
