/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Derivations vanish on algebraic elements in characteristic zero

Let `S` be a domain of characteristic zero and `D` a derivation of `S` vanishing on a subalgebra
`B`. Then `D` vanishes on every element `x` algebraic over `B`. Indeed, if `p` is a nonzero
polynomial over `B` of least degree with `p(x) = 0`, then `D` is `B`-linear and
`0 = D (p(x)) = p'(x) · D x`. In characteristic zero `p'` is nonzero, since `p` is not constant,
and it has smaller degree, so `p'(x) ≠ 0` and hence `D x = 0`.

The characteristic hypothesis cannot be dropped: in characteristic `q` the derivation `d/dX` of
`𝔽_q[X]` vanishes on the subalgebra `𝔽_q[X^q]`, over which `X` is algebraic, but not on `X`.

This is the algebraic input to the nonvanishing of the Jacobian determinant of a family of
polynomials over which the polynomial ring is algebraic
(`SymmetricAlgebra.jacobian_ne_zero`).

## Main results

* `Derivation.apply_eq_zero_of_isAlgebraic`: in a domain of characteristic zero, a derivation
  vanishing on a subalgebra vanishes on every element algebraic over it.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  Chapter 3, for this argument in the proof of the Jacobian criterion.
-/

public section

open Polynomial

namespace Derivation

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [CharZero S] [Algebra R S]

/-- In a domain of characteristic zero, a derivation vanishing on a subalgebra `B` vanishes on
every element algebraic over `B`. -/
theorem apply_eq_zero_of_isAlgebraic (D : Derivation R S S) {B : Subalgebra R S}
    (hD : ∀ b ∈ B, D b = 0) {x : S} (hx : IsAlgebraic B x) : D x = 0 := by
  classical
  -- Since `D` vanishes on `B`, it is a derivation over `B`.
  let D' : Derivation B S S :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun b s ↦ by
        simp [Subalgebra.smul_def, D.leibniz, hD b b.2]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  -- Choose an annihilating polynomial of `x` over `B` of least degree.
  have hex : ∃ n, ∃ p : B[X], p ≠ 0 ∧ aeval x p = 0 ∧ p.natDegree = n :=
    ⟨_, _, hx.choose_spec.1, hx.choose_spec.2, rfl⟩
  obtain ⟨p, hp0, hpx, hpn⟩ := Nat.find_spec hex
  have hinj : Function.Injective (algebraMap B S) := Subtype.val_injective
  -- It is not constant, so its derivative is nonzero of smaller degree.
  have hp1 : p.natDegree ≠ 0 := by
    intro h0
    rw [eq_C_of_natDegree_eq_zero h0, aeval_C, map_eq_zero_iff _ hinj] at hpx
    exact hp0 (by rw [eq_C_of_natDegree_eq_zero h0, hpx, map_zero])
  have hdp : derivative p ≠ 0 := by
    intro h
    have : derivative (p.map (algebraMap B S)) = 0 := by
      rw [derivative_map, h, Polynomial.map_zero]
    rw [derivative_eq_zero, natDegree_map_eq_of_injective hinj] at this
    exact hp1 this
  have hdx : aeval x (derivative p) ≠ 0 := fun h ↦
    (natDegree_derivative_lt hp1).not_ge (hpn ▸ Nat.find_min' hex ⟨_, hdp, h, rfl⟩)
  have h := D'.map_aeval p x
  rw [hpx, map_zero, smul_eq_mul] at h
  exact (mul_eq_zero.1 h.symm).resolve_left hdx

end Derivation
