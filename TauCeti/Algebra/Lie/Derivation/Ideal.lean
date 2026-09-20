/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations and powers of ideals

A derivation that preserves two ideals also preserves their product: the Leibniz rule
places its two summands in the product by differentiating one factor at a time. Consequently, a
derivation preserving an ideal preserves every power of that ideal.

The stronger condition that the whole range of a derivation lies in an ideal automatically gives
the required stability. This is useful for finite algebra quotients: once a derivation takes values
in an ideal `I`, it preserves the chosen power `I ^ n` and therefore descends to the quotient by
that power along `TauCeti.derivationQuotientHom`.

## Main results

* `TauCeti.mem_stableDerivations_mul`: a derivation preserving two ideals preserves their product.
* `TauCeti.mem_stableDerivations_pow`: a derivation preserving an ideal preserves all its powers.
* `TauCeti.mem_stableDerivations_pow_of_range_le`: if the range of a derivation lies in an ideal,
  every power of that ideal is stable under the derivation.

## Implementation notes

Stability is phrased throughout as membership in the Lie subalgebra `TauCeti.stableDerivations`,
the form in which `TauCeti.derivationQuotientHom` consumes it, rather than as a bare `Set.MapsTo`.
The stabilizer is indexed by a submodule over the base ring, so an ideal `I` of `A` enters it as
`I.restrictScalars R`.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- **A derivation preserving two ideals preserves their product.** -/
theorem mem_stableDerivations_mul {D : derivationLieAlgebra R A} {I J : Ideal A}
    (hI : D ∈ stableDerivations R (I.restrictScalars R))
    (hJ : D ∈ stableDerivations R (J.restrictScalars R)) :
    D ∈ stableDerivations R ((I * J).restrictScalars R) := by
  have hI' := (mem_stableDerivations R _ D).mp hI
  have hJ' := (mem_stableDerivations R _ D).mp hJ
  rw [mem_stableDerivations]
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx ⊢
  refine Submodule.mul_induction_on hx ?_ fun y z hy hz => ?_
  · intro i hi j hj
    rw [derivationLieAlgebra.leibniz]
    exact (I * J).add_mem (Ideal.mul_mem_mul (hI' i hi) hj) (Ideal.mul_mem_mul hi (hJ' j hj))
  · rw [map_add]
    exact (I * J).add_mem hy hz

/-- **A derivation preserving an ideal preserves each power of that ideal.** -/
theorem mem_stableDerivations_pow {D : derivationLieAlgebra R A} {I : Ideal A}
    (hI : D ∈ stableDerivations R (I.restrictScalars R)) (n : ℕ) :
    D ∈ stableDerivations R ((I ^ n).restrictScalars R) := by
  induction n with
  | zero =>
    rw [mem_stableDerivations]
    intro x _
    rw [Submodule.restrictScalars_mem, Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n hn =>
    rw [Submodule.pow_succ]
    exact mem_stableDerivations_mul R hn hI

/-- If the range of a derivation lies in an ideal, then every power of that ideal is
stable under the derivation. -/
theorem mem_stableDerivations_pow_of_range_le {D : derivationLieAlgebra R A} {I : Ideal A}
    (hD : LinearMap.range (D : Module.End R A) ≤ I.restrictScalars R) (n : ℕ) :
    D ∈ stableDerivations R ((I ^ n).restrictScalars R) :=
  mem_stableDerivations_pow R ((mem_stableDerivations R _ D).mpr
    fun x _ => hD (LinearMap.mem_range_self (D : Module.End R A) x)) n

end TauCeti
