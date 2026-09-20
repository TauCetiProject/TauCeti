/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Derivations and powers of ideals

A derivation that preserves two ideals also preserves their product: the Leibniz rule
places its two summands in the product by differentiating one factor at a time. Consequently, a
derivation preserving an ideal preserves every power of that ideal.

The stronger condition that the whole range of a derivation lies in an ideal automatically gives
the required stability. This is useful for finite algebra quotients: once a derivation takes values
in an ideal `I`, it preserves the chosen power `I ^ n` and therefore descends to the quotient by
that power.

## Main results

* `TauCeti.derivationLieAlgebra.mapsTo_mul`: a derivation preserving two ideals
  preserves their product.
* `TauCeti.derivationLieAlgebra.mapsTo_pow`: a derivation preserving an ideal preserves
  all its powers.
* `TauCeti.derivationLieAlgebra.mapsTo_pow_of_range_le`: if the range of a derivation lies in an
  ideal, every power of that ideal is stable under the derivation.
-/

public section

namespace TauCeti

namespace derivationLieAlgebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A derivation preserving two ideals preserves their product. -/
theorem mapsTo_mul (D : derivationLieAlgebra R A) {I J : Ideal A}
    (hI : Set.MapsTo D (I : Set A) (I : Set A))
    (hJ : Set.MapsTo D (J : Set A) (J : Set A)) :
    Set.MapsTo D ((I * J : Ideal A) : Set A) ((I * J : Ideal A) : Set A) := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ fun x y hx hy => ?_
  · intro i hi j hj
    rw [leibniz]
    exact (I * J).add_mem (Ideal.mul_mem_mul (hI hi) hj) (Ideal.mul_mem_mul hi (hJ hj))
  · rw [map_add]
    exact (I * J).add_mem hx hy

/-- A derivation preserving an ideal preserves each power of that ideal. -/
theorem mapsTo_pow (D : derivationLieAlgebra R A) (I : Ideal A)
    (hI : Set.MapsTo D (I : Set A) (I : Set A)) (n : ℕ) :
    Set.MapsTo D ((I ^ n : Ideal A) : Set A) ((I ^ n : Ideal A) : Set A) := by
  induction n with
  | zero =>
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact fun _ _ => Set.mem_univ _
  | succ n hn =>
    rw [Submodule.pow_succ]
    exact mapsTo_mul D hn hI

/-- If the range of a derivation lies in an ideal, then every power of that ideal is
stable under the derivation. -/
theorem mapsTo_pow_of_range_le (D : derivationLieAlgebra R A) (I : Ideal A)
    (hD : LinearMap.range (D : Module.End R A) ≤ I.restrictScalars R) (n : ℕ) :
    Set.MapsTo D ((I ^ n : Ideal A) : Set A) ((I ^ n : Ideal A) : Set A) :=
  mapsTo_pow D I (fun x _ ↦ hD (LinearMap.mem_range_self (D : Module.End R A) x)) n

end derivationLieAlgebra

end TauCeti
