/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.CharP.Frobenius.PrimeField

/-!
# Frobenius on tensor products

The tensor product of Frobenius endomorphisms agrees with Frobenius on the tensor product when
the rings have the expected characteristic.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (S T : Type*) [CommRing S] [CommRing T]
  [Algebra (ZMod p) S] [Algebra (ZMod p) T] [CharP S p] [CharP T p]
  [CharP (S ⊗[ZMod p] T) p]

/-- The tensor product of the `p`-power maps is the `p`-power map of the tensor product. -/
theorem map_iterateFrobeniusAlgHom_tensorProduct (n : ℕ) (z : S ⊗[ZMod p] T) :
    Algebra.TensorProduct.map (iterateFrobeniusAlgHom p n S) (iterateFrobeniusAlgHom p n T) z =
      z ^ p ^ n := by
  induction z with
  | zero => rw [map_zero, zero_pow (pow_ne_zero n (Nat.Prime.ne_zero Fact.out))]
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow,
        iterateFrobeniusAlgHom_apply, iterateFrobeniusAlgHom_apply]
  | add x y hx hy => rw [map_add, hx, hy, add_pow_char_pow]

/-- The tensor square of the `p`-power map is the `p`-power map of the tensor square. -/
theorem map_iterateFrobeniusAlgHom_tensorSquare [CharP (S ⊗[ZMod p] S) p]
    (n : ℕ) (z : S ⊗[ZMod p] S) :
    Algebra.TensorProduct.map (iterateFrobeniusAlgHom p n S) (iterateFrobeniusAlgHom p n S) z =
      z ^ p ^ n :=
  map_iterateFrobeniusAlgHom_tensorProduct p S S n z

end TauCeti
