/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import TauCeti.Algebra.CharP.Frobenius.PrimeField
public import TauCeti.Algebra.CharP.PrimeFieldAlgebra

/-!
# The Frobenius endomorphism of a commutative bialgebra over a prime field

Let `S` be a commutative bialgebra over `ZMod p`. Its counit makes it nontrivial, so it has
characteristic `p`, and the same argument applies to its tensor square; therefore the `p`-power
map is a ring endomorphism of both. On the tensor square that endomorphism is the tensor square
of the one on `S`, so the `p`-power map respects comultiplication, and the counit lands in the
prime field, where the `p`-power map is the identity. The `p`-power map is therefore a morphism
of bialgebras.

Contravariantly this is the Frobenius endomorphism of the affine group scheme represented by `S`:
on points over a value algebra of characteristic `p` it raises every coordinate to its `p`-th
power.

## Main declarations

* `TauCeti.charP_of_bialgebra` and `TauCeti.charP_tensorSquare_of_bialgebra`: a commutative
  bialgebra over `ZMod p` and its tensor square have characteristic `p`.
* `TauCeti.frobeniusBialgHom`: the `p`-power map as a bialgebra endomorphism.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

variable (p : ℕ) [Fact p.Prime] (S : Type u) [CommRing S] [Bialgebra (ZMod p) S]

/-- **A commutative bialgebra over the prime field has characteristic `p`.** Its counit is an
algebra morphism onto `ZMod p`, which rules out the trivial ring. -/
theorem charP_of_bialgebra : CharP S p :=
  charP_of_algHom_zmod p (Bialgebra.counitAlgHom (ZMod p) S)

/-- **The tensor square of a commutative bialgebra over the prime field has characteristic
`p`.** -/
theorem charP_tensorSquare_of_bialgebra : CharP (S ⊗[ZMod p] S) p :=
  charP_of_algHom_zmod p
    (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom (ZMod p) S)
      (Bialgebra.counitAlgHom (ZMod p) S) fun _ _ => Commute.all _ _)

/-- The tensor square of the `p`-power map is the `p`-power map of the tensor square. -/
private theorem map_frobenius_tmul (z : S ⊗[ZMod p] S) :
    letI : CharP S p := charP_of_bialgebra p S
    Algebra.TensorProduct.map (iterateFrobeniusAlgHom p 1 S) (iterateFrobeniusAlgHom p 1 S) z =
      z ^ p := by
  let : CharP S p := charP_of_bialgebra p S
  let : CharP (S ⊗[ZMod p] S) p := charP_tensorSquare_of_bialgebra p S
  induction z with
  | zero => rw [map_zero, zero_pow (Nat.Prime.ne_zero Fact.out)]
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow,
        iterateFrobeniusAlgHom_apply, iterateFrobeniusAlgHom_apply, pow_one]
  | add x y hx hy => rw [map_add, hx, hy, add_pow_char]

/-- **The `p`-power map of a commutative bialgebra over the prime field, as a bialgebra
endomorphism.** -/
noncomputable def frobeniusBialgHom : S →ₐc[ZMod p] S :=
  letI : CharP S p := charP_of_bialgebra p S
  BialgHom.ofAlgHom (iterateFrobeniusAlgHom p 1 S)
    (AlgHom.ext fun x => by
      rw [AlgHom.comp_apply, iterateFrobeniusAlgHom_apply, pow_one, map_pow, ZMod.pow_card])
    (AlgHom.ext fun x => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, map_frobenius_tmul,
        iterateFrobeniusAlgHom_apply, pow_one, map_pow])

/-- The Frobenius bialgebra endomorphism raises an element to its `p`-th power. -/
@[simp]
theorem frobeniusBialgHom_apply (x : S) : frobeniusBialgHom p S x = x ^ p := by
  let : CharP S p := charP_of_bialgebra p S
  rw [frobeniusBialgHom]
  exact (iterateFrobeniusAlgHom_apply p 1 S x).trans (by rw [pow_one])

end TauCeti
