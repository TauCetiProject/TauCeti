/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import TauCeti.Algebra.CharP.Frobenius.TensorProduct

/-!
# The Frobenius endomorphism of a commutative bialgebra over a finite field

Let `S` be a commutative bialgebra over a finite field `K`. Its algebra map is injective, so the
`#K`-power map is a ring endomorphism of `S` and of its tensor square. On the tensor square that
endomorphism is the tensor square of the one on `S`, so it respects comultiplication, and the
counit lands in `K`, where the `#K`-power map is the identity. The `#K`-power map is therefore a
morphism of bialgebras.

Contravariantly this is the Frobenius endomorphism of the affine monoid scheme represented by `S`.
When `S` is a Hopf algebra, this is an affine group-scheme endomorphism. On points over a
`K`-algebra, it raises every coordinate to its `#K`-th power.

## Main declarations

* `TauCeti.frobeniusBialgHom`: the `#K`-power map as a bialgebra endomorphism.

## References

* Mathlib's `FiniteField.frobeniusAlgHom`, the finite-field Frobenius algebra endomorphism.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

variable (K : Type*) [Field K] [Fintype K] (S : Type u) [CommSemiring S] [Bialgebra K S]

/-- **The `#K`-power map of a commutative bialgebra over a finite field, as a bialgebra
endomorphism.** -/
noncomputable def frobeniusBialgHom : S →ₐc[K] S :=
  let : CommRing S := (algebraMap K S).commSemiringToCommRing
  BialgHom.ofAlgHom (FiniteField.frobeniusAlgHom K S)
    (AlgHom.ext fun x => by
      simp only [AlgHom.comp_apply, FiniteField.coe_frobeniusAlgHom,
        map_pow, FiniteField.pow_card])
    (AlgHom.ext fun x => by
      simpa only [AlgHom.comp_apply,
        pow_one, FiniteField.coe_frobeniusAlgHom, map_pow] using
        (tensorProductMap_frobeniusAlgHom_pow_apply K S S 1
          ((Bialgebra.comulAlgHom K S) x)))

/-- The Frobenius bialgebra endomorphism raises an element to its `#K`-th power. -/
@[simp]
theorem frobeniusBialgHom_apply (x : S) : frobeniusBialgHom K S x = x ^ Fintype.card K := by
  let : CommRing S := (algebraMap K S).commSemiringToCommRing
  simp only [frobeniusBialgHom, BialgHom.ofAlgHom_apply,
    FiniteField.coe_frobeniusAlgHom]

end TauCeti
