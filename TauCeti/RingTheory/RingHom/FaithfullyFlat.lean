/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import TauCeti.RingTheory.Flat.Pi

/-!
# Faithful flatness of ring homomorphisms

Scalar extension `Algebra.TensorProduct.lTensor` preserves faithful flatness of algebra
homomorphisms, via the pushout identification used by Mathlib's `RingHom.Flat.lTensor`.
A finite family of flat ring homomorphisms `f i : R →+* S i` combines into a faithfully flat ring
homomorphism `RingHom.pi f : R →+* ∀ i, S i` as soon as every maximal ideal of `R` stays proper
under some `f i`.

## Main results

* `RingHom.FaithfullyFlat.lTensor`: scalar extension preserves faithful flatness.
* `RingHom.FaithfullyFlat.pi_of_exists_map_ne_top`: the criterion above.
-/

public section

open scoped TensorProduct

namespace RingHom.FaithfullyFlat

section lTensor

variable {R S : Type*} (A : Type*) {B D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [CommRing B] [Algebra R B]
  [CommRing D] [Algebra R D]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Tensoring an algebra homomorphism with an algebra preserves faithful flatness. -/
theorem lTensor {f : B →ₐ[R] D} (hf : f.FaithfullyFlat) :
    (Algebra.TensorProduct.lTensor (S := S) A f).FaithfullyFlat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end lTensor

/-- **A finite product of flat ring homomorphisms is faithfully flat as soon as no maximal ideal
becomes the unit ideal under every factor.** No single `f i` need be faithfully flat: each maximal
ideal `m` of `R` only has to stay proper under *some* `f i`, and which one may depend on `m`. Since
`m` is maximal, `m.map (f i) ≠ ⊤` holds exactly when some prime of `S i` lies over `m`.

This is `Module.FaithfullyFlat.pi_of_exists_submodule_ne_top` for the `R`-algebra structures
induced by the `f i`, with its condition `m • ⊤ ≠ ⊤` rephrased as `m.map (f i) ≠ ⊤`. The finiteness
of `ι` cannot be dropped: an infinite product of flat modules need not be flat. -/
theorem pi_of_exists_map_ne_top {R ι : Type*} [CommRing R] [_root_.Finite ι] {S : ι → Type*}
    [∀ i, CommRing (S i)] {f : ∀ i, R →+* S i} (hf : ∀ i, (f i).Flat)
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ i, m.map (f i) ≠ ⊤) : (RingHom.pi f).FaithfullyFlat := by
  let _ : ∀ i, Algebra R (S i) := fun i ↦ (f i).toAlgebra
  have _ : ∀ i, Module.Flat R (S i) := hf
  -- `RingHom.FaithfullyFlat` of `RingHom.pi` unfolds to `Module.FaithfullyFlat` of the product
  change Module.FaithfullyFlat R (∀ i, S i)
  refine Module.FaithfullyFlat.pi_of_exists_submodule_ne_top fun m hm ↦ (h m hm).imp fun i hi ↦ ?_
  rwa [Ideal.smul_top_eq_map, Ne, Submodule.restrictScalars_eq_top_iff]

end RingHom.FaithfullyFlat

end
