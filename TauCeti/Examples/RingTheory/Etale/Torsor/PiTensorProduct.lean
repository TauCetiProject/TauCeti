/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Torsor.PiTensorProduct

/-!
# Tests for finite tensor products of finite étale torsors

The factorwise action is found by instance search once it is enabled locally, both for split
torsors and for tensor products of Galois field extensions, which need not be fields. The rank of
the tensor product is the product of the ranks, and the inclusion of tensor factors along an
injective map of index types is injective.
-/

namespace TauCeti.Algebra

open scoped _root_.TensorProduct
open PiTensorProduct

attribute [local instance] rightRegularMulSemiringAction piMulSemiringAction

/-- A finite tensor product of split torsors is a torsor under the product group. -/
example (ι : Type*) [Finite ι] (G : ι → Type*) [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (A : Type*) [CommRing A] :
    IsFiniteEtaleTorsor (∀ i, G i) A (⨂[A] i, (G i → A)) :=
  inferInstance

/-- For finite Galois extensions `L i` of `K`, the algebra `⨂[K] i, L i` is a torsor under
`∀ i, Gal(L i/K)`, of rank `∏ i, [L i : K]`. -/
example (ι : Type*) [Fintype ι] (K : Type*) [Field K] (L : ι → Type*) [∀ i, Field (L i)]
    [∀ i, Algebra K (L i)] [∀ i, IsGalois K (L i)] [∀ i, FiniteDimensional K (L i)]
    (p : PrimeSpectrum K) :
    IsFiniteEtaleTorsor (∀ i, Gal(L i/K)) K (⨂[K] i, L i) ∧
      Module.rankAtStalk (R := K) (⨂[K] i, L i) p = ∏ i, Nat.card Gal(L i/K) :=
  ⟨inferInstance, by
    rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := ∀ i, Gal(L i/K)), Nat.card_pi]⟩

/-- The inclusion of tensor factors along an injective map of index types is injective. -/
example {σ τ : Type*} [Fintype σ] [Finite τ] [DecidableEq τ] (A : Type*) [CommRing A]
    (G : τ → Type*) [∀ j, Group (G j)] [∀ j, Finite (G j)] {f : σ → τ}
    (hf : Function.Injective f) :
    Function.Injective (fiberwiseMul (R := A) (A := fun j ↦ G j → A) f) :=
  IsFiniteEtaleTorsor.injective_fiberwiseMul G hf

end TauCeti.Algebra
