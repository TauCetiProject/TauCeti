/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Etale.Torsor.Tensor
import TauCeti.RingTheory.Etale.Torsor.Trivial

/-!
# Tests for tensor products of finite étale torsors

The factorwise action is found by instance search once it is enabled locally, both for split
torsors and for tensor products of Galois field extensions, which need not be fields.
-/

namespace TauCeti.Algebra

open _root_.TensorProduct

attribute [local instance] rightRegularMulSemiringAction
  Algebra.TensorProduct.prodMulSemiringAction

/-- The tensor product of two split torsors is a torsor under the product group. -/
example (G H A : Type*) [Group G] [Group H] [Finite G] [Finite H] [CommRing A] :
    IsFiniteEtaleTorsor (G × H) A ((G → A) ⊗[A] (H → A)) :=
  inferInstance

/-- For finite Galois extensions `L` and `M` of `K`, the algebra `L ⊗[K] M` is a torsor under
`Gal(L/K) × Gal(M/K)`, of rank `[L : K] * [M : K]`. -/
example (K L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [IsGalois K L] [IsGalois K M] [FiniteDimensional K L] [FiniteDimensional K M]
    (p : PrimeSpectrum K) :
    IsFiniteEtaleTorsor (Gal(L/K) × Gal(M/K)) K (L ⊗[K] M) ∧
      Module.rankAtStalk (R := K) (L ⊗[K] M) p = Nat.card Gal(L/K) * Nat.card Gal(M/K) :=
  ⟨inferInstance, by
    rw [IsFiniteEtaleTorsor.rankAtStalk_eq_card (G := Gal(L/K) × Gal(M/K)), Nat.card_prod]⟩

end TauCeti.Algebra
