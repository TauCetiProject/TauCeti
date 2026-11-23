/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction

/-!
# Differentials on reduced Hopf-algebra quotients

Because the quotient morphism `H →ₐc[R] H ⧸ (TauCeti.HopfIdeal.reduction R H).toIdeal` is
surjective, precomposition on counit-valued derivations along it is injective. Consequently,
every bialgebra morphism whose differential at the identity vanishes induces a reduced morphism
whose differential at the identity also vanishes.

## Main results

* `TauCeti.derivationComp_reductionBialgHom_eq_zero`: vanishing of the differential passes to
  `TauCeti.HopfIdeal.reductionBialgHom`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

/-- A bialgebra morphism with zero differential at the identity induces a reduced morphism with
zero differential at the identity. -/
theorem derivationComp_reductionBialgHom_eq_zero
    {R : Type u} [CommRing R] [IsReduced R]
    {H : Type v} [CommRing H] [_root_.HopfAlgebra R H]
    [IsReduced ((H ⧸ nilradical H) ⊗[R] (H ⧸ nilradical H))]
    {H' : Type w} [CommRing H'] [_root_.HopfAlgebra R H']
    [IsReduced ((H' ⧸ nilradical H') ⊗[R] (H' ⧸ nilradical H'))]
    {B : Type*} [Semiring B] [Algebra R B]
    (φ : H →ₐc[R] H') (hφ : derivationComp (B := B) φ = 0) :
    derivationComp (B := B) (HopfIdeal.reductionBialgHom φ) = 0 := by
  let q : H →ₐc[R] H ⧸ (HopfIdeal.reduction R H).toIdeal :=
    Bialgebra.Quotient.mkBialgHom (HopfIdeal.reduction R H).toIdeal
  ext d : 1
  apply derivationComp_injective_of_surjective q
    (Bialgebra.Quotient.mkBialgHom_surjective (HopfIdeal.reduction R H).toIdeal)
  rw [LinearMap.zero_apply, map_zero, ← LinearMap.comp_apply, ← derivationComp_comp,
    HopfIdeal.reductionBialgHom_comp_mkBialgHom, derivationComp_comp, hφ, LinearMap.comp_apply,
    LinearMap.zero_apply]

end TauCeti
