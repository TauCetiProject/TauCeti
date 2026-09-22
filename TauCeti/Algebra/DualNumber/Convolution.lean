/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import TauCeti.Algebra.DualNumber.Basic

/-!
# Convolution with dual-number coefficients

`WithConv.snd_comp_convMul` computes the first-order coefficient of a convolution
product. This product rule is used to differentiate the adjoint action.
-/

public section

namespace WithConv

/-- The infinitesimal coefficient of a convolution product of dual-number-valued maps
satisfies the product rule. No counit or coassociativity assumption is needed. -/
theorem snd_comp_convMul
    {R C B : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [CoalgebraStruct R C] [Semiring B] [Algebra R B]
    (f g : WithConv (C →ₗ[R] DualNumber B)) :
    (TrivSqZeroExt.sndHom B B).restrictScalars R ∘ₗ (f * g).ofConv =
      (WithConv.toConv ((TrivSqZeroExt.fstHom R B B).toLinearMap ∘ₗ f.ofConv) *
        WithConv.toConv ((TrivSqZeroExt.sndHom B B).restrictScalars R ∘ₗ g.ofConv) +
      WithConv.toConv ((TrivSqZeroExt.sndHom B B).restrictScalars R ∘ₗ f.ofConv) *
        WithConv.toConv ((TrivSqZeroExt.fstHom R B B).toLinearMap ∘ₗ g.ofConv)).ofConv := by
  ext c
  simp [Coalgebra.Repr.convMul_apply (Coalgebra.Repr.arbitrary R c),
    Finset.sum_add_distrib]

end WithConv
