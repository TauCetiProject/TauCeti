/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.Pure.Basic

import TauCeti.Algebra.Module.Injective.Envelope.Existence
import TauCeti.RingTheory.MatlisDuality.Finite

/-!
# Pure embeddings from finite modules over complete local rings

Over a complete Noetherian local ring, every pure embedding from a finitely generated module
admits a linear retraction. For example, a pure inclusion of the base ring into an algebra splits
even when the algebra is infinitely generated.

The proof uses Matlis biduality for finitely generated modules
(Stacks Project, Proposition 47.7.8, Tag 08Z9).
-/

public section

open IsLocalRing TensorProduct

namespace LinearMap.IsPure

/-- Over a complete Noetherian local ring, a pure map from a finitely generated module has a
linear left inverse. -/
theorem exists_leftInverse_of_isAdicComplete
    {R M N : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} (hf : f.IsPure) :
    ∃ g : N →ₗ[R] M, Function.LeftInverse g f := by
  obtain ⟨E, _, _, i, hi⟩ := TauCeti.exists_isInjectiveEnvelope R (ResidueField R)
  have := hi.moduleInjective
  let e := hi.evalEquivOfFinite M
  -- Purity lets us extend the evaluation pairing into the injective hull.
  obtain ⟨F, hF⟩ := Module.Injective.extension_property R E _ _
    (f.rTensor (M →ₗ[R] E)) (hf.rTensor_injective _) (TensorProduct.lift e.toLinearMap)
  refine ⟨e.symm.toLinearMap ∘ₗ TensorProduct.curry F, fun x ↦ e.injective ?_⟩
  rw [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro φ
  simpa only [comp_apply, rTensor_tmul, TensorProduct.lift.tmul, TensorProduct.curry_apply,
    LinearEquiv.coe_coe] using LinearMap.congr_fun hF (x ⊗ₜ[R] φ)

end LinearMap.IsPure
