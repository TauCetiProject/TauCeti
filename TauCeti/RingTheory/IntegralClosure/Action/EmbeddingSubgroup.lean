/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import TauCeti.FieldTheory.Galois.Restriction

/-!
# Embedding-subgroup action on integral closures

In a tower `L / E / K` of fields with a base ring `A` acting on `L`, acting on `integralClosure A L`
by `σ : L ≃ₐ[E] L` agrees with acting via `TauCeti.algEquivEquivEmbeddingSubgroup K E L σ` in
`TauCeti.embeddingSubgroup K E L`.

## Main results

* `AlgEquiv.algEquivEquivEmbeddingSubgroup_smul_integralClosure`: acting on `integralClosure A L` by
  `σ : L ≃ₐ[E] L` agrees with acting via `TauCeti.algEquivEquivEmbeddingSubgroup K E L σ`.
-/

public section

/-- Acting on `integralClosure A L` by `σ : L ≃ₐ[E] L` agrees with acting via
`TauCeti.algEquivEquivEmbeddingSubgroup K E L σ : TauCeti.embeddingSubgroup K E L`. -/
@[simp] theorem AlgEquiv.algEquivEquivEmbeddingSubgroup_smul_integralClosure {A K E L : Type*}
    [CommRing A] [Field K] [Field E] [Field L] [Algebra A L] [Algebra K E] [Algebra E L]
    [Algebra K L] [IsScalarTower K E L] [SMulCommClass (L ≃ₐ[K] L) A L]
    [SMulCommClass (L ≃ₐ[E] L) A L] (σ : L ≃ₐ[E] L) (x : integralClosure A L) :
    (TauCeti.algEquivEquivEmbeddingSubgroup K E L σ :
      TauCeti.embeddingSubgroup K E L) • x = σ • x :=
  Subtype.ext (by simp [Subgroup.smul_def, AlgEquiv.smul_def])
