/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.Algebra.GroupAction.AlgHom

/-!
# Embeddings of a simple field and roots of the minimal polynomial

An embedding of the simple field `F⟮α⟯` into an extension `K` is determined by the image of
its generator, which can be any root in `K` of `minpoly F α`.  Mathlib's
`IntermediateField.algHomAdjoinIntegralEquiv` expresses this using the root multiset.  This file
gives the corresponding equivalence for `Polynomial.rootSet`, the carrier used by polynomial
Galois actions.

## Main definitions

* `TauCeti.rootSetEquivAlgHomAdjoin`: the equivalence between roots of `minpoly F α` in `K`
  and `F`-embeddings `F⟮α⟯ → K`.
-/

public section

namespace TauCeti

open IntermediateField Polynomial

variable (F K : Type*) [Field F] [Field K]
variable {E : Type*} [Field E] [Algebra F E] [Algebra F K]

/-- The roots in `K` of the minimal polynomial of an integral element `α` correspond to the
`F`-embeddings of the simple field `F⟮α⟯` into `K`. -/
noncomputable def rootSetEquivAlgHomAdjoin (α : E) (hα : IsIntegral F α) :
    (minpoly F α).rootSet K ≃ (F⟮α⟯ →ₐ[F] K) :=
  ((Equiv.refl K).subtypeEquiv fun y ↦ by
    rw [Equiv.refl_apply, mem_rootSet, mem_aroots]).trans
    (algHomAdjoinIntegralEquiv F hα).symm

/-- Under `rootSetEquivAlgHomAdjoin`, the embedding corresponding to a root `y` sends the
adjoined generator to `y`. -/
@[simp]
theorem rootSetEquivAlgHomAdjoin_apply_gen (α : E) (hα : IsIntegral F α)
    (y : (minpoly F α).rootSet K) :
    rootSetEquivAlgHomAdjoin F K α hα y (AdjoinSimple.gen F α) = y := by
  exact algHomAdjoinIntegralEquiv_symm_apply_gen F hα _

end TauCeti
