/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Bases adapted to a subspace

A subspace of a finite-dimensional vector space is spanned by a subset of a finite basis
of the ambient space. The cardinality of that subset is the dimension of the subspace.
This is useful when constructions on coordinate summands must be applied to arbitrary subspaces.
The construction uses Mathlib's `Module.Basis.sumQuot`.
-/

public section

open Submodule

namespace Submodule

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- A subspace of a finite-dimensional vector space is a coordinate summand for a finite basis. -/
theorem exists_basis_span_image_eq (W : Submodule k V) :
    ∃ (b : Module.Basis (Fin (Module.finrank k V)) k V)
      (s : Finset (Fin (Module.finrank k V))),
      span k (b '' (s : Set (Fin (Module.finrank k V)))) = W ∧
        s.card = Module.finrank k W := by
  classical
  let bW := Module.finBasis k W
  let bQ := Module.finBasis k (V ⧸ W)
  let c := bW.sumQuot bQ
  let e : (Fin (Module.finrank k W) ⊕ Fin (Module.finrank k (V ⧸ W))) ≃
      Fin (Module.finrank k V) := Fintype.equivFinOfCardEq
    (Module.finrank_eq_card_basis c).symm
  let b := c.reindex e
  let s := Finset.univ.image (e ∘ Sum.inl)
  have hspan : span k (b '' (s : Set _)) = W := by
    have himage : b '' (s : Set _) = W.subtype '' Set.range bW := by
      ext x
      simp [b, s, c, Module.Basis.sumQuot_inl]
    rw [himage, ← Submodule.map_span, bW.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨b, s, hspan, ?_⟩
  rw [Finset.card_image_of_injective _ (e.injective.comp Sum.inl_injective)]
  simp

end Submodule
