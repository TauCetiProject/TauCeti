/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import TauCeti.GroupTheory.Perm.Cycle.Colouring

/-!
# The trace of a permutation of tensor factors

A permutation `σ` of a finite type `ι` acts on the tensor power `M^{⊗ι} = ⨂[R] _ : ι, M` of a
free module of rank `N` by permuting the tensor factors, `PiTensorProduct.reindex`. Its trace is

`tr(σ | M^{⊗ι}) = N ^ c(σ)`,

where `c(σ) = Multiset.card σ.fullCycleType` is the number of cycles of `σ`, fixed points
included. In the basis of pure tensors `e_p = ⨂ᵢ e_{p i}` of `M^{⊗ι}`, indexed by the functions
`p` from `ι` to the `N` indices of a basis of `M`, the permutation sends `e_p` to `e_{p ∘ σ⁻¹}`, so
its trace is the number of `p` constant on the cycles of `σ`
(`Equiv.Perm.card_invariantColouring`): one free choice of basis index for each cycle.

## Main results

* `PiTensorProduct.trace_reindex`: **the trace of a permutation of tensor factors** of a free
  module of finite rank `N` is `N ^ c(σ)`.
-/

public section

open Module

namespace PiTensorProduct

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- **The trace of a permutation of tensor factors.** On the tensor power of a free module of
finite rank `N`, reindexing the factors by `σ` has trace `N ^ c(σ)`, where `c(σ)` is the number of
cycles of `σ`, fixed points included. -/
@[simp]
theorem trace_reindex [Module.Free R M] [Module.Finite R M] (σ : Equiv.Perm ι) :
    LinearMap.trace R _ (reindex R (fun _ : ι => M) σ).toLinearMap =
      (finrank R M : R) ^ Multiset.card σ.fullCycleType := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  set b := Module.Free.chooseBasis R M
  set B := Basis.piTensorProduct fun _ : ι => b
  -- `σ` sends the basis tensor of `p` to that of `p ∘ σ⁻¹`
  have hB : ∀ p : ι → Free.ChooseBasisIndex R M,
      reindex R (fun _ : ι => M) σ (B p) = B (p ∘ σ.symm) := fun p => by
    simp only [B, Basis.piTensorProduct_apply, reindex_tprod, Function.comp_apply]
  have hfix : ∀ p : ι → Free.ChooseBasisIndex R M, p ∘ σ.symm = p ↔ p ∘ σ = p := fun p =>
    (σ.comp_symm_eq p p).trans eq_comm
  rw [LinearMap.trace_eq_matrix_trace R B, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hB,
    Basis.repr_self, Finsupp.single_apply, hfix, Finset.sum_boole]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Equiv.Perm.card_invariantColouring,
    Nat.card_eq_fintype_card, ← finrank_eq_card_chooseBasisIndex, Nat.cast_pow]

end PiTensorProduct
