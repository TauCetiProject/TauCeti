/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Sign
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import TauCeti.GroupTheory.Perm.Cycle.Colouring

/-!
# The character of a permutation of tensor factors

A permutation `σ` of a finite type `ι` acts on the tensor power `M^{⊗ι} = ⨂[R] _ : ι, M` of a
free module of rank `N` by permuting the tensor factors, `PiTensorProduct.reindexRepresentation`.
This file computes its trace:

`tr(σ | M^{⊗ι}) = N ^ c(σ)`,

where `c(σ) = Multiset.card σ.fullCycleType` is the number of cycles of `σ`, fixed points
included. In the basis of pure tensors `e_p = ⨂ᵢ e_{p i}` of `M^{⊗ι}`, indexed by the functions
`p` from `ι` to the `N` indices of a basis of `M`, the permutation sends `e_p` to `e_{p ∘ σ⁻¹}`, so
its trace is the number of `p` constant on the cycles of `σ`
(`Equiv.Perm.card_invariantColouring`): one free choice of basis index for each cycle.

Twisting by a linear character `χ`, such as the sign character
(`PiTensorProduct.signReindexRepresentation`) or one of its powers, multiplies the character by
`χ(σ)`. With the character in hand, Mathlib's identification of the character average with the
dimension of the invariants turns into a formula for the invariants of `W ⊗ M^{⊗ι} ⊗ χ`, and for the
multiplicity of `M^{⊗ι} ⊗ χ` in `W`, for any finite-dimensional representation `W` of the symmetric
group over a field in which `(#ι)!` is nonzero:

`dim (W ⊗ M^{⊗ι} ⊗ χ)^{S_ι} = (1 / (#ι)!) ∑_σ χ_W(σ) · χ(σ) · N ^ c(σ)`.

These are the character averages through which Browning and Sawin express the multiplicities of
`M^{⊗m} ⊗ sgn^ε` in the cohomology of the ordered configuration spaces of the plane, before
comparing them with the coefficients of a product of Euler factors ([BS], proof of Lemma 7.4).

## Main results

* `PiTensorProduct.trace_reindex`: **the trace of a permutation of tensor factors** of a free
  module of finite rank `N` is `N ^ c(σ)`.
* `PiTensorProduct.char_reindexRepresentation` and
  `PiTensorProduct.char_signReindexRepresentation`: the characters of the permutation action and of
  its sign twist.
* `PiTensorProduct.finrank_invariants_tprod_charTwist_reindexRepresentation`: **the dimension of
  the invariants of `W ⊗ M^{⊗ι} ⊗ χ`**, for a linear character `χ`, as a character average.
* `PiTensorProduct.finrank_intertwiningMap_charTwist_reindexRepresentation`: the multiplicity of
  `M^{⊗ι} ⊗ χ` in `W`, the dimension of the equivariant maps into `W`, as a character average.

## References

* [BS] T. Browning and W. Sawin, *A geometric version of the circle method*, Ann. of Math. 191
  (2020), 893–948, proof of Lemma 7.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 2.
-/

public section

open Module TauCeti
open scoped TensorProduct Nat

namespace PiTensorProduct

section CommRing

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- **The trace of a permutation of tensor factors.** On the tensor power of a free module of
finite rank `N`, reindexing the factors by `σ` has trace `N ^ c(σ)`, where `c(σ)` is the number of
cycles of `σ`, fixed points included: in the basis of pure tensors of basis vectors, `σ` permutes
the basis, and fixes exactly the basis tensors whose indices are constant on the cycles of `σ`. -/
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
  have hfix : ∀ p : ι → Free.ChooseBasisIndex R M, p ∘ σ.symm = p ↔ p ∘ σ = p := fun p => by
    rw [funext_iff, funext_iff, ← σ.forall_congr_right]
    simp [eq_comm]
  rw [LinearMap.trace_eq_matrix_trace R B, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hB,
    Basis.repr_self, Finsupp.single_apply, hfix, Finset.sum_boole]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Equiv.Perm.card_invariantColouring,
    Nat.card_eq_fintype_card, ← finrank_eq_card_chooseBasisIndex, Nat.cast_pow]

end CommRing

section Field

variable {k M ι : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [Fintype ι] [DecidableEq ι]

/-- **The character of the permutation action on a tensor power**: a permutation `σ` of the
factors of the tensor power of an `N`-dimensional space has character `N ^ c(σ)`, where `c(σ)` is
the number of cycles of `σ`, fixed points included. -/
@[simp]
theorem char_reindexRepresentation (σ : Equiv.Perm ι) :
    (reindexRepresentation k M ι).character σ =
      (finrank k M : k) ^ Multiset.card σ.fullCycleType := by
  rw [Representation.character, reindexRepresentation_apply, trace_reindex]

/-- **The character of the sign-twisted permutation action on a tensor power** is the sign times
`N ^ c(σ)`, where `c(σ)` is the number of cycles of `σ`, fixed points included. -/
@[simp]
theorem char_signReindexRepresentation (σ : Equiv.Perm ι) :
    (signReindexRepresentation k M ι).character σ =
      ((Equiv.Perm.sign σ : ℤ) : k) * (finrank k M : k) ^ Multiset.card σ.fullCycleType := by
  rw [Representation.character, signReindexRepresentation_apply, map_smul, trace_reindex,
    smul_eq_mul]

variable {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **The invariants of `W ⊗ M^{⊗ι} ⊗ χ`.** Let `W` be a finite-dimensional representation of the
symmetric group of `ι` over a field in which `(#ι)!` is nonzero, `M` a space of dimension `N`, and
`χ` a linear character, such as a power of the sign character. Then the invariants of
`W ⊗ M^{⊗ι} ⊗ χ` have dimension the character average
`(1 / (#ι)!) ∑_σ χ_W(σ) · χ(σ) · N ^ c(σ)`, where `c(σ)` is the number of cycles of `σ`, fixed
points included. -/
theorem finrank_invariants_tprod_charTwist_reindexRepresentation
    (h : ((Fintype.card ι)! : k) ≠ 0) (ρ : Representation k (Equiv.Perm ι) W)
    (χ : Equiv.Perm ι →* kˣ) :
    (finrank k (ρ.tprod ((reindexRepresentation k M ι).charTwist χ)).invariants : k) =
      ((Fintype.card ι)! : k)⁻¹ * ∑ σ : Equiv.Perm ι,
        ρ.character σ * ((χ σ : k) * (finrank k M : k) ^ Multiset.card σ.fullCycleType) := by
  have hG : (Nat.card (Equiv.Perm ι) : k) = ((Fintype.card ι)! : k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have : Invertible (Nat.card (Equiv.Perm ι) : k) := invertibleOfNonzero (hG ▸ h)
  rw [← Representation.card_inv_mul_sum_char_eq_finrank, hG]
  simp only [Representation.char_tensor, Pi.mul_apply, Representation.char_charTwist,
    char_reindexRepresentation]

/-- **The multiplicity of `M^{⊗ι} ⊗ χ` in a representation `W`.** Let `W` be a finite-dimensional
representation of the symmetric group of `ι` over a field in which `(#ι)!` is nonzero, `M` a space
of dimension `N`, and `χ` a linear character. Then the equivariant maps from `M^{⊗ι} ⊗ χ` to `W`
form a space of dimension `(1 / (#ι)!) ∑_σ χ_W(σ) · χ(σ⁻¹) · N ^ c(σ)`, where `c(σ)` is the number
of cycles of `σ`, fixed points included; `σ` and `σ⁻¹` have the same cycles. For a power of the
sign character, `χ(σ⁻¹) = χ(σ)`, and the average agrees with that of
`PiTensorProduct.finrank_invariants_tprod_charTwist_reindexRepresentation`. -/
theorem finrank_intertwiningMap_charTwist_reindexRepresentation
    (h : ((Fintype.card ι)! : k) ≠ 0) (ρ : Representation k (Equiv.Perm ι) W)
    (χ : Equiv.Perm ι →* kˣ) :
    (finrank k (Representation.IntertwiningMap
        ((reindexRepresentation k M ι).charTwist χ) ρ) : k) =
      ((Fintype.card ι)! : k)⁻¹ * ∑ σ : Equiv.Perm ι,
        ρ.character σ * ((χ σ⁻¹ : k) * (finrank k M : k) ^ Multiset.card σ.fullCycleType) := by
  have hG : (Nat.card (Equiv.Perm ι) : k) = ((Fintype.card ι)! : k) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have : Invertible (Nat.card (Equiv.Perm ι) : k) := invertibleOfNonzero (hG ▸ h)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank, hG]
  simp only [Representation.char_charTwist, char_reindexRepresentation,
    Equiv.Perm.fullCycleType_inv]

end Field

end PiTensorProduct
