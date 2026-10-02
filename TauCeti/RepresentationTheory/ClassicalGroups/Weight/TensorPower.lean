/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The tensor-power representation of `GL n k`, the symmetric-group action on the same space, and
-- the commutation of the two.
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower
-- The weight spaces of a representation with a basis of weight vectors.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis
-- The multiplicity vector `TauCeti.weightOfMultiset` of a multiset, and its torus character.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Combinatorics

/-!
# The weights of a tensor power of the standard representation

The standard representation of `GL n k` is the internal direct sum of its weight spaces, the
coordinate lines, with the `i`-th line carrying the weight `Pi.single i 1`
(`TauCeti.isInternal_weightSpace_stdRep`).  This file computes the weight spaces of its tensor
powers, the representations `(kⁿ)^{⊗d}`.

A pure tensor `e_{f 0} ⊗ ⋯ ⊗ e_{f (d-1)}` of standard basis vectors, for `f : Fin d → Fin n`, is
again a weight vector: a diagonal matrix scales it by the product `t_{f 0} ⋯ t_{f (d-1)}` of the
corresponding entries.  Its weight therefore depends on `f` only through the unordered tuple of
its values, and is the multiplicity vector `TauCeti.weightOfMultiset` of that unordered tuple,
exactly the weight the corresponding product of basis vectors carries in `Symᵈ(kⁿ)`.  Those pure
tensors are the basis `Basis.piTensorProduct` of `(kⁿ)^{⊗d}`, indexed by `Fin d → Fin n`.

The difference from the symmetric and exterior powers is that **the labelling is in general not
injective**, and that is the whole point of this file: the tuples of a given content all carry the
same weight, so they span a weight space of that many dimensions, which need not be a line (it is
one exactly when the content admits a single tuple).  The weight-`l` space is therefore the
coordinate *subspace* on the tuples of content `l`
(`TauCeti.weightSpace_tensorPowerRep_eq_span_image`), and its dimension is the number of such
tuples (`TauCeti.finrank_weightSpace_tensorPowerRep`).  That number is the multinomial coefficient
`d!/∏ᵢ lᵢ!`, and the sum of the corresponding monomials is the multinomial expansion of
`(t_0 + ⋯ + t_{n-1})^d`, which is the `d`-th power of the trace that
`TauCeti.char_tensorPowerRep` gives for the character of the tensor power, read on a diagonal
matrix; neither evaluation is carried out here, the dimension being stated as the count itself.

As in `TauCeti/RepresentationTheory/ClassicalGroups/Weight/Basic.lean`, every statement below that
pins a weight space down, rather than merely exhibiting vectors in it — the identification of the
weight spaces with coordinate subspaces, the description of the set of weights, the dimension
count and the internal direct sum — assumes that the coefficients separate weights, in the sense
that `l ↦ weightChar k l` is injective.  This is not automatic: over `𝔽₂` the diagonal torus of
`GL n 𝔽₂` is trivial, so every weight space of every representation is everything, and the
statements are false.  `TauCeti.weightChar_injective` discharges the hypothesis over an infinite
field.

Two features make these weight spaces the arena for the representations cut out of `(kⁿ)^{⊗d}` by
the symmetric group.  The set of weights is the same as for `Symᵈ(kⁿ)` — the nonnegative integer
vectors of total degree `d` — because every unordered tuple is the unordered tuple of an ordered
one (`TauCeti.Sym.ofFn_surjective`).  And the symmetric group acts on each weight space separately
(`TauCeti.map_weightSpace_tensorPowerRep_permTensorActionAlgHom_le`), because the two actions
commute; so once `(kⁿ)^{⊗d}` is the internal direct sum of its weight spaces
(`TauCeti.isInternal_weightSpace_tensorPowerRep`, over a field separating weights), a
subrepresentation cut out by an element of `k[S_d]` — a Young symmetrizer, say — inherits that
decomposition.

## Main results

* `TauCeti.tensorPowerRep_diagGL_apply_basis`: **a pure tensor of standard basis vectors is an
  eigenvector of every diagonal matrix**, with eigenvalue the product of the entries it lists.
* `TauCeti.basis_mem_weightSpace_tensorPowerRep`: that pure tensor lies in the weight space of the
  multiplicity vector of its unordered tuple of indices.
* `TauCeti.iSup_weightSpace_tensorPowerRep_eq_top`: **the weight spaces of a tensor power of the
  standard representation span it**, over any commutative ring, and
  `TauCeti.isInternal_weightSpace_tensorPowerRep`: **the tensor power is their internal direct
  sum**, over a field whose weight characters are distinct.
* `TauCeti.weightSpace_tensorPowerRep_eq_span_image`: **the weight spaces are the coordinate
  subspaces of the tensor basis**, the weight-`l` space being spanned by the pure tensors whose
  indices have content `l`, with `TauCeti.weightSpace_tensorPowerRep_eq_bot` for the weights that
  are not contents.
* `TauCeti.weightSpace_tensorPowerRep_ne_bot_iff_nonneg_sum_eq`: **the weights of `(kⁿ)^{⊗d}` are
  the nonnegative integer vectors of total degree `d`**, the same weights as `Symᵈ(kⁿ)`.
* `TauCeti.finrank_weightSpace_tensorPowerRep`: **the multiplicity of a weight is the number of
  tuples of that content.**
* `TauCeti.map_weightSpace_tensorPowerRep_permTensorActionAlgHom_le`: **the group algebra of the
  symmetric group preserves every weight space.**

Of these, `TauCeti.isInternal_weightSpace_tensorPowerRep`,
`TauCeti.weightSpace_tensorPowerRep_eq_span_image`, `TauCeti.weightSpace_tensorPowerRep_eq_bot`,
`TauCeti.weightSpace_tensorPowerRep_ne_bot_iff_nonneg_sum_eq` and
`TauCeti.finrank_weightSpace_tensorPowerRep` carry the weight-separation hypothesis described
above; the rest hold over any commutative ring.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

section CommRing

variable {k : Type u} [CommRing k] {n d : ℕ}

/-! ### The pure tensors of standard basis vectors are weight vectors -/

/-- **A pure tensor of standard basis vectors is an eigenvector of every diagonal matrix**, with
eigenvalue the product of the entries it lists, repetitions included.

This is deliberately not a `simp` lemma: `Representation.tensorPower_apply` already rewrites the
left-hand side to `PiTensorProduct.map (fun _ => stdRep k n (diagGL t))`, so it is not in `simp`
normal form. -/
theorem tensorPowerRep_diagGL_apply_basis (t : Fin n → kˣ) (f : Fin d → Fin n) :
    tensorPowerRep k n d (diagGL t)
        (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n)) f) =
      (∏ j, (t (f j) : k)) •
        Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n)) f := by
  simp only [Basis.piTensorProduct_apply, Representation.tensorPower_apply,
    PiTensorProduct.map_tprod, stdRep_diagGL_apply_basisFun]
  exact (PiTensorProduct.tprod k).map_smul_univ (fun j => (t (f j) : k)) _

/-- The pure tensor of the standard basis vectors listed by `f` has weight the multiplicity vector
of the unordered tuple of values of `f`. -/
theorem basis_mem_weightSpace_tensorPowerRep (f : Fin d → Fin n) :
    Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n)) f ∈
      weightSpace (tensorPowerRep k n d)
        (weightOfMultiset (TauCeti.Sym.ofFn f : Multiset (Fin n))) := by
  rw [mem_weightSpace_iff]
  intro t
  rw [tensorPowerRep_diagGL_apply_basis, weightChar_weightOfMultiset, TauCeti.Sym.coe_ofFn,
    Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn, Function.comp_def,
    Units.coe_prod]

/-- **The weight spaces of a tensor power of the standard representation span it**: the tensor
basis consists of weight vectors. -/
theorem iSup_weightSpace_tensorPowerRep_eq_top :
    ⨆ l : Fin n → ℤ, weightSpace (tensorPowerRep k n d) l = ⊤ :=
  (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n))).iSup_weightSpace_eq_top
    basis_mem_weightSpace_tensorPowerRep

/-- **The group algebra of the symmetric group preserves every weight space** of a tensor power of
the standard representation: it commutes with the general-linear action, hence with the torus.

This is what lets a subrepresentation of `(kⁿ)^{⊗d}` cut out by an element of `k[S_d]` inherit a
weight decomposition of the tensor power, once there is one to inherit:
`TauCeti.isInternal_weightSpace_tensorPowerRep` supplies it over a field whose weight characters
are distinct. -/
theorem map_weightSpace_tensorPowerRep_permTensorActionAlgHom_le
    (a : MonoidAlgebra k (Equiv.Perm (Fin d))) (l : Fin n → ℤ) :
    (weightSpace (tensorPowerRep k n d) l).map (permTensorActionAlgHom k n d a) ≤
      weightSpace (tensorPowerRep k n d) l :=
  map_weightSpace_le_of_commute l fun t =>
    commute_permTensorActionAlgHom_tensorPowerRep k n d a (diagGL t)

end CommRing

/-! ### The weight spaces are the coordinate subspaces of the tensor basis

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section IsCancelMulZero

variable {k : Type u} [CommRing k] [IsCancelMulZero k] {n d : ℕ}

/-- **The weight spaces of a tensor power of the standard representation are the coordinate
subspaces of the tensor basis**: the weight-`l` space of `(kⁿ)^{⊗d}` is spanned by the pure tensors
of standard basis vectors whose indices have content `l`.  Unlike for the symmetric and exterior
powers, this span need not be a line: all the tuples of one content contribute to the same weight,
and a content is in general realised by more than one tuple. -/
theorem weightSpace_tensorPowerRep_eq_span_image
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (tensorPowerRep k n d) l =
      Submodule.span k (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n)) ''
        {f | weightOfMultiset (TauCeti.Sym.ofFn f : Multiset (Fin n)) = l}) :=
  (Basis.piTensorProduct
      (fun _ : Fin d => Pi.basisFun k (Fin n))).weightSpace_eq_span_image
    basis_mem_weightSpace_tensorPowerRep hchar l

/-- **Only the contents of tuples are weights** of a tensor power of the standard
representation. -/
theorem weightSpace_tensorPowerRep_eq_bot
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ}
    (hl : ∀ f : Fin d → Fin n, l ≠ weightOfMultiset (TauCeti.Sym.ofFn f : Multiset (Fin n))) :
    weightSpace (tensorPowerRep k n d) l = ⊥ :=
  (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n))).weightSpace_eq_bot
    basis_mem_weightSpace_tensorPowerRep hchar hl

/-- **The weights of `(kⁿ)^{⊗d}` are exactly the multiplicity vectors of the unordered tuples of
indices of its basis tensors.** -/
theorem weightSpace_tensorPowerRep_ne_bot_iff [Nontrivial k]
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (tensorPowerRep k n d) l ≠ ⊥ ↔
      ∃ f : Fin d → Fin n, l = weightOfMultiset (TauCeti.Sym.ofFn f : Multiset (Fin n)) :=
  (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n))).weightSpace_ne_bot_iff
    basis_mem_weightSpace_tensorPowerRep hchar l

/-- **The weights of `(kⁿ)^{⊗d}` are the exponent vectors of the degree-`d` monomials in `n`
variables**: the nonnegative integer vectors of total degree `d`.  These are the same weights as
`Symᵈ(kⁿ)` has (`TauCeti.weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq`), every unordered tuple
being the unordered tuple of an ordered one; the two representations differ in the multiplicities,
not in the weights. -/
theorem weightSpace_tensorPowerRep_ne_bot_iff_nonneg_sum_eq [Nontrivial k]
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (tensorPowerRep k n d) l ≠ ⊥ ↔ (∀ i, 0 ≤ l i) ∧ ∑ i, l i = d := by
  rw [weightSpace_tensorPowerRep_ne_bot_iff hchar l, ← exists_sym_weightOfMultiset_eq_iff l]
  refine ⟨fun ⟨f, hf⟩ => ⟨TauCeti.Sym.ofFn f, hf.symm⟩, fun ⟨s, hs⟩ => ?_⟩
  obtain ⟨f, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  exact ⟨f, hs.symm⟩

end IsCancelMulZero

section Field

variable {k : Type u} [Field k] {n d : ℕ}

/-- **A tensor power of the standard representation is the internal direct sum of its weight
spaces.** -/
theorem isInternal_weightSpace_tensorPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ => weightSpace (tensorPowerRep k n d) l :=
  (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n))).isInternal_weightSpace
    basis_mem_weightSpace_tensorPowerRep hchar

/-- **The multiplicity of a weight of `(kⁿ)^{⊗d}` is the number of tuples of that content**: the
basis tensors of that content span the weight space and are part of a basis. -/
theorem finrank_weightSpace_tensorPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    Module.finrank k (weightSpace (tensorPowerRep k n d) l) =
      Nat.card {f : Fin d → Fin n //
        weightOfMultiset (TauCeti.Sym.ofFn f : Multiset (Fin n)) = l} :=
  (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n))).finrank_weightSpace_eq_card
    basis_mem_weightSpace_tensorPowerRep hchar l

end Field

end TauCeti
