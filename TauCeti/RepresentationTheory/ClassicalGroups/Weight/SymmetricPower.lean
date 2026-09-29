/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The symmetric-power representation of `GL n k` and the basis of `Sym[k]^d(Fin n → k)`.
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
-- The weight spaces of a representation with a basis of weight vectors.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis
-- The multiplicity vector `TauCeti.weightOfMultiset` of a multiset, and its torus character.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Combinatorics

/-!
# The weights of a symmetric power of the standard representation

The standard representation of `GL n k` is the internal direct sum of its weight spaces, the
coordinate lines, with the `i`-th line carrying the weight `Pi.single i 1`
(`TauCeti.isInternal_weightSpace_stdRep`).  This file computes the weight spaces of its symmetric
powers, the representations `Symᵈ(kⁿ)`.

A product `e_{i₁} ⋯ e_{i_d}` of standard basis vectors is again a weight vector: a diagonal matrix
scales it by the product `t_{i₁} ⋯ t_{i_d}` of the corresponding entries, repetitions included.
Its weight is therefore the **multiplicity vector** of the unordered tuple `{i₁, …, i_d}`, which is
`TauCeti.weightOfMultiset`.  Those products are the basis `Module.Basis.symmetricPower` of
`Sym[k]^d(Fin n → k)`, indexed by `Sym (Fin n) d`, and a multiset over `Fin n` is recovered from
its multiplicity vector, so the general machinery of
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis` applies verbatim: the weight-`l` space
is the line spanned by the product indexed by `s` when `l` is the multiplicity vector of `s`, and
is zero otherwise.

This is the exact counterpart of the exterior-power computation of
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.ExteriorPower`, and the difference between
the two is precisely the difference between a subset and a multiset.  In `⋀ᵈ(kⁿ)` the weights are
the `0`/`1` indicators of the `d`-element subsets; in `Symᵈ(kⁿ)` the multiplicities are
unconstrained, so the weights are *all* the nonnegative integer vectors of total degree `d` —
`TauCeti.exists_sym_weightOfMultiset_eq_iff` characterizes them that way, and
`TauCeti.weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq` reads that off as the description of
the weights of `Symᵈ(kⁿ)`: **the exponent vectors of the degree-`d` monomials in `n` variables**,
each of multiplicity one.  That is the weight-space refinement of
`TauCeti.char_symPowerRep_diagonal`, which sums those same monomials into the complete homogeneous
symmetric polynomial `h_d`.

For `d = 0` the only weight is `0`, and for `n = 0` and `d > 0` there is no weight at all, the
symmetric power being zero.  For `0 < n` the largest weight in the dominance order is
`(d, 0, …, 0)`; identifying it as the *highest* weight of `Symᵈ(kⁿ)` needs the highest-weight
classification and is not done here.

## Main results

* `TauCeti.symPowerRep_diagGL_apply_basis`: **a product of standard basis vectors is an
  eigenvector of every diagonal matrix**, with eigenvalue the product of the entries it lists.
* `TauCeti.basis_mem_weightSpace_symPowerRep`: that product lies in the weight space of the
  multiplicity vector of its index.
* `TauCeti.iSup_weightSpace_symPowerRep_eq_top` and
  `TauCeti.isInternal_weightSpace_symPowerRep`: **the symmetric power is the internal direct sum of
  its weight spaces.**
* `TauCeti.weightSpace_symPowerRep_eq_span`: **the weight spaces are the coordinate lines of the
  symmetric-power basis**, with `TauCeti.weightSpace_symPowerRep_eq_bot` for the weights that are
  not multiplicity vectors.
* `TauCeti.finrank_weightSpace_symPowerRep`: every weight of `Symᵈ(kⁿ)` has multiplicity one, while
  `TauCeti.weightSpace_symPowerRep_ne_bot_iff` and
  `TauCeti.weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq` say the weights are exactly the
  multiplicity vectors, that is, exactly the nonnegative vectors of total degree `d`.

## Implementation notes

Everything past the eigenvector computation is an instance of
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis`, which reads the weight spaces of a
representation off a basis of weight vectors; what is specific to the symmetric power is the
product basis, the multiset labelling, and the injectivity of that labelling.  The multiplicity
vector itself and the combinatorics of which vectors arise are
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.Combinatorics`, which mentions no
representation.

The coefficients are pinned to `k : Type` rather than a general universe, as everywhere in the
symmetric-power API: `TauCeti.SymmetricPower` is built on `PiTensorProduct` at that altitude.  The
exterior-power counterpart carries a universe variable for that reason alone.

As in `TauCeti/RepresentationTheory/ClassicalGroups/Weight/Basic.lean`, the statements that pin a
weight space down, rather than merely exhibiting vectors in it, assume that the coefficients
separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field.  Without it the statements are
false: over `𝔽₂` the diagonal torus of `GL n 𝔽₂` is trivial, so every weight space of every
representation is everything.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

section CommRing

variable {k : Type} [CommRing k] {n d : ℕ}

/-! ### The products of standard basis vectors are weight vectors -/

/-- **A product of standard basis vectors is an eigenvector of every diagonal matrix**, with
eigenvalue the product of the entries it lists, repetitions included.

This is deliberately not a `simp` lemma: `Representation.symmetricPower_apply` already rewrites
the left-hand side to `SymmetricPower.map (stdRep k n (diagGL t))`, so it is not in `simp` normal
form. -/
theorem symPowerRep_diagGL_apply_basis (t : Fin n → kˣ) (s : Sym (Fin n) d) :
    symPowerRep k n d (diagGL t) ((Pi.basisFun k (Fin n)).symmetricPower d s) =
      ((s : Multiset (Fin n)).map fun i => (t i : k)).prod •
        (Pi.basisFun k (Fin n)).symmetricPower d s := by
  rw [Representation.symmetricPower_apply,
    SymmetricPower.map_basis_symmetricPower_of_apply_basis (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) (stdRep_diagGL_apply_basisFun t) s]

/-- The product of the standard basis vectors listed by `s` has weight the multiplicity vector of
`s`. -/
theorem basis_mem_weightSpace_symPowerRep (s : Sym (Fin n) d) :
    (Pi.basisFun k (Fin n)).symmetricPower d s ∈
      weightSpace (symPowerRep k n d) (weightOfMultiset (s : Multiset (Fin n))) := by
  rw [mem_weightSpace_iff]
  intro t
  rw [symPowerRep_diagGL_apply_basis, weightChar_weightOfMultiset]
  congr 1
  exact Multiset.prod_hom' (s : Multiset (Fin n)) (Units.coeHom k) t

/-- **The weight spaces of a symmetric power of the standard representation span it**: the
symmetric-power basis consists of weight vectors. -/
theorem iSup_weightSpace_symPowerRep_eq_top :
    ⨆ l : Fin n → ℤ, weightSpace (symPowerRep k n d) l = ⊤ :=
  ((Pi.basisFun k (Fin n)).symmetricPower d).iSup_weightSpace_eq_top
    basis_mem_weightSpace_symPowerRep

end CommRing

/-! ### The weight spaces are the lines of the symmetric-power basis

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section IsCancelMulZero

variable {k : Type} [CommRing k] [IsCancelMulZero k] {n d : ℕ}

/-- **The weight spaces of a symmetric power of the standard representation are the coordinate
lines of the symmetric-power basis**: the weight-`l` space of `Symᵈ(kⁿ)`, for `l` the multiplicity
vector of an unordered `d`-tuple `s`, is the line spanned by the product of the standard basis
vectors listed by `s`. -/
theorem weightSpace_symPowerRep_eq_span
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (s : Sym (Fin n) d) :
    weightSpace (symPowerRep k n d) (weightOfMultiset (s : Multiset (Fin n))) =
      Submodule.span k {(Pi.basisFun k (Fin n)).symmetricPower d s} :=
  ((Pi.basisFun k (Fin n)).symmetricPower d).weightSpace_eq_span
    basis_mem_weightSpace_symPowerRep hchar
    (fun _ _ h => Subtype.val_injective (weightOfMultiset_injective h)) s

/-- **Only the multiplicity vectors are weights** of a symmetric power of the standard
representation. -/
theorem weightSpace_symPowerRep_eq_bot
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ}
    (hl : ∀ s : Sym (Fin n) d, l ≠ weightOfMultiset (s : Multiset (Fin n))) :
    weightSpace (symPowerRep k n d) l = ⊥ :=
  ((Pi.basisFun k (Fin n)).symmetricPower d).weightSpace_eq_bot
    basis_mem_weightSpace_symPowerRep hchar hl

/-- **The weights of `Symᵈ(kⁿ)` are exactly the multiplicity vectors of the unordered `d`-tuples
over `Fin n`.** -/
theorem weightSpace_symPowerRep_ne_bot_iff [Nontrivial k]
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (symPowerRep k n d) l ≠ ⊥ ↔
      ∃ s : Sym (Fin n) d, l = weightOfMultiset (s : Multiset (Fin n)) :=
  ((Pi.basisFun k (Fin n)).symmetricPower d).weightSpace_ne_bot_iff
    basis_mem_weightSpace_symPowerRep hchar l

/-- **The weights of `Symᵈ(kⁿ)` are the exponent vectors of the degree-`d` monomials in `n`
variables**: the nonnegative integer vectors of total degree `d`.  This is the weight-space
refinement of `TauCeti.char_symPowerRep_diagonal`, which sums those monomials into the complete
homogeneous symmetric polynomial. -/
theorem weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq [Nontrivial k]
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (symPowerRep k n d) l ≠ ⊥ ↔ (∀ i, 0 ≤ l i) ∧ ∑ i, l i = d := by
  rw [weightSpace_symPowerRep_ne_bot_iff hchar l, ← exists_sym_weightOfMultiset_eq_iff l]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩

end IsCancelMulZero

section Field

variable {k : Type} [Field k] {n d : ℕ}

/-- **A symmetric power of the standard representation is the internal direct sum of its weight
spaces.** -/
theorem isInternal_weightSpace_symPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ => weightSpace (symPowerRep k n d) l :=
  ((Pi.basisFun k (Fin n)).symmetricPower d).isInternal_weightSpace
    basis_mem_weightSpace_symPowerRep hchar

/-- **Every weight of `Symᵈ(kⁿ)` has multiplicity one.** -/
theorem finrank_weightSpace_symPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (s : Sym (Fin n) d) :
    Module.finrank k (weightSpace (symPowerRep k n d)
      (weightOfMultiset (s : Multiset (Fin n)))) = 1 :=
  ((Pi.basisFun k (Fin n)).symmetricPower d).finrank_weightSpace_eq_one
    basis_mem_weightSpace_symPowerRep hchar
    (fun _ _ h => Subtype.val_injective (weightOfMultiset_injective h)) s

end Field

end TauCeti
