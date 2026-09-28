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

/-!
# The weights of a symmetric power of the standard representation

The standard representation of `GL n k` is the internal direct sum of its weight spaces, the
coordinate lines, with the `i`-th line carrying the weight `Pi.single i 1`
(`TauCeti.isInternal_weightSpace_stdRep`).  This file computes the weight spaces of its symmetric
powers, the representations `Symᵈ(kⁿ)`.

A product `e_{i₁} ⋯ e_{i_d}` of standard basis vectors is again a weight vector: a diagonal matrix
scales it by the product `t_{i₁} ⋯ t_{i_d}` of the corresponding entries, repetitions included.
Its weight is therefore the **multiplicity vector** of the unordered tuple `{i₁, …, i_d}`, which is
`TauCeti.weightOfMultiset` below.  Those products are the basis `Module.Basis.symmetricPower` of
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
symmetric power being zero.  The largest weight in the dominance order is `(d, 0, …, 0)`;
identifying it as the *highest* weight of `Symᵈ(kⁿ)` needs the highest-weight classification and
is not done here.

## Main definitions

* `TauCeti.weightOfMultiset`: the weight of a multiset over `Fin n`, its multiplicity vector.

## Main results

* `TauCeti.exists_sym_weightOfMultiset_eq_iff`: **the multiplicity vectors of the unordered
  `d`-tuples over `Fin n` are exactly the nonnegative integer vectors summing to `d`.**
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

The multiset weight is packaged as `TauCeti.weightOfMultiset`, taking a bare `Multiset (Fin n)`
rather than an element of `Sym (Fin n) d`: nothing in the definition or in its injectivity uses
the cardinality, and the consumers below apply it to the underlying multiset of a basis index.
The cardinality reappears only in `TauCeti.sum_weightOfMultiset`, which records that a weight of
`Symᵈ(kⁿ)` has total degree `d`.  The vector itself is `Multiset.toFinsupp` read in `ℤ`, but it is
spelled as a plain function rather than through that equivalence because a weight is a plain
function `Fin n → ℤ`: routing it through a `Finsupp` coercion would leave every rewrite below
fighting the coercion for no gain.

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

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

/-! ### The weight of a multiset -/

/-- The **weight of a multiset** over `Fin n`: its multiplicity vector.  This is the weight carried
by the product of the standard basis vectors it lists. -/
def weightOfMultiset {n : ℕ} (s : Multiset (Fin n)) : Fin n → ℤ := fun i => Multiset.count i s

/-- The defining formula for `TauCeti.weightOfMultiset`. -/
@[simp]
theorem weightOfMultiset_apply {n : ℕ} (s : Multiset (Fin n)) (i : Fin n) :
    weightOfMultiset s i = Multiset.count i s :=
  (rfl)

/-- Multiplicities are nonnegative, so the weights of a symmetric power are. -/
theorem weightOfMultiset_nonneg {n : ℕ} (s : Multiset (Fin n)) (i : Fin n) :
    0 ≤ weightOfMultiset s i :=
  Int.natCast_nonneg _

/-- **A multiset is recovered from its weight**, a multiset over `Fin n` being determined by its
multiplicities. -/
theorem weightOfMultiset_injective {n : ℕ} : Function.Injective (weightOfMultiset (n := n)) :=
  fun _ _ h => Multiset.ext.mpr fun i => Nat.cast_injective (congrFun h i)

/-- The weight of a multiset has total degree its cardinality: the weights of `Symᵈ(kⁿ)` all lie
in degree `d`. -/
theorem sum_weightOfMultiset {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, weightOfMultiset s i = Multiset.card s := by
  simp only [weightOfMultiset_apply]
  rw [← Nat.cast_sum, Multiset.sum_count_eq_card fun a _ => Finset.mem_univ a]

/-- **The weights of `Symᵈ(kⁿ)` are the exponent vectors of the degree-`d` monomials in `n`
variables**: an integer vector is the multiplicity vector of an unordered `d`-tuple over `Fin n`
exactly when it is nonnegative and sums to `d`. -/
theorem exists_sym_weightOfMultiset_eq_iff {n d : ℕ} (l : Fin n → ℤ) :
    (∃ s : Sym (Fin n) d, weightOfMultiset (s : Multiset (Fin n)) = l) ↔
      (∀ i, 0 ≤ l i) ∧ ∑ i, l i = d := by
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨weightOfMultiset_nonneg _, by rw [sum_weightOfMultiset, Sym.card_coe]⟩
  · rintro ⟨hnonneg, hsum⟩
    -- assemble the multiset with `(l i).toNat` copies of each `i`
    set m : Multiset (Fin n) := ∑ i : Fin n, Multiset.replicate (l i).toNat i with hm
    have hcount : ∀ j, Multiset.count j m = (l j).toNat := by
      intro j
      simp [hm, Multiset.count_sum', Multiset.count_replicate]
    have hweight : weightOfMultiset m = l := by
      funext j
      rw [weightOfMultiset_apply, hcount j, Int.toNat_of_nonneg (hnonneg j)]
    refine ⟨⟨m, ?_⟩, hweight⟩
    have : ((Multiset.card m : ℕ) : ℤ) = (d : ℤ) := by
      rw [← sum_weightOfMultiset m, hweight, hsum]
    exact_mod_cast this

section CommRing

variable {k : Type} [CommRing k] {n d : ℕ}

/-- **The torus character of a multiset weight** is the product of the entries it lists. -/
@[simp]
theorem weightChar_weightOfMultiset (s : Multiset (Fin n)) (t : Fin n → kˣ) :
    weightChar k (weightOfMultiset s) t = (s.map t).prod := by
  rw [weightChar_apply, torusCharacter_def, Finset.prod_multiset_map_count]
  simp only [weightOfMultiset_apply, zpow_natCast]
  refine (Finset.prod_subset (Finset.subset_univ s.toFinset) fun i _ hi => ?_).symm
  rw [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero_of_notMem hi, pow_zero]

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
  iSup_weightSpace_eq_top_of_basis ((Pi.basisFun k (Fin n)).symmetricPower d)
    basis_mem_weightSpace_symPowerRep

end CommRing

/-! ### The weight spaces are the lines of the symmetric-power basis

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section Domain

variable {k : Type} [CommRing k] [IsDomain k] {n d : ℕ}

/-- The multiplicity vector of the index of a basis vector of `Symᵈ(kⁿ)` determines that index. -/
theorem weightOfMultiset_coe_injective :
    Function.Injective fun s : Sym (Fin n) d => weightOfMultiset (s : Multiset (Fin n)) :=
  fun _ _ h => Subtype.val_injective (weightOfMultiset_injective h)

/-- **The weight spaces of a symmetric power of the standard representation are the coordinate
lines of the symmetric-power basis**: the weight-`l` space of `Symᵈ(kⁿ)`, for `l` the multiplicity
vector of an unordered `d`-tuple `s`, is the line spanned by the product of the standard basis
vectors listed by `s`. -/
theorem weightSpace_symPowerRep_eq_span
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (s : Sym (Fin n) d) :
    weightSpace (symPowerRep k n d) (weightOfMultiset (s : Multiset (Fin n))) =
      Submodule.span k {(Pi.basisFun k (Fin n)).symmetricPower d s} :=
  weightSpace_eq_span_of_basis ((Pi.basisFun k (Fin n)).symmetricPower d)
    basis_mem_weightSpace_symPowerRep hchar weightOfMultiset_coe_injective s

/-- **Only the multiplicity vectors are weights** of a symmetric power of the standard
representation. -/
theorem weightSpace_symPowerRep_eq_bot
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ}
    (hl : ∀ s : Sym (Fin n) d, l ≠ weightOfMultiset (s : Multiset (Fin n))) :
    weightSpace (symPowerRep k n d) l = ⊥ :=
  weightSpace_eq_bot_of_basis ((Pi.basisFun k (Fin n)).symmetricPower d)
    basis_mem_weightSpace_symPowerRep hchar hl

/-- **The weights of `Symᵈ(kⁿ)` are exactly the multiplicity vectors of the unordered `d`-tuples
over `Fin n`.** -/
theorem weightSpace_symPowerRep_ne_bot_iff
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (symPowerRep k n d) l ≠ ⊥ ↔
      ∃ s : Sym (Fin n) d, l = weightOfMultiset (s : Multiset (Fin n)) :=
  weightSpace_ne_bot_iff_of_basis ((Pi.basisFun k (Fin n)).symmetricPower d)
    basis_mem_weightSpace_symPowerRep hchar weightOfMultiset_coe_injective l

/-- **The weights of `Symᵈ(kⁿ)` are the exponent vectors of the degree-`d` monomials in `n`
variables**: the nonnegative integer vectors of total degree `d`.  This is the weight-space
refinement of `TauCeti.char_symPowerRep_diagonal`, which sums those monomials into the complete
homogeneous symmetric polynomial. -/
theorem weightSpace_symPowerRep_ne_bot_iff_nonneg_sum_eq
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (symPowerRep k n d) l ≠ ⊥ ↔ (∀ i, 0 ≤ l i) ∧ ∑ i, l i = d := by
  rw [weightSpace_symPowerRep_ne_bot_iff hchar l, ← exists_sym_weightOfMultiset_eq_iff l]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩

end Domain

section Field

variable {k : Type} [Field k] {n d : ℕ}

/-- **A symmetric power of the standard representation is the internal direct sum of its weight
spaces.** -/
theorem isInternal_weightSpace_symPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ => weightSpace (symPowerRep k n d) l :=
  isInternal_weightSpace_of_basis ((Pi.basisFun k (Fin n)).symmetricPower d)
    basis_mem_weightSpace_symPowerRep hchar

/-- **Every weight of `Symᵈ(kⁿ)` has multiplicity one.** -/
theorem finrank_weightSpace_symPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (s : Sym (Fin n) d) :
    Module.finrank k (weightSpace (symPowerRep k n d)
      (weightOfMultiset (s : Multiset (Fin n)))) = 1 :=
  finrank_weightSpace_eq_one_of_basis ((Pi.basisFun k (Fin n)).symmetricPower d)
    basis_mem_weightSpace_symPowerRep hchar weightOfMultiset_coe_injective s

end Field

end TauCeti
