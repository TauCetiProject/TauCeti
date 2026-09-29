/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The exterior-power representation of `GL n k` and the basis of `⋀[k]^d (Fin n → k)`.
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
-- The weight spaces of a representation with a basis of weight vectors.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis

/-!
# The weights of an exterior power of the standard representation

The standard representation of `GL n k` is the internal direct sum of its weight spaces, the
coordinate lines, with the `i`-th line carrying the weight `Pi.single i 1`
(`TauCeti.isInternal_weightSpace_stdRep`). This file computes the weight spaces of its exterior
powers, the representations `⋀ᵈ(kⁿ)`.

A wedge `e_{i₁} ∧ ⋯ ∧ e_{i_d}` of standard basis vectors is again a weight vector: a diagonal
matrix scales it by the product `t_{i₁} ⋯ t_{i_d}` of the corresponding entries. Its weight is
therefore the `0`/`1` indicator of the `d`-element subset `{i₁, …, i_d}`, which is
`TauCeti.weightOfSubset` below. Those wedges are Mathlib's basis
`Module.Basis.exteriorPower` of `⋀ᵈ(kⁿ)`, indexed by `Set.powersetCard (Fin n) d`, and distinct
subsets carry distinct weights, so — once distinct weights give distinct characters of the torus —
the weight spaces are the coordinate lines of that basis: the weight-`l` space is the line spanned
by the wedge of `s` if `l` is the indicator of `s`, and is zero otherwise. In particular every
weight of `⋀ᵈ(kⁿ)` has multiplicity one, and there are `n.choose d` of them.

So the weights of `⋀ᵈ(kⁿ)` are exactly the sums `Pi.single i₁ 1 + ⋯ + Pi.single i_d 1` of `d`
distinct weights of the standard representation, each occurring once. For `d = 0` the only weight
is `0`, and for `d > n` there is no weight at all, the exterior power being zero. For `1 ≤ d ≤ n`
the largest weight in the dominance order is `(1, …, 1, 0, …, 0)` with `d` ones, the `d`-th
fundamental weight of `GL n`; identifying it as the *highest* weight of `⋀ᵈ(kⁿ)` needs the
highest-weight classification and is not done here.

## Main definitions

* `TauCeti.weightOfSubset`: the weight of a subset of `Fin n`, its `0`/`1` indicator.

## Main results

* `TauCeti.extPowerRep_diagGL_apply_basis`: **a wedge of standard basis vectors is an eigenvector
  of every diagonal matrix**, with eigenvalue the product of the entries it selects.
* `TauCeti.basis_mem_weightSpace_extPowerRep`: that wedge lies in the weight space of the
  indicator weight of its index set.
* `TauCeti.iSup_weightSpace_extPowerRep_eq_top` and
  `TauCeti.isInternal_weightSpace_extPowerRep`: **the exterior power is the internal direct sum of
  its weight spaces.**
* `TauCeti.weightSpace_extPowerRep_eq_span`: **the weight spaces are the coordinate lines of the
  wedge basis**, with `TauCeti.weightSpace_extPowerRep_eq_bot` for the weights that are not
  indicators.
* `TauCeti.finrank_weightSpace_extPowerRep`: every weight of `⋀ᵈ(kⁿ)` has multiplicity one, and
  `TauCeti.weightSpace_extPowerRep_ne_bot_iff` says the weights are exactly the indicators.

## Implementation notes

Everything past the eigenvector computation is an instance of
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basis`, which reads the weight spaces of a
representation off a basis of weight vectors; what is specific to the exterior power is the wedge
basis, the subset labelling, and the injectivity of that labelling.

The subset weight is packaged as `TauCeti.weightOfSubset`, taking a bare `Finset (Fin n)` rather
than an element of `Set.powersetCard (Fin n) d`: nothing in the definition or in its injectivity
uses the cardinality, and the consumers below apply it to the underlying finset of a basis index.
The cardinality reappears only in `TauCeti.sum_weightOfSubset`, which records that a weight of
`⋀ᵈ(kⁿ)` has total degree `d`.

As in `TauCeti/RepresentationTheory/ClassicalGroups/Weight/Basic.lean`, the statements that pin a
weight space down, rather than merely exhibiting vectors in it, assume that the coefficients
separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. Without it the statements are
false: over `𝔽₂` the diagonal torus of `GL n 𝔽₂` is trivial, so every weight space of every
representation is everything.

The eigenvector computation itself is `exteriorPower.map_basis_exteriorPower_of_apply_basis`, the
exterior-power analogue of `SymmetricPower.map_basis_symmetricPower_of_apply_basis`; it is what
`TauCeti.char_extPowerRep_diagonal` sums to get the elementary symmetric polynomial, and the
weight-space statements here refine that character identity to the decomposition behind it.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

/-! ### The weight of a subset -/

/-- The **weight of a subset** `s ⊆ Fin n`: its `0`/`1` indicator. This is the weight carried by
the wedge of the standard basis vectors indexed by `s`. -/
def weightOfSubset {n : ℕ} (s : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ s then 1 else 0

/-- The defining formula for `TauCeti.weightOfSubset`. -/
@[simp]
theorem weightOfSubset_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    weightOfSubset s i = if i ∈ s then 1 else 0 :=
  (rfl)

/-- **A subset is recovered from its weight**, the support of the indicator being the subset. -/
theorem weightOfSubset_injective {n : ℕ} : Function.Injective (weightOfSubset (n := n)) := by
  intro s t h
  ext i
  have hi := congrFun h i
  rw [weightOfSubset_apply, weightOfSubset_apply] at hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

/-- The weight of a subset has total degree its cardinality: the weights of `⋀ᵈ(kⁿ)` all lie in
degree `d`. -/
theorem sum_weightOfSubset {n : ℕ} (s : Finset (Fin n)) : ∑ i, weightOfSubset s i = s.card := by
  simp [Finset.sum_ite_mem]

section CommRing

variable {k : Type u} [CommRing k] {n d : ℕ}

/-- **The torus character of a subset weight** is the product of the entries it selects. -/
@[simp]
theorem weightChar_weightOfSubset (s : Finset (Fin n)) (t : Fin n → kˣ) :
    weightChar k (weightOfSubset s) t = ∏ i ∈ s, t i := by
  rw [weightChar_apply, torusCharacter_def]
  rw [Finset.prod_congr rfl fun i _ => ?_, Finset.prod_ite_mem, Finset.univ_inter]
  rw [weightOfSubset_apply]
  by_cases hi : i ∈ s <;> simp [hi]

/-! ### The wedges of standard basis vectors are weight vectors -/

/-- **A wedge of standard basis vectors is an eigenvector of every diagonal matrix**, with
eigenvalue the product of the entries it selects.

This is deliberately not a `simp` lemma: `Representation.exteriorPower_apply` already rewrites the
left-hand side to `exteriorPower.map d (stdRep k n (diagGL t))`, so it is not in `simp` normal
form. -/
theorem extPowerRep_diagGL_apply_basis (t : Fin n → kˣ) (s : Set.powersetCard (Fin n) d) :
    extPowerRep k n d (diagGL t) ((Pi.basisFun k (Fin n)).exteriorPower d s) =
      (∏ i ∈ (s : Finset (Fin n)), (t i : k)) • (Pi.basisFun k (Fin n)).exteriorPower d s := by
  rw [Representation.exteriorPower_apply,
    exteriorPower.map_basis_exteriorPower_of_apply_basis (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) (stdRep_diagGL_apply_basisFun t) d s]

/-- The wedge of the standard basis vectors indexed by `s` has weight the indicator of `s`. -/
theorem basis_mem_weightSpace_extPowerRep (s : Set.powersetCard (Fin n) d) :
    (Pi.basisFun k (Fin n)).exteriorPower d s ∈
      weightSpace (extPowerRep k n d) (weightOfSubset (s : Finset (Fin n))) := by
  rw [mem_weightSpace_iff]
  intro t
  rw [extPowerRep_diagGL_apply_basis, weightChar_weightOfSubset, Units.coe_prod]

/-- **The weight spaces of an exterior power of the standard representation span it**: the wedge
basis consists of weight vectors. -/
theorem iSup_weightSpace_extPowerRep_eq_top :
    ⨆ l : Fin n → ℤ, weightSpace (extPowerRep k n d) l = ⊤ :=
  ((Pi.basisFun k (Fin n)).exteriorPower d).iSup_weightSpace_eq_top
    basis_mem_weightSpace_extPowerRep

end CommRing

/-! ### The weight spaces are the lines of the wedge basis

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section IsCancelMulZero

variable {k : Type u} [CommRing k] [IsCancelMulZero k] {n d : ℕ}

/-- **The weight spaces of an exterior power of the standard representation are the coordinate
lines of the wedge basis**: the weight-`l` space of `⋀ᵈ(kⁿ)`, for `l` the indicator of a
`d`-element subset `s`, is the line spanned by the wedge of the standard basis vectors indexed by
`s`. -/
theorem weightSpace_extPowerRep_eq_span
    (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (s : Set.powersetCard (Fin n) d) :
    weightSpace (extPowerRep k n d) (weightOfSubset (s : Finset (Fin n))) =
      Submodule.span k {(Pi.basisFun k (Fin n)).exteriorPower d s} :=
  ((Pi.basisFun k (Fin n)).exteriorPower d).weightSpace_eq_span
    basis_mem_weightSpace_extPowerRep hchar
    (fun _ _ h => Subtype.val_injective (weightOfSubset_injective h)) s

/-- **Only the indicators are weights** of an exterior power of the standard representation. -/
theorem weightSpace_extPowerRep_eq_bot
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ}
    (hl : ∀ s : Set.powersetCard (Fin n) d, l ≠ weightOfSubset (s : Finset (Fin n))) :
    weightSpace (extPowerRep k n d) l = ⊥ :=
  ((Pi.basisFun k (Fin n)).exteriorPower d).weightSpace_eq_bot
    basis_mem_weightSpace_extPowerRep hchar hl

/-- **The weights of `⋀ᵈ(kⁿ)` are exactly the indicators of the `d`-element subsets of
`Fin n`**, of which there are `n.choose d`. -/
theorem weightSpace_extPowerRep_ne_bot_iff [Nontrivial k]
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace (extPowerRep k n d) l ≠ ⊥ ↔
      ∃ s : Set.powersetCard (Fin n) d, l = weightOfSubset (s : Finset (Fin n)) :=
  ((Pi.basisFun k (Fin n)).exteriorPower d).weightSpace_ne_bot_iff
    basis_mem_weightSpace_extPowerRep hchar l

end IsCancelMulZero

section Field

variable {k : Type u} [Field k] {n d : ℕ}

/-- **An exterior power of the standard representation is the internal direct sum of its weight
spaces.** -/
theorem isInternal_weightSpace_extPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ => weightSpace (extPowerRep k n d) l :=
  ((Pi.basisFun k (Fin n)).exteriorPower d).isInternal_weightSpace
    basis_mem_weightSpace_extPowerRep hchar

/-- **Every weight of `⋀ᵈ(kⁿ)` has multiplicity one.** -/
theorem finrank_weightSpace_extPowerRep
    (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (s : Set.powersetCard (Fin n) d) :
    Module.finrank k (weightSpace (extPowerRep k n d)
      (weightOfSubset (s : Finset (Fin n)))) = 1 :=
  ((Pi.basisFun k (Fin n)).exteriorPower d).finrank_weightSpace_eq_one
    basis_mem_weightSpace_extPowerRep hchar
    (fun _ _ h => Subtype.val_injective (weightOfSubset_injective h)) s

end Field

end TauCeti
