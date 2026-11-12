/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic
import TauCeti.Order.Preorder.Finite

/-!
# The primitive idempotents of the strands algebra and of `A(Z)`

The idempotents `I(S)` of the strands algebra `A(n)` of Lipshitz, Ozsváth and Thurston, the
identity diagrams on the subsets `S` of the points, are orthogonal and sum to the unit. This file
shows that they are **primitive**: none of them is the sum of two nonzero orthogonal idempotents.
The algebra `A(Z)` of a pointed matched circle has the idempotents `I(s)`, one for each set `s`
of pairs: `I(s)` is the sum of the `I(S)` over the sets `S` containing one point of each pair in
`s`. Such an `I(s)` is generally not primitive in `A(n)`, where it splits into its summands, but it
is primitive in `A(Z)`. So the `I(s)` form a complete set of primitive orthogonal idempotents of
`A(Z)`, and over a coefficient ring the left ideals `A(Z) I(s)` are indecomposable modules
(`TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`). The type `D` structures and box
tensor products of bordered Floer theory are taken over the ring of idempotents spanned by these
`I(s)`.

The coefficient ring is any commutative semiring in which `1` is primitive, such as a field or a
local ring (`TauCeti.isPrimitiveIdempotent_one`); bordered Floer theory uses `𝔽₂`.

## The argument

The argument is the one for the vertex idempotents of a path algebra
(`TauCeti.isPrimitiveIdempotent_vertexIdempotent`), with the identity diagrams in the role of the
trivial paths.

* The coefficient on an identity diagram `I(S)` is multiplicative
  (`TauCeti.StrandsAlgebra.repr_mul_idOn`), since `I(S)` factors only as `I(S) I(S)`.
* An idempotent with no coefficient on any identity diagram vanishes
  (`TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero`). Measure a
  diagram by the total rise of its strands. A diagram `χ` of least rise in the idempotent `f = f²`
  is a composite `φ ψ` of diagrams of `f`. Since `ψ` is not an identity diagram it rises, so `φ`
  has less rise than `χ`, a contradiction.

If `e = f₁ + f₂` splits into orthogonal idempotents, the coefficients of `f₁` and `f₂` on an
identity diagram `I(S)` of `e` split `1` into orthogonal idempotents of the coefficient ring, so one
of them vanishes. In `A(n)` the identity diagram `I(S)` is the only one with a nonzero
coefficient in `e = I(S)`. In `A(Z)` the coefficients of an element on the summands of `I(s)` all
agree, since these summands differ by moving horizontal strands within matched pairs. Either way
the vanishing summand has no coefficient on any identity diagram, so it is zero.

## Main results

* `TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero`: an idempotent
  of the strands algebra with no coefficient on any identity diagram is zero.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`: the idempotents `I(S)` of the strands algebra
  are primitive.
* `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_idem`: the `I(S)`, over the subsets `S`
  of the points, are a complete family of orthogonal idempotents of the strands algebra.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem`: the idempotents `I(s)` of the matched
  subalgebra are primitive there.
* `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`: the `I(s)`, over the sets `s`
  of pairs, are a complete family of orthogonal idempotents of the matched subalgebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 (the
  idempotents of the strands algebra) and §3.2 (the idempotents `I(s)` of `A(Z)`).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The total rise of the strands of `φ`, each point measured by the number of points below it:
the sum of these numbers over the end points minus their sum over the starting points. -/
private def rise (φ : StrandDiagram α) : ℤ :=
  ∑ t ∈ φ.target, (#{y | y < t} : ℤ) - ∑ s ∈ φ.source, (#{y | y < s} : ℤ)

/-- The rise is additive under concatenation. -/
private theorem rise_trans_of_target_eq {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).rise = φ.rise + ψ.rise := by
  rw [rise, rise, rise, source_trans_of_target_eq h, target_trans_of_target_eq h, h]
  ring

/-- A diagram which is not an identity diagram has a strand that rises, so its rise is
positive. -/
private theorem rise_pos {φ : StrandDiagram α} (hφ : φ ≠ idOn φ.source) : 0 < φ.rise := by
  have hrank : StrictMono fun x : α ↦ #{z | z < x} := fun _ _ ↦ card_filter_lt_lt_card_filter_lt
  rw [rise, target_eq_image, sum_image (injOn_getD φ), ← sum_sub_distrib]
  refine sum_pos' (fun s hs ↦ sub_nonneg.2 (by exact_mod_cast hrank.monotone (le_getD hs))) ?_
  -- Some strand rises: otherwise every strand is horizontal and `φ` is an identity diagram.
  by_contra! hflat
  refine hφ (ext fun i ↦ ?_)
  by_cases hi : i ∈ φ.source
  · have hle : (φ i).getD i ≤ i := by
      by_contra! hlt
      have hlt' : #{y | y < i} < #{y | y < (φ i).getD i} := hrank hlt
      have := hflat i hi
      omega
    have hmem := getD_mem hi
    rw [le_antisymm hle (le_getD hi)] at hmem
    simpa [hi] using hmem
  · simp [apply_eq_none_of_notMem_source hi, hi]

end StrandDiagram

namespace StrandsAlgebra

open StrandDiagram

variable {R α : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-- **An idempotent of the strands algebra is detected by the identity diagrams.** An idempotent
with no coefficient on any identity diagram `I(S)` is zero. In other words, the span of the
diagrams that are not identity diagrams contains no nonzero idempotent. -/
theorem eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero {f : StrandsAlgebra R α}
    (hf : IsIdempotentElem f) (h : ∀ s, (basis R α).repr f (idOn s) = 0) : f = 0 := by
  by_contra hne
  -- A diagram of `f` of least rise.
  obtain ⟨χ, hχ, hmin⟩ := ((basis R α).repr f).support.exists_min_image rise
    (Finsupp.support_nonempty_iff.2 ((basis R α).repr.map_ne_zero_iff.2 hne))
  rw [Finsupp.mem_support_iff, ← hf.eq] at hχ
  obtain ⟨φ, ψ, hc, rfl, hφ, hψ⟩ := exists_of_repr_mul_ne_zero hχ
  -- The second factor is not an identity diagram, so the first has less rise than `χ`.
  have hrise := rise_pos (φ := ψ) fun hψ' ↦ hψ (by rw [hψ']; exact h _)
  have := hmin φ (Finsupp.mem_support_iff.2 hφ)
  rw [rise_trans_of_target_eq hc.target_eq] at this
  omega

/-- The splitting step behind the primitivity of the idempotents. Let `e = f₁ + f₂` split into
orthogonal idempotents, with `I(S)` an identity diagram of coefficient `1` in `e`. If, on every
identity diagram with a nonzero coefficient in `e`, each `fᵢ` has its coefficient on `I(S)`, then
`f₁` or `f₂` vanishes. -/
private theorem eq_zero_or_eq_zero_of_add_eq (hR : IsPrimitiveIdempotent (1 : R))
    {e f₁ f₂ : StrandsAlgebra R α} {S : Finset α} (he : (basis R α).repr e (idOn S) = 1)
    (hcoord₁ : ∀ t, (basis R α).repr e (idOn t) ≠ 0 →
      (basis R α).repr f₁ (idOn t) = (basis R α).repr f₁ (idOn S))
    (hcoord₂ : ∀ t, (basis R α).repr e (idOn t) ≠ 0 →
      (basis R α).repr f₂ (idOn t) = (basis R α).repr f₂ (idOn S))
    (h₁ : IsIdempotentElem f₁) (h₂ : IsIdempotentElem f₂) (h₁₂ : f₁ * f₂ = 0)
    (h₂₁ : f₂ * f₁ = 0) (hsum : f₁ + f₂ = e) : f₁ = 0 ∨ f₂ = 0 := by
  -- A summand of `e` whose coefficient on `I(S)` vanishes has no coefficient on any identity
  -- diagram, since it equals `e` times itself.
  have key {f : StrandsAlgebra R α} (hf : IsIdempotentElem f) (hef : e * f = f)
      (hcoord : ∀ t, (basis R α).repr e (idOn t) ≠ 0 →
        (basis R α).repr f (idOn t) = (basis R α).repr f (idOn S))
      (hS : (basis R α).repr f (idOn S) = 0) : f = 0 := by
    refine eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero hf fun t ↦ ?_
    rw [← hef, repr_mul_idOn]
    by_cases ht : (basis R α).repr e (idOn t) = 0
    · rw [ht, zero_mul]
    · rw [hcoord t ht, hS, mul_zero]
  have hcoeff {f g : StrandsAlgebra R α} (hfg : f * g = 0) :
      (basis R α).repr f (idOn S) * (basis R α).repr g (idOn S) = 0 := by
    rw [← repr_mul_idOn, hfg, map_zero, Finsupp.zero_apply]
  refine (hR.eq_zero_or_eq_zero_of_add (by rw [IsIdempotentElem, ← repr_mul_idOn, h₁.eq])
    (by rw [IsIdempotentElem, ← repr_mul_idOn, h₂.eq]) (hcoeff h₁₂) (hcoeff h₂₁)
    (by rw [← Finsupp.add_apply, ← map_add, hsum, he])).imp (key h₁ ?_ hcoord₁)
    (key h₂ ?_ hcoord₂)
  · rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero]
  · rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add]

/-- **The idempotents `I(S)` of the strands algebra are primitive**, as soon as `1` is primitive in
the coefficient semiring. -/
theorem isPrimitiveIdempotent_idem (hR : IsPrimitiveIdempotent (1 : R)) (S : Finset α) :
    IsPrimitiveIdempotent (idem S : StrandsAlgebra R α) := by
  have := hR.nontrivial
  -- The only identity diagram with a nonzero coefficient in `I(S)` is `I(S)` itself.
  have hcoord (f : StrandsAlgebra R α) (t : Finset α)
      (ht : (basis R α).repr (idem S) (idOn t) ≠ 0) :
      (basis R α).repr f (idOn t) = (basis R α).repr f (idOn S) := by
    rw [idem_def, basis_repr_of, Finsupp.single_apply, ite_ne_right_iff] at ht
    rw [← source_idOn t, ← ht.1, source_idOn]
  refine ⟨isIdempotentElem_idem S, ?_, fun h₁ h₂ h₁₂ h₂₁ hsum ↦
    eq_zero_or_eq_zero_of_add_eq hR ?_ (hcoord _) (hcoord _) h₁ h₂ h₁₂ h₂₁ hsum⟩
  · rw [idem_def, ← basis_apply]
    exact (basis R α).ne_zero _
  · rw [idem_def, basis_repr_of, Finsupp.single_eq_same]

/-- **The idempotents `I(S)` of the strands algebra are a complete family of orthogonal
idempotents**, indexed by the subsets `S` of the points: they are orthogonal idempotents summing to
the unit. With `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_idem`, they are a complete set of
primitive orthogonal idempotents of the strands algebra. -/
theorem completeOrthogonalIdempotents_idem :
    CompleteOrthogonalIdempotents (idem : Finset α → StrandsAlgebra R α) where
  idem := isIdempotentElem_idem
  ortho _ _ := idem_mul_idem_of_ne
  complete := sum_idem

section Matched

variable {β : Type*} [DecidableEq β] {M : α → β}

/-- **The idempotents `I(s)` of the matched subalgebra are primitive** there, for every set `s` of
pairs of the matching, as soon as `1` is primitive in the coefficient semiring. For the matching of
a pointed matched circle `Z`, these are the idempotents of the algebra `A(Z)`. -/
theorem isPrimitiveIdempotent_matchedIdem (hR : IsPrimitiveIdempotent (1 : R)) {s : Finset β}
    (hs : s ⊆ univ.image M) :
    IsPrimitiveIdempotent (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ :
      matchedSubalgebra R M) := by
  have := hR.nontrivial
  obtain ⟨S, hS⟩ := matchedChoices_nonempty_iff.2 hs
  have hsum : (matchedIdem R M s : StrandsAlgebra R α) = matchedSum R M (idOn S) := by
    rw [matchedIdem_eq_horizontalCompletion, horizontalCompletion_eq_matchedSum
      (isMatchedGenerator_idOn_empty M s) hS, idOn_addHorizontal, empty_union]
  have he : (basis R α).repr (matchedIdem R M s) (idOn S) = 1 := by
    classical
    rw [hsum, repr_matchedSum_apply, ite_eq_left ((matchedSetoid M).iseqv.refl _)]
  -- The identity diagrams with a nonzero coefficient in `I(s)` are related to `I(S)` by moving
  -- horizontal strands within matched pairs, so elements of the matched subalgebra have equal
  -- coefficients on them.
  have hcoord (f : matchedSubalgebra R M) (t : Finset α)
      (ht : (basis R α).repr (matchedIdem R M s) (idOn t) ≠ 0) :
      (basis R α).repr f (idOn t) = (basis R α).repr f (idOn S) := by
    classical
    rw [hsum, repr_matchedSum_apply, ite_ne_right_iff] at ht
    exact repr_eq_of_matchedSetoid f.2 ((matchedSetoid M).iseqv.symm ht.1)
  refine ⟨Subtype.ext (isIdempotentElem_matchedIdem M s), fun h0 ↦ ?_,
    fun {f₁ f₂} h₁ h₂ h₁₂ h₂₁ hsum ↦ ?_⟩
  · have := congrArg (fun x : matchedSubalgebra R M ↦ (basis R α).repr x (idOn S)) h0
    simp only [he, ZeroMemClass.coe_zero, map_zero, Finsupp.zero_apply] at this
    exact one_ne_zero this
  · refine (eq_zero_or_eq_zero_of_add_eq hR he (hcoord f₁) (hcoord f₂)
      (congrArg Subtype.val h₁) (congrArg Subtype.val h₂) (congrArg Subtype.val h₁₂)
      (congrArg Subtype.val h₂₁) (congrArg Subtype.val hsum)).imp Subtype.ext Subtype.ext

/-- **The idempotents `I(s)` of the matched subalgebra are a complete family of orthogonal
idempotents**, indexed by the sets `s` of pairs of the matching: they are orthogonal idempotents
summing to its unit. With `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem`, they are a
complete set of primitive orthogonal idempotents of the matched subalgebra. -/
theorem completeOrthogonalIdempotents_matchedIdem :
    CompleteOrthogonalIdempotents fun s : (univ.image M).powerset ↦
      (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) where
  idem s := Subtype.ext (isIdempotentElem_matchedIdem M s)
  ortho s t hst := Subtype.ext <| by
    simp [matchedIdem_mul_matchedIdem, Subtype.coe_injective.ne hst]
  complete := Subtype.ext <| by
    simp [matchedOne_def, sum_attach (univ.image M).powerset (matchedIdem R M)]

end Matched

end StrandsAlgebra

end TauCeti
