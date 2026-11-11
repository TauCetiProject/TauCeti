/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Length
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.RingTheory.Idempotents.Primitive.Basic
import TauCeti.Data.Finset.Basic

/-!
# The primitive idempotents of the algebra of a matching

The algebra `A(Z)` of a pointed matched circle `Z` is the matched subalgebra of the strands
algebra for the matching `M` of `Z` (`TauCeti.StrandsAlgebra.matchedSubalgebra`). Its idempotents
`I(s)` (`TauCeti.StrandsAlgebra.matchedIdem`), one for each set `s` of matched pairs, are the
sums of the identity diagrams `I(S)` over the sets `S` containing one point of each pair in `s`.
This file shows that they are the primitive idempotents of a decomposition of the unit: they are
orthogonal idempotents summing to the unit of `A(Z)`
(`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`), and each of them is
primitive (`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem`), as in the summands
`A(Z, i)` with a fixed number of strands
(`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem_matchedSummand`,
`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_matchedSummand`). The type `D`
structures over `A(Z)` are modules over the ring of these idempotents, and their generators each
lie over one of them.

The argument rests on the two facts of `TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Length`:
the coefficient of an identity diagram is multiplicative, and an element without identity
diagrams is nilpotent. An element of the matched subalgebra has the same coefficient on the
identity diagrams of all the sets `S` lying over `s`, since moving one horizontal strand at a time
to the matched point joins any two of them
(`TauCeti.StrandsAlgebra.repr_idOn_eq_of_image_eq`). So if `I(s) = f₁ + f₂` with `f₁` and `f₂`
orthogonal idempotents, the coefficients `c₁` and `c₂` of `f₁` and `f₂` on these identity diagrams
are orthogonal idempotents of the coefficient ring summing to `1`, and one of them vanishes when
`1` is primitive there, for instance over a field such as `𝔽₂`. The corresponding `fᵢ` then has no
identity diagram at all, the coefficients on the other identity diagrams being killed by
`I(s) fᵢ = fᵢ`, so it is a nilpotent idempotent and vanishes.

## Main results

* `TauCeti.StrandsAlgebra.repr_idOn_eq_of_image_eq`: an element of the matched subalgebra has the
  same coefficient on the identity diagrams of sets mapped injectively onto the same set of pairs.
* `TauCeti.StrandsAlgebra.matchedIdem_eq_zero_iff`: `I(s)` vanishes exactly when `s` is not a set
  of pairs.
* `TauCeti.StrandsAlgebra.eq_zero_or_eq_zero_of_add_eq_matchedIdem`: `I(s)` is not the sum of two
  nonzero orthogonal idempotents of the matched subalgebra.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`,
  `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_matchedSummand_iff`: `I(s)` is a
  primitive idempotent of the matched subalgebra, and of its summand with `#s` strands, exactly
  when `s` is a set of pairs.
* `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`,
  `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem_matchedSummand`: the `I(s)`
  form a complete family of orthogonal idempotents of the matched subalgebra and of each summand.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  idempotents `I(s)` of the algebra `A(Z)` and the ring of idempotents `I(Z)`).
-/

public section

namespace TauCeti

open Finset StrandDiagram

namespace StrandsAlgebra

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [DecidableEq β]
  {M : α → β} {s : Finset β}

/-- **The identity diagrams over a set of pairs have the same coefficient.** If `M` maps `S` and
`T` injectively onto the same set, an element of the matched subalgebra has the same coefficient
on `I(S)` and on `I(T)`. -/
theorem repr_idOn_eq_of_image_eq {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M)
    {S T : Finset α} (hS : Set.InjOn M S) (hT : Set.InjOn M T) (h : S.image M = T.image M) :
    (basis R α).repr x (idOn S) = (basis R α).repr x (idOn T) := by
  classical
  induction hn : #(S \ T) generalizing S with
  | zero =>
    have hST : S ⊆ T := sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hn)
    rw [eq_of_subset_of_card_le hST
      (by rw [← card_image_of_injOn hT, ← h, card_image_of_injOn hS])]
  | succ n ih =>
    obtain ⟨a, ha⟩ : (S \ T).Nonempty := card_pos.1 (by omega)
    obtain ⟨haS, haT⟩ := mem_sdiff.1 ha
    obtain ⟨b, hbT, hab⟩ := mem_image.1 (h ▸ mem_image_of_mem M haS)
    have hbS : b ∉ S := fun hbS ↦ haT (hS haS hbS hab.symm ▸ hbT)
    rw [← (mem_matchedSubalgebra.1 hx).2 (idOn S) a b hab.symm, swapHorizontal_idOn haS hbS]
    refine ih ((injOn_insert_erase_iff haS hbS hab.symm).2 hS) ?_ ?_
    · rw [image_insert, hab, ← image_insert, insert_erase haS, h]
    · rw [insert_sdiff_of_mem _ hbT, erase_sdiff_comm, card_erase_of_mem ha]
      omega

/-- The coefficient of `I(s)` on the identity diagram of a set mapped injectively onto `s` is
`1`. -/
private theorem repr_matchedIdem_idOn {S : Finset α} (hS : Set.InjOn M S) :
    (basis R α).repr (matchedIdem R M (S.image M)) (idOn S) = 1 := by
  rw [repr_matchedIdem_apply, source_idOn, card_image_of_injOn hS]
  exact ite_eq_left ⟨rfl, rfl, rfl⟩

/-- **`I(s)` vanishes exactly when `s` is not a set of pairs**, that is, when some element of `s`
is the image of no point. -/
theorem matchedIdem_eq_zero_iff [Nontrivial R] :
    matchedIdem R M s = 0 ↔ ¬s ⊆ univ.image M := by
  refine ⟨fun h hs ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨S, -, hS, rfl⟩ := exists_subset_injOn_image_eq_of_surjOn Set.univ s fun b hb ↦ by
      obtain ⟨a, -, rfl⟩ := mem_image.1 (hs hb)
      exact ⟨a, trivial, rfl⟩
    have h1 := repr_matchedIdem_idOn (R := R) hS
    rw [h, map_zero, Finsupp.zero_apply] at h1
    exact zero_ne_one h1
  · rw [matchedIdem_def]
    refine sum_eq_zero fun S hS ↦ absurd ?_ hs
    rw [← (mem_filter.1 hS).2.1]
    exact image_subset_image (subset_univ S)

/-- An idempotent of the matched subalgebra fixed by `I(s)` on the left vanishes as soon as its
coefficient on the identity diagram of one set mapped injectively onto `s` does. -/
theorem eq_zero_of_isIdempotentElem_of_repr_idOn_eq_zero {f : StrandsAlgebra R α}
    (hf : f ∈ matchedSubalgebra R M) (he : IsIdempotentElem f) (hsf : matchedIdem R M s * f = f)
    {S : Finset α} (hS : Set.InjOn M S) (hSs : S.image M = s)
    (h0 : (basis R α).repr f (idOn S) = 0) : f = 0 := by
  refine he.eq_zero_of_isNilpotent (isNilpotent_of_forall_repr_idOn_eq_zero fun T ↦ ?_)
  by_cases hT : T.image M = s ∧ #T = #s
  · rw [repr_idOn_eq_of_image_eq hf (card_image_iff.1 (by rw [hT.1, hT.2])) hS
      (hT.1.trans hSs.symm), h0]
  · rw [← hsf, repr_mul_idOn, repr_matchedIdem_apply, source_idOn,
      ite_eq_right fun h ↦ hT h.2, zero_mul]

/-- **`I(s)` does not split in the matched subalgebra.** If `1` is a primitive idempotent of the
coefficient semiring, `I(s)` is not the sum of two nonzero orthogonal idempotents of the matched
subalgebra. -/
theorem eq_zero_or_eq_zero_of_add_eq_matchedIdem (hk : IsPrimitiveIdempotent (1 : R))
    {f₁ f₂ : StrandsAlgebra R α} (hf₁ : f₁ ∈ matchedSubalgebra R M)
    (hf₂ : f₂ ∈ matchedSubalgebra R M) (h₁ : IsIdempotentElem f₁) (h₂ : IsIdempotentElem f₂)
    (h₁₂ : f₁ * f₂ = 0) (h₂₁ : f₂ * f₁ = 0) (hsum : f₁ + f₂ = matchedIdem R M s) :
    f₁ = 0 ∨ f₂ = 0 := by
  have hc₁ : matchedIdem R M s * f₁ = f₁ := by rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero]
  have hc₂ : matchedIdem R M s * f₂ = f₂ := by rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add]
  by_cases hs : matchedIdem R M s = 0
  · left
    rw [← hc₁, hs, zero_mul]
  -- Some set `S` lies over `s`, since `I(s)` is the sum of the `I(S)` over these sets.
  rw [matchedIdem_def] at hs
  obtain ⟨S, hS, -⟩ := exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨rfl, hSc⟩ := (mem_filter.1 hS).2
  replace hS : Set.InjOn M S := card_image_iff.1 hSc.symm
  set c₁ := (basis R α).repr f₁ (idOn S)
  set c₂ := (basis R α).repr f₂ (idOn S)
  have hsq₁ : c₁ * c₁ = c₁ := by rw [← repr_mul_idOn, h₁.eq]
  have hsq₂ : c₂ * c₂ = c₂ := by rw [← repr_mul_idOn, h₂.eq]
  have hmul₁₂ : c₁ * c₂ = 0 := by rw [← repr_mul_idOn, h₁₂, map_zero, Finsupp.zero_apply]
  have hmul₂₁ : c₂ * c₁ = 0 := by rw [← repr_mul_idOn, h₂₁, map_zero, Finsupp.zero_apply]
  have hone : c₁ + c₂ = 1 := by
    rw [← Finsupp.add_apply, ← map_add, hsum, repr_matchedIdem_idOn hS]
  exact (hk.eq_zero_or_eq_zero_of_add hsq₁ hsq₂ hmul₁₂ hmul₂₁ hone).imp
    (eq_zero_of_isIdempotentElem_of_repr_idOn_eq_zero hf₁ h₁ hc₁ hS rfl)
    (eq_zero_of_isIdempotentElem_of_repr_idOn_eq_zero hf₂ h₂ hc₂ hS rfl)

/-! ### The idempotents of the matched subalgebra -/

/-- **The idempotents `I(s)` of the matched subalgebra are primitive.** If `1` is a primitive
idempotent of the coefficient semiring, for instance over a field such as `𝔽₂`, then `I(s)` is a
primitive idempotent of the matched subalgebra exactly when `s` is a set of pairs. -/
theorem isPrimitiveIdempotent_matchedIdem_iff (hk : IsPrimitiveIdempotent (1 : R)) :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) ↔
      s ⊆ univ.image M := by
  have := hk.nontrivial
  refine ⟨fun h ↦ not_not.1 fun hs ↦ h.ne_zero (Subtype.ext (matchedIdem_eq_zero_iff.2 hs)),
    fun hs ↦ ⟨Subtype.ext (isIdempotentElem_matchedIdem M s),
      fun h ↦ matchedIdem_eq_zero_iff.1 (congrArg Subtype.val h) hs, ?_⟩⟩
  intro e₁ e₂ h₁ h₂ h₁₂ h₂₁ hsum
  have key {e : matchedSubalgebra R M} (he : IsIdempotentElem e) :
      IsIdempotentElem (e : StrandsAlgebra R α) := by
    rw [IsIdempotentElem, ← NonUnitalSubalgebra.coe_mul, he.eq]
  refine (eq_zero_or_eq_zero_of_add_eq_matchedIdem (s := s) hk e₁.2 e₂.2 (key h₁) (key h₂) ?_ ?_
    ?_).imp (fun h ↦ Subtype.ext h) fun h ↦ Subtype.ext h
  · rw [← NonUnitalSubalgebra.coe_mul, h₁₂, ZeroMemClass.coe_zero]
  · rw [← NonUnitalSubalgebra.coe_mul, h₂₁, ZeroMemClass.coe_zero]
  · rw [← NonUnitalSubalgebra.coe_add, hsum]

/-- **The idempotents `I(s)` of the sets `s` of pairs form a complete family of orthogonal
idempotents of the matched subalgebra**: they are orthogonal idempotents summing to its unit. -/
theorem completeOrthogonalIdempotents_matchedIdem :
    CompleteOrthogonalIdempotents fun s : (univ.image M).powerset ↦
      (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) where
  idem s := Subtype.ext (isIdempotentElem_matchedIdem M s)
  ortho s t hst := Subtype.ext (by
    rw [NonUnitalSubalgebra.coe_mul, matchedIdem_mul_matchedIdem,
      ite_eq_right fun h ↦ hst (Subtype.ext h), ZeroMemClass.coe_zero])
  complete := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum, coe_matchedSubalgebra_one, matchedOne_def,
      ← sum_coe_sort (univ.image M).powerset])

/-! ### The idempotents of a matched summand -/

/-- **The idempotents `I(s)` of the matched summands are primitive.** If `1` is a primitive
idempotent of the coefficient semiring, then `I(s)` is a primitive idempotent of the summand of
the matched subalgebra with `#s` strands exactly when `s` is a set of pairs. -/
theorem isPrimitiveIdempotent_matchedIdem_matchedSummand_iff (hk : IsPrimitiveIdempotent (1 : R)) :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSummand M s⟩ : matchedSummand R M #s) ↔
      s ⊆ univ.image M := by
  have := hk.nontrivial
  refine ⟨fun h ↦ not_not.1 fun hs ↦ h.ne_zero (Subtype.ext (matchedIdem_eq_zero_iff.2 hs)),
    fun hs ↦ ⟨Subtype.ext (isIdempotentElem_matchedIdem M s),
      fun h ↦ matchedIdem_eq_zero_iff.1 (congrArg Subtype.val h) hs, ?_⟩⟩
  intro e₁ e₂ h₁ h₂ h₁₂ h₂₁ hsum
  have key {e : matchedSummand R M #s} (he : IsIdempotentElem e) :
      IsIdempotentElem (e : StrandsAlgebra R α) := by
    rw [IsIdempotentElem, ← NonUnitalSubalgebra.coe_mul, he.eq]
  refine (eq_zero_or_eq_zero_of_add_eq_matchedIdem (s := s) hk
    (matchedSummand_le_matchedSubalgebra _ e₁.2) (matchedSummand_le_matchedSubalgebra _ e₂.2)
    (key h₁) (key h₂) ?_ ?_ ?_).imp (fun h ↦ Subtype.ext h) fun h ↦ Subtype.ext h
  · rw [← NonUnitalSubalgebra.coe_mul, h₁₂, ZeroMemClass.coe_zero]
  · rw [← NonUnitalSubalgebra.coe_mul, h₂₁, ZeroMemClass.coe_zero]
  · rw [← NonUnitalSubalgebra.coe_add, hsum]

/-- **The idempotents `I(s)` of the sets `s` of `k` pairs form a complete family of orthogonal
idempotents of the matched summand with `k` strands**: they are orthogonal idempotents summing to
its unit. -/
theorem completeOrthogonalIdempotents_matchedIdem_matchedSummand (k : ℕ) :
    CompleteOrthogonalIdempotents fun s : {s ∈ (univ.image M).powerset | #s = k} ↦
      (⟨matchedIdem R M s, by
        have h := matchedIdem_mem_matchedSummand (R := R) M s
        rwa [(mem_filter.1 s.2).2] at h⟩ : matchedSummand R M k) where
  idem s := Subtype.ext (isIdempotentElem_matchedIdem M s)
  ortho s t hst := Subtype.ext (by
    rw [NonUnitalSubalgebra.coe_mul, matchedIdem_mul_matchedIdem,
      ite_eq_right fun h ↦ hst (Subtype.ext h), ZeroMemClass.coe_zero])
  complete := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finsetSum, coe_matchedSummand_one, matchedSummandOne_def,
      ← sum_coe_sort {s ∈ (univ.image M).powerset | #s = k}])

end StrandsAlgebra

end TauCeti
