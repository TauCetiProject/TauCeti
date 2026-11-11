/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# The primitive idempotents of the algebra of a matching

The algebra `A(Z)` of a pointed matched circle `Z` is the matched subalgebra of the strands algebra
(`TauCeti.StrandsAlgebra.matchedSubalgebra`). Its ground ring is spanned by the idempotents
`I(s) = ∑ I(S)`, one for each set `s` of matched pairs, the sum running over the sets `S`
containing one point of each pair in `s`. This file shows that the `I(s)` are the primitive
idempotents of `A(Z)`: they are a complete family of orthogonal idempotents
(`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`), and each of them is
primitive (`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`). So the type `D`
structures and modules over `A(Z)`, whose generators each lie over one of these idempotents, are
graded by the sets of pairs, and no idempotent of `A(Z)` splits these summands further.

In the strands algebra itself `I(s)` is the sum of the orthogonal idempotents `I(S)`, so it is not
primitive as soon as `s` contains a pair. In the matched subalgebra the coefficients of an element
are constant along the sets `S` over `s`
(`TauCeti.StrandsAlgebra.repr_idOn_eq_of_mem_matchedChoices`), which glues the `I(S)` together.
Primitivity is then a statement about the corner ring of `I(s)`, and comes from the length of
strand diagrams (`TauCeti.StrandDiagram.length`): the coefficient of an identity diagram is
multiplicative (`TauCeti.StrandsAlgebra.repr_mul_apply_idOn`), and an
idempotent with no identity terms vanishes
(`TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero`). An idempotent
`f` of the corner ring therefore has a constant identity coefficient `c` over `s` with `c² = c`;
when the coefficient ring has no idempotents besides `0` and `1`, either `f` or `I(s) - f` has no
identity terms (`TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem`).

The condition on the coefficients is also necessary: an idempotent `r` of `R` gives the idempotent
`r • I(s)` of the corner ring. Over `𝔽₂`, the coefficients of bordered Heegaard Floer homology,
the `I(s)` are primitive exactly for the sets `s` of matched pairs; for the other sets of values
of the matching, `I(s)` is zero.

## Main results

* `TauCeti.StrandsAlgebra.matchedIdem_ne_zero_iff`: `I(s) ≠ 0` exactly when `s` is a set of
  matched pairs.
* `TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem`: the corner ring of `I(s)` in the matched
  subalgebra has no idempotents besides `0` and `I(s)`.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`: `I(s)` is a primitive idempotent
  of the matched subalgebra exactly when `s` is a set of matched pairs and `1` is primitive in `R`.
* `TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`: the `I(s)` over the sets of
  matched pairs are a complete family of orthogonal idempotents of the matched subalgebra.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  idempotents `I(s)` of the algebra `A(Z)` and its ground ring `I(Z)`).
-/

public section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq β] {M : α → β}

section Semiring

variable {R : Type*} [CommSemiring R]

/-! ### The identity coefficients of the matched subalgebra -/

omit [LinearOrder α] in
/-- There is a choice of one point of each pair in `s` exactly when `s` is a set of matched
pairs. -/
theorem matchedChoices_nonempty_iff {s : Finset β} :
    (matchedChoices M s).Nonempty ↔ s ⊆ univ.image M := by
  refine ⟨fun ⟨U, hU⟩ ↦ ?_, fun hs ↦ ?_⟩
  · rw [← (mem_matchedChoices.1 hU).1]
    exact image_subset_image (subset_univ U)
  · obtain ⟨U, -, hU, himage⟩ := exists_subset_injOn_image_eq_of_surjOn (f := M) Set.univ s
      fun b hb ↦ by simpa using hs hb
    exact ⟨U, mem_matchedChoices.2 ⟨himage, hU⟩⟩

/-- The coefficient of `I(s)` on the identity diagram of a choice of one point of each pair in `s`
is `1`. -/
theorem repr_matchedIdem_apply_idOn {s : Finset β} {U : Finset α} (hU : U ∈ matchedChoices M s) :
    (basis R α).repr (matchedIdem R M s) (idOn U) = 1 := by
  obtain ⟨himage, hinj⟩ := mem_matchedChoices.1 hU
  have hcard : #U = #s := by rw [← himage, card_image_of_injOn hinj]
  simp [repr_matchedIdem_apply, himage, hcard]

/-- **The identity coefficients of an element of the matched subalgebra are constant over a set
of pairs.** The identity diagrams of any two choices of one point of each pair in `s` are related by
moving horizontal strands to matched points. -/
theorem repr_idOn_eq_of_mem_matchedChoices {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) {s : Finset β} {U V : Finset α}
    (hU : U ∈ matchedChoices M s) (hV : V ∈ matchedChoices M s) :
    (basis R α).repr x (idOn U) = (basis R α).repr x (idOn V) := by
  refine repr_eq_of_matchedSetoid hx ?_
  simpa [idOn_addHorizontal] using
    (isMatchedGenerator_idOn_empty M s).matchedSetoid_addHorizontal hU hV

/-- `I(s)` is zero unless `s` is a set of matched pairs: for any other `s` no set of points is
mapped bijectively onto `s`. -/
theorem matchedIdem_eq_zero_of_not_subset {s : Finset β} (hs : ¬s ⊆ univ.image M) :
    matchedIdem R M s = 0 := by
  rw [matchedIdem_def]
  refine sum_eq_zero fun S hS ↦ absurd ?_ hs
  rw [← (mem_filter.1 hS).2.1]
  exact image_subset_image (subset_univ S)

/-- **`I(s)` is nonzero exactly when `s` is a set of matched pairs**, over a nontrivial ring. -/
theorem matchedIdem_ne_zero_iff [Nontrivial R] {s : Finset β} :
    matchedIdem R M s ≠ 0 ↔ s ⊆ univ.image M := by
  refine ⟨fun h ↦ not_not.1 fun hs ↦ h (matchedIdem_eq_zero_of_not_subset hs), fun hs h ↦ ?_⟩
  obtain ⟨U, hU⟩ := matchedChoices_nonempty_iff.2 hs
  have h1 := repr_matchedIdem_apply_idOn (R := R) hU
  rw [h, map_zero, Finsupp.zero_apply] at h1
  exact zero_ne_one h1

/-- **The idempotents `I(s)` are a complete family of orthogonal idempotents** of the matched
subalgebra, indexed by the sets `s` of matched pairs. -/
theorem completeOrthogonalIdempotents_matchedIdem :
    CompleteOrthogonalIdempotents fun s : (univ.image M).powerset ↦
      (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) where
  idem s := Subtype.ext (isIdempotentElem_matchedIdem M s)
  ortho s t hst := Subtype.ext <| by
    simp [matchedIdem_mul_matchedIdem, Subtype.coe_injective.ne hst]
  complete := Subtype.ext <| by
    simp [matchedOne_def, sum_attach]

/-! ### The corner ring of `I(s)` -/

/-- An idempotent of the matched subalgebra absorbed by `I(s)` on the left vanishes once its
coefficient on the identity diagram of one choice of points over `s` does: by constancy and
multiplicativity of the identity coefficients, all of them vanish. -/
private theorem eq_zero_of_matchedIdem_mul_eq {s : Finset β} {U : Finset α}
    (hU : U ∈ matchedChoices M s) {g : StrandsAlgebra R α} (hg : g ∈ matchedSubalgebra R M)
    (hgg : IsIdempotentElem g) (hsg : matchedIdem R M s * g = g)
    (hgU : (basis R α).repr g (idOn U) = 0) : g = 0 := by
  refine eq_zero_of_isIdempotentElem_of_forall_repr_idOn_eq_zero hgg fun S ↦ ?_
  rw [← hsg, repr_mul_apply_idOn]
  by_cases hS : S ∈ matchedChoices M s
  · rw [repr_idOn_eq_of_mem_matchedChoices hg hS hU, hgU, mul_zero]
  · have h0 : (basis R α).repr (matchedIdem R M s) (idOn S) = 0 := by
      rw [repr_matchedIdem_apply, source_idOn]
      exact ite_eq_right_iff.2 fun ⟨_, himage, hcard⟩ ↦
        absurd (mem_matchedChoices.2 ⟨himage, card_image_iff.1 (by rw [himage, hcard])⟩) hS
    rw [h0, zero_mul]

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-- **The corner ring of `I(s)` has no idempotents besides `0` and `I(s)`.** If the coefficient
ring has no idempotents besides `0` and `1`, every idempotent `f` of the matched subalgebra with
`I(s) f = f = f I(s)` is `0` or `I(s)`. -/
theorem eq_zero_or_eq_matchedIdem (hR : ∀ r : R, IsIdempotentElem r → r = 0 ∨ r = 1)
    {s : Finset β} {f : StrandsAlgebra R α} (hf : f ∈ matchedSubalgebra R M)
    (hff : IsIdempotentElem f) (hsf : matchedIdem R M s * f = f)
    (hfs : f * matchedIdem R M s = f) : f = 0 ∨ f = matchedIdem R M s := by
  by_cases hs : s ⊆ univ.image M
  swap
  · rw [matchedIdem_eq_zero_of_not_subset hs, zero_mul] at hsf
    exact Or.inl hsf.symm
  obtain ⟨U, hU⟩ := matchedChoices_nonempty_iff.2 hs
  -- The identity coefficient `c` of `f` over `s` is an idempotent of `R`.
  have hc : IsIdempotentElem ((basis R α).repr f (idOn U)) := by
    rw [IsIdempotentElem, ← repr_mul_apply_idOn, hff.eq]
  rcases hR _ hc with hc0 | hc1
  · exact Or.inl (eq_zero_of_matchedIdem_mul_eq hU hf hff hsf hc0)
  -- If `c = 1`, the complement `I(s) - f` has identity coefficient `0`.
  refine Or.inr (sub_eq_zero.1 (eq_zero_of_matchedIdem_mul_eq hU
    (sub_mem (matchedIdem_mem_matchedSubalgebra M s) hf)
    (hff.sub (isIdempotentElem_matchedIdem M s) hfs hsf) ?_ ?_)).symm
  · rw [mul_sub, (isIdempotentElem_matchedIdem M s).eq, hsf]
  · rw [map_sub, Finsupp.sub_apply, repr_matchedIdem_apply_idOn hU, hc1, sub_self]

/-! ### Primitivity -/

/-- **The idempotents `I(s)` are primitive.** The idempotent `I(s)` is a primitive idempotent of
the matched subalgebra exactly when `s` is a set of matched pairs and the coefficient ring has no
idempotents besides `0` and `1`; for instance over a field, such as `𝔽₂`. -/
theorem isPrimitiveIdempotent_matchedIdem_iff {s : Finset β} :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) ↔
      s ⊆ univ.image M ∧ IsPrimitiveIdempotent (1 : R) := by
  set e : matchedSubalgebra R M := ⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩
  have he : IsIdempotentElem e := Subtype.ext (isIdempotentElem_matchedIdem M s)
  constructor
  · intro hprim
    have hne : matchedIdem R M s ≠ 0 := fun h ↦ hprim.ne_zero (Subtype.ext h)
    -- `R` is nontrivial: otherwise the strands algebra, and `I(s)`, would vanish.
    have : Nontrivial R := by
      by_contra hR
      rw [not_nontrivial_iff_subsingleton] at hR
      exact hne ((basis R α).repr.injective (Subsingleton.elim _ _))
    have hs := matchedIdem_ne_zero_iff.1 hne
    obtain ⟨U, hU⟩ := matchedChoices_nonempty_iff.2 hs
    refine ⟨hs, isPrimitiveIdempotent_one_iff.2 fun r hr ↦ ?_⟩
    -- An idempotent `r` of `R` gives the idempotent `r • I(s)` of the corner ring of `I(s)`.
    have hre : IsIdempotentElem (r • e) := by
      rw [IsIdempotentElem, smul_mul_smul_comm, hr.eq, he.eq]
    have h := hprim.eq_zero_or_eq hre (by rw [mul_smul_comm, he.eq])
      (by rw [smul_mul_assoc, he.eq])
    have hcoe (t : R) : (basis R α).repr ((t • e : matchedSubalgebra R M) : StrandsAlgebra R α)
        (idOn U) = t := by
      rw [NonUnitalSubalgebra.coe_smul, map_smul, Finsupp.smul_apply,
        repr_matchedIdem_apply_idOn hU, smul_eq_mul, mul_one]
    refine h.imp (fun h0 ↦ ?_) fun h1 ↦ ?_
    · rw [← hcoe r, h0]
      simp
    · rw [← hcoe r, h1, ← hcoe 1, one_smul]
  · rintro ⟨hs, hR⟩
    have : Nontrivial R := hR.nontrivial
    refine isPrimitiveIdempotent_of_eq_zero_or_eq he
      (fun h ↦ matchedIdem_ne_zero_iff.2 hs (congrArg Subtype.val h)) fun f hf hef hfe ↦ ?_
    refine (eq_zero_or_eq_matchedIdem (isPrimitiveIdempotent_one_iff.1 hR) f.2
      (congrArg Subtype.val hf.eq) (congrArg Subtype.val hef)
      (congrArg Subtype.val hfe)).imp Subtype.ext Subtype.ext

end Ring

end StrandsAlgebra

end TauCeti
