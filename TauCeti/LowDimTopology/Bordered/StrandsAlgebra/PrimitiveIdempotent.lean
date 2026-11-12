/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.LengthFiltration
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# The primitive idempotents of the matched subalgebra

The algebra `A(Z)` of a pointed matched circle, the matched subalgebra of the strands algebra
(`TauCeti.StrandsAlgebra.matchedSubalgebra`), has the idempotents `I(s)`
(`TauCeti.StrandsAlgebra.matchedIdem`), one for each set `s` of matched pairs. They are orthogonal
and sum to the unit (`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`), and
this file shows that they are **primitive** idempotents of `A(Z)`, provided
`1` is primitive in the ground ring, that is, the ground ring is nontrivial and has no idempotents
besides `0` and `1`; over `𝔽₂` they are therefore the primitive idempotents of a complete
orthogonal decomposition of the unit, which is the ring of idempotents over which type `D`
structures and type `A` modules of bordered Floer theory are defined. Precisely, `I(s)` is
primitive exactly when `s` consists of matched pairs and `1` is primitive in the ground ring
(`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`).

The proof uses the filtration of the strands algebra by the total length of the strands
(`TauCeti.StrandsAlgebra.lengthFiltration`), whose part `F_1`, the elements with no identity
diagram in their support, consists of nilpotent elements. An element `f` of the corner ring
`I(s) A(Z) I(s)` takes the same value `c` at every identity diagram `I(S)` with `S` a set of points
over `s`, because the coefficients of an element of the matched subalgebra do not change when a
horizontal strand moves within a matched pair, and it vanishes at the other identity diagrams. So
`f - c I(s)` lies in `F_1`. When `f` is idempotent, reducing `f² = f` modulo `F_1` shows that `c`
is an idempotent of the ground ring, so `c = 0` or `c = 1`, and then `f` or `I(s) - f` is an
idempotent in `F_1`, hence nilpotent and zero.

## Main results

* `TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`: when `1` is primitive in
  the ground ring, the only idempotents of the corner ring of `I(s)` in the matched subalgebra are
  `0` and `I(s)`.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`: `I(s)` is a primitive idempotent
  of the matched subalgebra exactly when `s` is a set of matched pairs and `1` is primitive in the
  ground ring.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  idempotents `I(s)` and the subalgebra of idempotents of `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

/-! ### The primitive idempotents of the matched subalgebra -/

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [DecidableEq β]
  {M : α → β} {s : Finset β}

/-- **The corner ring of `I(s)` modulo `F_1`.** An element `x` of the matched subalgebra with
`I(s) x = x` agrees with `c I(s)` modulo the elements with no identity diagram in their support,
where `c` is its coefficient at the identity diagram of any set `S` of points over `s`. -/
theorem sub_smul_matchedIdem_mem_lengthFiltration {R : Type*} [CommRing R]
    {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M) (hex : matchedIdem R M s * x = x)
    {S : Finset α} (hS : S ∈ matchedChoices M s) :
    x - (basis R α).repr x (idOn S) • matchedIdem R M s ∈ lengthFiltration R 1 := by
  refine mem_lengthFiltration_one_iff.2 fun T ↦ ?_
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hT : T ∈ matchedChoices M s
  · rw [repr_matchedIdem_apply_idOn hT, mul_one, repr_apply_idOn_eq hx hS hT, sub_self]
  · have h0 : (basis R α).repr x (idOn T) = 0 := by
      rw [← hex, repr_matchedIdem_mul_apply, source_idOn]
      simp [hT]
    have h1 : (basis R α).repr (matchedIdem R M s) (idOn T) = 0 := by
      rw [← (isIdempotentElem_matchedIdem M s).eq, repr_matchedIdem_mul_apply, source_idOn]
      simp [hT]
    rw [h0, h1, mul_zero, sub_zero]

/-- **The idempotents of the corner ring of `I(s)`.** When `1` is primitive in the ground ring,
that is, the ground ring is nontrivial and has no idempotents besides `0` and `1`, the only
idempotents `x` of the matched subalgebra with `I(s) x = x I(s) = x` are `0` and `I(s)`. -/
theorem eq_zero_or_eq_matchedIdem_of_isIdempotentElem {R : Type*} [CommRing R]
    (h1 : IsPrimitiveIdempotent (1 : R)) {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) (hxx : IsIdempotentElem x) (hex : matchedIdem R M s * x = x)
    (hxe : x * matchedIdem R M s = x) : x = 0 ∨ x = matchedIdem R M s := by
  by_cases hs : s ⊆ univ.image M
  swap
  · left
    rw [← hex, matchedIdem_eq_horizontalCompletion, horizontalCompletion_eq_zero_of_not_subset _ hs,
      zero_mul]
  obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
  have hn : x - (basis R α).repr x (idOn S) • matchedIdem R M s ∈ lengthFiltration R 1 :=
    sub_smul_matchedIdem_mem_lengthFiltration hx hex hS
  -- Reducing `x² = x` modulo `F_1` shows that the coefficient `c` of `x` at `I(S)` is an
  -- idempotent of `R`, so it is `0` or `1`.
  generalize hc : (basis R α).repr x (idOn S) = c at hn
  have hcc : IsIdempotentElem c := by
    generalize hn' : x - c • matchedIdem R M s = n at hn
    have hx' : x = c • matchedIdem R M s + n := by rw [← hn', add_sub_cancel]
    have h2 : x - (c * c) • matchedIdem R M s =
        c • (matchedIdem R M s * n) + c • (n * matchedIdem R M s) + n * n := by
      conv_lhs => rw [← hxx.eq, hx']
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
        (isIdempotentElem_matchedIdem M s).eq]
      abel
    have hF (y : StrandsAlgebra R α) : y ∈ lengthFiltration R 0 := by simp
    have hsq : x - (c * c) • matchedIdem R M s ∈ lengthFiltration R 1 := by
      rw [h2]
      refine add_mem (add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) ?_
      · simpa using mul_mem_lengthFiltration (hF _) hn
      · simpa using mul_mem_lengthFiltration hn (hF _)
      · exact lengthFiltration_antitone (by norm_num) (mul_mem_lengthFiltration hn hn)
    have hdiff := mem_lengthFiltration_one_iff.1 (sub_mem hsq (hn' ▸ hn)) S
    rw [sub_sub_sub_cancel_left, ← sub_smul, map_smul, Finsupp.smul_apply,
      repr_matchedIdem_apply_idOn hS, smul_eq_mul, mul_one, sub_eq_zero] at hdiff
    exact hdiff.symm
  -- Then `x` or `I(s) - x` is an idempotent in `F_1`, hence nilpotent and zero.
  have := h1.nontrivial
  rcases isPrimitiveIdempotent_one_iff.1 h1 c hcc with rfl | rfl
  · rw [zero_smul, sub_zero] at hn
    exact .inl (hxx.eq_zero_of_isNilpotent (isNilpotent_of_mem_lengthFiltration_one hn))
  · rw [one_smul] at hn
    have hsub : IsIdempotentElem (matchedIdem R M s - x) :=
      hxx.sub (isIdempotentElem_matchedIdem M s) hxe hex
    refine .inr (sub_eq_zero.1 (hsub.eq_zero_of_isNilpotent ?_)).symm
    exact isNilpotent_of_mem_lengthFiltration_one (by simpa only [neg_sub] using neg_mem hn)

/-- **The idempotents `I(s)` are primitive.** The idempotent `I(s)` of the matched subalgebra is
primitive exactly when `s` is a set of matched pairs and `1` is primitive in the ground ring, that
is, the ground ring is nontrivial and has no idempotents besides `0` and `1`, as for `𝔽₂`. -/
theorem isPrimitiveIdempotent_matchedIdem_iff {R : Type*} [CommRing R] :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) ↔
      IsPrimitiveIdempotent (1 : R) ∧ s ⊆ univ.image M := by
  set e : matchedSubalgebra R M := ⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩
  have he : IsIdempotentElem e := Subtype.ext (isIdempotentElem_matchedIdem M s)
  constructor
  · intro hprim
    have hs : s ⊆ univ.image M := by
      by_contra hs
      exact hprim.ne_zero (Subtype.ext ((matchedIdem_eq_horizontalCompletion M s).trans
        (horizontalCompletion_eq_zero_of_not_subset _ hs)))
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    have : Nontrivial R := by
      refine (subsingleton_or_nontrivial R).resolve_left fun _ ↦ hprim.ne_zero ?_
      exact Subtype.ext ((basis R α).repr.injective (Subsingleton.elim _ _))
    refine ⟨isPrimitiveIdempotent_one_iff.2 fun r hr ↦ ?_, hs⟩
    -- `r I(s)` is an idempotent of the corner ring of `I(s)`, so it is `0` or `I(s)`.
    have hre : IsIdempotentElem (r • e) := by
      rw [IsIdempotentElem, smul_mul_smul_comm, hr.eq, he.eq]
    have key := hprim.eq_zero_or_eq hre (by rw [mul_smul_comm, he.eq]) (by rw [smul_mul_assoc,
      he.eq])
    have hcoeff : (basis R α).repr ((r • e : matchedSubalgebra R M) : StrandsAlgebra R α)
        (idOn S) = r := by
      rw [NonUnitalSubalgebra.coe_smul, map_smul, Finsupp.smul_apply,
        repr_matchedIdem_apply_idOn hS, smul_eq_mul, mul_one]
    refine key.imp (fun h ↦ ?_) fun h ↦ ?_ <;> rw [← hcoeff, h]
    · simp
    · exact repr_matchedIdem_apply_idOn hS
  · rintro ⟨h1, hs⟩
    have := h1.nontrivial
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    refine isPrimitiveIdempotent_of_eq_zero_or_eq he (fun he0 ↦ ?_) fun f hf hef hfe ↦ ?_
    · -- The ambient element of `e = 0` is `I(s) = 0`, but `I(s)` has coefficient `1` at `I(S)`.
      have h0 : matchedIdem R M s = 0 := by simpa [e] using congrArg Subtype.val he0
      simpa [h0] using repr_matchedIdem_apply_idOn (R := R) hS
    refine (eq_zero_or_eq_matchedIdem_of_isIdempotentElem h1 f.2 (congrArg Subtype.val hf.eq)
      (congrArg Subtype.val hef) (congrArg Subtype.val hfe)).imp Subtype.ext Subtype.ext

end StrandsAlgebra

end TauCeti
