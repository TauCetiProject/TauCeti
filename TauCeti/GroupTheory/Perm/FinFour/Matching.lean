/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# The symmetric group on four letters acting on the three perfect matchings

The set `Fin 4` has three perfect matchings,

`M₀ = 01|23`, `M₁ = 03|12`, `M₂ = 02|13`,

and a permutation of `Fin 4` carries each of them to another. This defines a homomorphism
`q : S₄ → S₃`, the exceptional homomorphism through which the two-dimensional irreducible
representation of `S₄` factors. Here a matching is recorded by the product of the two
transpositions that swap its pairs, so `S₄` acts on matchings by conjugation; this is the
action of `S₄` by conjugation on the three nontrivial elements of the Klein four-group.

The homomorphism `q` is surjective, and its kernel is the Klein four-group
`{1, (01)(23), (02)(13), (03)(12)}`, the image in `S₄` of Mathlib's
`alternatingGroup.kleinFour (Fin 4)`. Hence `S₄ / V₄ ≃ S₃`.

## Main definitions

* `TauCeti.symmetricGroupFourMatching`: the double transpositions of the matchings
  `M₀`, `M₁`, `M₂`.
* `TauCeti.symmetricGroupFourMatchingHom`: the homomorphism `q : S₄ →* S₃` recording how a
  permutation moves the three matchings.
* `TauCeti.symmetricGroupFourQuotientMatchingEquiv`: the isomorphism `S₄ / ker q ≃* S₃`.

## Main results

* `TauCeti.cycleType_eq_two_two_iff_exists_symmetricGroupFourMatching`: the permutations of
  `Fin 4` of cycle type `{2, 2}` are the double transpositions of the three matchings.
* `TauCeti.symmetricGroupFourMatching_symmetricGroupFourMatchingHom_apply`: `q σ` sends `m` to
  the matching whose double transposition is the conjugate by `σ` of that of `m`.
* `TauCeti.symmetricGroupFourMatchingHom_surjective`: `q` is surjective.
* `TauCeti.mem_ker_symmetricGroupFourMatchingHom_iff`: the kernel of `q` consists of the
  identity and the three double transpositions.
* `TauCeti.ker_symmetricGroupFourMatchingHom`: the kernel of `q` is the Klein four-group.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3.
* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 18.
-/

public section

namespace TauCeti

open Equiv

/-- **The three perfect matchings of `Fin 4`**, each recorded by the product of the two
transpositions swapping its pairs: `M₀ = 01|23`, `M₁ = 03|12` and `M₂ = 02|13` give `(01)(23)`,
`(03)(12)` and `(02)(13)`. -/
def symmetricGroupFourMatching : Fin 3 → Perm (Fin 4) :=
  ![swap 0 1 * swap 2 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3]

/-- The matching `M₀ = 01|23` swaps `0 ↔ 1` and `2 ↔ 3`. -/
@[simp]
theorem symmetricGroupFourMatching_zero : symmetricGroupFourMatching 0 = swap 0 1 * swap 2 3 :=
  (rfl)

/-- The matching `M₁ = 03|12` swaps `0 ↔ 3` and `1 ↔ 2`. -/
@[simp]
theorem symmetricGroupFourMatching_one : symmetricGroupFourMatching 1 = swap 0 3 * swap 1 2 :=
  (rfl)

/-- The matching `M₂ = 02|13` swaps `0 ↔ 2` and `1 ↔ 3`. -/
@[simp]
theorem symmetricGroupFourMatching_two : symmetricGroupFourMatching 2 = swap 0 2 * swap 1 3 :=
  (rfl)

/-- Distinct matchings have distinct double transpositions. -/
theorem symmetricGroupFourMatching_injective : Function.Injective symmetricGroupFourMatching := by
  unfold Function.Injective
  decide

/-- The double transposition of each matching is an even permutation. -/
theorem symmetricGroupFourMatching_mem_alternatingGroup (m : Fin 3) :
    symmetricGroupFourMatching m ∈ alternatingGroup (Fin 4) := by
  rw [Perm.mem_alternatingGroup]
  revert m
  decide

/-- **A fixed-point-free involution of `Fin 4` is the double transposition of a matching.** -/
theorem exists_eq_symmetricGroupFourMatching_of_sq_eq_one_of_forall_apply_ne {σ : Perm (Fin 4)}
    (h2 : σ ^ 2 = 1) (hσ : ∀ x, σ x ≠ x) : ∃ m, σ = symmetricGroupFourMatching m := by
  revert σ
  decide

/-- **The permutations of `Fin 4` of cycle type `{2, 2}` are the double transpositions of the
three matchings.** -/
theorem cycleType_eq_two_two_iff_exists_symmetricGroupFourMatching {σ : Perm (Fin 4)} :
    σ.cycleType = {2, 2} ↔ ∃ m, σ = symmetricGroupFourMatching m := by
  refine ⟨fun hσ => ?_, ?_⟩
  · -- `Equiv.Perm.cycleType` does not reduce, so read off from the cycle type `{2, 2}` that `σ` is
    -- a fixed-point-free involution.
    refine exists_eq_symmetricGroupFourMatching_of_sq_eq_one_of_forall_apply_ne ?_ fun x => ?_
    · rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, hσ]
      simp
    · rw [← Perm.mem_support,
        Finset.eq_univ_of_card σ.support (by rw [← Perm.sum_cycleType, hσ]; simp)]
      exact Finset.mem_univ x
  · rintro ⟨m, rfl⟩
    fin_cases m <;> exact Perm.cycleType_swap_mul_swap_of_nodup (by decide)

/-- The matching containing the pair `{0, g 0}`, read off from the partner of `0`. -/
private def matchingIndex (g : Perm (Fin 4)) : Fin 3 :=
  ![0, 0, 2, 1] (g 0)

/-- Conjugating a double transposition gives the double transposition of another matching. -/
private theorem symmetricGroupFourMatching_matchingIndex_conj (σ : Perm (Fin 4)) (m : Fin 3) :
    symmetricGroupFourMatching (matchingIndex (σ * symmetricGroupFourMatching m * σ⁻¹)) =
      σ * symmetricGroupFourMatching m * σ⁻¹ := by
  revert σ m
  decide

/-- The matching onto which `σ` carries the matching `m`. -/
private def matchingConj (σ : Perm (Fin 4)) (m : Fin 3) : Fin 3 :=
  matchingIndex (σ * symmetricGroupFourMatching m * σ⁻¹)

private theorem matchingConj_one (m : Fin 3) : matchingConj 1 m = m :=
  symmetricGroupFourMatching_injective <| by
    rw [matchingConj, symmetricGroupFourMatching_matchingIndex_conj, one_mul, inv_one, mul_one]

private theorem matchingConj_mul (σ τ : Perm (Fin 4)) (m : Fin 3) :
    matchingConj (σ * τ) m = matchingConj σ (matchingConj τ m) :=
  symmetricGroupFourMatching_injective <| by
    unfold matchingConj
    rw [symmetricGroupFourMatching_matchingIndex_conj,
      symmetricGroupFourMatching_matchingIndex_conj, symmetricGroupFourMatching_matchingIndex_conj]
    group

/-- **The action of `S₄` on the three perfect matchings of `Fin 4`**, the homomorphism
`q : S₄ →* S₃` sending `σ` to the permutation `M ↦ σ(M)` of the matchings
`M₀ = 01|23`, `M₁ = 03|12`, `M₂ = 02|13`. Its kernel is the Klein four-group. -/
def symmetricGroupFourMatchingHom : Perm (Fin 4) →* Perm (Fin 3) where
  toFun σ :=
    { toFun := matchingConj σ
      invFun := matchingConj σ⁻¹
      left_inv m := by rw [← matchingConj_mul, inv_mul_cancel, matchingConj_one]
      right_inv m := by rw [← matchingConj_mul, mul_inv_cancel, matchingConj_one] }
  map_one' := Equiv.ext matchingConj_one
  map_mul' σ τ := Equiv.ext (matchingConj_mul σ τ)

/-- **The defining property of `q`**: the matching `q σ m` is the image of `m` under `σ`, that is,
its double transposition is the conjugate by `σ` of that of `m`. -/
theorem symmetricGroupFourMatching_symmetricGroupFourMatchingHom_apply (σ : Perm (Fin 4))
    (m : Fin 3) :
    symmetricGroupFourMatching (symmetricGroupFourMatchingHom σ m) =
      σ * symmetricGroupFourMatching m * σ⁻¹ :=
  symmetricGroupFourMatching_matchingIndex_conj σ m

/-- The transposition `(01)` fixes `M₀ = 01|23` and swaps `M₁ = 03|12` with `M₂ = 02|13`. -/
@[simp]
theorem symmetricGroupFourMatchingHom_swap_zero_one :
    symmetricGroupFourMatchingHom (swap 0 1) = swap 1 2 := by
  decide

/-- The transposition `(12)` fixes `M₁ = 03|12` and swaps `M₀ = 01|23` with `M₂ = 02|13`. -/
@[simp]
theorem symmetricGroupFourMatchingHom_swap_one_two :
    symmetricGroupFourMatchingHom (swap 1 2) = swap 0 2 := by
  decide

/-- The transposition `(23)` fixes `M₀ = 01|23` and swaps `M₁ = 03|12` with `M₂ = 02|13`. -/
@[simp]
theorem symmetricGroupFourMatchingHom_swap_two_three :
    symmetricGroupFourMatchingHom (swap 2 3) = swap 1 2 := by
  decide

/-- The double transposition `(01)(23)` fixes every matching. -/
theorem symmetricGroupFourMatchingHom_swap_zero_one_mul_swap_two_three :
    symmetricGroupFourMatchingHom (swap 0 1 * swap 2 3) = 1 := by
  decide

/-- The three-cycle `(012)` cycles the matchings `M₀ → M₁ → M₂ → M₀`. -/
theorem symmetricGroupFourMatchingHom_formPerm_zero_one_two :
    symmetricGroupFourMatchingHom [0, 1, 2].formPerm = [0, 1, 2].formPerm := by
  decide

/-- The four-cycle `(0123)` swaps `M₀ = 01|23` with `M₁ = 03|12` and fixes `M₂ = 02|13`. -/
theorem symmetricGroupFourMatchingHom_formPerm_zero_one_two_three :
    symmetricGroupFourMatchingHom [0, 1, 2, 3].formPerm = swap 0 1 := by
  decide

/-- **Every permutation of the three matchings comes from a permutation of `Fin 4`.** -/
theorem symmetricGroupFourMatchingHom_surjective :
    Function.Surjective symmetricGroupFourMatchingHom := by
  unfold Function.Surjective
  decide

/-- **The kernel of `q` is `{1, (01)(23), (02)(13), (03)(12)}`**: a permutation fixing all three
matchings is the identity or one of their double transpositions. -/
theorem mem_ker_symmetricGroupFourMatchingHom_iff {σ : Perm (Fin 4)} :
    σ ∈ symmetricGroupFourMatchingHom.ker ↔ σ = 1 ∨ ∃ m, σ = symmetricGroupFourMatching m := by
  rw [MonoidHom.mem_ker]
  revert σ
  decide

/-- **The kernel of `q` is the Klein four-group** `alternatingGroup.kleinFour (Fin 4)`, viewed in
`S₄`. -/
theorem ker_symmetricGroupFourMatchingHom :
    symmetricGroupFourMatchingHom.ker =
      (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype := by
  ext σ
  rw [mem_ker_symmetricGroupFourMatchingHom_iff, ← SetLike.mem_coe, Subgroup.coe_map,
    alternatingGroup.coe_kleinFour_of_card_eq_four (Nat.card_eq_fintype_card.trans rfl)]
  constructor
  · rintro (rfl | ⟨m, rfl⟩)
    · exact ⟨1, Or.inl rfl, rfl⟩
    · exact ⟨⟨_, symmetricGroupFourMatching_mem_alternatingGroup m⟩,
        Or.inr (cycleType_eq_two_two_iff_exists_symmetricGroupFourMatching.2 ⟨m, rfl⟩), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rcases hg with hg | hg
    · exact Or.inl (by simp [Set.mem_singleton_iff.mp hg])
    · exact Or.inr (cycleType_eq_two_two_iff_exists_symmetricGroupFourMatching.1 hg)

/-- **`S₄` modulo the Klein four-group is `S₃`**: the isomorphism `S₄ / ker q ≃* S₃` induced by
the action on matchings. -/
noncomputable def symmetricGroupFourQuotientMatchingEquiv :
    Perm (Fin 4) ⧸ symmetricGroupFourMatchingHom.ker ≃* Perm (Fin 3) :=
  QuotientGroup.quotientKerEquivOfSurjective _ symmetricGroupFourMatchingHom_surjective

/-- The isomorphism `S₄ / ker q ≃* S₃` sends the class of `σ` to `q σ`. -/
@[simp]
theorem symmetricGroupFourQuotientMatchingEquiv_mk (σ : Perm (Fin 4)) :
    symmetricGroupFourQuotientMatchingEquiv σ = symmetricGroupFourMatchingHom σ :=
  (rfl)

end TauCeti
