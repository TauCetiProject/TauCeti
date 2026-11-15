/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandCount

/-!
# The occupancy summands of the strands algebra and of the matched subalgebra

Every strand diagram has as many end points as starting points, and the strands product and the
differential do not change the number of strands. So the strands algebra `A(n)` of Lipshitz,
Ozsváth and Thurston is the direct sum of the algebras `A(n, k)` spanned by the diagrams with `k`
strands (`TauCeti.StrandsAlgebra.strandSummand`), and products of elements with different numbers
of strands vanish. The unit of `A(n, k)` is the sum `∑_{|S| = k} I(S)` of the idempotents on the
sets with `k` points (`TauCeti.StrandsAlgebra.strandSummandOne`); these sums are orthogonal
idempotents adding up to the unit of `A(n)`, and each `A(n, k)` is a two-sided ideal.

For a matching `M`, the matched subalgebra splits in the same way into the summands
`TauCeti.StrandsAlgebra.matchedSummand R M k` of its elements with `k` strands. For the matching of
a pointed matched circle `Z` with `4g` points these are the summands `A(Z, i)` of `A(Z)` with
`g + i` strands, for `-g ≤ i ≤ g`; the summand `A(Z, 0)` is the algebra of bordered Heegaard Floer
homology for a connected boundary. The idempotent `I(s)` of a set `s` of pairs has `#s` strands,
and the unit of the summand with `k` strands is the sum of the `I(s)` over the sets of `k` pairs
(`TauCeti.StrandsAlgebra.matchedSummandOne`). With this unit each summand is an `R`-algebra, and
over a ring of characteristic two the restricted differential makes it an ungraded differential
algebra. On the summands with at most one strand the differential vanishes. As an `R`-algebra the
matched subalgebra is the product of its summands, compatibly with the differentials.

The summand with one strand contains the idempotents `I({p})` of the matched pairs `p`
(`TauCeti.StrandsAlgebra.oneStrandIdem`), which are orthogonal and add up to its unit, and the
single strands of the chords `i < j` (`TauCeti.StrandsAlgebra.oneStrandChord`). A chord starts at
the idempotent of the pair of `i` and ends at that of the pair of `j`, and two chords multiply to
their concatenation when the first ends where the second starts, and to zero otherwise. For the
genus-one pointed matched circle this summand is the torus algebra.

## Main definitions

* `TauCeti.StrandsAlgebra.strandSummand R α k`: the elements of the strands algebra with `k`
  strands, the algebra `A(n, k)`.
* `TauCeti.StrandsAlgebra.strandSummandOne R α k`: the unit `∑_{|S| = k} I(S)` of `A(n, k)`.
* `TauCeti.StrandsAlgebra.matchedSummand R M k`: the elements of the matched subalgebra with `k`
  strands.
* `TauCeti.StrandsAlgebra.matchedSummandOne R M k`: its unit, the sum of the `I(s)` over the sets
  `s` of `k` pairs.
* `TauCeti.StrandsAlgebra.matchedSummandDifferential R M k`: the differential restricted to the
  matched summand.
* `TauCeti.StrandsAlgebra.oneStrandIdem R M p`, `TauCeti.StrandsAlgebra.oneStrandChord R M h`: the
  idempotent `I({p})` of a matched pair `p` and the single strand of a chord `i < j`, as elements
  of the matched summand with one strand.
* `TauCeti.StrandsAlgebra.matchedSummandAlgEquiv R M`: as an `R`-algebra, the matched subalgebra
  is the product of its summands.

## Main results

* `TauCeti.StrandsAlgebra.mul_eq_zero_of_mem_strandSummand`: products of elements with different
  numbers of strands vanish.
* `TauCeti.StrandsAlgebra.differential_mem_strandSummand`: the differential preserves the number of
  strands.
* `TauCeti.StrandsAlgebra.isInternal_strandSummand`: the strands algebra is the internal direct
  sum of the `A(n, k)`.
* `TauCeti.StrandsAlgebra.iSupIndep_matchedSummand`,
  `TauCeti.StrandsAlgebra.iSup_matchedSummand`: the matched subalgebra is the internal direct sum
  of its summands.
* `TauCeti.StrandsAlgebra.isUngradedDGAlgebra_matchedSummandDifferential`: over a ring of
  characteristic two, each matched summand is an ungraded differential algebra.
* `TauCeti.StrandsAlgebra.matchedSummandDifferential_apply_of_le_one`: the differential vanishes
  on the matched summands with at most one strand.
* `TauCeti.StrandsAlgebra.oneStrandIdem_mul_oneStrandIdem`,
  `TauCeti.StrandsAlgebra.sum_oneStrandIdem`: the idempotents `I({p})` are orthogonal and add up
  to the unit of the matched summand with one strand.
* `TauCeti.StrandsAlgebra.oneStrandIdem_mul_oneStrandChord`,
  `TauCeti.StrandsAlgebra.oneStrandChord_mul_oneStrandIdem`,
  `TauCeti.StrandsAlgebra.oneStrandChord_mul_oneStrandChord`: the products of chords with the
  idempotents and with each other.
* `TauCeti.StrandsAlgebra.matchedSummandAlgEquiv_matchedDifferential`: the decomposition of the
  matched subalgebra into its summands intertwines the differentials.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1,
  Definition 3.2 (the algebras `A(n, k)`), and §3.2 (the summands `A(Z, i)` and the decomposition
  `A(Z) = ⊕ᵢ A(Z, i)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α]

/-! ### The summands of the strands algebra -/

section StrandSummand

variable {k l : ℕ} {x y : StrandsAlgebra R α}

variable (R α) in
/-- The summand `A(n, k)` of the strands algebra: the elements all of whose diagrams have `k`
strands. It is a two-sided ideal (`TauCeti.StrandsAlgebra.mul_mem_strandSummand_left`,
`TauCeti.StrandsAlgebra.mul_mem_strandSummand_right`), and a unital algebra with unit
`TauCeti.StrandsAlgebra.strandSummandOne R α k`, which differs from the unit of the strands
algebra when `R` is nontrivial and `α` is nonempty. -/
def strandSummand (k : ℕ) : NonUnitalSubalgebra R (StrandsAlgebra R α) where
  carrier := {x | ∀ φ, (basis R α).repr x φ ≠ 0 → #φ.source = k}
  add_mem' {x y} hx hy φ h := by
    rw [map_add, Finsupp.add_apply] at h
    by_cases hxφ : (basis R α).repr x φ = 0
    · exact hy φ (by simpa [hxφ] using h)
    · exact hx φ hxφ
  zero_mem' φ h := absurd (by simp) h
  smul_mem' r x hx φ h := hx φ fun hxφ ↦ h (by simp [hxφ])
  mul_mem' {x _} hx _ χ hχ := by
    -- A diagram in a product starts where a diagram of the first factor starts.
    obtain ⟨φ, ψ, hc, rfl, hφ, -⟩ := exists_of_repr_mul_ne_zero hχ
    rw [source_trans_of_target_eq hc.target_eq]
    exact hx φ hφ

/-- An element of the strands algebra lies in `A(n, k)` when every diagram with a nonzero
coefficient has `k` strands. -/
theorem mem_strandSummand :
    x ∈ strandSummand R α k ↔ ∀ φ, (basis R α).repr x φ ≠ 0 → #φ.source = k :=
  Iff.rfl

/-- A strand diagram with `k` strands lies in `A(n, k)`. -/
theorem of_mem_strandSummand {φ : StrandDiagram α} (h : #φ.source = k) :
    (of φ : StrandsAlgebra R α) ∈ strandSummand R α k := by
  intro ψ hψ
  rw [basis_repr_of, Finsupp.single_apply] at hψ
  rwa [← (ite_ne_right_iff.1 hψ).1]

/-- Over a nontrivial ring, a strand diagram lies in `A(n, k)` exactly when it has `k` strands. -/
@[simp]
theorem of_mem_strandSummand_iff [Nontrivial R] {φ : StrandDiagram α} :
    (of φ : StrandsAlgebra R α) ∈ strandSummand R α k ↔ #φ.source = k :=
  ⟨fun h ↦ h φ (by simp), of_mem_strandSummand⟩

/-- The idempotent `I(s)` lies in `A(n, #s)`. -/
theorem idem_mem_strandSummand (s : Finset α) :
    (idem s : StrandsAlgebra R α) ∈ strandSummand R α #s := by
  rw [idem_def]
  exact of_mem_strandSummand (by rw [source_idOn])

/-- `A(n, k)` is a right ideal: multiplying an element with `k` strands on the right keeps it in
`A(n, k)`. -/
theorem mul_mem_strandSummand_left (hx : x ∈ strandSummand R α k) (y : StrandsAlgebra R α) :
    x * y ∈ strandSummand R α k := by
  intro χ hχ
  obtain ⟨φ, ψ, hc, rfl, hφ, -⟩ := exists_of_repr_mul_ne_zero hχ
  rw [source_trans_of_target_eq hc.target_eq]
  exact hx φ hφ

/-- `A(n, k)` is a left ideal: multiplying an element with `k` strands on the left keeps it in
`A(n, k)`, since a composable diagram ends at as many points as the second factor. -/
theorem mul_mem_strandSummand_right (x : StrandsAlgebra R α) (hy : y ∈ strandSummand R α k) :
    x * y ∈ strandSummand R α k := by
  intro χ hχ
  obtain ⟨φ, ψ, hc, rfl, -, hψ⟩ := exists_of_repr_mul_ne_zero hχ
  rw [source_trans_of_target_eq hc.target_eq, ← card_target, hc.target_eq]
  exact hy ψ hψ

/-- **The differential preserves the number of strands.** Resolving a crossing keeps the starting
points of a diagram. -/
theorem differential_mem_strandSummand (hx : x ∈ strandSummand R α k) :
    differential R α x ∈ strandSummand R α k := by
  have := Fintype.ofFinite (StrandDiagram α)
  intro χ hχ
  rw [repr_differential_apply] at hχ
  obtain ⟨φ, -, hφ⟩ := exists_ne_zero_of_sum_ne_zero hχ
  obtain ⟨q, -, hq⟩ := exists_ne_zero_of_sum_ne_zero hφ
  rw [ne_eq, ite_eq_right_iff, not_imp] at hq
  obtain ⟨⟨-, rfl⟩, hq⟩ := hq
  rw [source_resolve]
  exact hx φ hq

variable (R α) in
/-- The unit of `A(n, k)`: the sum of the idempotents `I(S)` over the sets `S` with `k` points. -/
def strandSummandOne (k : ℕ) : StrandsAlgebra R α :=
  ∑ S with #S = k, idem S

theorem strandSummandOne_def (k : ℕ) :
    strandSummandOne R α k = ∑ S with #S = k, idem S :=
  (rfl)

theorem strandSummandOne_mem_strandSummand (k : ℕ) :
    strandSummandOne R α k ∈ strandSummand R α k :=
  sum_mem fun S hS ↦ (mem_filter.1 hS).2 ▸ idem_mem_strandSummand S

/-- The units of the summands are cycles. -/
@[simp]
theorem differential_strandSummandOne (k : ℕ) : differential R α (strandSummandOne R α k) = 0 := by
  simp [strandSummandOne_def]

/-- Left multiplication by the unit of `A(n, k)` keeps the diagrams with `k` strands and kills the
others. -/
@[simp]
theorem strandSummandOne_mul_of (k : ℕ) (φ : StrandDiagram α) :
    strandSummandOne R α k * of φ = if #φ.source = k then of φ else 0 := by
  simp [strandSummandOne_def, sum_mul, idem_mul_of, sum_ite_eq']

/-- Right multiplication by the unit of `A(n, k)` keeps the diagrams with `k` strands and kills
the others. -/
@[simp]
theorem of_mul_strandSummandOne (k : ℕ) (φ : StrandDiagram α) :
    of φ * strandSummandOne R α k = if #φ.source = k then of φ else 0 := by
  simp [strandSummandOne_def, mul_sum, of_mul_idem, sum_ite_eq, card_target]

/-- `TauCeti.StrandsAlgebra.strandSummandOne R α k` is a left identity on `A(n, k)`. -/
theorem strandSummandOne_mul_of_mem (hx : x ∈ strandSummand R α k) :
    strandSummandOne R α k * x = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [mul_sum]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [mul_smul_comm, basis_apply, strandSummandOne_mul_of, ite_eq_left (hx φ hφ)]

/-- `TauCeti.StrandsAlgebra.strandSummandOne R α k` is a right identity on `A(n, k)`. -/
theorem mul_strandSummandOne_of_mem (hx : x ∈ strandSummand R α k) :
    x * strandSummandOne R α k = x := by
  let := Fintype.ofFinite (StrandDiagram α)
  conv_rhs => rw [← (basis R α).sum_repr x]
  conv_lhs => rw [← (basis R α).sum_repr x]
  rw [sum_mul]
  refine sum_congr rfl fun φ _ ↦ ?_
  by_cases hφ : (basis R α).repr x φ = 0
  · simp [hφ]
  · rw [smul_mul_assoc, basis_apply, of_mul_strandSummandOne, ite_eq_left (hx φ hφ)]

/-- An element lies in `A(n, k)` exactly when the unit of `A(n, k)` fixes it. -/
theorem mem_strandSummand_iff_strandSummandOne_mul :
    x ∈ strandSummand R α k ↔ strandSummandOne R α k * x = x :=
  ⟨strandSummandOne_mul_of_mem, fun h ↦
    h ▸ mul_mem_strandSummand_left (strandSummandOne_mem_strandSummand k) x⟩

/-- **Products of elements with different numbers of strands vanish.** -/
theorem mul_eq_zero_of_mem_strandSummand (hx : x ∈ strandSummand R α k)
    (hy : y ∈ strandSummand R α l) (hkl : k ≠ l) : x * y = 0 := by
  have := Fintype.ofFinite (StrandDiagram α)
  refine (basis R α).repr.injective (Finsupp.ext fun χ ↦ ?_)
  by_contra hχ
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hχ
  exact hkl ((mul_mem_strandSummand_left hx y χ hχ).symm.trans
    (mul_mem_strandSummand_right x hy χ hχ))

/-- The units of the summands are orthogonal idempotents. -/
@[simp]
theorem strandSummandOne_mul_strandSummandOne (k l : ℕ) :
    strandSummandOne R α k * strandSummandOne R α l =
      if k = l then strandSummandOne R α k else 0 := by
  split_ifs with h
  · exact h ▸ strandSummandOne_mul_of_mem (strandSummandOne_mem_strandSummand k)
  · exact mul_eq_zero_of_mem_strandSummand (strandSummandOne_mem_strandSummand k)
      (strandSummandOne_mem_strandSummand l) h

/-- The units of the summands add up to the unit of the strands algebra. A set of points of `α`
has at most `Fintype.card α` points, so the summands with more strands vanish. -/
theorem sum_strandSummandOne :
    ∑ k ∈ range (Fintype.card α + 1), strandSummandOne R α k = 1 := by
  rw [← sum_idem]
  simp only [strandSummandOne_def]
  exact sum_fiberwise_of_maps_to (fun S _ ↦ mem_range.2 (Nat.lt_succ_of_le (card_le_univ S))) _

/-- Left multiplication by the unit of `A(n, k)` projects onto `A(n, k)`. -/
theorem strandSummandOne_mul_mem (k : ℕ) (x : StrandsAlgebra R α) :
    strandSummandOne R α k * x ∈ strandSummand R α k :=
  mul_mem_strandSummand_left (strandSummandOne_mem_strandSummand k) x

instance : One (strandSummand R α k) :=
  ⟨⟨strandSummandOne R α k, strandSummandOne_mem_strandSummand k⟩⟩

/-- The unit of `A(n, k)` is `TauCeti.StrandsAlgebra.strandSummandOne R α k`. -/
@[simp]
theorem coe_strandSummand_one :
    ((1 : strandSummand R α k) : StrandsAlgebra R α) = strandSummandOne R α k :=
  (rfl)

/-- `A(n, k)` is a unital algebra, with unit `TauCeti.StrandsAlgebra.strandSummandOne R α k`. -/
instance : Semiring (strandSummand R α k) where
  __ := (strandSummand R α k).toNonUnitalSemiring
  one_mul x := Subtype.ext (strandSummandOne_mul_of_mem x.2)
  mul_one x := Subtype.ext (mul_strandSummandOne_of_mem x.2)

instance {R : Type*} [CommRing R] : Ring (strandSummand R α k) where
  __ := (inferInstance : Semiring (strandSummand R α k))
  __ := (strandSummand R α k).toNonUnitalRing

instance : Algebra R (strandSummand R α k) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- The summands `A(n, k)` are independent. -/
theorem iSupIndep_strandSummand :
    iSupIndep fun k ↦ (strandSummand R α k).toSubmodule := by
  refine iSupIndep_def.2 fun k ↦ Submodule.disjoint_def.2 fun x hx hx' ↦ ?_
  -- Left multiplication by the unit of `A(n, k)` kills the other summands and fixes `x`.
  have hle : (⨆ (l) (_ : l ≠ k), (strandSummand R α l).toSubmodule) ≤
      LinearMap.ker (LinearMap.mulLeft R (strandSummandOne R α k)) :=
    iSup₂_le fun l hl y hy ↦ mul_eq_zero_of_mem_strandSummand
      (strandSummandOne_mem_strandSummand k) hy (Ne.symm hl)
  rw [← strandSummandOne_mul_of_mem hx]
  exact hle hx'

/-- The summands `A(n, k)` span the strands algebra. -/
theorem iSup_strandSummand :
    ⨆ k, (strandSummand R α k).toSubmodule = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [← one_mul x, ← sum_strandSummandOne, sum_mul]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.mem_iSup_of_mem k (strandSummandOne_mul_mem k x)

/-- **The strands algebra is the direct sum of the algebras `A(n, k)`.** -/
theorem isInternal_strandSummand {R : Type*} [CommRing R] :
    DirectSum.IsInternal fun k ↦ (strandSummand R α k).toSubmodule :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top iSupIndep_strandSummand
    iSup_strandSummand

end StrandSummand

/-! ### The summands of the matched subalgebra -/

section MatchedSummand

variable {M : α → β} {k : ℕ} {x : StrandsAlgebra R α}

variable (R M) in
/-- The summand of the matched subalgebra with `k` strands: its elements all of whose diagrams
have `k` strands. For the matching of a pointed matched circle `Z` with `4g` points this is the
summand `A(Z, k - g)` of the algebra `A(Z)` of Lipshitz, Ozsváth and Thurston. -/
def matchedSummand (M : α → β) (k : ℕ) : NonUnitalSubalgebra R (StrandsAlgebra R α) :=
  matchedSubalgebra R M ⊓ strandSummand R α k

theorem mem_matchedSummand :
    x ∈ matchedSummand R M k ↔ x ∈ matchedSubalgebra R M ∧ x ∈ strandSummand R α k :=
  Iff.rfl

theorem matchedSummand_le_matchedSubalgebra (k : ℕ) :
    matchedSummand R M k ≤ matchedSubalgebra R M :=
  inf_le_left

theorem matchedSummand_le_strandSummand (k : ℕ) :
    matchedSummand R M k ≤ strandSummand R α k :=
  inf_le_right

/-- The summands of the matched subalgebra are closed under the differential. -/
theorem differential_mem_matchedSummand (hx : x ∈ matchedSummand R M k) :
    differential R α x ∈ matchedSummand R M k :=
  ⟨differential_mem_matchedSubalgebra hx.1, differential_mem_strandSummand hx.2⟩

variable [DecidableEq β]

/-- The idempotent `I(s)` of a set `s` of pairs has `#s` strands. -/
theorem matchedIdem_mem_strandSummand (M : α → β) (s : Finset β) :
    matchedIdem R M s ∈ strandSummand R α #s := by
  rw [matchedIdem_def]
  exact sum_mem fun S hS ↦ (mem_filter.1 hS).2.2 ▸ idem_mem_strandSummand S

/-- The idempotent `I(s)` of a set `s` of pairs lies in the matched summand with `#s` strands. -/
theorem matchedIdem_mem_matchedSummand (M : α → β) (s : Finset β) :
    matchedIdem R M s ∈ matchedSummand R M #s :=
  ⟨matchedIdem_mem_matchedSubalgebra M s, matchedIdem_mem_strandSummand M s⟩

variable (R M) in
/-- The unit of the matched summand with `k` strands: the sum of the idempotents `I(s)` over the
sets `s` of `k` pairs. -/
def matchedSummandOne (M : α → β) (k : ℕ) : StrandsAlgebra R α :=
  ∑ s ∈ (univ.image M).powerset with #s = k, matchedIdem R M s

theorem matchedSummandOne_def (M : α → β) (k : ℕ) :
    matchedSummandOne R M k = ∑ s ∈ (univ.image M).powerset with #s = k, matchedIdem R M s :=
  (rfl)

theorem matchedSummandOne_mem_matchedSummand (M : α → β) (k : ℕ) :
    matchedSummandOne R M k ∈ matchedSummand R M k := by
  rw [matchedSummandOne_def]
  exact sum_mem fun s hs ↦ (mem_filter.1 hs).2 ▸ matchedIdem_mem_matchedSummand M s

/-- The units of the matched summands are cycles. -/
@[simp]
theorem differential_matchedSummandOne (M : α → β) (k : ℕ) :
    differential R α (matchedSummandOne R M k) = 0 := by
  simp [matchedSummandOne_def]

/-- The units of the matched summands add up to the unit of the matched subalgebra. -/
theorem sum_matchedSummandOne (M : α → β) :
    ∑ k ∈ range (Fintype.card α + 1), matchedSummandOne R M k = matchedOne R M := by
  simp only [matchedSummandOne_def, matchedOne_def]
  refine sum_fiberwise_of_maps_to (fun s hs ↦ mem_range.2 (Nat.lt_succ_of_le ?_)) _
  exact (card_le_card (mem_powerset.1 hs)).trans (card_image_le.trans (card_univ (α := α)).le)

/-- The unit of the matched summand with `k` strands is the part of the unit of the matched
subalgebra with `k` strands. -/
theorem strandSummandOne_mul_matchedOne (M : α → β) (k : ℕ) :
    strandSummandOne R α k * matchedOne R M = matchedSummandOne R M k := by
  rw [matchedOne_def, mul_sum, matchedSummandOne_def, sum_filter]
  refine sum_congr rfl fun s _ ↦ ?_
  split_ifs with h
  · exact strandSummandOne_mul_of_mem (h ▸ matchedIdem_mem_strandSummand M s)
  · exact mul_eq_zero_of_mem_strandSummand (strandSummandOne_mem_strandSummand k)
      (matchedIdem_mem_strandSummand M s) (Ne.symm h)

/-- The unit of the matched summand with `k` strands is the part of the unit of the matched
subalgebra with `k` strands. -/
theorem matchedOne_mul_strandSummandOne (M : α → β) (k : ℕ) :
    matchedOne R M * strandSummandOne R α k = matchedSummandOne R M k := by
  rw [matchedOne_def, sum_mul, matchedSummandOne_def, sum_filter]
  refine sum_congr rfl fun s _ ↦ ?_
  split_ifs with h
  · exact mul_strandSummandOne_of_mem (h ▸ matchedIdem_mem_strandSummand M s)
  · exact mul_eq_zero_of_mem_strandSummand (matchedIdem_mem_strandSummand M s)
      (strandSummandOne_mem_strandSummand k) h

/-- `TauCeti.StrandsAlgebra.matchedSummandOne R M k` is a left identity on the matched summand with
`k` strands. -/
theorem matchedSummandOne_mul_of_mem (hx : x ∈ matchedSummand R M k) :
    matchedSummandOne R M k * x = x := by
  rw [← strandSummandOne_mul_matchedOne, mul_assoc, matchedOne_mul_of_mem_matchedSubalgebra hx.1,
    strandSummandOne_mul_of_mem hx.2]

/-- `TauCeti.StrandsAlgebra.matchedSummandOne R M k` is a right identity on the matched summand
with `k` strands. -/
theorem mul_matchedSummandOne_of_mem (hx : x ∈ matchedSummand R M k) :
    x * matchedSummandOne R M k = x := by
  rw [← matchedOne_mul_strandSummandOne, ← mul_assoc,
    mul_matchedOne_of_mem_matchedSubalgebra hx.1, mul_strandSummandOne_of_mem hx.2]

/-- Left multiplication by the unit of the matched summand with `k` strands projects the matched
subalgebra onto that summand. -/
theorem matchedSummandOne_mul_mem (hx : x ∈ matchedSubalgebra R M) :
    matchedSummandOne R M k * x ∈ matchedSummand R M k :=
  ⟨mul_mem (matchedSummandOne_mem_matchedSummand M k).1 hx,
    mul_mem_strandSummand_left (matchedSummandOne_mem_matchedSummand M k).2 x⟩

instance : One (matchedSummand R M k) :=
  ⟨⟨matchedSummandOne R M k, matchedSummandOne_mem_matchedSummand M k⟩⟩

/-- The unit of the matched summand with `k` strands is
`TauCeti.StrandsAlgebra.matchedSummandOne R M k`. -/
@[simp]
theorem coe_matchedSummand_one :
    ((1 : matchedSummand R M k) : StrandsAlgebra R α) = matchedSummandOne R M k :=
  (rfl)

/-- The matched summand with `k` strands is a unital algebra, with unit
`TauCeti.StrandsAlgebra.matchedSummandOne R M k`. -/
instance : Semiring (matchedSummand R M k) where
  __ := (matchedSummand R M k).toNonUnitalSemiring
  one_mul x := Subtype.ext (matchedSummandOne_mul_of_mem x.2)
  mul_one x := Subtype.ext (mul_matchedSummandOne_of_mem x.2)

instance {R : Type*} [CommRing R] : Ring (matchedSummand R M k) where
  __ := (inferInstance : Semiring (matchedSummand R M k))
  __ := (matchedSummand R M k).toNonUnitalRing

instance : Algebra R (matchedSummand R M k) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

end MatchedSummand

section MatchedDecomposition

variable {M : α → β}

variable (R M) in
/-- The summands of the matched subalgebra are independent. -/
theorem iSupIndep_matchedSummand :
    iSupIndep fun k ↦ (matchedSummand R M k).toSubmodule :=
  iSupIndep_strandSummand.mono fun k ↦ matchedSummand_le_strandSummand (M := M) k

variable (R M) in
/-- The summands of the matched subalgebra span it. -/
theorem iSup_matchedSummand :
    ⨆ k, (matchedSummand R M k).toSubmodule = (matchedSubalgebra R M).toSubmodule := by
  classical
  refine le_antisymm (iSup_le fun k ↦ matchedSummand_le_matchedSubalgebra k) fun x hx ↦ ?_
  rw [← matchedOne_mul_of_mem_matchedSubalgebra hx, ← sum_matchedSummandOne, sum_mul]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.mem_iSup_of_mem k (matchedSummandOne_mul_mem hx)

end MatchedDecomposition

/-! ### The differential of a matched summand -/

section Differential

variable {M : α → β}

variable (R M) in
/-- The differential of the strands algebra restricted to the matched summand with `k`
strands. -/
def matchedSummandDifferential (M : α → β) (k : ℕ) :
    matchedSummand R M k →ₗ[R] matchedSummand R M k :=
  (differential R α).restrict (p := (matchedSummand R M k).toSubmodule)
    (q := (matchedSummand R M k).toSubmodule) fun _ hx ↦ differential_mem_matchedSummand hx

@[simp]
theorem coe_matchedSummandDifferential {k : ℕ} (x : matchedSummand R M k) :
    (matchedSummandDifferential R M k x : StrandsAlgebra R α) = differential R α x :=
  (rfl)

variable [DecidableEq β] in
/-- The unit of a matched summand is a cycle. -/
@[simp]
theorem matchedSummandDifferential_one (k : ℕ) : matchedSummandDifferential R M k 1 = 0 :=
  Subtype.ext (by simp)

/-- Over a ring of characteristic two, such as `𝔽₂`, each summand of the matched subalgebra with
the restricted differential is an ungraded differential algebra. -/
theorem isUngradedDGAlgebra_matchedSummandDifferential [DecidableEq β] {R : Type*} [CommRing R]
    [CharP R 2] (k : ℕ) :
    IsUngradedDGAlgebra (matchedSummandDifferential R M k) where
  map_mul a b := Subtype.ext (by simp [differential_mul])
  map_map a := Subtype.ext (by simp [differential_differential])

/-- The differential vanishes on the matched summands with at most one strand, whose diagrams have
no crossing to resolve. -/
@[simp]
theorem matchedSummandDifferential_apply_of_le_one {k : ℕ} (hk : k ≤ 1)
    (x : matchedSummand R M k) : matchedSummandDifferential R M k x = 0 :=
  Subtype.ext <| differential_eq_zero_of_mem_strandCountPart hk <|
    mem_strandCountPart.2 fun φ hφ ↦ x.2.2 φ (Finsupp.mem_support_iff.1 hφ)

end Differential

/-! ### The idempotents and chords of the matched summand with one strand -/

section OneStrand

variable (M : α → β)

variable (R) in
/-- The chord from `i` to `j`, a single strand from `i` to `j` for `i < j`, as an element of the
matched summand with one strand. -/
def oneStrandChord {i j : α} (h : i < j) : matchedSummand R M 1 :=
  ⟨of (single i j h.le), mem_matchedSummand.2
    ⟨by classical simpa using oneStrandFamily_mem_matchedSubalgebra (R := R) M (.inr ⟨(i, j), h⟩),
      of_mem_strandSummand (by rw [source_single, card_singleton])⟩⟩

@[simp]
theorem coe_oneStrandChord {i j : α} (h : i < j) :
    (oneStrandChord R M h : StrandsAlgebra R α) = of (single i j h.le) :=
  (rfl)

/-- Two chords multiply to their concatenation when the first ends where the second starts. -/
@[simp]
theorem oneStrandChord_mul_oneStrandChord {i j k : α} (hij : i < j) (hjk : j < k) :
    oneStrandChord R M hij * oneStrandChord R M hjk = oneStrandChord R M (hij.trans hjk) :=
  Subtype.ext (of_single_mul_of_single _ _)

/-- Two chords multiply to zero when the first ends where the second does not start. -/
theorem oneStrandChord_mul_oneStrandChord_of_ne {i j j' k : α} (hij : i < j) (hjk : j' < k)
    (hj : j ≠ j') : oneStrandChord R M hij * oneStrandChord R M hjk = 0 :=
  Subtype.ext (of_single_mul_of_single_of_ne _ _ hj)

/-- Over a nontrivial ring the chords are nonzero. -/
@[simp]
theorem oneStrandChord_ne_zero [Nontrivial R] {i j : α} (h : i < j) : oneStrandChord R M h ≠ 0 :=
  fun h' ↦ by
    classical
    exact (linearIndependent_oneStrandFamily (R := R) M).ne_zero (.inr ⟨(i, j), h⟩)
      (by simpa using congrArg Subtype.val h')

variable [DecidableEq β]

variable (R) in
/-- The idempotent `I({p})` of a matched pair `p` of `M`, as an element of the matched summand with
one strand. For a pair `p = {a, b}` it is `I({a}) + I({b})`. -/
def oneStrandIdem (p : Set.range M) : matchedSummand R M 1 :=
  ⟨matchedIdem R M {p.1}, by simpa using matchedIdem_mem_matchedSummand (R := R) M {p.1}⟩

@[simp]
theorem coe_oneStrandIdem (p : Set.range M) :
    (oneStrandIdem R M p : StrandsAlgebra R α) = matchedIdem R M {p.1} :=
  (rfl)

/-- The idempotents `I({p})` are orthogonal: `I({p}) I({q})` is `I({p})` when `p = q` and zero
otherwise. -/
@[simp]
theorem oneStrandIdem_mul_oneStrandIdem (p q : Set.range M) :
    oneStrandIdem R M p * oneStrandIdem R M q = if p = q then oneStrandIdem R M p else 0 := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, coe_oneStrandIdem, coe_oneStrandIdem, matchedIdem_mul_matchedIdem,
    apply_ite Subtype.val, coe_oneStrandIdem, ZeroMemClass.coe_zero]
  exact if_congr (by rw [singleton_inj, Subtype.ext_iff]) rfl rfl

theorem isIdempotentElem_oneStrandIdem (p : Set.range M) :
    IsIdempotentElem (oneStrandIdem R M p) :=
  (oneStrandIdem_mul_oneStrandIdem M p p).trans (ite_eq_left rfl)

/-- The idempotents `I({p})` of the matched pairs add up to the unit of the matched summand with one
strand. -/
theorem sum_oneStrandIdem : ∑ p, oneStrandIdem R M p = 1 := by
  refine Subtype.ext ?_
  rw [coe_matchedSummand_one, matchedSummandOne_def, ← powersetCard_eq_filter, powersetCard_one,
    sum_map, AddSubmonoidClass.coe_finsetSum]
  exact (sum_subtype _ (by simp) fun b ↦ matchedIdem R M {b}).symm

/-- Over a nontrivial ring the idempotents `I({p})` are nonzero. -/
@[simp]
theorem oneStrandIdem_ne_zero [Nontrivial R] (p : Set.range M) : oneStrandIdem R M p ≠ 0 :=
  fun h ↦ (linearIndependent_oneStrandFamily (R := R) M).ne_zero (.inl p)
    (by simpa using congrArg Subtype.val h)

/-- A chord from `i` starts at the idempotent of the pair of `i`: `I({p})` times the chord is the
chord when `p` is the pair of `i`, and zero otherwise. -/
@[simp]
theorem oneStrandIdem_mul_oneStrandChord (p : Set.range M) {i j : α} (h : i < j) :
    oneStrandIdem R M p * oneStrandChord R M h = if p.1 = M i then oneStrandChord R M h else 0 := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, apply_ite Subtype.val, ZeroMemClass.coe_zero, coe_oneStrandIdem,
    coe_oneStrandChord, ← horizontalCompletion_empty (M := M),
    matchedIdem_mul_horizontalCompletion _ (isMatchedGenerator_single_empty M h)]
  refine if_congr ?_ rfl rfl
  rw [source_single, image_singleton, union_empty, singleton_inj]

/-- A chord to `j` ends at the idempotent of the pair of `j`: the chord times `I({p})` is the chord
when `p` is the pair of `j`, and zero otherwise. -/
@[simp]
theorem oneStrandChord_mul_oneStrandIdem (p : Set.range M) {i j : α} (h : i < j) :
    oneStrandChord R M h * oneStrandIdem R M p = if p.1 = M j then oneStrandChord R M h else 0 := by
  refine Subtype.ext ?_
  rw [MulMemClass.coe_mul, apply_ite Subtype.val, ZeroMemClass.coe_zero, coe_oneStrandIdem,
    coe_oneStrandChord, ← horizontalCompletion_empty (M := M),
    horizontalCompletion_mul_matchedIdem (isMatchedGenerator_single_empty M h)]
  refine if_congr ?_ rfl rfl
  rw [target_single, image_singleton, union_empty, singleton_inj, eq_comm]

end OneStrand

/-! ### The occupancy decomposition of the matched subalgebra -/

section AlgEquiv

variable {M : α → β} [DecidableEq β]

/-- Left multiplication by an element with `k` strands sees only the summand with `k` strands of
a family of elements, one with each number of strands. -/
theorem mul_sum_eq_mul_of_mem_strandSummand {k : Fin (Fintype.card α + 1)}
    {a : StrandsAlgebra R α} (ha : a ∈ strandSummand R α k)
    {y : Fin (Fintype.card α + 1) → StrandsAlgebra R α}
    (hy : ∀ j : Fin (Fintype.card α + 1), y j ∈ strandSummand R α j) :
    a * ∑ j, y j = a * y k := by
  rw [mul_sum]
  exact sum_eq_single k (fun j _ hj ↦ mul_eq_zero_of_mem_strandSummand ha (hy j)
    (Fin.val_injective.ne hj.symm)) (by simp)

/-- An element of the matched subalgebra is the sum of its parts with each number of strands. -/
theorem sum_matchedSummandOne_mul {x : StrandsAlgebra R α} (hx : x ∈ matchedSubalgebra R M) :
    ∑ k : Fin (Fintype.card α + 1), matchedSummandOne R M k * x = x := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ matchedSummandOne R M k * x), ← sum_mul,
    sum_matchedSummandOne, matchedOne_mul_of_mem_matchedSubalgebra hx]

variable (R M) in
/-- **The occupancy decomposition of the matched subalgebra.** As an `R`-algebra, the matched
subalgebra is the product of its summands with `k ≤ Fintype.card α` strands; the component with `k`
strands of `x` is `TauCeti.StrandsAlgebra.matchedSummandOne R M k * x`. For the matching of a
pointed matched circle `Z` this is the decomposition `A(Z) = ⊕ᵢ A(Z, i)` of Lipshitz, Ozsváth and
Thurston as a product of algebras. Its compatibility with the differential is
`TauCeti.StrandsAlgebra.matchedSummandAlgEquiv_matchedDifferential`. -/
def matchedSummandAlgEquiv :
    matchedSubalgebra R M ≃ₐ[R] Π k : Fin (Fintype.card α + 1), matchedSummand R M k where
  toFun x k := ⟨matchedSummandOne R M k * x, matchedSummandOne_mul_mem x.2⟩
  invFun y := ⟨∑ k, (y k : StrandsAlgebra R α),
    sum_mem fun k _ ↦ matchedSummand_le_matchedSubalgebra (k : ℕ) (y k).2⟩
  left_inv x := Subtype.ext (sum_matchedSummandOne_mul x.2)
  right_inv y := funext fun k ↦ Subtype.ext <| by
    -- `dsimp only` projects the values out of the anonymous constructors above.
    dsimp only
    rw [mul_sum_eq_mul_of_mem_strandSummand (matchedSummandOne_mem_matchedSummand M k).2
      fun j ↦ (y j).2.2, matchedSummandOne_mul_of_mem (y k).2]
  map_mul' x y := funext fun k ↦ Subtype.ext <| by
    -- Only the part of `y` with `k` strands contributes to `(e_k x) y`.
    dsimp only
    rw [Pi.mul_apply, MulMemClass.coe_mul, MulMemClass.coe_mul]
    have h := mul_sum_eq_mul_of_mem_strandSummand (matchedSummandOne_mul_mem (k := k) x.2).2
      (y := fun j ↦ matchedSummandOne R M j * y) fun j ↦ (matchedSummandOne_mul_mem y.2).2
    rw [sum_matchedSummandOne_mul y.2] at h
    rw [← mul_assoc, h]
  map_add' x y := funext fun k ↦ Subtype.ext (mul_add _ _ _)
  commutes' r := funext fun k ↦ Subtype.ext <| by
    simp [Algebra.algebraMap_eq_smul_one,
      mul_matchedOne_of_mem_matchedSubalgebra (matchedSummandOne_mem_matchedSummand M k).1]

/-- The component of `x` with `k` strands is `matchedSummandOne R M k * x`. -/
@[simp]
theorem coe_matchedSummandAlgEquiv_apply (x : matchedSubalgebra R M)
    (k : Fin (Fintype.card α + 1)) :
    (matchedSummandAlgEquiv R M x k : StrandsAlgebra R α) = matchedSummandOne R M k * x :=
  (rfl)

/-- An element of the matched subalgebra is the sum of its components. -/
@[simp]
theorem coe_matchedSummandAlgEquiv_symm_apply
    (y : Π k : Fin (Fintype.card α + 1), matchedSummand R M k) :
    ((matchedSummandAlgEquiv R M).symm y : StrandsAlgebra R α) = ∑ k, (y k : StrandsAlgebra R α) :=
  (rfl)

/-- The occupancy decomposition intertwines the differential of the matched subalgebra with the
differentials of its summands. -/
theorem matchedSummandAlgEquiv_matchedDifferential (x : matchedSubalgebra R M)
    (k : Fin (Fintype.card α + 1)) :
    matchedSummandAlgEquiv R M (matchedDifferential R M x) k =
      matchedSummandDifferential R M k (matchedSummandAlgEquiv R M x k) := by
  refine Subtype.ext ?_
  rw [coe_matchedSummandAlgEquiv_apply, coe_matchedSummandDifferential,
    coe_matchedSummandAlgEquiv_apply, coe_matchedDifferential]
  -- The differential of `x` is the sum of the differentials of its parts, and each of these keeps
  -- its number of strands.
  conv_lhs => rw [← sum_matchedSummandOne_mul x.2, map_sum]
  rw [mul_sum_eq_mul_of_mem_strandSummand (matchedSummandOne_mem_matchedSummand M k).2
      (y := fun j ↦ differential R α (matchedSummandOne R M j * x))
      fun j ↦ (differential_mem_matchedSummand (matchedSummandOne_mul_mem x.2)).2,
    matchedSummandOne_mul_of_mem
      (differential_mem_matchedSummand (matchedSummandOne_mul_mem x.2))]

end AlgEquiv

end StrandsAlgebra

end TauCeti
