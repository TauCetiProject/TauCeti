/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Grading
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Resolution

/-!
# The refined grading group `G(Z)` of a matched circle

The strands algebra on the `4k` points of a pointed matched circle `Z` is graded by the group
`G'(4k)` (`TauCeti.StrandGradingGroup.gPrime`), a central extension of the relative homology group
`H₁(Z', a)` by the Maslov component. Lipshitz, Ozsváth and Thurston refine this grading on the
algebra `A(Z)` to one with values in a smaller group `G(Z)`, which has a direct topological
meaning: it is a central extension of `H₁(F(Z)) ≅ ℤ ^ (2k)` by `ℤ`, the homology of the closed
surface `F(Z)` parametrized by `Z`, and its commutators are even powers of `λ`. The refined
grading is the one used to grade bordered modules and their box tensor products.

A class `β ∈ H₁(Z', a)` closes up to a cycle of `F(Z)`, by adding multiples of the cores of the
one-handles attached along the matched pairs, exactly when its boundary pushes forward to zero
under the matching `M`: the multiplicities of `∂β` at the two points of each pair cancel. So
`H₁(F(Z))` is identified with the classes satisfying this condition, and `G(Z)` is the subgroup of
`G'(4k)` of the elements whose class satisfies it. As in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched`, the matching is an arbitrary map
`M : α → β` whose fibres are the matched sets (`TauCeti.StrandGradingGroup.matchedSubgroup M`).

* **The central extension.** The elements of `G(Z)` with zero class are exactly the powers of `λ`
  (`TauCeti.StrandGradingGroup.mem_zpowers_lambda_iff_mem_matchedSubgroup`), and every class whose
  boundary cancels on the matched sets is the class of an element of `G(Z)`
  (`TauCeti.StrandGradingGroup.mk_mem_matchedSubgroup`), so
  `ℤ → G(Z) → ker (M_* ∘ ∂)` is exact, with `1 ↦ λ`.
* **Commutators.** When every matched set has at most two points, the form `L` takes integral
  values on the classes of `G(Z)` (`TauCeti.StrandGradingGroup.exists_linking_eq_intCast`), and
  `g h = h g λ^(2 L([g], [h]))`
  (`TauCeti.StrandGradingGroup.exists_mul_eq_mul_mul_lambda_zpow`). This is the relation
  `g h = h g λ^(2 [g] ∩ [h])` of Lipshitz, Ozsváth and Thurston, where `L` restricted to these
  classes is the intersection pairing of `F(Z)`; that identification is topological and is not
  formalized here.
* **The refined grading.** Grading refinement data consist of a base set of pairs `s₀` and, for
  each set of pairs `s` of the same size, an element `ψ(s)` of `G'(4k)` whose class has boundary
  pushing forward to `s - s₀`. The refined grading of a strand diagram `φ : S → T` is
  `ψ(M S) gr(φ) ψ(M T)⁻¹` (`TauCeti.StrandDiagram.refinedGrading`). For a diagram with no two
  matched starting points and no two matched end points it lies in `G(Z)`
  (`TauCeti.StrandDiagram.refinedGrading_mem_matchedSubgroup`); it is multiplicative on composable
  diagrams (`TauCeti.StrandDiagram.refinedGrading_trans`) and resolving a crossing multiplies it by
  `λ⁻¹` (`TauCeti.StrandDiagram.refinedGrading_resolve`). Other refinement data conjugate it by an
  idempotent-dependent element (`TauCeti.StrandDiagram.refinedGrading_eq_mul_mul_inv`).

## Main definitions

* `TauCeti.StrandGradingGroup.matchedSubgroup M`: the refined grading group `G(Z)`.
* `TauCeti.StrandDiagram.refinedGrading M ψ φ`: the refined grading of a strand diagram.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.3.2
  (the group `G(Z)`, Lemma 3.43, the grading refinement data and Lemma 3.45, Remark 3.46).
-/

public section

open Finset

namespace TauCeti

namespace StrandGradingGroup

variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq β] {M : α → β}

omit [LinearOrder α] in
/-- If the sums of `δ` over the fibres of `M` vanish, so does its total sum. -/
private theorem sum_eq_zero_of_forall_sum_filter_eq_zero {δ : α → ℤ}
    (hδ : ∀ b, ∑ p ∈ ({p | M p = b} : Finset α), δ p = 0) : ∑ p, δ p = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := M) (t := Finset.univ.image M)
    fun p _ ↦ Finset.mem_image_of_mem M (Finset.mem_univ p)]
  exact Finset.sum_eq_zero fun b _ ↦ hδ b

variable (M) in
/-- **The refined grading group** `G(Z)` of Lipshitz, Ozsváth and Thurston, for a matching
`M : α → β` whose fibres are the matched sets: the subgroup of `G'(n)` of the elements whose class
`β` has boundary pushing forward to zero under `M`, that is, the multiplicities of `∂β` on each
matched set add up to zero. For a pointed matched circle these classes are those that close up to
cycles of the surface `F(Z)`. -/
def matchedSubgroup : Subgroup (StrandGradingGroup α) where
  carrier := {g | g ∈ gPrime ∧ ∀ b, ∑ p ∈ ({p | M p = b} : Finset α), g.boundary p = 0}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    exact ⟨mul_mem hg hh, fun b ↦ by simp [Finset.sum_add_distrib, hg' b, hh' b]⟩
  one_mem' := ⟨one_mem _, fun b ↦ by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨inv_mem hg, fun b ↦ by simp [hg' b]⟩

theorem mem_matchedSubgroup {g : StrandGradingGroup α} :
    g ∈ matchedSubgroup M ↔
      g ∈ gPrime ∧ ∀ b, ∑ p ∈ ({p | M p = b} : Finset α), g.boundary p = 0 :=
  Iff.rfl

theorem matchedSubgroup_le_gPrime : matchedSubgroup M ≤ gPrime :=
  fun _ hg ↦ hg.1

theorem lambda_mem_matchedSubgroup : (lambda : StrandGradingGroup α) ∈ matchedSubgroup M :=
  ⟨lambda_mem_gPrime, fun b ↦ by simp⟩

/-- **The kernel of `G(Z) → H₁(F(Z))`.** The elements of `G(Z)` with zero class are exactly the
powers of `λ`. -/
theorem mem_zpowers_lambda_iff_mem_matchedSubgroup {g : StrandGradingGroup α} :
    g ∈ Subgroup.zpowers lambda ↔ g ∈ matchedSubgroup M ∧ g.boundary = 0 := by
  rw [mem_zpowers_lambda_iff]
  exact ⟨fun h ↦ ⟨⟨h.1, fun b ↦ by simp [h.2]⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩

/-- **The image of `G(Z) → H₁(F(Z))`.** Every class whose boundary cancels on each matched set is
the class of an element of `G(Z)`, with Maslov component `ε(β)`. -/
theorem mk_mem_matchedSubgroup {δ : α → ℤ}
    (hδ : ∀ b, ∑ p ∈ ({p | M p = b} : Finset α), δ p = 0) :
    mk (#(parityChanges δ) / 4) δ ∈ matchedSubgroup M :=
  ⟨mk_mem_gPrime (sum_eq_zero_of_forall_sum_filter_eq_zero hδ), by simpa using hδ⟩

omit [LinearOrder α] [Fintype α] in
/-- On a set over which `δ` sums to zero, `δ` is odd at an even number of points. -/
private theorem even_card_filter_odd {s : Finset α} {δ : α → ℤ} (hδ : ∑ p ∈ s, δ p = 0) :
    Even #{p ∈ s | Odd (δ p)} := by
  obtain ⟨k, hk⟩ := exists_sum_eq_card_parityChanges_add (fun p : s ↦ δ p)
  rw [Finset.sum_coe_sort s δ, hδ] at hk
  have hcard : #(parityChanges fun p : s ↦ δ p) = #{p ∈ s | Odd (δ p)} := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext p
    simp [mem_parityChanges, and_comm]
  rw [hcard] at hk
  exact (Int.even_natCast _).1 ⟨-k, by omega⟩

omit [LinearOrder α] [Fintype α] in
/-- On a set of at most two points over which `δ` sums to zero, `δ` is odd at no point or at
every point. -/
private theorem card_filter_odd_eq_zero_or_eq {s : Finset α} {δ : α → ℤ} (hs : #s ≤ 2)
    (hδ : ∑ p ∈ s, δ p = 0) : #{p ∈ s | Odd (δ p)} = 0 ∨ {p ∈ s | Odd (δ p)} = s := by
  obtain ⟨m, hm⟩ := even_card_filter_odd hδ
  have hle := Finset.card_filter_le s fun p ↦ Odd (δ p)
  rcases Nat.lt_or_ge m 1 with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega))

/-- **The form `L` is integral on `G(Z)`.** If every matched set has at most two points and the
boundaries `δ₁`, `δ₂` cancel on each of them, then `L(δ₁, δ₂)` is an integer. -/
theorem exists_linking_eq_intCast (hM : ∀ b, #({p | M p = b} : Finset α) ≤ 2) {δ₁ δ₂ : α → ℤ}
    (hδ₁ : ∀ b, ∑ p ∈ ({p | M p = b} : Finset α), δ₁ p = 0)
    (hδ₂ : ∀ b, ∑ p ∈ ({p | M p = b} : Finset α), δ₂ p = 0) :
    ∃ k : ℤ, linking δ₁ δ₂ = k := by
  obtain ⟨k, hk⟩ := exists_linking_eq_card_inter_parityChanges_add δ₁ δ₂
  -- The common parity changes form a union of matched sets of two points each.
  have heven : Even #(parityChanges δ₁ ∩ parityChanges δ₂) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := M) (t := Finset.univ.image M)
      fun p _ ↦ Finset.mem_image_of_mem M (Finset.mem_univ p)]
    refine Finset.even_sum _ fun b _ ↦ ?_
    have hfib : ({p ∈ parityChanges δ₁ ∩ parityChanges δ₂ | M p = b} : Finset α) =
        {p ∈ ({p ∈ ({p | M p = b} : Finset α) | Odd (δ₁ p)}) | Odd (δ₂ p)} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, mem_parityChanges, Finset.mem_univ,
        true_and]
      tauto
    rw [hfib]
    rcases card_filter_odd_eq_zero_or_eq (hM b) (hδ₁ b) with h | h
    · rw [Finset.card_eq_zero.1 h]
      simp
    · rw [h]
      exact even_card_filter_odd (hδ₂ b)
  obtain ⟨m, hm⟩ := heven
  refine ⟨m + k, ?_⟩
  rw [hk, hm]
  push_cast
  ring

/-- **Commutators in `G(Z)`** (Lipshitz, Ozsváth and Thurston, equation (3.42)). If every matched
set has at most two points, two elements of `G(Z)` commute up to an even power of `λ`:
`g h = h g λ^(2 L([g], [h]))`, with `L([g], [h])` an integer. -/
theorem exists_mul_eq_mul_mul_lambda_zpow (hM : ∀ b, #({p | M p = b} : Finset α) ≤ 2)
    {g h : StrandGradingGroup α} (hg : g ∈ matchedSubgroup M) (hh : h ∈ matchedSubgroup M) :
    ∃ k : ℤ, linking g.boundary h.boundary = k ∧ g * h = h * g * lambda ^ (2 * k) := by
  obtain ⟨k, hk⟩ := exists_linking_eq_intCast hM hg.2 hh.2
  refine ⟨k, hk, ?_⟩
  have hswap := linking_add_linking_swap g.boundary h.boundary
  have hsum : ∑ p, (g.boundary p : ℚ) = 0 := by exact_mod_cast (mem_gPrime.1 hg.1).2
  rw [hsum, zero_mul, neg_zero] at hswap
  rw [mul_lambda_zpow]
  ext
  · simp only [mul_maslov, mk_maslov]
    push_cast
    linear_combination -hswap + 2 * hk
  · simp [add_comm]

end StrandGradingGroup

namespace StrandDiagram

open StrandGradingGroup

variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq β] {M : α → β}

variable (M) in
/-- The refined grading `ψ(M S) gr(φ) ψ(M T)⁻¹` of a strand diagram `φ : S → T`, for grading
refinement data `ψ` assigning an element of the grading group to each set of matched pairs. -/
def refinedGrading (ψ : Finset β → StrandGradingGroup α) (φ : StrandDiagram α) :
    StrandGradingGroup α :=
  ψ (φ.source.image M) * φ.grading * (ψ (φ.target.image M))⁻¹

theorem refinedGrading_def (ψ : Finset β → StrandGradingGroup α) (φ : StrandDiagram α) :
    refinedGrading M ψ φ = ψ (φ.source.image M) * φ.grading * (ψ (φ.target.image M))⁻¹ :=
  (rfl)

/-- The identity diagrams have refined grading `1`. -/
@[simp]
theorem refinedGrading_idOn (ψ : Finset β → StrandGradingGroup α) (s : Finset α) :
    refinedGrading M ψ (idOn s) = 1 := by
  simp [refinedGrading_def]

/-- The refined grading is multiplicative on composable diagrams. -/
theorem refinedGrading_trans (ψ : Finset β → StrandGradingGroup α) {φ φ' : StrandDiagram α}
    (h : φ.Composable φ') :
    refinedGrading M ψ (φ.trans φ') = refinedGrading M ψ φ * refinedGrading M ψ φ' := by
  simp only [refinedGrading_def, grading_trans h, source_trans_of_target_eq h.target_eq,
    target_trans_of_target_eq h.target_eq, h.target_eq]
  group

/-- Resolving a crossing multiplies the refined grading by `λ⁻¹`. -/
theorem refinedGrading_resolve (ψ : Finset β → StrandGradingGroup α) {φ : StrandDiagram α}
    {p : α × α} (h : p ∈ φ.resolvableInversions) :
    refinedGrading M ψ (φ.resolve p) = lambda⁻¹ * refinedGrading M ψ φ := by
  have hc := Subgroup.inv_mem _ (lambda_mem_center (α := α))
  simp only [refinedGrading_def, grading_resolve h, source_resolve, target_resolve,
    ← mul_assoc, Subgroup.mem_center_iff.1 hc]

/-- **Changing the grading refinement data** conjugates the refined grading in an
idempotent-dependent way (Lipshitz, Ozsváth and Thurston, Remark 3.46). -/
theorem refinedGrading_eq_mul_mul_inv (ψ ψ' : Finset β → StrandGradingGroup α)
    (φ : StrandDiagram α) :
    refinedGrading M ψ' φ = ψ' (φ.source.image M) * (ψ (φ.source.image M))⁻¹ *
      refinedGrading M ψ φ * (ψ' (φ.target.image M) * (ψ (φ.target.image M))⁻¹)⁻¹ := by
  simp only [refinedGrading_def]
  group

omit [LinearOrder α] [Fintype α] in
/-- Points of a set on which `M` is injective, matched to `b`: one if `b` is the image of a point
of the set, none otherwise. -/
private theorem card_filter_eq_ite_mem_image {s : Finset α} (hs : Set.InjOn M s) (b : β) :
    #{p ∈ s | M p = b} = if b ∈ s.image M then 1 else 0 := by
  split_ifs with hb
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
    exact Finset.card_eq_one.2 ⟨p, Finset.eq_singleton_iff_unique_mem.2
      ⟨by simp [hp], fun q hq ↦ hs (Finset.mem_filter.1 hq).1 hp (Finset.mem_filter.1 hq).2⟩⟩
  · exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun p hp hpb ↦
      hb (Finset.mem_image.2 ⟨p, hp, hpb⟩))

/-- If `M` is injective on the starting points and on the end points of `φ : S → T`, the boundary
of the class of `φ` pushes forward to the difference `M T - M S` of sets of pairs. -/
theorem sum_boundary_filter_eq {φ : StrandDiagram α} (hS : Set.InjOn M φ.source)
    (hT : Set.InjOn M φ.target) (b : β) :
    ∑ p ∈ ({p | M p = b} : Finset α), φ.boundary p =
      (if b ∈ φ.target.image M then 1 else 0) - if b ∈ φ.source.image M then 1 else 0 := by
  simp only [boundary_apply, Finset.sum_sub_distrib, Finset.sum_boole, Finset.filter_filter]
  have e (s : Finset α) : ({p | M p = b ∧ p ∈ s} : Finset α) = {p ∈ s | M p = b} := by
    ext
    simp [and_comm]
  rw [e, e, card_filter_eq_ite_mem_image hT, card_filter_eq_ite_mem_image hS]
  push_cast
  rfl

/-- **The refined grading takes values in `G(Z)`** (Lipshitz, Ozsváth and Thurston, Lemma 3.45).
Let `ψ` be grading refinement data with base set of pairs `s₀`: for each set of pairs `s` with as
many pairs as `s₀`, `ψ(s)` lies in `G'(n)` and its class has boundary pushing forward to `s - s₀`.
Then a diagram with no two matched starting points and no two matched end points, starting on
`#s₀` pairs, has refined grading in `G(Z)`. -/
theorem refinedGrading_mem_matchedSubgroup {s₀ : Finset β} {ψ : Finset β → StrandGradingGroup α}
    (hψ : ∀ s : Finset β, #s = #s₀ → ψ s ∈ gPrime ∧ ∀ b, ∑ p ∈ ({p | M p = b} : Finset α),
      (ψ s).boundary p = (if b ∈ s then 1 else 0) - if b ∈ s₀ then 1 else 0)
    {φ : StrandDiagram α} (hS : Set.InjOn M φ.source) (hT : Set.InjOn M φ.target)
    (hcard : #(φ.source.image M) = #s₀) :
    refinedGrading M ψ φ ∈ matchedSubgroup M := by
  have hcard' : #(φ.target.image M) = #s₀ := by
    rw [Finset.card_image_of_injOn hT, card_target, ← Finset.card_image_of_injOn hS, hcard]
  obtain ⟨hψS, hψS'⟩ := hψ _ hcard
  obtain ⟨hψT, hψT'⟩ := hψ _ hcard'
  refine ⟨mul_mem (mul_mem hψS (grading_mem_gPrime φ)) (inv_mem hψT), fun b ↦ ?_⟩
  simp only [refinedGrading_def, mul_boundary, inv_boundary, grading_boundary, Pi.add_apply,
    Pi.neg_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib, hψS' b, hψT' b,
    sum_boundary_filter_eq hS hT b]
  ring

end StrandDiagram

end TauCeti
