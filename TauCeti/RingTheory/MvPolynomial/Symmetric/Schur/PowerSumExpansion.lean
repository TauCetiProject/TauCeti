/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayama

/-!
# The power-sum products in the Schur basis, by iterated rim-hook removal

Multiplying a Schur polynomial by a power sum adds a rim hook:
`TauCeti.psum_mul_schurPoly` reads

`p_r · s_ν = ∑_μ (-1) ^ ht(μ / ν) · s_μ`,

the sum over the diagrams `μ` whose complement of `ν` is a rim hook with `r` cells.  Starting from
`s_∅ = 1` and applying this once for each part of a partition `ρ` expands the whole power-sum
product `p_ρ` in the Schur basis.  This file runs that iteration.

The coefficient it produces is `TauCeti.murnaghanNakayamaCoeff`: for a list `l` of part sizes and a
Young diagram `μ`,

`c_[] μ = if μ = ⊥ then 1 else 0`,  `c_{r :: l} μ = ∑_ν (-1) ^ ht(μ / ν) · c_l ν`,

the inner sum running over the diagrams `ν` obtained from `μ` by deleting a rim hook with `r` cells
(`TauCeti.rimHookSubdiagrams`).  Unwound, `c_l μ` is the signed count of the ways to strip `μ` down
to the empty diagram by removing rim hooks of sizes `l₁, l₂, …` in order, each contributing the
sign `(-1)` to the height of the hook it removes.  The theorem is
`TauCeti.prod_map_psum_eq_sum_smul_schurPoly`, with
`TauCeti.psumPart_eq_sum_smul_schurPoly` its form for `MvPolynomial.psumPart`, the power-sum
product indexed by a partition rather than by a list.

The list, not the partition, is what the recursion runs on: the rim hooks are removed one after
another, so the parts come in an order, and `MvPolynomial.psumPart` has to be fed a list of them.
Any list with the right multiset of parts does, the left-hand side being a product over a multiset;
the corollary uses `Multiset.toList`.

Only the coefficients the recursion produces are claimed here.  That they are the irreducible
characters of the symmetric group evaluated at the cycle type `l` -- Frobenius's formula, which
turns this expansion into the Murnaghan-Nakayama rule for those characters -- is a statement about
Specht modules and is not proved here.

## Main definitions

* `TauCeti.rimHookSubdiagrams`: the diagrams obtained from a diagram by deleting a rim hook with a
  given number of cells.
* `TauCeti.murnaghanNakayamaCoeff`: the signed rim-hook-stripping count of a list of part sizes at
  a diagram.

## Main results

* `TauCeti.murnaghanNakayamaCoeff_eq_zero_of_card_ne`: the coefficient vanishes unless the diagram
  has as many cells as the parts sum to, so the expansion below is supported in one degree.
* `TauCeti.murnaghanNakayamaCoeff_singleton`: a single part strips exactly the diagrams that are
  themselves a rim hook of that size.
* `TauCeti.prod_map_psum_eq_sum_smul_schurPoly`: **the Schur expansion of a product of power
  sums.**
* `TauCeti.psumPart_eq_sum_smul_schurPoly`: the same, for the power-sum product of a partition.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 7, where the power sums are expanded in the Schur functions.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.17.3, the border-strip-tableau
  form of the same signed count.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7, "the Frobenius characteristic", whose power-sum expansion `p_μ = ∑_λ χ^λ(μ) s_λ` this
  supplies the symmetric-function half of, and Layer 6, "Rim hooks and Murnaghan-Nakayama", whose
  recursion this is.
-/

public section

open MvPolynomial Finset

namespace TauCeti

open scoped Classical in
/-- **The diagrams obtained from `μ` by deleting a rim hook with `r` cells**: the Young diagrams
`ν` with `|ν| + r = |μ|` whose complement in `μ` is a rim hook.  This is the index set of one step
of the Murnaghan-Nakayama recursion.

The cell count is imposed as `|ν| + r = |μ|` rather than `|ν| = |μ| - r`, so that the set is empty
once `r` exceeds `|μ|`; with truncated subtraction the latter would admit the empty diagram
whenever `μ` is a rim hook of fewer than `r` cells. -/
noncomputable def rimHookSubdiagrams (μ : YoungDiagram) (r : ℕ) : Finset YoungDiagram :=
  {ν ∈ Finset.image (diagramOf (n := μ.card - r)) Finset.univ |
    ν.card + r = μ.card ∧ μ.IsRimHook ν}

open scoped Classical in
/-- Membership in `TauCeti.rimHookSubdiagrams`: the enumeration by partitions in the definition is
there only to produce a `Finset`, and imposes nothing beyond the cell count. -/
theorem mem_rimHookSubdiagrams {μ ν : YoungDiagram} {r : ℕ} :
    ν ∈ rimHookSubdiagrams μ r ↔ ν.card + r = μ.card ∧ μ.IsRimHook ν := by
  simp only [rimHookSubdiagrams, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨⟨toPartition ν (by omega), diagramOf_toPartition ν _⟩, h⟩⟩

open scoped Classical in
/-- **The Murnaghan-Nakayama coefficient** of a list `l` of part sizes at a Young diagram `μ`: the
number of ways of stripping `μ` down to the empty diagram by deleting rim hooks of sizes
`l₁, l₂, …` in order, each way counted with the sign `(-1)` to the sum of the heights of the hooks
deleted.  The empty list strips only the empty diagram.

It is the coefficient of `s_μ` in the power-sum product `p_l`, by
`TauCeti.prod_map_psum_eq_sum_smul_schurPoly`. -/
noncomputable def murnaghanNakayamaCoeff : List ℕ → YoungDiagram → ℤ
  | [], μ => if μ = ⊥ then 1 else 0
  | r :: l, μ => ∑ ν ∈ rimHookSubdiagrams μ r,
      (-1) ^ μ.rimHookHeight ν * murnaghanNakayamaCoeff l ν

open scoped Classical in
/-- The empty list strips only the empty diagram. -/
theorem murnaghanNakayamaCoeff_nil (μ : YoungDiagram) :
    murnaghanNakayamaCoeff [] μ = if μ = ⊥ then 1 else 0 :=
  (rfl)

/-- The recursion step: delete a rim hook with `r` cells, then strip what is left. -/
theorem murnaghanNakayamaCoeff_cons (r : ℕ) (l : List ℕ) (μ : YoungDiagram) :
    murnaghanNakayamaCoeff (r :: l) μ = ∑ ν ∈ rimHookSubdiagrams μ r,
      (-1) ^ μ.rimHookHeight ν * murnaghanNakayamaCoeff l ν :=
  (rfl)

/-- **The coefficient vanishes outside its degree**: stripping `μ` by hooks of sizes `l` can only
succeed when the sizes account for every cell of `μ`. -/
theorem murnaghanNakayamaCoeff_eq_zero_of_card_ne :
    ∀ (l : List ℕ) {μ : YoungDiagram}, μ.card ≠ l.sum → murnaghanNakayamaCoeff l μ = 0
  | [], μ, h => by
    have hne : μ ≠ ⊥ := fun hb => h (by simp [hb])
    simp [murnaghanNakayamaCoeff_nil, hne]
  | r :: l, μ, h => by
    rw [murnaghanNakayamaCoeff_cons]
    refine Finset.sum_eq_zero fun ν hν => ?_
    rw [murnaghanNakayamaCoeff_eq_zero_of_card_ne l, mul_zero]
    have := (mem_rimHookSubdiagrams.mp hν).1
    rw [List.sum_cons] at h
    omega

open scoped Classical in
/-- **A single part strips exactly the rim hooks of that size**: the diagrams `μ` with a nonzero
coefficient at `[r]` are those that are a rim hook with `r` cells over the empty diagram, and the
coefficient is the sign of that hook. -/
theorem murnaghanNakayamaCoeff_singleton (r : ℕ) (μ : YoungDiagram) :
    murnaghanNakayamaCoeff [r] μ =
      if r = μ.card ∧ μ.IsRimHook ⊥ then (-1) ^ μ.rimHookHeight ⊥ else 0 := by
  have hbc : (⊥ : YoungDiagram).card = 0 := Finset.card_eq_zero.mpr YoungDiagram.cells_bot
  have key : ∀ ν ∈ rimHookSubdiagrams μ r,
      (-1) ^ μ.rimHookHeight ν * murnaghanNakayamaCoeff [] ν
        = if ν = ⊥ then (-1) ^ μ.rimHookHeight ⊥ else 0 := fun ν _ => by
    by_cases h : ν = ⊥
    · subst h; simp [murnaghanNakayamaCoeff_nil]
    · simp [murnaghanNakayamaCoeff_nil, h]
  rw [murnaghanNakayamaCoeff_cons, Finset.sum_congr rfl key, Finset.sum_ite_eq' _ _ _]
  simp only [mem_rimHookSubdiagrams, hbc, zero_add]

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]

open scoped Classical in
/-- **A product of power sums, expanded in the Schur basis.**  For a list `l` of positive part
sizes summing to `n`, the product `p_{l₁} ⋯ p_{l_k}` is the combination of the Schur polynomials of
the partitions of `n` whose coefficients are the signed rim-hook-stripping counts
`TauCeti.murnaghanNakayamaCoeff`.

The proof is the iteration the Murnaghan-Nakayama rule was proved for: the empty list gives
`s_∅ = 1`, and multiplying the expansion of `p_l` by `p_r` adds a rim hook with `r` cells to each
diagram by `TauCeti.psum_mul_schurPoly`, which is one exchange of summation away from prepending
`r` to the list in the recursion. -/
theorem prod_map_psum_eq_sum_smul_schurPoly (l : List ℕ) (hl : ∀ r ∈ l, 0 < r) {n : ℕ}
    (hn : l.sum = n) :
    (l.map (psum σ R)).prod
      = ∑ μ : n.Partition, murnaghanNakayamaCoeff l (diagramOf μ) • schurPoly σ R μ := by
  induction l generalizing n with
  | nil =>
    rw [List.sum_nil] at hn
    subst hn
    rw [List.map_nil, List.prod_nil, Fintype.sum_unique]
    have hbot : diagramOf (default : Nat.Partition 0) = ⊥ :=
      YoungDiagram.ext ((Finset.card_eq_zero.mp (card_diagramOf _)).trans
        YoungDiagram.cells_bot.symm)
    rw [hbot, murnaghanNakayamaCoeff_nil, schurPoly_partition_zero]
    simp
  | cons r l ih =>
    have hr : 0 < r := hl r (List.mem_cons_self ..)
    have hl' : ∀ s ∈ l, 0 < s := fun s hs => hl s (List.mem_cons_of_mem _ hs)
    have hn' : l.sum + r = n := by rw [List.sum_cons] at hn; omega
    subst hn'
    -- One factor at a time: the rim-hook rule turns `p_r · s_ν` into a sum over the diagrams that
    -- contain `ν` with a rim hook of `r` cells as complement.
    have hL : ∀ ν : l.sum.Partition,
        psum σ R r * murnaghanNakayamaCoeff l (diagramOf ν) • schurPoly σ R ν
          = ∑ μ : (l.sum + r).Partition,
              if (diagramOf μ).IsRimHook (diagramOf ν) then
                ((-1) ^ (diagramOf μ).rimHookHeight (diagramOf ν) *
                  murnaghanNakayamaCoeff l (diagramOf ν)) • schurPoly σ R μ
              else 0 := by
      intro ν
      rw [mul_smul_comm, psum_mul_schurPoly ν hr, Finset.smul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun μ _ => ?_
      by_cases h : (diagramOf μ).IsRimHook (diagramOf ν)
      · simp only [h, ite_true]
        ring
      · simp [h]
    -- The same sum read the other way round: one step of the recursion at a fixed diagram, with
    -- its index set enumerated by the partitions of `l.sum`.
    have hR : ∀ μ : (l.sum + r).Partition,
        murnaghanNakayamaCoeff (r :: l) (diagramOf μ) • schurPoly σ R μ
          = ∑ ν : l.sum.Partition,
              if (diagramOf μ).IsRimHook (diagramOf ν) then
                ((-1) ^ (diagramOf μ).rimHookHeight (diagramOf ν) *
                  murnaghanNakayamaCoeff l (diagramOf ν)) • schurPoly σ R μ
              else 0 := by
      intro μ
      have hset : rimHookSubdiagrams (diagramOf μ) r
          = Finset.image (diagramOf (n := l.sum))
              {ν : l.sum.Partition | (diagramOf μ).IsRimHook (diagramOf ν)} := by
        ext ν'
        rw [mem_rimHookSubdiagrams, card_diagramOf, Finset.mem_image]
        constructor
        · rintro ⟨hc, h⟩
          have hc' : ν'.card = l.sum := by omega
          refine ⟨toPartition ν' hc', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
            diagramOf_toPartition ν' hc'⟩
          rwa [diagramOf_toPartition ν' hc']
        · rintro ⟨ν, hν, rfl⟩
          exact ⟨by rw [card_diagramOf], (Finset.mem_filter.mp hν).2⟩
      rw [murnaghanNakayamaCoeff_cons, hset,
        Finset.sum_image fun a _ b _ h => diagramOf_injective h, Finset.sum_smul,
        Finset.sum_filter]
    rw [List.map_cons, List.prod_cons, ih hl' rfl, Finset.mul_sum,
      Finset.sum_congr rfl fun ν _ => hL ν, Finset.sum_congr rfl fun μ _ => hR μ,
      Finset.sum_comm]

/-- **The power-sum product of a partition, expanded in the Schur basis.**  This is
`TauCeti.prod_map_psum_eq_sum_smul_schurPoly` for `MvPolynomial.psumPart`, the parts of the
partition listed in some order; the order affects the individual coefficients only through the
order in which the rim hooks are stripped, the sum being `MvPolynomial.psumPart` either way. -/
theorem psumPart_eq_sum_smul_schurPoly {n : ℕ} (ρ : n.Partition) :
    psumPart σ R ρ
      = ∑ μ : n.Partition,
          murnaghanNakayamaCoeff ρ.parts.toList (diagramOf μ) • schurPoly σ R μ := by
  rw [← prod_map_psum_eq_sum_smul_schurPoly (σ := σ) (R := R) ρ.parts.toList
    (fun r hr => ρ.parts_pos (by simpa using hr)) (by simpa using ρ.parts_sum)]
  rw [psumPart, ← Multiset.coe_toList ρ.parts]
  simp

end TauCeti
