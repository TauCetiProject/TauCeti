/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.RimHook

/-!
# Stripping a Young diagram by rim hooks

Deleting a rim hook with `r` cells from a Young diagram `μ` leaves one of the diagrams in
`YoungDiagram.rimHookSubdiagrams μ r`.  Iterating that step along a list `l` of sizes and counting
the ways of reaching the empty diagram, each with the sign `(-1)` to the sum of the heights of the
hooks deleted, gives `TauCeti.murnaghanNakayamaCoeff l μ`:

`c_[] μ = if μ = ⊥ then 1 else 0`,  `c_{r :: l} μ = ∑_ν (-1) ^ ht(μ / ν) · c_l ν`,

the inner sum running over `YoungDiagram.rimHookSubdiagrams μ r`.

The cell count in the index set is imposed as `|ν| + r = |μ|` rather than `|ν| = |μ| - r`, so that
the set is empty once `r` exceeds `|μ|`; with truncated subtraction the latter would admit the
empty diagram whenever `μ` is a rim hook of fewer than `r` cells, and the count would then fail to
vanish outside its degree.  That it does vanish outside its degree is
`TauCeti.murnaghanNakayamaCoeff_eq_zero_of_card_ne_sum`.

These counts are the coefficients of the Schur expansion of a product of power sums; that is
`TauCeti.prod_map_psum_eq_sum_murnaghanNakayamaCoeff_smul_schurPoly`, in
`TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayama`.  Nothing about the symmetric
group is claimed here.

## Main definitions

* `YoungDiagram.rimHookSubdiagrams`: the diagrams obtained from a diagram by deleting a rim hook
  with a given number of cells.
* `TauCeti.murnaghanNakayamaCoeff`: the signed rim-hook-stripping count of a list of part sizes at
  a diagram.

## Main results

* `TauCeti.rimHookSubdiagrams_eq_image`: the index set of one step, enumerated by the partitions of
  the number of cells that remain.
* `TauCeti.murnaghanNakayamaCoeff_eq_zero_of_card_ne_sum`: the count vanishes unless the sizes
  account for every cell of the diagram.
* `TauCeti.murnaghanNakayamaCoeff_singleton`: a single size strips exactly the diagrams that are
  themselves a rim hook of that size.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 7, where the power sums are expanded in the Schur functions.
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Theorem 7.17.3, the border-strip-tableau
  form of the same signed count.
-/

public section

namespace YoungDiagram

/-- **The diagrams obtained from `μ` by deleting a rim hook with `r` cells**: the Young diagrams
`ν` with `|ν| + r = |μ|` whose complement in `μ` is a rim hook.  This is the index set of one step
of the Murnaghan-Nakayama recursion.

The cell count is imposed as `|ν| + r = |μ|` rather than `|ν| = |μ| - r`, so that the set is empty
once `r` exceeds `|μ|`; with truncated subtraction the latter would admit the empty diagram
whenever `μ` is a rim hook of fewer than `r` cells. -/
noncomputable def rimHookSubdiagrams (μ : YoungDiagram) (r : ℕ) : Finset YoungDiagram :=
  Set.Finite.toFinset (s := {ν : YoungDiagram | ν.card + r = μ.card ∧ μ.IsRimHook ν})
    ((finite_Iic μ).subset fun _ h => Set.mem_Iic.mpr h.2.le)

@[simp]
theorem mem_rimHookSubdiagrams {μ ν : YoungDiagram} {r : ℕ} :
    ν ∈ μ.rimHookSubdiagrams r ↔ ν.card + r = μ.card ∧ μ.IsRimHook ν :=
  Set.Finite.mem_toFinset _

end YoungDiagram

namespace TauCeti

open scoped Classical in
/-- **One step of the recursion, enumerated by partitions**: when `n + r = |μ|`, the diagrams
obtained from `μ` by deleting a rim hook with `r` cells are exactly the diagrams of the partitions
of `n` whose complement in `μ` is a rim hook.  This is the bridge between the `Finset`
`YoungDiagram.rimHookSubdiagrams` and the `Fintype` of partitions of `n`. -/
theorem rimHookSubdiagrams_eq_image {μ : YoungDiagram} {n r : ℕ} (h : n + r = μ.card) :
    μ.rimHookSubdiagrams r
      = Finset.image (diagramOf (n := n)) {ν : n.Partition | μ.IsRimHook (diagramOf ν)} := by
  ext ν
  rw [YoungDiagram.mem_rimHookSubdiagrams, Finset.mem_image]
  constructor
  · rintro ⟨hc, hrh⟩
    have hc' : ν.card = n := by omega
    exact ⟨toPartition ν hc', Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by rwa [diagramOf_toPartition ν hc']⟩, diagramOf_toPartition ν hc'⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨by rw [card_diagramOf]; omega, (Finset.mem_filter.mp hξ).2⟩

open scoped Classical in
/-- **The Murnaghan-Nakayama coefficient** of a list `l` of part sizes at a Young diagram `μ`: the
number of ways of stripping `μ` down to the empty diagram by deleting rim hooks of sizes
`l₁, l₂, …` in order, each way counted with the sign `(-1)` to the sum of the heights of the hooks
deleted.  The empty list strips only the empty diagram.

For a list of positive part sizes, it is a coefficient in the Schur expansion of the power-sum
product `p_l`, by
`TauCeti.prod_map_psum_eq_sum_murnaghanNakayamaCoeff_smul_schurPoly`. -/
noncomputable def murnaghanNakayamaCoeff : List ℕ → YoungDiagram → ℤ
  | [], μ => if μ = ⊥ then 1 else 0
  | r :: l, μ => ∑ ν ∈ μ.rimHookSubdiagrams r,
      (-1) ^ μ.rimHookHeight ν * murnaghanNakayamaCoeff l ν

open scoped Classical in
/-- The empty list strips only the empty diagram. -/
@[simp]
theorem murnaghanNakayamaCoeff_nil (μ : YoungDiagram) :
    murnaghanNakayamaCoeff [] μ = if μ = ⊥ then 1 else 0 :=
  (rfl)

/-- The recursion step: delete a rim hook with `r` cells, then strip what is left. -/
theorem murnaghanNakayamaCoeff_cons (r : ℕ) (l : List ℕ) (μ : YoungDiagram) :
    murnaghanNakayamaCoeff (r :: l) μ = ∑ ν ∈ μ.rimHookSubdiagrams r,
      (-1) ^ μ.rimHookHeight ν * murnaghanNakayamaCoeff l ν :=
  (rfl)

/-- **The coefficient vanishes outside its degree**: stripping `μ` by hooks of sizes `l` can only
succeed when the sizes account for every cell of `μ`. -/
theorem murnaghanNakayamaCoeff_eq_zero_of_card_ne_sum :
    ∀ (l : List ℕ) {μ : YoungDiagram}, μ.card ≠ l.sum → murnaghanNakayamaCoeff l μ = 0
  | [], μ, h => by
    have hne : μ ≠ ⊥ := fun hb => h (by simp [hb])
    simp [hne]
  | r :: l, μ, h => by
    rw [murnaghanNakayamaCoeff_cons]
    refine Finset.sum_eq_zero fun ν hν => ?_
    rw [murnaghanNakayamaCoeff_eq_zero_of_card_ne_sum l, mul_zero]
    have := (YoungDiagram.mem_rimHookSubdiagrams.mp hν).1
    rw [List.sum_cons] at h
    omega

open scoped Classical in
/-- **A single part strips exactly the rim hooks of that size**: the diagrams `μ` with a nonzero
coefficient at `[r]` are those that are a rim hook with `r` cells over the empty diagram, and the
coefficient is the sign of that hook. -/
theorem murnaghanNakayamaCoeff_singleton (r : ℕ) (μ : YoungDiagram) :
    murnaghanNakayamaCoeff [r] μ =
      if r = μ.card ∧ μ.IsRimHook ⊥ then (-1) ^ μ.rimHookHeight ⊥ else 0 := by
  have key : ∀ ν ∈ μ.rimHookSubdiagrams r,
      (-1) ^ μ.rimHookHeight ν * murnaghanNakayamaCoeff [] ν
        = if ν = ⊥ then (-1) ^ μ.rimHookHeight ⊥ else 0 := fun ν _ => by
    by_cases h : ν = ⊥
    · subst h; simp
    · simp [h]
  rw [murnaghanNakayamaCoeff_cons, Finset.sum_congr rfl key, Finset.sum_ite_eq' _ _ _]
  simp only [YoungDiagram.mem_rimHookSubdiagrams, YoungDiagram.card_bot, zero_add]

end TauCeti
