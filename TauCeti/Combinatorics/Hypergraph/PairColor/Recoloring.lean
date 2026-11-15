/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Regular recolorings of a pair of disjoint sets

Let `S` be a pair-color system with a finite palette `κ`, let `s` and `t` be disjoint vertex
sets, and let `p` be a probability distribution on `κ`. If `s` and `t` are large enough in terms
of `ε` and the palette size, the pairs between `s` and `t` can be recolored so that every color
`c` has density within `ε` of `p c` on every rectangle `s' ×ˢ t'` with `s' ⊆ s`, `t' ⊆ t`,
`ε * #s ≤ #s'` and `ε * #t ≤ #t'`. The new system (`TauCeti.PairColorSystem.recolorProduct`) has
the same palette reversal and the same colors on all pairs that do not join `s` and `t`; the pairs
from `t` to `s` receive the reversed colors. In particular `(s, t)` becomes a `2ε`-regular pair
whose color densities are within `ε` of `p`, and every subrectangle `s' ×ˢ t'` (`s' ⊆ s`, `t' ⊆ t`)
has color-count discrepancy at most `3 * ε * (#s * #t)`.

When local recolorings have been constructed for pairs of cells of a partition `P`, choosing a
linear order on `P.parts` glues them into one global reversal-coherent `PairColorSystem`
(`TauCeti.PairColorSystem.exists_cellwise_recoloring`).

## Main definitions

* `TauCeti.PairColorSystem.recolorProduct`: recolor `s ×ˢ t` by `x`, `t ×ˢ s` by `S.rev ∘ x ∘ swap`,
  and preserve `S` elsewhere.

## Main results

* `TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le`: a recoloring between
  `s` and `t` in which every large rectangle has color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_recoloring_isRegularPair`: a recoloring between `s` and `t`
  that makes `(s, t)` a `2ε`-regular pair with color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_recoloring_abs_card_filter_sub_le`: rectangle-count counterpart
  giving discrepancy at most `3 * ε * (#s * #t)` on all subrectangles `s' ×ˢ t'`.
* `TauCeti.PairColorSystem.exists_cellwise_recoloring`: glue reversal-compatible local systems on
  ordered pairs of parts of a partition `P` along a linear order on `P.parts`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the regular approximation lemma.
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), §9.3
  (quasi-random graphs).
-/

public section

open Finset Real

namespace TauCeti

namespace PairColorSystem

variable {κ V : Type*}

open Classical in
/-- Recolor the pairs from `s` to `t` by `x`, the pairs from `t` to `s` by the reversed colors,
and keep all other colors of `S`. -/
noncomputable def recolorProduct (S : PairColorSystem κ V) {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) : PairColorSystem κ V where
  color q :=
    if q.1 ∈ s ×ˢ t then x q.1 else if q.1.swap ∈ s ×ˢ t then S.rev (x q.1.swap) else S.color q
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev q := by
    obtain ⟨⟨u, v⟩, huv⟩ := q
    have hboth : ¬((u, v) ∈ s ×ˢ t ∧ (v, u) ∈ s ×ˢ t) := fun ⟨h₁, h₂⟩ ↦
      disjoint_left.1 hst (mem_product.1 h₂).1 (mem_product.1 h₁).2
    simp only [Prod.swap_prod_mk]
    by_cases h₁ : (u, v) ∈ s ×ˢ t <;> by_cases h₂ : (v, u) ∈ s ×ˢ t
    · exact absurd ⟨h₁, h₂⟩ hboth
    · simp [h₁, h₂]
    · simp [h₁, h₂]
    · simpa [h₁, h₂] using S.color_rev ⟨(u, v), huv⟩

open Classical in
/-- Action of `recolorProduct` on an ordered distinct pair. -/
@[simp]
theorem recolorProduct_color (S : PairColorSystem κ V) {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) (q : {q : V × V // q.1 ≠ q.2}) :
    (S.recolorProduct hst x).color q =
      if q.1 ∈ s ×ˢ t then x q.1 else if q.1.swap ∈ s ×ˢ t then S.rev (x q.1.swap) else S.color q :=
  (rfl)

/-- `recolorProduct` preserves the palette reversal of `S`. -/
@[simp]
theorem recolorProduct_rev (S : PairColorSystem κ V) {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) :
    (S.recolorProduct hst x).rev = S.rev :=
  (rfl)

variable {S : PairColorSystem κ V} {s t : Finset V} (hst : Disjoint s t) (x : V × V → κ)

/-- On `s ×ˢ t`, `recolorProduct` assigns the color `x (u, v)`. -/
theorem colorOfPair_recolorProduct_of_mem {u v : V} (h : (u, v) ∈ s ×ˢ t) :
    (S.recolorProduct hst x).colorOfPair u v = some (x (u, v)) := by
  have huv : u ≠ v := hst.forall_ne_finset (mem_product.1 h).1 (mem_product.1 h).2
  rw [colorOfPair_of_ne _ huv]
  simp [h]

/-- On pairs whose reversal lies in `s ×ˢ t`, `recolorProduct` assigns `S.rev (x (v, u))`. -/
theorem colorOfPair_recolorProduct_of_swap_mem {u v : V} (h : (v, u) ∈ s ×ˢ t) :
    (S.recolorProduct hst x).colorOfPair u v = some (S.rev (x (v, u))) := by
  have huv : u ≠ v := (hst.forall_ne_finset (mem_product.1 h).1 (mem_product.1 h).2).symm
  have hnot : (u, v) ∉ s ×ˢ t := fun h' ↦
    disjoint_left.1 hst (mem_product.1 h').1 (mem_product.1 h).2
  rw [colorOfPair_of_ne _ huv]
  simp [hnot, h]

/-- Outside `s ×ˢ t` and `t ×ˢ s`, `recolorProduct` preserves the colors of `S`. -/
theorem colorOfPair_recolorProduct_of_not_mem {u v : V} (hs : u ∈ s → v ∉ t)
    (ht : u ∈ t → v ∉ s) : (S.recolorProduct hst x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  have h₁ : (u, v) ∉ s ×ˢ t := fun h ↦ hs (mem_product.1 h).1 (mem_product.1 h).2
  have h₂ : (v, u) ∉ s ×ˢ t := fun h ↦ ht (mem_product.1 h).2 (mem_product.1 h).1
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp [h₁, h₂]

/-- **Regular recoloring with prescribed densities.** Let `S` be a pair-color system with a
finite palette `κ`, let `s` and `t` be disjoint vertex sets with `card κ + 1 ≤ ε ^ 6 * #s` and
`card κ + 1 ≤ ε ^ 6 * #t`, and let `p` be a probability distribution on `κ`. Then there is a
pair-color system `S'` with the palette reversal of `S` that agrees with `S` on all pairs not
joining `s` and `t`, such that on every rectangle `s' ×ˢ t'` with `s' ⊆ s`, `t' ⊆ t`,
`ε * #s ≤ #s'` and `ε * #t ≤ #t'` the density of every color `c` is within `ε` of `p c`. -/
theorem exists_recoloring_abs_pairColorDensity_sub_le [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ}
    (hε : 0 < ε) (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, ε * #s ≤ #s' → ε * #t ≤ #t' →
        |(pairColorDensity S' c s' t' : ℝ) - p c| ≤ ε := by
  classical
  have : Nonempty κ := by
    by_contra! h
    simp at hp1
  have hs0 : (0 : ℝ) < #s :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hs) (by positivity)
  have ht0 : (0 : ℝ) < #t :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) ht) (by positivity)
  have hub := two_mul_two_pow_mul_two_pow_add_mul_exp_lt (κ := κ) (r := 0) (δ := ε ^ 3) le_rfl
    (by linarith : (Fintype.card κ : ℝ) + 1 + 0 ≤ (ε ^ 3) ^ 2 * #s)
    (by linarith : (Fintype.card κ : ℝ) + 1 + 0 ≤ (ε ^ 3) ^ 2 * #t)
  -- A coloring of `s ×ˢ t` with small deviations on all rectangles `s' ×ˢ t'`.
  obtain ⟨x, hx⟩ := exists_forall_abs_card_filter_sub_mul_card_lt hp hp1
    (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2) (N := #s * #t)
    (fun i ↦ by
      obtain ⟨hs', ht'⟩ := mem_product.1 i.2
      rw [card_product]
      exact Nat.mul_le_mul (card_le_card (mem_powerset.1 hs')) (card_le_card (mem_powerset.1 ht')))
    (a := ε ^ 3 * #s * #t)
    (mul_pos (mul_pos (pow_pos hε 3) hs0) ht0)
    (by simpa using hub)
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x, ?_⟩
  intro c s' hs' t' ht' hs's ht't
  have hpos : (0 : ℝ) < #s' * #t' :=
    mul_pos ((mul_pos hε hs0).trans_le hs's) ((mul_pos hε ht0).trans_le ht't)
  have hdev := hx ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
  -- On `s' ×ˢ t' ⊆ s ×ˢ t` the recolored system has the colors of `x`, and the color count is the
  -- density times `#s' * #t'`, since `s'` and `t'` are disjoint.
  have hcount : (#{q ∈ s' ×ˢ t' | x q = c} : ℝ) =
      pairColorDensity (S.recolorProduct hst x) c s' t' * (#s' * #t') := by
    have hfilter : {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
        {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun q hq ↦ by
      rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
        Option.some_inj]
    rw [← hfilter]
    exact mod_cast (pairColorDensity_mul_card_of_disjoint _ c (hst.mono hs' ht')).symm
  rw [hcount, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos hpos] at hdev
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ ≤ ε ^ 3 * #s * #t := hdev.le
    _ = ε * ((ε * #s) * (ε * #t)) := by ring
    _ ≤ ε * (#s' * #t') := by gcongr

/-- **Regular recoloring.** Under the hypotheses of
`TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le`, the pairs between `s`
and `t` can be recolored so that `(s, t)` becomes a `2ε`-regular pair whose color densities are
within `ε` of `p`, keeping the palette reversal and all colors on pairs not joining `s` and
`t`. -/
theorem exists_recoloring_isRegularPair [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ}
    (hε : 0 < ε) (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      S'.IsRegularPair (2 * ε) s t ∧ ∀ c, |(pairColorDensity S' c s t : ℝ) - p c| ≤ ε := by
  obtain ⟨S', hrev, hagree, hdens⟩ :=
    S.exists_recoloring_abs_pairColorDensity_sub_le hst hp hp1 hε hs ht
  have hthr {ε' : ℝ} (hε' : ε' ≤ 1) (u : Finset V) : ε' * #u ≤ #u :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) hε'
  -- For `ε ≤ 1` the pair `(s, t)` itself passes the size thresholds; otherwise densities in
  -- `[0, 1]` are trivially within `ε` of each other.
  have hfull (c : κ) : |(pairColorDensity S' c s t : ℝ) - p c| ≤ ε := by
    obtain hε1 | hε1 := le_or_gt ε 1
    · exact hdens c s subset_rfl t subset_rfl (hthr hε1 s) (hthr hε1 t)
    have h₀ : (0 : ℝ) ≤ pairColorDensity S' c s t := mod_cast pairColorDensity_nonneg S' c s t
    have h₁ : (pairColorDensity S' c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S' c s t
    have hpc : p c ≤ 1 := hp1 ▸ single_le_sum (fun c _ ↦ hp c) (mem_univ c)
    exact (abs_sub_le_iff.2 ⟨by linarith [hp c], by linarith [hp c]⟩).trans hε1.le
  refine ⟨S', hrev, hagree, ?_, hfull⟩
  obtain hε2 | _ := le_or_gt 1 (2 * ε)
  · exact isRegularPair_of_one_le hε2
  rw [isRegularPair_iff]
  intro c s' hs' t' ht' hs's ht't
  have hmono (u u' : Finset V) (hu : 2 * ε * #u ≤ #u') : ε * #u ≤ #u' :=
    le_trans (by nlinarith [(Nat.cast_nonneg #u : (0 : ℝ) ≤ _)]) hu
  have h₁ := hdens c s' hs' t' ht' (hmono s s' hs's) (hmono t t' ht't)
  have h₂ := hfull c
  calc _ ≤ |(pairColorDensity S' c s' t' : ℝ) - p c| + |p c - pairColorDensity S' c s t| :=
        abs_sub_le _ _ _
    _ ≤ 2 * ε := by rw [abs_sub_comm (p c)]; linarith

/-- **Uncoupled rectangle-count recoloring.** Under `card κ + 1 ≤ ε ^ 6 * #s` and
`card κ + 1 ≤ ε ^ 6 * #t`, recoloring `s ×ˢ t` toward `p` achieves rectangle count discrepancy at
most `3 * ε * (#s * #t)` on *every* subrectangle `s' ×ˢ t'` (`s' ⊆ s`, `t' ⊆ t`). -/
theorem exists_recoloring_abs_card_filter_sub_le [Fintype κ] [DecidableEq κ]
    (S : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ} (hε : 0 < ε)
    (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          3 * ε * (#s * #t) := by
  obtain ⟨S', hrev, hagree, hreg, hdens⟩ :=
    S.exists_recoloring_isRegularPair hst hp hp1 hε hs ht
  refine ⟨S', hrev, hagree, fun c s' hs' t' ht' ↦ ?_⟩
  have h₁ := hreg.abs_card_filter_colorOfPair_sub_le (c := c) hst hs' ht'
  have hst' : (#s' : ℝ) * #t' ≤ #s * #t :=
    mul_le_mul (Nat.cast_le.2 (card_le_card hs')) (Nat.cast_le.2 (card_le_card ht'))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h₂ : |(pairColorDensity S' c s t : ℝ) * #s' * #t' - p c * (#s' * #t')| ≤ ε * (#s * #t) := by
    rw [mul_assoc (pairColorDensity S' c s t : ℝ), ← sub_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ #s' * #t')]
    exact (mul_le_mul_of_nonneg_right (hdens c) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hst' hε.le)
  linarith [abs_sub_le (#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ)
    (pairColorDensity S' c s t * #s' * #t') (p c * (#s' * #t'))]

/-- **Cellwise gluing of local pair-color systems.** Given a partition `P` of `V`, a linear order
`order` on `P.parts`, and local systems `T A B` with `(T A B).rev = S.rev` whenever `order.le A B`,
selecting `T (min A B) (max A B)` on pairs between `A` and `B` produces a single global
`R : PairColorSystem κ V` with `R.rev = S.rev` that agrees with `T A B` on `A ×ˢ B` whenever
`order.le A B`. -/
theorem exists_cellwise_recoloring [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)
    (P : Finpartition (univ : Finset V)) (order : LinearOrder P.parts)
    (T : P.parts → P.parts → PairColorSystem κ V)
    (hrev : ∀ A B, order.le A B → (T A B).rev = S.rev) :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      ∀ A B : P.parts, order.le A B → ∀ x ∈ A.1, ∀ y ∈ B.1,
        R.colorOfPair x y = (T A B).colorOfPair x y := by
  classical
  let : LinearOrder P.parts := order
  let : LE P.parts := order.toLE
  let cell (x : V) : P.parts := ⟨P.part x, P.part_mem.2 (mem_univ x)⟩
  have hcell (A : P.parts) {x : V} (hx : x ∈ A.1) : cell x = A :=
    Subtype.ext (P.part_eq_of_mem A.2 hx)
  -- The minimum and maximum select the same local system in both orientations.
  let R : PairColorSystem κ V :=
    { color := fun p ↦ (T (min (cell p.1.1) (cell p.1.2))
        (max (cell p.1.1) (cell p.1.2))).color p
      rev := S.rev
      rev_involutive := S.rev_involutive
      color_rev := fun p ↦ by
        dsimp only [Prod.fst_swap, Prod.snd_swap]
        rw [min_comm (cell p.1.2), max_comm (cell p.1.2), (T _ _).color_rev,
          hrev _ _ (min_le_max (a := cell p.1.1) (b := cell p.1.2))] }
  refine ⟨R, rfl, fun A B hAB x hx y hy ↦ ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  · simp [colorOfPair_of_ne _ hxy, R, hcell A hx, hcell B hy, min_eq_left hAB, max_eq_right hAB]

end PairColorSystem

end TauCeti
