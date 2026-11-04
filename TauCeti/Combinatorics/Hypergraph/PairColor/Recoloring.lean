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
`ε * #s ≤ #s'` and `ε * #t ≤ #t'`. The new system has the same palette reversal and the same
colors on all pairs that do not join `s` and `t`; the pairs from `t` to `s` receive the reversed
colors. In particular `(s, t)` becomes a `2ε`-regular pair whose color densities are within `ε`
of `p`.

Thus any prescribed color densities are realized up to `ε` by a regular pair. This is the step
of a regular approximation in which the coloring of an irregular pair of cells, or of a pair of
cells whose densities must be adjusted, is replaced by a quasi-random coloring with the required
densities, while the rest of the coloring is kept.

The coloring is a random coloring of `s ×ˢ t` with distribution `p`, whose color counts on all
rectangles are simultaneously close to their means
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`). The size condition
`card κ + 1 ≤ ε ^ 6 * #s` and `card κ + 1 ≤ ε ^ 6 * #t` makes the union bound over the
`2 ^ (#s + #t)` rectangles and the palette succeed.

## Main results

* `TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le`: a recoloring between
  `s` and `t` in which every large rectangle has color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_recoloring_isRegularPair`: a recoloring between `s` and `t`
  that makes `(s, t)` a `2ε`-regular pair with color densities within `ε` of `p`.

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
private noncomputable def recolorProduct (S : PairColorSystem κ V) {s t : Finset V}
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

variable {S : PairColorSystem κ V} {s t : Finset V} (hst : Disjoint s t) (x : V × V → κ)

private theorem colorOfPair_recolorProduct_of_mem {u v : V} (h : (u, v) ∈ s ×ˢ t) :
    (S.recolorProduct hst x).colorOfPair u v = some (x (u, v)) := by
  have huv : u ≠ v := hst.forall_ne_finset (mem_product.1 h).1 (mem_product.1 h).2
  rw [colorOfPair_of_ne _ huv]
  simp [recolorProduct, h]

private theorem colorOfPair_recolorProduct_of_not_mem {u v : V} (hs : u ∈ s → v ∉ t)
    (ht : u ∈ t → v ∉ s) : (S.recolorProduct hst x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  have h₁ : (u, v) ∉ s ×ˢ t := fun h ↦ hs (mem_product.1 h).1 (mem_product.1 h).2
  have h₂ : (v, u) ∉ s ×ˢ t := fun h ↦ ht (mem_product.1 h).2 (mem_product.1 h).1
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp [recolorProduct, h₁, h₂]

/-- The size condition `card κ + 1 ≤ ε ^ 6 * #u` forces `u` to be nonempty. -/
private theorem cast_card_pos_of_add_one_le [Fintype κ] {ε : ℝ} {u : Finset V}
    (h : Fintype.card κ + 1 ≤ ε ^ 6 * #u) : (0 : ℝ) < #u := by
  by_contra! h'
  have : ε ^ 6 * #u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h'
  linarith [(Nat.cast_nonneg (Fintype.card κ) : (0 : ℝ) ≤ _)]

/-- The union bound succeeds: for `card κ + 1 ≤ ε ^ 6 * #s` and `card κ + 1 ≤ ε ^ 6 * #t`, twice
the number of rectangles times the palette size times `exp (-2 (ε³ #s #t)² / (#s #t))` is less
than one. -/
private theorem two_mul_two_pow_mul_two_pow_mul_exp_lt [Fintype κ] [Nonempty κ] {ε : ℝ}
    (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    2 * (2 ^ #s * 2 ^ #t : ℕ) * Fintype.card κ *
      exp (-2 * (ε ^ 3 * #s * #t) ^ 2 / (#s * #t : ℕ)) < 1 := by
  have hK : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
  have hm := cast_card_pos_of_add_one_le hs
  have hn := cast_card_pos_of_add_one_le ht
  -- Bound each factor by an exponential, using `x + 1 ≤ exp x`.
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
    calc (2 : ℝ) ^ k ≤ exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ = exp k := by rw [← exp_nat_mul, mul_one]
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ - 1) := by
    linarith [add_one_le_exp ((Fintype.card κ : ℝ) - 1)]
  have hexp : -2 * (ε ^ 3 * #s * #t) ^ 2 / ((#s * #t : ℕ) : ℝ) = -2 * (ε ^ 6 * #s) * #t := by
    push_cast
    field_simp
  calc 2 * ((2 ^ #s * 2 ^ #t : ℕ) : ℝ) * Fintype.card κ *
        exp (-2 * (ε ^ 3 * #s * #t) ^ 2 / (#s * #t : ℕ))
      ≤ exp 1 * (exp #s * exp #t) * exp (Fintype.card κ - 1) *
          exp (-2 * (ε ^ 6 * #s) * #t) := by
        rw [hexp]
        push_cast
        gcongr
        all_goals exact hpow _
    _ = exp (#s + #t + Fintype.card κ - 2 * (ε ^ 6 * #s) * #t) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        -- `2 ε⁶ #s #t ≥ (card κ + 1) (#s + #t) > #s + #t + card κ`.
        have hm1 : (1 : ℝ) ≤ #s := Nat.one_le_cast.2 (Nat.cast_pos.1 hm)
        have hn1 : (1 : ℝ) ≤ #t := Nat.one_le_cast.2 (Nat.cast_pos.1 hn)
        nlinarith [mul_le_mul_of_nonneg_right hs hn.le, mul_le_mul_of_nonneg_right ht hm.le,
          le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ Fintype.card κ) hm1,
          le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ Fintype.card κ) hn1]

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
  have hs0 := cast_card_pos_of_add_one_le hs
  have ht0 := cast_card_pos_of_add_one_le ht
  -- A coloring of `s ×ˢ t` with small deviations on all rectangles `s' ×ˢ t'`.
  obtain ⟨x, hx⟩ := exists_forall_abs_card_filter_sub_mul_card_lt hp hp1
    (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2) (N := #s * #t)
    (fun i ↦ by
      obtain ⟨hs', ht'⟩ := mem_product.1 i.2
      rw [card_product]
      exact Nat.mul_le_mul (card_le_card (mem_powerset.1 hs')) (card_le_card (mem_powerset.1 ht')))
    (a := ε ^ 3 * #s * #t)
    (mul_pos (mul_pos (pow_pos hε 3) hs0) ht0)
    (by simpa using two_mul_two_pow_mul_two_pow_mul_exp_lt hs ht)
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
  obtain hε2 | hε2 := le_or_gt 1 (2 * ε)
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

end PairColorSystem

end TauCeti
