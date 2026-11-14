/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import TauCeti.Combinatorics.Enumerative.CoupledColoring
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

When `(s, t)` is already `η`-regular for `S` and its color densities are close to `p`, an
independent recoloring would still edit a constant fraction of `s ×ˢ t`. Using coupled
low-discrepancy recoloring (`TauCeti.exists_coupled_coloring_abs_card_filter_sub_le`), the pairs
between `s` and `t` can instead be recolored so that the edit count on `s ×ˢ t` is controlled by
the `L¹`-gap between `pairColorDensity S · s t` and `p`, while every rectangle `s' ×ˢ t'` has color
counts within `card κ * (η + ε³) * #s * #t` of `p · (#s' * #t')`.

## Main results

* `TauCeti.PairColorSystem.exists_recoloring_abs_card_filter_colorOfPair_sub_le`: a recoloring
  between `s` and `t` in which every rectangle has color counts within `ε³ #s #t` of `p`.
* `TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le`: a recoloring between
  `s` and `t` in which every large rectangle has color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_recoloring_isRegularPair`: a recoloring between `s` and `t`
  that makes `(s, t)` a `2ε`-regular pair with color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_colorOfPair_sub_le`: a coupled
  recoloring of an `η`-regular pair with small rectangle discrepancy and edit count controlled by
  the density gap to `p`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2 (the regular approximation lemma).
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

open Classical in
/-- **Regular recoloring with small rectangle discrepancy.** Let `S` be a pair-color system with a
finite palette `κ`, let `s` and `t` be disjoint vertex sets with `card κ + 1 ≤ ε ^ 6 * #s` and
`card κ + 1 ≤ ε ^ 6 * #t`, and let `p` be a probability distribution on `κ`. Then there is a
pair-color system `S'` with the palette reversal of `S` agreeing with `S` on all pairs not joining
`s` and `t`, such that on every rectangle `s' ×ˢ t'` with `s' ⊆ s` and `t' ⊆ t` the number of pairs
of color `c` is within `ε ^ 3 * #s * #t` of `p c * (#s' * #t')`. -/
theorem exists_recoloring_abs_card_filter_colorOfPair_sub_le [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ}
    (hε : 0 < ε) (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          ε ^ 3 * #s * #t := by
  classical
  have : Nonempty κ := by
    by_contra! h
    simp at hp1
  have hs0 := cast_card_pos_of_add_one_le hs
  have ht0 := cast_card_pos_of_add_one_le ht
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
  intro c s' hs' t' ht'
  have hdev := (hx ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c).le
  have hfilter : {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
      {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun q hq ↦ by
    rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
      Option.some_inj]
  simpa only [hfilter, card_product, Nat.cast_mul] using hdev

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
  have hs0 := cast_card_pos_of_add_one_le hs
  have ht0 := cast_card_pos_of_add_one_le ht
  obtain ⟨S', hrev, hagree, hcount⟩ :=
    S.exists_recoloring_abs_card_filter_colorOfPair_sub_le hst hp hp1 hε hs ht
  refine ⟨S', hrev, hagree, fun c s' hs' t' ht' hs's ht't ↦ ?_⟩
  have hpos : (0 : ℝ) < #s' * #t' :=
    mul_pos ((mul_pos hε hs0).trans_le hs's) ((mul_pos hε ht0).trans_le ht't)
  have hdev := hcount c s' hs' t' ht'
  have hd : (#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) =
      pairColorDensity S' c s' t' * (#s' * #t') :=
    mod_cast (pairColorDensity_mul_card_of_disjoint S' c (hst.mono hs' ht')).symm
  rw [hd, ← sub_mul, abs_mul, abs_of_pos hpos] at hdev
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ ≤ ε ^ 3 * #s * #t := hdev
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

/-- The coupled union bound succeeds once `card κ + 2 ≤ ε ^ 6 * #s` and `card κ + 2 ≤ ε ^ 6 * #t`,
absorbing the extra test on the full product `s ×ˢ t`. -/
private theorem two_mul_two_pow_mul_two_pow_add_one_mul_exp_lt [Fintype κ] [Nonempty κ] {ε : ℝ}
    (hs : Fintype.card κ + 2 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 2 ≤ ε ^ 6 * #t) :
    2 * (2 ^ #s * 2 ^ #t + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (ε ^ 3 * #s * #t) ^ 2 / (#s * #t : ℕ)) < 1 := by
  have hm := cast_card_pos_of_add_one_le (by linarith : (Fintype.card κ : ℝ) + 1 ≤ ε ^ 6 * #s)
  have hn := cast_card_pos_of_add_one_le (by linarith : (Fintype.card κ : ℝ) + 1 ≤ ε ^ 6 * #t)
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ exp 2 :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = exp 2 := by rw [← exp_nat_mul]; norm_num
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
    calc (2 : ℝ) ^ k ≤ exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ = exp k := by rw [← exp_nat_mul, mul_one]
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ - 1) := by
    linarith [add_one_le_exp ((Fintype.card κ : ℝ) - 1)]
  have hcard1 : (2 : ℝ) * (2 ^ #s * 2 ^ #t + 1 : ℕ) ≤ 4 * (2 ^ #s * 2 ^ #t : ℝ) := by
    have hge1 : (1 : ℝ) ≤ 2 ^ #s * 2 ^ #t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    push_cast
    linarith
  have hexp : -2 * (ε ^ 3 * #s * #t) ^ 2 / ((#s * #t : ℕ) : ℝ) = -2 * (ε ^ 6 * #s) * #t := by
    push_cast
    field_simp
  calc 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) * Fintype.card κ *
        exp (-2 * (ε ^ 3 * #s * #t) ^ 2 / (#s * #t : ℕ))
      ≤ 4 * (2 ^ #s * 2 ^ #t : ℝ) * Fintype.card κ * exp (-2 * (ε ^ 6 * #s) * #t) := by
        rw [hexp]
        gcongr
    _ ≤ exp 2 * (exp #s * exp #t) * exp (Fintype.card κ - 1) * exp (-2 * (ε ^ 6 * #s) * #t) := by
        gcongr
        all_goals exact hpow _
    _ = exp (#s + #t + Fintype.card κ + 1 - 2 * (ε ^ 6 * #s) * #t) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        have hm1 : (1 : ℝ) ≤ #s := Nat.one_le_cast.2 (Nat.cast_pos.1 hm)
        have hn1 : (1 : ℝ) ≤ #t := Nat.one_le_cast.2 (Nat.cast_pos.1 hn)
        nlinarith [mul_le_mul_of_nonneg_right hs hn.le, mul_le_mul_of_nonneg_right ht hm.le,
          le_mul_of_one_le_right (Nat.cast_nonneg (Fintype.card κ)) hm1,
          le_mul_of_one_le_right (Nat.cast_nonneg (Fintype.card κ)) hn1]

/-- Extend `S.color` from off-diagonal pairs to all of `V × V` by choosing an arbitrary color on
the diagonal. -/
private noncomputable def pairColorFn [Nonempty κ] (S : PairColorSystem κ V) (q : V × V) : κ :=
  open Classical in if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ

open Classical in
/-- On a subrectangle `s' ×ˢ t'` of a disjoint pair `(s, t)`, `pairColorFn` agrees with
`S.colorOfPair`, and an `η`-regular pair satisfies the fiberwise discrepancy bound required by
coupled coloring. -/
private theorem pairColorFn_spec [Nonempty κ] (S : PairColorSystem κ V) (hst : Disjoint s t) :
    (∀ {q}, q ∈ s ×ˢ t → S.colorOfPair q.1 q.2 = some (S.pairColorFn q)) ∧
    (∀ c, (#{q ∈ s ×ˢ t | S.pairColorFn q = c} : ℝ) = pairColorDensity S c s t * (#s * #t)) ∧
    ∀ {η : ℝ}, S.IsRegularPair η s t → (0 : ℝ) < #s → (0 : ℝ) < #t →
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S.pairColorFn q = c} : ℝ) -
          (#{q ∈ s ×ˢ t | S.pairColorFn q = c} : ℝ) / #(s ×ˢ t) * #(s' ×ˢ t')| ≤
            η * #s * #t := by
  have hx₀ {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t) {q : V × V} (hq : q ∈ s' ×ˢ t') :
      S.colorOfPair q.1 q.2 = some (S.pairColorFn q) := by
    have hne : q.1 ≠ q.2 := hst.forall_ne_finset (hs' (mem_product.1 hq).1)
      (ht' (mem_product.1 hq).2)
    simp [pairColorFn, hne]
  have hcnt {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t) (c : κ) :
      #{q ∈ s' ×ˢ t' | S.pairColorFn q = c} = #{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c} :=
    congrArg card (filter_congr fun q hq ↦ by rw [hx₀ hs' ht' hq, Option.some_inj])
  have hfull (c : κ) : (#{q ∈ s ×ˢ t | S.pairColorFn q = c} : ℝ) =
      pairColorDensity S c s t * (#s * #t) := by
    rw [hcnt subset_rfl subset_rfl c]
    exact mod_cast (pairColorDensity_mul_card_of_disjoint S c hst).symm
  refine ⟨hx₀ subset_rfl subset_rfl, hfull, fun hreg hs0 ht0 c s' hs' t' ht' ↦ ?_⟩
  have hdiv : (#{q ∈ s ×ˢ t | S.pairColorFn q = c} : ℝ) / #(s ×ˢ t) = pairColorDensity S c s t := by
    rw [hfull c, card_product, Nat.cast_mul, mul_div_cancel_right₀ _ (mul_pos hs0 ht0).ne']
  rw [hdiv, hcnt hs' ht' c, card_product, Nat.cast_mul, ← mul_assoc]
  exact hreg.abs_card_filter_colorOfPair_sub_le hst hs' ht'

open Classical in
/-- **Coupled regular recoloring.** Let `(s, t)` be an `η`-regular pair of disjoint vertex sets for
`S` with `card κ + 2 ≤ ε ^ 6 * #s` and `card κ + 2 ≤ ε ^ 6 * #t`, and let `p` be a probability
distribution on `κ`. Then there is a pair-color system `S'` with the palette reversal of `S`
agreeing with `S` on all pairs not joining `s` and `t`, such that:
1. the number of edited pairs on `s ×ˢ t` is at most half the count-scaled `L¹`-gap between the
   densities of `S` on `(s, t)` and `p`, plus `card κ * ε ^ 3 * #s * #t`; and
2. on every rectangle `s' ×ˢ t'` with `s' ⊆ s` and `t' ⊆ t`, the number of pairs of color `c` in
   `S'` is within `card κ * (η + ε ^ 3) * #s * #t` of `p c * (#s' * #t')`. -/
theorem exists_coupled_recoloring_abs_card_filter_colorOfPair_sub_le [Fintype κ]
    (S : PairColorSystem κ V) (hst : Disjoint s t) {η : ℝ} (hreg : S.IsRegularPair η s t)
    {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ} (hε : 0 < ε)
    (hs : Fintype.card κ + 2 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 2 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (∑ c, (#s * #t : ℝ) * |(pairColorDensity S c s t : ℝ) - p c|) / 2 +
          Fintype.card κ * ε ^ 3 * #s * #t ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          Fintype.card κ * (η + ε ^ 3) * #s * #t := by
  have : Nonempty κ := by by_contra! h; simp at hp1
  have hs0 := cast_card_pos_of_add_one_le (by linarith : (Fintype.card κ : ℝ) + 1 ≤ ε ^ 6 * #s)
  have ht0 := cast_card_pos_of_add_one_le (by linarith : (Fintype.card κ : ℝ) + 1 ≤ ε ^ 6 * #t)
  obtain ⟨hx₀, hfull, hfib⟩ := S.pairColorFn_spec hst
  obtain ⟨x, -, hedit, hdisc⟩ := exists_coupled_coloring_abs_card_filter_sub_le (s ×ˢ t)
    S.pairColorFn hp hp1 (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2)
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    (N := #s * #t) (by rw [card_product]) (a := ε ^ 3 * #s * #t)
    (mul_pos (mul_pos (pow_pos hε 3) hs0) ht0)
    (by simpa using two_mul_two_pow_mul_two_pow_add_one_mul_exp_lt hs ht)
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x,
    ?_, ?_⟩
  · have hfeq : {q ∈ s ×ˢ t | (S.recolorProduct hst x).colorOfPair q.1 q.2 ≠
        S.colorOfPair q.1 q.2} = {q ∈ s ×ˢ t | x q ≠ S.pairColorFn q} :=
      filter_congr fun q hq ↦ by
        rw [colorOfPair_recolorProduct_of_mem hst x hq, hx₀ hq, ne_eq, Option.some_inj]
    have hgap (c : κ) : |(#{q ∈ s ×ˢ t | S.pairColorFn q = c} : ℝ) - p c * #(s ×ˢ t)| =
        (#s * #t : ℝ) * |(pairColorDensity S c s t : ℝ) - p c| := by
      rw [hfull c, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos (mul_pos hs0 ht0),
        mul_comm]
    rw [hfeq]
    refine hedit.trans ?_
    simp_rw [hgap]
    linarith
  · intro c s' hs' t' ht'
    have hfeq : {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
        {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun q hq ↦ by
      rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
        Option.some_inj]
    have hd := hdisc ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
    dsimp only at hd
    rw [hfeq]
    refine (by simpa only [← Nat.cast_mul, ← card_product] using hd :
      |(#{q ∈ s' ×ˢ t' | x q = c} : ℝ) - p c * (#s' * #t')| ≤ _).trans ?_
    calc _ ≤ (∑ _c₀ : κ, η * #s * #t) + Fintype.card κ * (ε ^ 3 * #s * #t) :=
          add_le_add (sum_le_sum fun c₀ _ ↦ hfib hreg hs0 ht0 c₀ s' hs' t' ht') le_rfl
      _ = Fintype.card κ * (η + ε ^ 3) * #s * #t := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          ring

end PairColorSystem

end TauCeti
