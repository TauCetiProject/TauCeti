/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring
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
densities, while the rest of the coloring is kept. When `(s, t)` is already `η`-regular for `S`,
coupled low-discrepancy recoloring (`TauCeti.exists_recoloring_abs_card_filter_sub_mul_card_le`)
achieves small rectangle discrepancy toward `p` while editing at most half the `L¹` density shift
plus `card κ * η * (#s * #t)` pairs on `s ×ˢ t`.

The uncoupled coloring is a random coloring of `s ×ˢ t` with distribution `p`, whose color counts
on all rectangles are simultaneously close to their means
(`TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt`). When local recolorings have been
constructed for pairs of cells of a partition `P`, ordering the cells via a key `f : P.parts → α`
into a linearly ordered type `α` glues them into one global reversal-coherent `PairColorSystem`
preserving `S` wherever `f` coincides (`TauCeti.PairColorSystem.exists_recoloring_colorOfPair_eq`).

## Main results

* `TauCeti.PairColorSystem.exists_recoloring_abs_pairColorDensity_sub_le`: a recoloring between
  `s` and `t` in which every large rectangle has color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_recoloring_isRegularPair`: a recoloring between `s` and `t`
  that makes `(s, t)` a `2ε`-regular pair with color densities within `ε` of `p`.
* `TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le`: a recoloring between
  `s` and `t` with small rectangle discrepancy toward `p` and, when `S.IsRegularPair η s t`,
  total-variation edit bound on `s ×ˢ t`.
* `TauCeti.PairColorSystem.exists_recoloring_colorOfPair_eq`: glue reversal-compatible local
  systems on ordered pairs of parts of a partition `P` along a linearly ordered key
  `f : P.parts → α`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the regular approximation lemma.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), coupled edge modification.
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

private theorem colorOfPair_recolorProduct_of_notMem {u v : V} (hs : u ∈ s → v ∉ t)
    (ht : u ∈ t → v ∉ s) : (S.recolorProduct hst x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  have h₁ : (u, v) ∉ s ×ˢ t := fun h ↦ hs (mem_product.1 h).1 (mem_product.1 h).2
  have h₂ : (v, u) ∉ s ×ˢ t := fun h ↦ ht (mem_product.1 h).2 (mem_product.1 h).1
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp [recolorProduct, h₁, h₂]

open Classical in
private theorem filter_colorOfPair_recolorProduct_eq {s' t' : Finset V} (hs' : s' ⊆ s)
    (ht' : t' ⊆ t) (d : κ) :
    {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some d} =
      {q ∈ s' ×ˢ t' | x q = d} :=
  filter_congr fun _ hq ↦ by
    rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
      Option.some_inj]

/-- **Rectangle union-bound inequality.** For `r ≥ 0` and natural numbers `m`, `n`, `k`, once
`k + 1 + r ≤ δ ^ 2 * m` and `k + 1 + r ≤ δ ^ 2 * n`, the Hoeffding union-bound quantity
`2 * (2 ^ m * 2 ^ n + r) * k * exp (-2 * (δ * m * n) ^ 2 / (m * n))` is strictly less than `1`.
Setting `r = 0` handles uncoupled rectangle recolorings, and setting `r = 1` handles coupled
rectangle recolorings with one additional stay-put event per source color. -/
private theorem two_mul_two_pow_mul_two_pow_add_mul_exp_lt_one {m n k : ℕ} {r δ : ℝ}
    (hr : 0 ≤ r) (hm : k + 1 + r ≤ δ ^ 2 * m) (hn : k + 1 + r ≤ δ ^ 2 * n) :
    2 * ((2 ^ m * 2 ^ n : ℕ) + r) * k *
      exp (-2 * (δ * m * n) ^ 2 / (m * n : ℕ)) < 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  set K : ℝ := (k : ℝ)
  have hK : 1 ≤ K := Nat.one_le_cast.2 hk
  have hm0 : (0 : ℝ) < m := pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hm) (sq_nonneg δ)
  have hn0 : (0 : ℝ) < n := pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hn) (sq_nonneg δ)
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 (Nat.cast_pos.1 hm0)
  -- Bound `2`, `2 ^ m * 2 ^ n + r`, and `K` by exponentials via `x + 1 ≤ exp x`.
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (j : ℕ) : (2 : ℝ) ^ j ≤ exp j :=
    (pow_le_pow_left₀ (by norm_num) h2 j).trans_eq (by rw [← exp_nat_mul, mul_one])
  have hrect : ((2 ^ m * 2 ^ n : ℕ) : ℝ) + r ≤ (exp m * exp n) * exp r := by
    have hA1 : (1 : ℝ) ≤ ((2 ^ m * 2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.pow_pos two_pos) (Nat.pow_pos two_pos)
    calc ((2 ^ m * 2 ^ n : ℕ) : ℝ) + r
        ≤ ((2 ^ m * 2 ^ n : ℕ) : ℝ) * (r + 1) := by nlinarith
      _ ≤ (exp m * exp n) * exp r := by
          push_cast
          gcongr
          · exact hpow m
          · exact hpow n
          · exact add_one_le_exp r
  have hKexp : K ≤ exp (K - 1) := by linarith [add_one_le_exp (K - 1)]
  have hexp : -2 * (δ * m * n) ^ 2 / ((m * n : ℕ) : ℝ) = -2 * (δ ^ 2 * m) * n := by
    push_cast
    field_simp
  calc 2 * (((2 ^ m * 2 ^ n : ℕ) : ℝ) + r) * K * exp (-2 * (δ * m * n) ^ 2 / (m * n : ℕ))
      ≤ exp 1 * ((exp m * exp n) * exp r) * exp (K - 1) * exp (-2 * (δ ^ 2 * m) * n) := by
        rw [hexp]
        gcongr
    _ = exp (m + n + K + r - 2 * (δ ^ 2 * m) * n) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        -- `2 δ² m n = (δ² m) n + m (δ² n) ≥ (K + 1 + r) (m + n) > m + n + K + r`.
        have heq : 2 * (δ ^ 2 * m) * n = (δ ^ 2 * m) * n + m * (δ ^ 2 * n) := by ring
        rw [heq]
        nlinarith [hm1, mul_le_mul_of_nonneg_right hm hn0.le,
          mul_le_mul_of_nonneg_left hn hm0.le]

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
  have hs0 : (0 : ℝ) < #s :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hs) (by positivity)
  have ht0 : (0 : ℝ) < #t :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) ht) (by positivity)
  have hub := two_mul_two_pow_mul_two_pow_add_mul_exp_lt_one (k := Fintype.card κ) (r := 0)
    (δ := ε ^ 3) le_rfl
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
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_notMem hst x, ?_⟩
  intro c s' hs' t' ht' hs's ht't
  have hpos : (0 : ℝ) < #s' * #t' :=
    mul_pos ((mul_pos hε hs0).trans_le hs's) ((mul_pos hε ht0).trans_le ht't)
  have hdev := hx ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
  -- On `s' ×ˢ t' ⊆ s ×ˢ t` the recolored system has the colors of `x`, and the color count is the
  -- density times `#s' * #t'`, since `s'` and `t'` are disjoint.
  have hcount : (#{q ∈ s' ×ˢ t' | x q = c} : ℝ) =
      pairColorDensity (S.recolorProduct hst x) c s' t' * (#s' * #t') := by
    rw [← filter_colorOfPair_recolorProduct_eq hst x hs' ht' c]
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

open Classical in
/-- Coupled recoloring on an already `η`-regular block `(s, t)`, achieving small rectangle
discrepancy toward `p` and the total-variation edit bound on `s ×ˢ t`. -/
private theorem exists_coupled_recoloring_of_isRegularPair [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {η : ℝ}
    (hη : 0 < η) (hs : Fintype.card κ + 3 ≤ η ^ 2 * #s)
    (ht : Fintype.card κ + 3 ≤ η ^ 2 * #t) (hreg : S.IsRegularPair η s t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) →
        S'.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ s' ⊆ s, ∀ t' ⊆ t, ∀ d : κ,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some d} : ℝ) - p d * (#s' * #t')| ≤
          2 * (max (Fintype.card κ) 1 : ℕ) * η * (#s * #t)) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (∑ c : κ, |(pairColorDensity S c s t : ℝ) - p c| * (#s * #t)) / 2 +
          Fintype.card κ * η * (#s * #t) := by
  classical
  have : Nonempty κ := by by_contra! h; simp at hp1
  have hs0 : (0 : ℝ) < #s :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hs) (by positivity)
  have ht0 : (0 : ℝ) < #t :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) ht) (by positivity)
  set I := ↥(s.powerset ×ˢ t.powerset)
  set Trect : I → Finset (V × V) := fun i ↦ i.1.1 ×ˢ i.1.2
  have hcardI : Fintype.card I = 2 ^ #s * 2 ^ #t := by
    simp [I, card_product, card_powerset]
  have hub := two_mul_two_pow_mul_two_pow_add_mul_exp_lt_one (m := #s) (n := #t)
    (k := Fintype.card κ) (r := 1) (δ := η) zero_le_one (by linarith) (by linarith)
  have ha : 0 < η * #s * #t := mul_pos (mul_pos hη hs0) ht0
  let x₀ : V × V → κ := fun q ↦ if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ
  have hx₀_eq {q : V × V} (hq : q ∈ s ×ˢ t) (c : κ) :
      (x₀ q = c) ↔ (S.colorOfPair q.1 q.2 = some c) := by
    have hne : q.1 ≠ q.2 := hst.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2
    simp [x₀, hne]
  have hx₀_count (c : κ) :
      (#{q ∈ s ×ˢ t | x₀ q = c} : ℝ) = (pairColorDensity S c s t : ℝ) * (#s * #t) := by
    rw [filter_congr fun q hq ↦ hx₀_eq hq c]
    exact mod_cast (pairColorDensity_mul_card_of_disjoint S c hst).symm
  have hx₀_dens (c : κ) :
      (#{q ∈ s ×ˢ t | x₀ q = c} : ℝ) / #(s ×ˢ t) = pairColorDensity S c s t := by
    rw [hx₀_count, card_product, Nat.cast_mul, mul_div_cancel_right₀ _ (mul_pos hs0 ht0).ne']
  obtain ⟨x, _, hedit, hdisc⟩ := exists_recoloring_abs_card_filter_sub_mul_card_le
    (s ×ˢ t) x₀ hp hp1 Trect
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    ha ha.le (fun i c ↦ by
      obtain ⟨hs', ht'⟩ := mem_product.1 i.2
      have hs's := mem_powerset.1 hs'
      have ht't := mem_powerset.1 ht'
      have hf : {q ∈ i.1.1 ×ˢ i.1.2 | x₀ q = c} =
          {q ∈ i.1.1 ×ˢ i.1.2 | S.colorOfPair q.1 q.2 = some c} :=
        filter_congr fun q hq ↦ hx₀_eq (product_subset_product hs's ht't hq) c
      dsimp only [Trect]
      rw [hf, hx₀_dens, card_product, Nat.cast_mul, ← mul_assoc]
      exact hreg.abs_card_filter_colorOfPair_sub_le hst hs's ht't)
    (by simpa [hcardI, card_product] using hub)
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_notMem hst x,
    fun s' hs' t' ht' d ↦ ?_, ?_⟩
  · have hqle : (Fintype.card κ : ℝ) ≤ (max (Fintype.card κ) 1 : ℕ) := by
      exact_mod_cast le_max_left _ _
    have hd := hdisc ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ d
    simp only [Trect, card_product, Nat.cast_mul] at hd
    rw [filter_colorOfPair_recolorProduct_eq hst x hs' ht' d]
    calc |(#{q ∈ s' ×ˢ t' | x q = d} : ℝ) - p d * (#s' * #t')|
        ≤ Fintype.card κ * (η * #s * #t + η * #s * #t) := hd
      _ ≤ (max (Fintype.card κ) 1 : ℕ) * (2 * η * (#s * #t)) := by nlinarith [mul_pos hs0 ht0]
      _ = 2 * (max (Fintype.card κ) 1 : ℕ) * η * (#s * #t) := by ring
  · have hf_ed : {q ∈ s ×ˢ t | (S.recolorProduct hst x).colorOfPair q.1 q.2 ≠
        S.colorOfPair q.1 q.2} = {q ∈ s ×ˢ t | x q ≠ x₀ q} :=
      filter_congr fun q hq ↦ by
        have hne : q.1 ≠ q.2 := hst.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2
        rw [colorOfPair_recolorProduct_of_mem hst x hq]
        simp [x₀, hne]
    have hL1 (c : κ) :
        |(#{q ∈ s ×ˢ t | x₀ q = c} : ℝ) - p c * #(s ×ˢ t)| =
          |(pairColorDensity S c s t : ℝ) - p c| * (#s * #t) := by
      rw [hx₀_count, card_product, Nat.cast_mul, ← sub_mul, abs_mul,
        abs_of_pos (mul_pos hs0 ht0)]
    rw [hf_ed]
    refine hedit.trans_eq ?_
    simp only [hL1]; ring

open Classical in
/-- **Coupled regular recoloring with rectangle discrepancy and edit bound.** Let `S` be a
pair-color system on a finite palette `κ`, let `s` and `t` be disjoint vertex sets with
`card κ + 3 ≤ η ^ 2 * #s` and `card κ + 3 ≤ η ^ 2 * #t`, and let `p` be a probability
distribution on `κ`. Then there is a pair-color system `S'` with `S'.rev = S.rev` agreeing with
`S` outside pairs joining `s` and `t`, whose rectangle counts on `s' ×ˢ t'` lie within
`2 * max (card κ) 1 * η * (#s * #t)` of `p d * (#s' * #t')`, and which—whenever
`S.IsRegularPair η s t`—edits at most
`(∑ c, |d_c(s, t) - p c| * (#s * #t)) / 2 + card κ * η * (#s * #t)` pairs of `s ×ˢ t`. -/
theorem exists_coupled_recoloring_abs_card_filter_sub_le [Fintype κ] (S : PairColorSystem κ V)
    (hst : Disjoint s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {η : ℝ}
    (hη : 0 < η) (hs : Fintype.card κ + 3 ≤ η ^ 2 * #s)
    (ht : Fintype.card κ + 3 ≤ η ^ 2 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) →
        S'.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ s' ⊆ s, ∀ t' ⊆ t, ∀ d : κ,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some d} : ℝ) - p d * (#s' * #t')| ≤
          2 * (max (Fintype.card κ) 1 : ℕ) * η * (#s * #t)) ∧
      (S.IsRegularPair η s t →
        (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
          (∑ c : κ, |(pairColorDensity S c s t : ℝ) - p c| * (#s * #t)) / 2 +
            Fintype.card κ * η * (#s * #t)) := by
  classical
  by_cases hreg : S.IsRegularPair η s t
  · obtain ⟨S', hrev, hagree, hdisc, hedit⟩ :=
      S.exists_coupled_recoloring_of_isRegularPair hst hp hp1 hη hs ht hreg
    exact ⟨S', hrev, hagree, hdisc, fun _ ↦ hedit⟩
  have hs0 : (0 : ℝ) < #s :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hs) (by positivity)
  have ht0 : (0 : ℝ) < #t :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) ht) (by positivity)
  set I := ↥(s.powerset ×ˢ t.powerset)
  set Trect : I → Finset (V × V) := fun i ↦ i.1.1 ×ˢ i.1.2
  have hcardI : Fintype.card I = 2 ^ #s * 2 ^ #t := by
    simp [I, card_product, card_powerset]
  have hq1 : (1 : ℝ) ≤ (max (Fintype.card κ) 1 : ℕ) := by exact_mod_cast le_max_right _ _
  have hub' := two_mul_two_pow_mul_two_pow_add_mul_exp_lt_one (m := #s) (n := #t)
    (k := Fintype.card κ) (r := 0) (δ := η) le_rfl (by linarith) (by linarith)
  obtain ⟨x, hx⟩ := exists_forall_abs_card_filter_sub_mul_card_lt hp hp1 Trect
    (N := #s * #t) (fun i ↦ by
      obtain ⟨hs', ht'⟩ := mem_product.1 i.2
      dsimp only [Trect]
      rw [card_product]
      exact Nat.mul_le_mul (card_le_card (mem_powerset.1 hs'))
        (card_le_card (mem_powerset.1 ht')))
    (mul_pos (mul_pos hη hs0) ht0) (by simpa [hcardI] using hub')
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_notMem hst x,
    fun s' hs' t' ht' d ↦ ?_, fun h ↦ absurd h hreg⟩
  have hd := (hx ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ d).le
  simp only [Trect, card_product, Nat.cast_mul] at hd
  rw [filter_colorOfPair_recolorProduct_eq hst x hs' ht' d]
  calc |(#{q ∈ s' ×ˢ t' | x q = d} : ℝ) - p d * (#s' * #t')|
      ≤ η * #s * #t := hd
    _ ≤ 2 * (max (Fintype.card κ) 1 : ℕ) * η * (#s * #t) := by
        nlinarith [mul_pos hη (mul_pos hs0 ht0)]

/-- **Keyed gluing of local pair-color systems.** Given a partition `P` of `V`, a key
`f : P.parts → α` into a linearly ordered type `α`, and local systems `T A B` with
`(T A B).rev = S.rev` whenever `f A < f B`, selecting `T A B` for `f A < f B`, `T B A` for
`f B < f A`, and `S` for `f A = f B` produces a global `R : PairColorSystem κ V` with
`R.rev = S.rev` agreeing with `T A B` on `A ×ˢ B` whenever `f A < f B` and with `S` whenever
`f A = f B`. -/
theorem exists_recoloring_colorOfPair_eq {α : Type*} [LinearOrder α] [Fintype V] [DecidableEq V]
    (S : PairColorSystem κ V) (P : Finpartition (univ : Finset V))
    (f : P.parts → α) (T : P.parts → P.parts → PairColorSystem κ V)
    (hrev : ∀ A B, f A < f B → (T A B).rev = S.rev) :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      (∀ A B : P.parts, f A < f B → ∀ x ∈ A.1, ∀ y ∈ B.1,
        R.colorOfPair x y = (T A B).colorOfPair x y) ∧
      (∀ A B : P.parts, f A = f B → ∀ x ∈ A.1, ∀ y ∈ B.1,
        R.colorOfPair x y = S.colorOfPair x y) := by
  classical
  let cell (x : V) : P.parts := ⟨P.part x, P.part_mem.2 (mem_univ x)⟩
  have hcell (A : P.parts) {x : V} (hx : x ∈ A.1) : cell x = A :=
    Subtype.ext (P.part_eq_of_mem A.2 hx)
  -- Ordered pairs choose the local system indexed by the smaller key; equal keys preserve `S`.
  let R : PairColorSystem κ V :=
    { color := fun p ↦
        let A := cell p.1.1
        let B := cell p.1.2
        if f A < f B then (T A B).color p
        else if f B < f A then (T B A).color p
        else S.color p
      rev := S.rev
      rev_involutive := S.rev_involutive
      color_rev := fun p ↦ by
        obtain ⟨⟨u, v⟩, huv⟩ := p
        by_cases h₁ : f (cell u) < f (cell v)
        · have h₂ : ¬ f (cell v) < f (cell u) := lt_asymm h₁
          simpa [h₁, h₂, hrev _ _ h₁] using (T (cell u) (cell v)).color_rev ⟨(u, v), huv⟩
        · by_cases h₂ : f (cell v) < f (cell u)
          · simpa [h₁, h₂, hrev _ _ h₂] using (T (cell v) (cell u)).color_rev ⟨(u, v), huv⟩
          · simpa [h₁, h₂] using S.color_rev ⟨(u, v), huv⟩ }
  refine ⟨R, rfl, fun A B hAB x hx y hy ↦ ?_, fun A B hAB x hx y hy ↦ ?_⟩
  · by_cases hxy : x = y
    · simp [hxy]
    · simp [colorOfPair_of_ne _ hxy, R, hcell A hx, hcell B hy, hAB]
  · by_cases hxy : x = y
    · simp [hxy]
    · simp [colorOfPair_of_ne _ hxy, R, hcell A hx, hcell B hy, hAB]

end PairColorSystem

end TauCeti
