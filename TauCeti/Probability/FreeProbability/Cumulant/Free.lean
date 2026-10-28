/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Multilinear
public import TauCeti.Probability.FreeProbability.Cumulant.Product
public import TauCeti.Probability.FreeProbability.Independence

/-!
# Freeness is the vanishing of mixed free cumulants

Let `φ : A →ₗ[R] R` be a linear functional on an algebra `A` over a commutative ring `R`, and let
`B i` be unital subalgebras of `A`. A free cumulant `κ_n(a₁, …, aₙ)` is *mixed* for the family
`(B i)` when `aⱼ ∈ B iⱼ` for labels `iⱼ` that are not all equal. For a normalised `φ`, the family is
freely independent exactly when every mixed free cumulant vanishes. This turns freeness, a
condition on centred alternating words, into the vanishing of the off-diagonal cumulants, which is
what makes cumulants additive on free families and underlies the free convolution.

The words are indexed by a finite set `s` of positions in a linear order, so that the results apply
to every subword of a word; the cumulants `κ_n` are the case `s = Finset.univ : Finset (Fin n)`.

## Main results

* `TauCeti.IsFreelyIndependent.freeCumulant_eq_zero` — for a normalised `φ` and a free family, the
  free cumulant of a word with letters in the family vanishes when the labels are not all equal.
* `TauCeti.isFreelyIndependent_of_freeCumulant_eq_zero` — if every mixed cumulant `κ_n` vanishes,
  the family is free.
* `TauCeti.isFreelyIndependent_iff_freeCumulant_eq_zero` — for a normalised `φ`, freeness is
  equivalent to the vanishing of all mixed free cumulants.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 11.16 and its
  proof via Theorem 11.12 and Proposition 11.15.
* R. Speicher, *Multiplicative functions on the lattice of non-crossing partitions and free
  convolution*, Math. Ann. 298 (1994), 611–628.
-/

public section

open Finset Function

namespace TauCeti

variable {R A ι α : Type*} [CommRing R] [Semiring A] [Algebra R A] [LinearOrder α]
  {φ : A →ₗ[R] R} {B : ι → Subalgebra R A} {s : Finset α} {ℓ : α → ι}

/-- Under the induction hypothesis that mixed free cumulants of words shorter than `s` vanish, a
noncrossing partition `π ≠ 1` of `s` with a mixed part contributes zero to the moment–cumulant
formula. -/
private theorem prod_freeCumulant_eq_zero_of_mixed
    (ih : ∀ t : Finset α, #t < #s → ∀ b : α → A, (∀ z ∈ t, b z ∈ B (ℓ z)) →
      ∀ x ∈ t, ∀ y ∈ t, ℓ x ≠ ℓ y → freeCumulant φ b t = 0)
    {b : α → A} (hb : ∀ z ∈ s, b z ∈ B (ℓ z)) {π : NoncrossingPartition s} (hπ : π ≠ ⊤)
    {X : Finset α} (hX : X ∈ π.1.parts) {u v : α} (hu : u ∈ X) (hv : v ∈ X) (huv : ℓ u ≠ ℓ v) :
    ∏ X ∈ π.1.parts, freeCumulant φ b X = 0 := by
  refine prod_eq_zero hX (ih X ?_ b (fun z hz => hb z (π.1.le hX hz)) u hu v hv huv)
  refine card_lt_card (ssubset_of_subset_of_ne (π.1.le hX) fun hXs => hπ ?_)
  exact Subtype.ext <| (Finpartition.eq_top_of_mem_parts (hXs ▸ hX)).trans
    NoncrossingPartition.coe_top.symm

/-- Let `f` be monotone on `s` and identify no two positions other than `i ≤ j`, which are adjacent
in `s`. If the join in `NC(s)` of `π` with the partition `σ_f` into the fibres of `f` is `1`, then
`s` is the union of the parts of `π` through `i` and `j`: merging these two parts gives a
noncrossing partition above `π` and `σ_f`. -/
private theorem mem_union_of_sup_comap_eq_top {f : α → α} (hf : MonotoneOn f s) {i j : α}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≤ j) (hadj : ∀ z ∈ s, z ≤ i ∨ j ≤ z)
    (hfeq : ∀ {u v}, f u = f v → u ≠ v → (u = i ∨ u = j) ∧ (v = i ∨ v = j))
    {π : NoncrossingPartition s} (hπ : π ⊔ NoncrossingPartition.comap hf ⊥ = ⊤) {z : α}
    (hz : z ∈ s) : z ∈ π.1.part i ∪ π.1.part j := by
  obtain ⟨Q, hQ, hπQ, hQi⟩ := π.2.exists_part_eq_union hi hj hij hadj
  have hiQ : ∀ {u}, u = i ∨ u = j → u ∈ Q.part i := by
    rintro u (rfl | rfl) <;> rw [hQi]
    exacts [mem_union_left _ (π.1.mem_part_self.2 hi), mem_union_right _ (π.1.mem_part_self.2 hj)]
  -- The fibres of `f` lie in the parts of `Q`.
  have hσQ : (NoncrossingPartition.comap hf ⊥ : Finpartition s) ≤ Q := by
    intro b hb
    obtain ⟨x, hx⟩ := Finpartition.nonempty_of_mem_parts _ hb
    have hxs := Finpartition.le _ hb hx
    refine ⟨Q.part x, Q.part_mem.2 hxs, fun w hw => ?_⟩
    rw [← Finpartition.part_eq_of_mem _ hb hx, NoncrossingPartition.coe_comap,
      NoncrossingPartition.coe_bot, Finpartition.part_comap_bot hxs] at hw
    obtain ⟨-, hwx⟩ := mem_filter.1 hw
    rcases eq_or_ne w x with rfl | hne
    · exact Q.mem_part_self.2 hxs
    obtain ⟨hw', hx'⟩ := hfeq hwx hne
    rw [Q.part_eq_of_mem (Q.part_mem.2 hi) (hiQ hx')]
    exact hiQ hw'
  have htop : Q = ⊤ := congrArg Subtype.val
    (top_le_iff.1 (hπ ▸ sup_le hπQ hσQ) : (⟨Q, hQ⟩ : NoncrossingPartition s) = ⊤)
  rw [← hQi, htop, Finpartition.part_eq_of_mem _ (by
    rw [Finpartition.parts_top (nonempty_of_ne_empty (ne_empty_of_mem hi)).ne_empty]
    exact mem_singleton_self s) hi]
  exact hz

/-- Collapsing a position `j` onto the position `i < j` adjacent to it in `s` is monotone on `s`,
identifies no two positions other than `i` and `j`, and makes `s` smaller. -/
private theorem collapse_spec {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i < j)
    (hadj : ∀ z ∈ s, z ≤ i ∨ j ≤ z) :
    MonotoneOn (fun z => if z = j then i else z) s ∧
      (∀ {u v}, (if u = j then i else u) = (if v = j then i else v) → u ≠ v →
        (u = i ∨ u = j) ∧ (v = i ∨ v = j)) ∧
      #(s.image fun z => if z = j then i else z) < #s :=
  ⟨fun z hz w _ hzw => by grind [hadj z hz], fun huv hne => by grind,
    card_image_le.lt_of_ne fun h => hij.ne (card_image_iff.1 h hi hj (by simp))⟩

/-- The inductive step when two adjacent letters `a i`, `a j` of a mixed word have equal labels:
grouping them into the letter `a i * a j` gives a shorter mixed word, whose cumulant is the
cumulant of `a` plus contributions of noncrossing partitions `π ≠ 1` that vanish by induction. -/
private theorem freeCumulant_eq_zero_of_label_eq
    (ih : ∀ t : Finset α, #t < #s → ∀ b : α → A, (∀ z ∈ t, b z ∈ B (ℓ z)) →
      ∀ x ∈ t, ∀ y ∈ t, ℓ x ≠ ℓ y → freeCumulant φ b t = 0)
    {a : α → A} (ha : ∀ x ∈ s, a x ∈ B (ℓ x)) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : ℓ x ≠ ℓ y) {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i < j)
    (hadj : ∀ z ∈ s, z ≤ i ∨ j ≤ z) (hℓ : ℓ i = ℓ j) : freeCumulant φ a s = 0 := by
  -- Collapse `j` onto `i`; this preserves labels and the order of the positions of `s`.
  obtain ⟨hf, hfeq, hcard⟩ := collapse_spec hi hj hij hadj
  set f : α → α := fun z => if z = j then i else z
  have hfℓ : ∀ z, ℓ (f z) = ℓ z := fun z => by by_cases h : z = j <;> simp [f, h, hℓ]
  -- The grouped word is shorter, and its letters lie in the subalgebras, since grouping preserves
  -- labels; it is mixed, so its cumulant vanishes.
  have hmem : ∀ z ∈ s.image f, fiberProd a s f z ∈ B (ℓ z) := fun z _ => by
    refine fiberProd_def a s f z ▸ Subalgebra.list_prod_mem _ (List.forall_mem_map.2 fun w hw => ?_)
    obtain ⟨hws, rfl⟩ := mem_filter.1 ((mem_sort _).1 hw)
    exact hfℓ w ▸ ha w hws
  have hzero := ih _ hcard _ hmem _ (mem_image_of_mem f hx) _ (mem_image_of_mem f hy)
    (by rwa [hfℓ, hfℓ])
  rw [freeCumulant_fiberProd_eq_sum_prod φ a hf, sum_eq_single_of_mem ⊤ (by simp) ?_] at hzero
  · rwa [← partitionCumulant_eq_prod_freeCumulant, ← freeCumulant_def] at hzero
  -- Every other `π` with `π ⊔ σ_f = 1` contributes zero: `s` is the union of its parts through `i`
  -- and `j`, and a letter of `s` whose label is not `ℓ i = ℓ j` makes one of these parts mixed.
  intro π hπ hπtop
  obtain ⟨z, hz, hzi⟩ : ∃ z ∈ s, ℓ z ≠ ℓ i := by
    by_contra! h
    exact hxy ((h x hx).trans (h y hy).symm)
  rcases mem_union.1 (mem_union_of_sup_comap_eq_top hf hi hj hij.le hadj hfeq
    (mem_filter.1 hπ).2 hz) with hz' | hz'
  · exact prod_freeCumulant_eq_zero_of_mixed ih ha hπtop (π.1.part_mem.2 hi) hz'
      (π.1.mem_part_self.2 hi) hzi
  · exact prod_freeCumulant_eq_zero_of_mixed ih ha hπtop (π.1.part_mem.2 hj) hz'
      (π.1.mem_part_self.2 hj) (hℓ ▸ hzi)

/-- The case when all adjacent labels of a word differ: centring the letters does not change the
cumulant, and every noncrossing partition has an interval part, along which the centred word
alternates, so its moment vanishes by freeness. -/
private theorem freeCumulant_eq_zero_of_isChain (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1)
    {a : α → A} (ha : ∀ x ∈ s, a x ∈ B (ℓ x)) (hs : 1 < #s)
    (halt : (s.sort.map ℓ).IsChain (· ≠ ·)) : freeCumulant φ a s = 0 := by
  set b : α → A := fun z => a z + algebraMap R A (-φ (a z)) with hb
  have hbc : ∀ z, φ (b z) = 0 := fun z => by
    simp [hb, Algebra.algebraMap_eq_smul_one, hφ]
  rw [← freeCumulant_add_algebraMap φ a hφ (fun z => -φ (a z)) hs,
    freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine sum_eq_zero fun π _ => ?_
  obtain ⟨X, hX, hint⟩ := π.2.exists_interval_mem_parts (card_pos.1 (by omega))
  have hXs := π.1.le hX
  obtain ⟨x, hx⟩ := π.1.nonempty_of_mem_parts hX
  have hne : X.sort.map (fun z => (ℓ z, b z)) ≠ [] :=
    List.ne_nil_of_mem (List.mem_map_of_mem ((mem_sort _).2 hx))
  have hzero := isFreelyIndependent_iff.1 h _ hne (by
    rw [List.map_map]
    refine isChain_map_sort_iff.2 fun u hu v hv huv hadj => isChain_map_sort_iff.1 halt u
      (hXs hu) v (hXs hv) huv fun z hz => ?_
    by_contra! hz'
    exact (hadj z (hint u hu v hv z hz hz'.1 hz'.2)).elim hz'.1.not_ge hz'.2.not_ge)
    (by simpa using fun z hz => add_mem (ha z (hXs hz)) (Subalgebra.algebraMap_mem _ _))
    (by simp [hbc])
  rw [List.map_map] at hzero
  rw [partitionMoment_def, prod_eq_zero hX hzero, mul_zero]

/-- *Free cumulants detect freeness*, the vanishing direction: if the subalgebras `B i` are freely
independent for a normalised `φ`, then the free cumulant `κ_s(a)` of a word whose letters satisfy
`a x ∈ B (ℓ x)` vanishes as soon as two of its labels differ. -/
theorem IsFreelyIndependent.freeCumulant_eq_zero (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1)
    {a : α → A} (ha : ∀ x ∈ s, a x ∈ B (ℓ x)) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : ℓ x ≠ ℓ y) : freeCumulant φ a s = 0 := by
  -- Induct on the length. If two adjacent letters have equal labels, group them into one letter:
  -- by the formula for cumulants with products as arguments, the shorter mixed cumulant is the
  -- original one plus cumulants of partitions `π ≠ 1` that vanish by induction. If all adjacent
  -- labels differ, centre the letters: every block moment of the centred word has an interval
  -- part, along which the word alternates, so it vanishes by freeness, and so does the cumulant.
  induction hn : #s using Nat.strong_induction_on generalizing s a x y with | _ n ih =>
  have ih' : ∀ t : Finset α, #t < #s → ∀ b : α → A, (∀ z ∈ t, b z ∈ B (ℓ z)) →
      ∀ x ∈ t, ∀ y ∈ t, ℓ x ≠ ℓ y → freeCumulant φ b t = 0 :=
    fun t ht b hb x hx y hy hxy => ih #t (hn ▸ ht) hb hx hy hxy rfl
  by_cases hA : ∃ i ∈ s, ∃ j ∈ s, i < j ∧ (∀ z ∈ s, z ≤ i ∨ j ≤ z) ∧ ℓ i = ℓ j
  · obtain ⟨i, hi, j, hj, hij, hadj, hℓ⟩ := hA
    exact freeCumulant_eq_zero_of_label_eq ih' ha hx hy hxy hi hj hij hadj hℓ
  · push Not at hA
    exact freeCumulant_eq_zero_of_isChain h hφ ha
      (one_lt_card.2 ⟨x, hx, y, hy, ne_of_apply_ne ℓ hxy⟩) (isChain_map_sort_iff.2 hA)

/-- *Free cumulants detect freeness*, the converse direction: if every mixed free cumulant
`κ_n(a₁, …, aₙ)`, with letters `aₖ ∈ B (ℓ k)` whose labels are not all equal, vanishes, then the
subalgebras `B i` are freely independent. No normalisation of `φ` is needed. -/
theorem isFreelyIndependent_of_freeCumulant_eq_zero
    (h : ∀ (n : ℕ) (a : Fin n → A) (ℓ : Fin n → ι), (∀ k, a k ∈ B (ℓ k)) → ∀ k k', ℓ k ≠ ℓ k' →
      freeCumulant φ a univ = 0) :
    IsFreelyIndependent φ B := by
  -- In the moment–cumulant formula for a centred alternating word, every noncrossing partition
  -- has a singleton part, whose cumulant is a centred moment, or a part containing two adjacent
  -- letters, whose labels differ; either way it contributes zero.
  rw [isFreelyIndependent_iff]
  intro w hne halt hw hc
  -- Read the word as letters `a k` with labels `ℓ k` at the positions `k : Fin w.length`.
  set a : Fin w.length → A := fun k => w[(k : ℕ)].2
  set ℓ : Fin w.length → ι := fun k => w[(k : ℕ)].1
  have hlen : w.length ≠ 0 := by simpa using hne
  have halt' : ((univ : Finset (Fin w.length)).sort.map ℓ).IsChain (· ≠ ·) := by
    rwa [Fin.sort_univ, ← List.ofFn_eq_map, List.ofFn_getElem_eq_map]
  rw [← List.ofFn_getElem_eq_map, apply_prod_ofFn_eq_sum_prod_freeCumulant φ hlen]
  refine sum_eq_zero fun π _ => ?_
  obtain ⟨X, hX, hX1 | ⟨u, hu, v, hv, huv, hadj⟩⟩ :=
    π.2.exists_mem_parts_card_eq_one_or_adjacent (univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩)
  · obtain ⟨k, rfl⟩ := card_eq_one.1 hX1
    exact prod_eq_zero hX (by rw [freeCumulant_singleton]; exact hc _ (List.getElem_mem _))
  -- Relabel the part `X`, which has two adjacent positions with distinct labels, by `Fin #X`.
  refine prod_eq_zero hX ?_
  set e := X.orderEmbOfFin rfl
  obtain ⟨k, hk⟩ : u ∈ Set.range e := by rwa [range_orderEmbOfFin]
  obtain ⟨k', hk'⟩ : v ∈ Set.range e := by rwa [range_orderEmbOfFin]
  rw [← image_orderEmbOfFin_univ X rfl, ← freeCumulant_comp_of_strictMonoOn φ
    (e.strictMono.strictMonoOn _) a]
  refine h _ (a ∘ e) (ℓ ∘ e) (fun k => hw _ (List.getElem_mem _)) k k' ?_
  simp only [comp_apply, hk, hk']
  exact isChain_map_sort_iff.1 halt' u (mem_univ u) v (mem_univ v) huv hadj

/-- *Free cumulants detect freeness*: for a normalised `φ`, the subalgebras `B i` are freely
independent exactly when every mixed free cumulant `κ_n(a₁, …, aₙ)`, with letters
`aₖ ∈ B (ℓ k)` whose labels are not all equal, vanishes. -/
theorem isFreelyIndependent_iff_freeCumulant_eq_zero (hφ : φ 1 = 1) :
    IsFreelyIndependent φ B ↔
      ∀ (n : ℕ) (a : Fin n → A) (ℓ : Fin n → ι), (∀ k, a k ∈ B (ℓ k)) → ∀ k k', ℓ k ≠ ℓ k' →
        freeCumulant φ a univ = 0 :=
  ⟨fun h _ _ _ ha k k' hk => h.freeCumulant_eq_zero hφ (fun z _ => ha z) (mem_univ k)
    (mem_univ k') hk, isFreelyIndependent_of_freeCumulant_eq_zero⟩

end TauCeti
