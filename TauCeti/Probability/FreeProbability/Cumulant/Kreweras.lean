/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Interlace
public import TauCeti.Probability.FreeProbability.Cumulant.Free

/-!
# Moments and free cumulants of products of free families

Let `φ : A →ₗ[R] R` be a normalised linear functional, and let `(aₓ)` and `(bₓ)` be two words
indexed by a finite set `s = {x₁ < ⋯ < xₙ}` of positions, with letters in two freely independent
subalgebras. The moments of the alternating product `a_{x₁} b_{x₁} ⋯ a_{xₙ} b_{xₙ}` are given by
the free cumulants of the first word and the block moments of the second, glued along the
Kreweras complement:

`φ (a_{x₁} b_{x₁} ⋯ a_{xₙ} b_{xₙ}) = ∑_{π ∈ NC(s)} κ_π(a) φ_{K(π)}(b)`.

Apply the moment–cumulant formula to the interlaced word `a_{x₁}, b_{x₁}, …, a_{xₙ}, b_{xₙ}`.
By freeness, only noncrossing partitions of the interlaced positions that do not mix the two words
contribute; these are the interlaced partitions of a noncrossing partition `π` of the `a`-letters
and a noncrossing partition `π'` of the `b`-letters with `π' ≤ K(π)`. Summing the cumulants of
`b` over `π' ≤ K(π)` gives the block moment `φ_{K(π)}(b)`.

The free cumulants of the products `a₁ b₁, …, aₙ bₙ` are given by the free cumulants of both
words, glued along the Kreweras complement on `NC(n)`:

`κ_n(a₁ b₁, …, aₙ bₙ) = ∑_{π ∈ NC(n)} κ_π(a) κ_{K(π)}(b)`.

The products are the letters of the interlaced word grouped along the pairs of a position and the
bar after it, so by the formula for cumulants with products as arguments the left side is the sum
of the cumulants of the noncrossing partitions of the interlaced positions whose join with these
pairs is `1`. Again only the interlaced partitions of `π` and `π' ≤ K(π)` contribute, and the join
condition says `π ⊔ π' = 1`, which holds exactly for `π' = K(π)`
(`TauCeti.NoncrossingPartition.sup_eq_top_iff_eq_kreweras`).

No traciality is needed. For `s = ∅`, respectively `n = 0`, both sides are `1`.

## Main results

* `TauCeti.IsFreelyIndependent.apply_prod_mul_eq_sum_partitionCumulant_mul_partitionMoment` —
  `φ (a_{x₁} b_{x₁} ⋯ a_{xₙ} b_{xₙ}) = ∑_{π ∈ NC(s)} κ_π(a) φ_{K(π)}(b)` for words with letters in
  two distinct members of a free family of subalgebras.
* `TauCeti.IsFreelyIndependent.apply_prod_ofFn_mul_eq_sum_partitionCumulant_mul_partitionMoment`
  — the same formula for `φ (a₁ b₁ ⋯ aₙ bₙ)`, summing over `NC(n)`.
* `TauCeti.IsFreelyIndependent.freeCumulant_mul_eq_sum_partitionCumulant_mul_partitionCumulant`
  — `κ_n(a₁ b₁, …, aₙ bₙ) = ∑_{π ∈ NC(n)} κ_π(a) κ_{K(π)}(b)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 14.4.
* A. Nica, R. Speicher, *On the multiplication of free N-tuples of noncommutative random
  variables*, Amer. J. Math. 118 (1996), 799–837.
-/

public section

open Finset

namespace TauCeti

variable {R A ι α : Type*} [CommRing R] [Semiring A] [Algebra R A] [LinearOrder α]
  {φ : A →ₗ[R] R} {B : ι → Subalgebra R A} {s : Finset α}

/-- The interlaced word of `a` and `b`: the letter `a x` at the position `(x, false)` and the letter
`b x` at the bar `(x, true)` after it. -/
private def interlaceWord (a b : α → A) (p : α ×ₗ Bool) : A :=
  bif (ofLex p).2 then b (ofLex p).1 else a (ofLex p).1

/-- Grouping the interlaced word along the pairs of a position and the bar after it gives the word
of products `a x * b x`. -/
private theorem fiberProd_interlaceWord (a b : α → A) {x : α} (hx : x ∈ s) :
    fiberProd (interlaceWord a b) s.interlace (fun p => (ofLex p).1) x = a x * b x := by
  have hfib : {p ∈ s.interlace | (ofLex p).1 = x} = {toLex (x, false), toLex (x, true)} := by
    ext p
    obtain ⟨⟨y, c⟩, rfl⟩ := toLex.surjective p
    simp only [mem_filter, mem_interlace, ofLex_toLex, mem_insert, mem_singleton]
    cases c <;> simp +contextual [hx]
  rw [fiberProd_def, hfib, sort_pair _ (show toLex (x, false) ≤ toLex (x, true) from
      Prod.Lex.toLex_le_toLex.2 (Or.inr ⟨rfl, Bool.false_le _⟩))
    (fun h => Bool.noConfusion (Prod.mk.inj (toLex.injective h)).2)]
  simp [interlaceWord]

/-- The product of the interlaced word along the interlaced positions of `s` is the product of the
letters `a x * b x` along `s`. -/
private theorem prod_map_sort_interlace (a b : α → A) :
    (s.interlace.sort.map (interlaceWord a b)).prod = (s.sort.map fun x => a x * b x).prod := by
  -- Group the interlaced positions along their first coordinate.
  rw [prod_map_sort_eq_prod_map_sort_image (Prod.Lex.monotone_fst_ofLex.monotoneOn _),
    image_fst_interlace]
  exact congrArg List.prod (List.map_congr_left fun x hx =>
    (fiberProd_def _ _ _ x).symm.trans (fiberProd_interlaceWord a b ((mem_sort _).1 hx)))

/-- The free cumulant of the interlaced word along a set of positions placed on one sheet is the
free cumulant of the corresponding word. -/
private theorem freeCumulant_interlaceWord_image (a b : α → A) (β : Bool) (X : Finset α) :
    freeCumulant φ (interlaceWord a b) (X.image fun x => toLex (x, β)) =
      freeCumulant φ (bif β then b else a) X := by
  rw [← freeCumulant_comp_of_strictMonoOn φ
    (fun _ _ _ _ h => Prod.Lex.toLex_lt_toLex.2 (Or.inl h))]
  congr 1
  funext x
  cases β <;> simp [interlaceWord]

/-- If the letters of `a` and `b` lie in two distinct members of a free family, a noncrossing
partition of the interlaced positions contributes to the moment–cumulant formula of the interlaced
word only if none of its parts meets both the positions and the bars. -/
private theorem forall_mem_part_snd_eq_of_prod_ne_zero (h : IsFreelyIndependent φ B)
    (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : α → A} (ha : ∀ x ∈ s, a x ∈ B i)
    (hb : ∀ x ∈ s, b x ∈ B j) {σ : Finpartition s.interlace}
    (hσ : ∏ C ∈ σ.parts, freeCumulant φ (interlaceWord a b) C ≠ 0) :
    ∀ p ∈ s.interlace, ∀ q ∈ σ.part p, (ofLex q).2 = (ofLex p).2 := by
  intro p hp q hq
  by_contra hne
  refine hσ (prod_eq_zero (σ.part_mem.2 hp) ?_)
  -- Label the interlaced positions by `i` on the positions and `j` on the bars.
  refine h.freeCumulant_eq_zero (ℓ := fun p => bif (ofLex p).2 then j else i) hφ
    (fun z hz => ?_) (σ.mem_part_self.2 hp) hq ?_
  · have hzs := mem_interlace.1 (σ.part_subset p hz)
    unfold interlaceWord
    cases (ofLex z).2
    exacts [ha _ hzs, hb _ hzs]
  · revert hne
    cases (ofLex p).2 <;> cases (ofLex q).2 <;> simp [hij, hij.symm]

/-- *Moments of products of free families*: if the letters of `a` and `b` lie in two distinct
members `B i`, `B j` of a free family of subalgebras, for a normalised `φ`, then
`φ (a_{x₁} b_{x₁} ⋯ a_{xₙ} b_{xₙ}) = ∑_{π ∈ NC(s)} κ_π(a) φ_{K(π)}(b)` for `s = {x₁ < ⋯ < xₙ}`,
where `K(π)` is the Kreweras complement of `π`. -/
theorem IsFreelyIndependent.apply_prod_mul_eq_sum_partitionCumulant_mul_partitionMoment
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : α → A}
    (ha : ∀ x ∈ s, a x ∈ B i) (hb : ∀ x ∈ s, b x ∈ B j) :
    φ (s.sort.map fun x => a x * b x).prod =
      ∑ π : NoncrossingPartition s,
        partitionCumulant φ a π * partitionMoment φ b (NoncrossingPartition.kreweras π).1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [Fintype.sum_subsingleton _ ⊥, NoncrossingPartition.kreweras_bot,
      Subsingleton.elim (⊤ : NoncrossingPartition (∅ : Finset α)) ⊥]
    simp [hφ, partitionMoment_bot]
  -- Expand the right-hand side over the pairs `(π, π')` with `π' ≤ K(π)`.
  have hR : ∑ π : NoncrossingPartition s,
      partitionCumulant φ a π * partitionMoment φ b (NoncrossingPartition.kreweras π).1 =
        ∑ x ∈ univ.sigma fun π : NoncrossingPartition s => Iic (NoncrossingPartition.kreweras π),
          (∏ X ∈ x.1.1.parts, freeCumulant φ a X) * ∏ X ∈ x.2.1.parts, freeCumulant φ b X := by
    rw [sum_sigma]
    refine sum_congr rfl fun π _ => ?_
    rw [← sum_Iic_partitionCumulant, mul_sum, partitionCumulant_eq_prod_freeCumulant]
    simp_rw [partitionCumulant_eq_prod_freeCumulant]
  -- Expand the left-hand side by the moment–cumulant formula for the interlaced word, and match
  -- the pairs `(π, π')` with the noncrossing partitions of the interlaced positions that do not
  -- mix the two words; the others contribute zero by freeness.
  rw [hR, ← prod_map_sort_interlace a b,
    apply_prod_eq_sum_prod_freeCumulant φ _
      (let ⟨x, hx⟩ := hs; ⟨toLex (x, false), toLex_mem_interlace.2 hx⟩)]
  have hval (P Q : Finpartition s) :
      (∏ X ∈ P.parts, freeCumulant φ a X) * ∏ X ∈ Q.parts, freeCumulant φ b X =
        ∏ C ∈ (P.interlace Q).parts, freeCumulant φ (interlaceWord a b) C := by
    simp only [Finpartition.prod_parts_interlace, freeCumulant_interlaceWord_image,
      Bool.cond_false, Bool.cond_true]
  have hle : ∀ x ∈ univ.sigma fun π : NoncrossingPartition s => Iic π.kreweras,
      x.2.1 ≤ x.1.1.kreweras := fun x hx => by
    rw [← NoncrossingPartition.coe_kreweras, Subtype.coe_le_coe]
    exact mem_Iic.1 (mem_sigma.1 hx).2
  symm
  refine sum_bij_ne_zero (fun x hx _ => ⟨x.1.1.interlace x.2.1,
      Finpartition.isNoncrossing_interlace_iff.2 ⟨x.1.2, x.2.2, hle x hx⟩⟩)
    (fun _ _ _ => mem_univ _) (fun x _ _ y _ _ hxy => ?_) (fun σ _ hσ => ?_) (fun x _ _ => ?_)
  · obtain ⟨hP, hQ⟩ := Finpartition.interlace_inj.1 (congrArg Subtype.val hxy)
    exact Sigma.ext (Subtype.ext hP) (heq_of_eq (Subtype.ext hQ))
  · obtain ⟨P, Q, hPQ⟩ := Finpartition.exists_eq_interlace
      (forall_mem_part_snd_eq_of_prod_ne_zero h hφ hij ha hb hσ)
    obtain ⟨hP, hQ, hK⟩ := Finpartition.isNoncrossing_interlace_iff.1 (hPQ ▸ σ.2)
    refine ⟨⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩, mem_sigma.2 ⟨mem_univ _, mem_Iic.2 ?_⟩,
      (hval P Q).trans_ne (hPQ ▸ hσ), Subtype.ext hPQ.symm⟩
    rwa [← Subtype.coe_le_coe, NoncrossingPartition.coe_kreweras]
  · exact hval _ _

/-- *Moments of products of free families*, for words `a₁, …, aₙ` and `b₁, …, bₙ` with letters in
two distinct members `B i`, `B j` of a free family of subalgebras and a normalised `φ`:
`φ (a₁ b₁ ⋯ aₙ bₙ) = ∑_{π ∈ NC(n)} κ_π(a) φ_{K(π)}(b)`. -/
theorem IsFreelyIndependent.apply_prod_ofFn_mul_eq_sum_partitionCumulant_mul_partitionMoment
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {n : ℕ}
    {a b : Fin n → A} (ha : ∀ k, a k ∈ B i) (hb : ∀ k, b k ∈ B j) :
    φ (List.ofFn fun k => a k * b k).prod =
      ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        partitionCumulant φ a π * partitionMoment φ b (NoncrossingPartition.kreweras π).1 := by
  rw [← h.apply_prod_mul_eq_sum_partitionCumulant_mul_partitionMoment hφ hij
    (fun k _ => ha k) (fun k _ => hb k), Fin.sort_univ, List.ofFn_eq_map]

/-- *Free cumulants of products of free families*: if the letters of `a` and `b` lie in two
distinct members `B i`, `B j` of a free family of subalgebras, for a normalised `φ`, then
`κ_n(a₁ b₁, …, aₙ bₙ) = ∑_{π ∈ NC(n)} κ_π(a) κ_{K(π)}(b)`, where `K(π)` is the Kreweras complement
of `π`. For `n = 0` both sides are `1`. -/
theorem IsFreelyIndependent.freeCumulant_mul_eq_sum_partitionCumulant_mul_partitionCumulant
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {n : ℕ}
    {a b : Fin n → A} (ha : ∀ k, a k ∈ B i) (hb : ∀ k, b k ∈ B j) :
    freeCumulant φ (fun k => a k * b k) univ =
      ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        partitionCumulant φ a π * partitionCumulant φ b (NoncrossingPartition.kreweras π) := by
  have hf : MonotoneOn (fun p : Fin n ×ₗ Bool => (ofLex p).1) (univ : Finset (Fin n)).interlace :=
    Prod.Lex.monotone_fst_ofLex.monotoneOn _
  -- Expand the cumulant of the products as a cumulant of the interlaced word `a₁, b₁, …, aₙ, bₙ`
  -- with the letters grouped along the pairs `{(k, false), (k, true)}`: a sum over the noncrossing
  -- partitions `σ` of the interlaced positions whose join with these pairs is `1`.
  have hL : freeCumulant φ (fun k => a k * b k) univ =
      ∑ σ : NoncrossingPartition (univ : Finset (Fin n)).interlace with
        σ ⊔ NoncrossingPartition.comap hf ⊥ = ⊤,
        ∏ C ∈ σ.1.parts, freeCumulant φ (interlaceWord a b) C := by
    rw [← freeCumulant_fiberProd_eq_sum_prod φ _ hf, image_fst_interlace]
    exact freeCumulant_congr φ fun k _ => (fiberProd_interlaceWord a b (mem_univ k)).symm
  have hval (P Q : Finpartition (univ : Finset (Fin n))) :
      (∏ X ∈ P.parts, freeCumulant φ a X) * ∏ X ∈ Q.parts, freeCumulant φ b X =
        ∏ C ∈ (P.interlace Q).parts, freeCumulant φ (interlaceWord a b) C := by
    simp only [Finpartition.prod_parts_interlace, freeCumulant_interlaceWord_image,
      Bool.cond_false, Bool.cond_true]
  simp_rw [hL, partitionCumulant_eq_prod_freeCumulant, hval]
  -- By freeness only the partitions `σ` that do not mix the two words contribute. These are the
  -- interlaced partitions of a noncrossing `π` and a noncrossing `π' ≤ K(π)`, and the join
  -- condition says that `π ⊔ π' = 1`, that is, `π' = K(π)`.
  symm
  refine sum_bij_ne_zero (fun π _ _ => ⟨π.1.interlace (NoncrossingPartition.kreweras π).1,
      Finpartition.isNoncrossing_interlace_iff.2
        ⟨π.2, (NoncrossingPartition.kreweras π).2, (NoncrossingPartition.coe_kreweras π).le⟩⟩)
    (fun π _ _ => mem_filter.2 ⟨mem_univ _,
      (NoncrossingPartition.interlace_sup_comap_bot_eq_top_iff (Q := π.kreweras) _ hf).2
        (NoncrossingPartition.sup_kreweras_eq_top π)⟩)
    (fun π _ _ π' _ _ hππ' => Subtype.ext
      (Finpartition.interlace_inj.1 (congrArg Subtype.val hππ')).1)
    (fun σ hσ hσ0 => ?_) (fun _ _ _ => rfl)
  obtain ⟨P, Q, hPQ⟩ := Finpartition.exists_eq_interlace
    (forall_mem_part_snd_eq_of_prod_ne_zero h hφ hij (fun k _ => ha k) (fun k _ => hb k) hσ0)
  obtain ⟨hP, hQ, hK⟩ := Finpartition.isNoncrossing_interlace_iff.1 (hPQ ▸ σ.2)
  have hσ' : σ = ⟨P.interlace Q, hPQ ▸ σ.2⟩ := Subtype.ext hPQ
  have htop := (mem_filter.1 hσ).2
  rw [hσ', NoncrossingPartition.interlace_sup_comap_bot_eq_top_iff (P := ⟨P, hP⟩) (Q := ⟨Q, hQ⟩),
    NoncrossingPartition.sup_eq_top_iff_eq_kreweras
      (by rwa [← Subtype.coe_le_coe, NoncrossingPartition.coe_kreweras])] at htop
  refine ⟨⟨P, hP⟩, mem_univ _, ?_, ?_⟩
  · rw [hσ'] at hσ0
    rwa [← htop]
  · rw [hσ']
    exact Subtype.ext (congrArg P.interlace (congrArg Subtype.val htop).symm)

end TauCeti
