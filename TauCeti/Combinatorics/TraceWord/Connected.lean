/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TraceWord.Counting
public import TauCeti.Data.Fintype.SmallRange

/-!
# Connected pairs of trace words

In the moment expansion of the covariance of two matrix traces `trace (H ^ k₁)` and
`trace (H ^ k₂)` with independent centered entries, pairs of closed walks `(w₁, w₂)` whose
unordered cyclic edge sets are disjoint cancel by independence, while pairs whose combined edge
multiset contains a singleton edge vanish by centering. Every remaining pair shares at least one
unordered cyclic edge and traverses each unordered cyclic edge at least twice across the pair.

Concatenating two walks at a common vertex gives a walk of `k₁ + k₂` steps visiting at most
`(k₁ + k₂) / 2 + 1` vertices. Equality `#(V₁ ∪ V₂) = (k₁ + k₂) / 2 + 1` cannot occur: saturating
the path vertex bound `card V = card N + 1` equips the visited vertices with a `ℤ/2ℤ`-valued
labeling that flips exclusively across a chosen nonloop edge, forcing each closed walk `w₁` and
`w₂` to traverse their shared edge an even—hence at least twice—number of times, which requires at
least `4 + 2 * ((k₁ + k₂) / 2 - 1) > k₁ + k₂` steps. Therefore a connected singleton-free pair
visits at most `(k₁ + k₂) / 2` vertices overall, losing a full factor of `n` compared with two
independent leading walks and yielding `O(n⁻²)` variance bounds for normalized traces.

## Main results

* `TauCeti.two_mul_card_sum_cyclic_edges_le_of_no_singleton_edge`: a pair of cyclic words with no
  singleton unordered edge across `Fin k₁ ⊕ Fin k₂` uses at most `(k₁ + k₂) / 2` distinct
  unordered edges.
* `TauCeti.card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_edge`: if two cyclic
  words of lengths `k₁` and `k₂` share an unordered cyclic edge and have no singleton unordered
  edge across `Fin k₁ ⊕ Fin k₂`, their union visits at most `(k₁ + k₂) / 2` vertices.
* `TauCeti.card_filter_shared_edge_and_no_singleton_edge_le`: over a nonempty alphabet `β`, at
  most `|β|^((k₁ + k₂) / 2) * ((k₁ + k₂) / 2)^(k₁ + k₂)` word pairs share an unordered cyclic
  edge and have no singleton unordered edge across the pair.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.4, proof of Lemma 2.1.7.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.3.4.
-/

public section

open Finset

namespace TauCeti

variable {α : Type*} [DecidableEq α]

/-- When an `n`-step path visits `1 + #N` vertices (attaining the path tree bound), any nonloop
unordered pair `e₀` induces a vertex labeling whose parity changes exclusively across steps with
unordered edge `e₀`. -/
private theorem exists_mod_two_color_of_card_image_eq (p : ℕ → α) (n : ℕ) (e₀ : Sym2 α)
    (he₀ : ∀ x, s(x, x) ≠ e₀)
    (hv : #((range (n + 1)).image p) =
      #(((range n).filter fun r ↦ p r ≠ p (r + 1)).image fun r ↦ s(p r, p (r + 1))) + 1) :
    ∃ c : α → ℕ, ∀ r < n,
      (c (p r) + c (p (r + 1))) % 2 = if s(p r, p (r + 1)) = e₀ then 1 else 0 := by
  induction n with
  | zero => exact ⟨fun _ ↦ 0, by simp⟩
  | succ n ih =>
    set Vn := (range (n + 1)).image p
    set Vn1 := (range (n + 2)).image p
    set Nn := ((range n).filter fun r ↦ p r ≠ p (r + 1)).image fun r ↦ s(p r, p (r + 1))
    set Nn1 := ((range (n + 1)).filter fun r ↦ p r ≠ p (r + 1)).image fun r ↦ s(p r, p (r + 1))
    have hle : #Vn ≤ #Nn + 1 := card_image_range_le_card_nonloop_edges_add_one p n
    have hNsub : Nn ⊆ Nn1 := image_subset_image (filter_subset_filter _ (range_mono (by omega)))
    have hNle : #Nn ≤ #Nn1 := card_le_card hNsub
    have hVstep : Vn1 = insert (p (n + 1)) Vn := by simp [Vn, Vn1, range_add_one]
    by_cases hmem : p (n + 1) ∈ Vn
    · have hVeq : #Vn1 = #Vn := by rw [hVstep, insert_eq_of_mem hmem]
      obtain ⟨c, hc⟩ := ih (by omega)
      refine ⟨c, fun r hr ↦ ?_⟩
      by_cases hlt : r < n
      · exact hc r hlt
      · obtain rfl : r = n := by omega
        by_cases hloop : p r = p (r + 1)
        · simp only [← hloop, he₀ (p r), ↓reduceIte]
          omega
        · have hNeq : Nn = Nn1 := eq_of_subset_of_card_le hNsub (by omega)
          have hin : s(p r, p (r + 1)) ∈ Nn := by
            rw [hNeq]
            exact mem_image.mpr ⟨r, mem_filter.mpr ⟨mem_range.mpr (by omega), hloop⟩, rfl⟩
          obtain ⟨q, hqN, hqe⟩ := mem_image.mp hin
          have hql : q < r := mem_range.mp (mem_filter.mp hqN).1
          have hsum : c (p r) + c (p (r + 1)) = c (p q) + c (p (q + 1)) := by
            rcases Sym2.eq_iff.mp hqe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, add_comm]
          rw [hsum, ← hqe, hc q hql]
    · have hloop : p n ≠ p (n + 1) := fun h ↦
        hmem (mem_image.mpr ⟨n, mem_range.mpr (by omega), h⟩)
      have hnotN : s(p n, p (n + 1)) ∉ Nn := fun hin ↦ by
        obtain ⟨q, hqN, hqe⟩ := mem_image.mp hin
        have hql : q < n := mem_range.mp (mem_filter.mp hqN).1
        have hm : p (n + 1) ∈ s(p q, p (q + 1)) := by rw [hqe]; exact Sym2.mem_mk_right _ _
        rcases Sym2.mem_iff.mp hm with h | h
        · exact hmem (mem_image.mpr ⟨q, mem_range.mpr (by omega), h.symm⟩)
        · exact hmem (mem_image.mpr ⟨q + 1, mem_range.mpr (by omega), h.symm⟩)
      have hNcard : #Nn1 = #Nn + 1 := by
        simp [Nn, Nn1, range_add_one, filter_insert, hloop, hnotN]
      have hVcard : #Vn1 = #Vn + 1 := by rw [hVstep, card_insert_of_notMem hmem]
      obtain ⟨c, hc⟩ := ih (by omega)
      refine ⟨Function.update c (p (n + 1))
        (c (p n) + if s(p n, p (n + 1)) = e₀ then 1 else 0), fun r hr ↦ ?_⟩
      by_cases hlt : r < n
      · have hpr : p r ≠ p (n + 1) := fun h ↦
          hmem (mem_image.mpr ⟨r, mem_range.mpr (by omega), h⟩)
        have hpr1 : p (r + 1) ≠ p (n + 1) := fun h ↦
          hmem (mem_image.mpr ⟨r + 1, mem_range.mpr (by omega), h⟩)
        simpa only [Function.update_of_ne hpr, Function.update_of_ne hpr1] using hc r hlt
      · obtain rfl : r = n := by omega
        simp only [Function.update_of_ne hloop, Function.update_self]
        split_ifs <;> omega

/-- If `c` flips parity exclusively across steps with unordered edge `e₀`, any closed walk
traverses `e₀` an even number of times. -/
private theorem card_filter_cyclic_edge_mod_two_eq_zero {k : ℕ} (w : Fin k → α) (c : α → ℕ)
    (e₀ : Sym2 α)
    (hc : ∀ i, (c (w i) + c (w (finRotate k i))) % 2 =
      if s(w i, w (finRotate k i)) = e₀ then 1 else 0) :
    #{i | s(w i, w (finRotate k i)) = e₀} % 2 = 0 := by
  have h1 (i : Fin k) : (if s(w i, w (finRotate k i)) = e₀ then 1 else 0) =
      (c (w i) + c (w (finRotate k i))) % 2 := (hc i).symm
  rw [card_filter]
  simp_rw [h1]
  rw [← sum_nat_mod, sum_add_distrib, Equiv.sum_comp (finRotate k) (fun i ↦ c (w i))]
  omega

private theorem fin_ofNat_add_step {k : ℕ} (a₀ : Fin (k + 1)) (r : ℕ) :
    Fin.ofNat (k + 1) (a₀.val + (r + 1)) =
      finRotate (k + 1) (Fin.ofNat (k + 1) (a₀.val + r)) := by
  rw [finRotate_apply]
  apply Fin.ext
  simp [Fin.val_add, Fin.ofNat_eq_cast, ← Nat.add_assoc, Nat.add_mod]

private theorem exists_lt_fin_ofNat_add_eq {k : ℕ} (a₀ i : Fin (k + 1)) :
    ∃ r < k + 1, Fin.ofNat (k + 1) (a₀.val + r) = i := by
  by_cases hia : a₀.val ≤ i.val
  · refine ⟨i.val - a₀.val, by omega, ?_⟩
    apply Fin.ext
    simp [Fin.ofNat_eq_cast, Nat.add_sub_of_le hia]
  · refine ⟨i.val + (k + 1) - a₀.val, by omega, ?_⟩
    apply Fin.ext
    have hsum : a₀.val + (i.val + (k + 1) - a₀.val) = i.val + (k + 1) := by omega
    simp [Fin.ofNat_eq_cast, hsum, Nat.mod_eq_of_lt i.isLt]

/-- Two cyclic walks sharing a vertex `w₁ a₀ = w₂ b₀` concatenate into a walk of `k₁ + k₂` steps
whose visited vertices are `image w₁ ∪ image w₂` and whose steps cover all cyclic steps of `w₁`
and `w₂` without introducing any new nonloop edges. -/
private theorem exists_concat_path_of_eq {k₁ k₂ : ℕ} (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α)
    (a₀ : Fin k₁) (b₀ : Fin k₂) (hab : w₁ a₀ = w₂ b₀) :
    ∃ p : ℕ → α,
      (range (k₁ + k₂ + 1)).image p = univ.image w₁ ∪ univ.image w₂ ∧
      (((range (k₁ + k₂)).filter fun r ↦ p r ≠ p (r + 1)).image fun r ↦ s(p r, p (r + 1))) ⊆
        univ.image (Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
          (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j)))) ∧
      (∀ i, ∃ r < k₁ + k₂, p r = w₁ i ∧ p (r + 1) = w₁ (finRotate k₁ i)) ∧
      (∀ j, ∃ r < k₁ + k₂, p r = w₂ j ∧ p (r + 1) = w₂ (finRotate k₂ j)) := by
  cases k₁ with
  | zero => exact Fin.elim0 a₀
  | succ k₁ =>
    cases k₂ with
    | zero => exact Fin.elim0 b₀
    | succ k₂ =>
      let idx₁ (r : ℕ) : Fin (k₁ + 1) := Fin.ofNat (k₁ + 1) (a₀.val + r)
      let idx₂ (r : ℕ) : Fin (k₂ + 1) := Fin.ofNat (k₂ + 1) (b₀.val + r)
      let p (r : ℕ) : α := if r ≤ k₁ + 1 then w₁ (idx₁ r) else w₂ (idx₂ (r - (k₁ + 1)))
      have hseam : p (k₁ + 1) = w₂ (idx₂ 0) := by
        have ha : idx₁ (k₁ + 1) = a₀ := Fin.ext (by
          simp [idx₁, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt a₀.isLt])
        have hb : idx₂ 0 = b₀ := Fin.ext (by simp [idx₂, Fin.ofNat_eq_cast])
        simp [p, ha, hb, hab]
      have hidx₁_step (r : ℕ) : idx₁ (r + 1) = finRotate (k₁ + 1) (idx₁ r) :=
        fin_ofNat_add_step a₀ r
      have hidx₂_step (r : ℕ) : idx₂ (r + 1) = finRotate (k₂ + 1) (idx₂ r) :=
        fin_ofNat_add_step b₀ r
      have hstep₁ (r : ℕ) (hr : r < k₁ + 1) :
          p r = w₁ (idx₁ r) ∧ p (r + 1) = w₁ (finRotate (k₁ + 1) (idx₁ r)) := by
        have h1 : r ≤ k₁ + 1 := by omega
        have h2 : r + 1 ≤ k₁ + 1 := by omega
        simp [p, h1, h2, hidx₁_step]
      have hstep₂ (s : ℕ) :
          p (k₁ + 1 + s) = w₂ (idx₂ s) ∧
            p (k₁ + 1 + s + 1) = w₂ (finRotate (k₂ + 1) (idx₂ s)) := by
        rcases eq_or_ne s 0 with rfl | hs
        · refine ⟨hseam, ?_⟩
          have h2 : ¬ (k₁ + 1 + 1 ≤ k₁ + 1) := by omega
          simpa [p, h2] using congrArg w₂ (hidx₂_step 0)
        · have h1 : ¬ (k₁ + 1 + s ≤ k₁ + 1) := by omega
          have h2 : ¬ (k₁ + 1 + s + 1 ≤ k₁ + 1) := by omega
          have hsub : k₁ + 1 + s + 1 - (k₁ + 1) = s + 1 := by omega
          simp [p, h1, h2, hsub, hidx₂_step]
      refine ⟨p, ?_, ?_, fun i ↦ ?_, fun j ↦ ?_⟩
      · ext x
        simp only [mem_image, mem_range, mem_union, mem_univ, true_and]
        constructor
        · rintro ⟨r, -, rfl⟩
          by_cases hle : r ≤ k₁ + 1
          · exact Or.inl ⟨idx₁ r, by simp [p, hle]⟩
          · exact Or.inr ⟨idx₂ (r - (k₁ + 1)), by simp [p, hle]⟩
        · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
          · obtain ⟨r, hr, hi⟩ := exists_lt_fin_ofNat_add_eq a₀ i
            exact ⟨r, by omega, (hstep₁ r hr).1.trans (congrArg w₁ hi)⟩
          · obtain ⟨s, hs, hj⟩ := exists_lt_fin_ofNat_add_eq b₀ j
            exact ⟨k₁ + 1 + s, by omega, (hstep₂ s).1.trans (congrArg w₂ hj)⟩
      · intro e he
        obtain ⟨r, -, rfl⟩ := mem_image.mp he
        by_cases hr1 : r < k₁ + 1
        · obtain ⟨h1, h2⟩ := hstep₁ r hr1
          exact mem_image.mpr ⟨.inl (idx₁ r), mem_univ _, by simp [h1, h2]⟩
        · obtain ⟨h1, h2⟩ := hstep₂ (r - (k₁ + 1))
          have hadd : k₁ + 1 + (r - (k₁ + 1)) = r := by omega
          exact mem_image.mpr ⟨.inr (idx₂ (r - (k₁ + 1))), mem_univ _, by
            simpa only [Sum.elim_inr, hadd] using (congrArg₂ Sym2.mk h1 h2).symm⟩
      · obtain ⟨r, hr, hi⟩ := exists_lt_fin_ofNat_add_eq a₀ i
        exact ⟨r, by omega, by simpa only [idx₁, hi] using hstep₁ r hr⟩
      · obtain ⟨s, hs, hj⟩ := exists_lt_fin_ofNat_add_eq b₀ j
        exact ⟨k₁ + 1 + s, by omega, by simpa only [idx₂, hj] using hstep₂ s⟩

private theorem two_le_card_sum_edge_fiber_of_no_singleton_edge {k₁ k₂ : ℕ}
    (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α)
    (h : ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t)
    (e : Sym2 α)
    (he : e ∈ univ.image (Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
      (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))))) :
    2 ≤ #{t : Fin k₁ ⊕ Fin k₂ |
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t = e} := by
  obtain ⟨t, -, rfl⟩ := mem_image.mp he
  obtain ⟨t', htt', ht'⟩ := h t
  exact one_lt_card.mpr ⟨t, by simp, t', mem_filter.mpr ⟨mem_univ _, ht'⟩, htt'.symm⟩

private theorem four_add_two_mul_sub_one_le_card_of_fiber_four {ι β : Type*} [Fintype ι]
    [DecidableEq β] (f : ι → β) {e₀ : β} (he₀ : e₀ ∈ univ.image f)
    (h4 : 4 ≤ #{t : ι | f t = e₀})
    (h2 : ∀ e ∈ univ.image f, 2 ≤ #{t : ι | f t = e}) :
    4 + 2 * (#(univ.image f) - 1) ≤ Fintype.card ι := by
  have htotal : Fintype.card ι = ∑ e ∈ univ.image f, #{t : ι | f t = e} := by
    simpa only [card_univ] using card_eq_sum_card_image f (univ : Finset ι)
  have herase : ∑ _e ∈ (univ.image f).erase e₀, 2 ≤
      ∑ e ∈ (univ.image f).erase e₀, #{t : ι | f t = e} :=
    sum_le_sum fun e he ↦ h2 e (mem_of_mem_erase he)
  rw [← add_sum_erase _ _ he₀] at htotal
  have hcard_erase : #((univ.image f).erase e₀) = #(univ.image f) - 1 :=
    card_erase_of_mem he₀
  simp only [sum_const, smul_eq_mul, hcard_erase] at herase
  omega

/-- A pair of cyclic words with no singleton unordered cyclic edge across `Fin k₁ ⊕ Fin k₂`
traverses at most `(k₁ + k₂) / 2` distinct unordered edges in total. Loops count as edges. -/
theorem two_mul_card_sum_cyclic_edges_le_of_no_singleton_edge {k₁ k₂ : ℕ}
    (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α)
    (h : ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t) :
    2 * #(univ.image (Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
      (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))))) ≤ k₁ + k₂ := by
  simpa only [card_univ, Fintype.card_sum, Fintype.card_fin] using
    mul_card_image_le_card (univ : Finset (Fin k₁ ⊕ Fin k₂)) 2
      (two_le_card_sum_edge_fiber_of_no_singleton_edge w₁ w₂ h)

/-- **Connected two-trace vertex bound.** If two cyclic words `w₁` and `w₂` of lengths `k₁` and
`k₂` share at least one unordered cyclic edge and have no singleton unordered cyclic edge across
`Fin k₁ ⊕ Fin k₂`, then their union visits at most `(k₁ + k₂) / 2` vertices. Both even and odd
total lengths `k₁ + k₂`, as well as loops, are allowed. -/
theorem card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_edge {k₁ k₂ : ℕ}
    (w₁ : Fin k₁ → α) (w₂ : Fin k₂ → α)
    (hshare : ∃ i j, s(w₁ i, w₁ (finRotate k₁ i)) = s(w₂ j, w₂ (finRotate k₂ j)))
    (h : ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t' =
      Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
        (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j))) t) :
    #(univ.image w₁ ∪ univ.image w₂) ≤ (k₁ + k₂) / 2 := by
  obtain ⟨i₀, j₀, hij₀⟩ := hshare
  have hcommon : ∃ b₀ : Fin k₂, w₁ i₀ = w₂ b₀ := by
    rcases Sym2.mem_iff.mp (hij₀ ▸ Sym2.mem_mk_left _ _) with h1 | h2
    · exact ⟨j₀, h1⟩
    · exact ⟨finRotate k₂ j₀, h2⟩
  obtain ⟨b₀, hab₀⟩ := hcommon
  obtain ⟨p, hpV, hpE, hpw₁, hpw₂⟩ := exists_concat_path_of_eq w₁ w₂ i₀ b₀ hab₀
  set stepEdge := Sum.elim (fun i ↦ s(w₁ i, w₁ (finRotate k₁ i)))
    (fun j ↦ s(w₂ j, w₂ (finRotate k₂ j)))
  set E := univ.image stepEdge
  set N := ((range (k₁ + k₂)).filter fun r ↦ p r ≠ p (r + 1)).image fun r ↦ s(p r, p (r + 1))
  have hVleN : #(univ.image w₁ ∪ univ.image w₂) ≤ #N + 1 :=
    hpV ▸ card_image_range_le_card_nonloop_edges_add_one p (k₁ + k₂)
  have hNleE : #N ≤ #E := card_le_card hpE
  have h2E : 2 * #E ≤ k₁ + k₂ := two_mul_card_sum_cyclic_edges_le_of_no_singleton_edge w₁ w₂ h
  by_contra hgt
  have hNE : N = E := eq_of_subset_of_card_le hpE (by omega)
  set e₀ := s(w₁ i₀, w₁ (finRotate k₁ i₀))
  have he₀E : e₀ ∈ E := mem_image.mpr ⟨.inl i₀, mem_univ _, rfl⟩
  have hEpos : 1 ≤ #E := card_pos.mpr ⟨e₀, he₀E⟩
  have he₀_noloop : ∀ x, s(x, x) ≠ e₀ := fun x hx ↦ by
    obtain ⟨r, hr, hre⟩ := mem_image.mp (hNE.symm ▸ he₀E)
    rcases Sym2.eq_iff.mp (hre.trans hx.symm) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact (mem_filter.mp hr).2 (h1.trans h2.symm)
  have hVN : #((range (k₁ + k₂ + 1)).image p) = #N + 1 := by rw [hpV]; omega
  obtain ⟨c, hc⟩ := exists_mod_two_color_of_card_image_eq p (k₁ + k₂) e₀ he₀_noloop hVN
  have hmod₁ : #{i | s(w₁ i, w₁ (finRotate k₁ i)) = e₀} % 2 = 0 :=
    card_filter_cyclic_edge_mod_two_eq_zero w₁ c e₀ fun i ↦
      let ⟨r, hr, h1, h2⟩ := hpw₁ i; by simpa only [h1, h2] using hc r hr
  have hmod₂ : #{j | s(w₂ j, w₂ (finRotate k₂ j)) = e₀} % 2 = 0 :=
    card_filter_cyclic_edge_mod_two_eq_zero w₂ c e₀ fun j ↦
      let ⟨r, hr, h1, h2⟩ := hpw₂ j; by simpa only [h1, h2] using hc r hr
  have hpos₁ : 1 ≤ #{i | s(w₁ i, w₁ (finRotate k₁ i)) = e₀} := card_pos.mpr ⟨i₀, by simp [e₀]⟩
  have hpos₂ : 1 ≤ #{j | s(w₂ j, w₂ (finRotate k₂ j)) = e₀} :=
    card_pos.mpr ⟨j₀, by simp [e₀, hij₀]⟩
  have hfiber₀ : 4 ≤ #{t : Fin k₁ ⊕ Fin k₂ | stepEdge t = e₀} := by
    have hsplit : #{t : Fin k₁ ⊕ Fin k₂ | stepEdge t = e₀} =
        #{i | s(w₁ i, w₁ (finRotate k₁ i)) = e₀} +
          #{j | s(w₂ j, w₂ (finRotate k₂ j)) = e₀} := by
      simp only [card_filter, Fintype.sum_sum_type, stepEdge, Sum.elim_inl, Sum.elim_inr]
      congr 1
    omega
  have h4 : 4 + 2 * (#E - 1) ≤ Fintype.card (Fin k₁ ⊕ Fin k₂) :=
    four_add_two_mul_sub_one_le_card_of_fiber_four stepEdge he₀E hfiber₀
      (two_le_card_sum_edge_fiber_of_no_singleton_edge w₁ w₂ h)
  simp only [Fintype.card_sum, Fintype.card_fin] at h4
  omega

/-- Over a nonempty finite alphabet `β`, at most `|β|^((k₁ + k₂) / 2) * ((k₁ + k₂) / 2)^(k₁ + k₂)`
pairs of cyclic words of lengths `k₁` and `k₂` share an unordered cyclic edge and have no
singleton unordered cyclic edge across `Fin k₁ ⊕ Fin k₂`. -/
theorem card_filter_shared_edge_and_no_singleton_edge_le {β : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] (k₁ k₂ : ℕ) :
    #{p : (Fin k₁ → β) × (Fin k₂ → β) |
        (∃ i j, s(p.1 i, p.1 (finRotate k₁ i)) = s(p.2 j, p.2 (finRotate k₂ j))) ∧
          ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t' =
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t} ≤
      Fintype.card β ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) := by
  have hbound : #{p : (Fin k₁ → β) × (Fin k₂ → β) | #(univ.image p.1 ∪ univ.image p.2) ≤
      (k₁ + k₂) / 2} ≤ Fintype.card β ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) := by
    simpa using
      card_filter_card_image_union_le (ι₁ := Fin k₁) (ι₂ := Fin k₂) (β := β) ((k₁ + k₂) / 2)
  refine (card_le_card fun p hp ↦ ?_).trans hbound
  obtain ⟨-, hshare, hno⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_univ _,
    card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_edge p.1 p.2 hshare hno⟩

end TauCeti
