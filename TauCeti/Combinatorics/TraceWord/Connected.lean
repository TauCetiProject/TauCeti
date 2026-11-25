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

This file bounds the combined vertex set and cardinality of such connected singleton-free pairs
`(w₁, w₂)` of lengths `k₁` and `k₂`: their union visits at most `(k₁ + k₂) / 2` vertices, so over a
finite alphabet `β` there are at most
`|β| ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂)` such pairs. For `n × n` Wigner matrices with
`n⁻¹/²`-scaled entries, the factor `n ^ ((k₁ + k₂) / 2)` is absorbed by the entry scaling
`((√n)⁻¹) ^ (k₁ + k₂)`, leaving `O(n⁻²)` after the two `n⁻¹` trace normalizations.

## Main results

* `TauCeti.two_mul_card_sum_cyclic_edges_le_of_no_singleton_edge`: a pair of cyclic words with no
  singleton unordered edge across `Fin k₁ ⊕ Fin k₂` uses at most `(k₁ + k₂) / 2` distinct
  unordered edges.
* `TauCeti.card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_edge`: if two cyclic
  words of lengths `k₁` and `k₂` share an unordered cyclic edge and have no singleton unordered
  edge across `Fin k₁ ⊕ Fin k₂`, their union visits at most `(k₁ + k₂) / 2` vertices.
* `TauCeti.card_filter_shared_edge_and_no_singleton_edge_le`: over a finite alphabet `β`, at
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
      -- Concatenate `w₁` starting at `a₀` with `w₂` starting at `b₀` across the seam `k₁ + 1`.
      let rot {k : ℕ} (x : Fin (k + 1)) (r : ℕ) : Fin (k + 1) := x + Fin.ofNat (k + 1) r
      let p (r : ℕ) : α := if r ≤ k₁ + 1 then w₁ (rot a₀ r) else w₂ (rot b₀ (r - (k₁ + 1)))
      have hseam : p (k₁ + 1) = w₂ (rot b₀ 0) := by simp [p, rot, hab]
      have hrot {k : ℕ} (x : Fin (k + 1)) (r : ℕ) :
          rot x (r + 1) = finRotate (k + 1) (rot x r) := by
        simp only [rot, finRotate_apply, add_assoc]; congr 1
        exact Fin.ext (by simp [Fin.ofNat, Fin.add_def, Nat.add_mod])
      have hhit {k : ℕ} (x y : Fin (k + 1)) : rot x (y - x).val = y := by simp [rot]
      have hstep₁ {r : ℕ} (hr : r < k₁ + 1) :
          p r = w₁ (rot a₀ r) ∧ p (r + 1) = w₁ (finRotate (k₁ + 1) (rot a₀ r)) := by
        simp [p, hr.le, Nat.succ_le_of_lt hr, hrot]
      have hstep₂ (s : ℕ) : p (k₁ + 1 + s) = w₂ (rot b₀ s) ∧
          p (k₁ + 1 + s + 1) = w₂ (finRotate (k₂ + 1) (rot b₀ s)) := by
        rcases eq_or_ne s 0 with rfl | hs
        · exact ⟨hseam, by simpa [p] using congrArg w₂ (hrot b₀ 0)⟩
        · have hle₁ : ¬ k₁ + 1 + s ≤ k₁ + 1 := by omega
          have hle₂ : ¬ k₁ + 1 + s + 1 ≤ k₁ + 1 := by omega
          have hsub : k₁ + 1 + s + 1 - (k₁ + 1) = s + 1 := by omega
          simp [p, hle₁, hle₂, hsub, hrot]
      refine ⟨p, ?_, ?_, fun i ↦ ?_, fun j ↦ ?_⟩
      · ext x; simp only [mem_image, mem_range, mem_union, mem_univ, true_and]
        refine ⟨fun ⟨r, _, hx⟩ ↦ ?_, ?_⟩
        · by_cases hle : r ≤ k₁ + 1
          · exact Or.inl ⟨rot a₀ r, by simp [← hx, p, hle]⟩
          · exact Or.inr ⟨rot b₀ (r - (k₁ + 1)), by simp [← hx, p, hle]⟩
        · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
          · exact ⟨(i - a₀).val, by omega, by simpa only [hhit] using (hstep₁ (i - a₀).isLt).1⟩
          · exact ⟨k₁ + 1 + (j - b₀).val, by omega,
              by simpa only [hhit] using (hstep₂ (j - b₀).val).1⟩
      · intro e he; obtain ⟨r, -, rfl⟩ := mem_image.mp he
        by_cases hr1 : r < k₁ + 1
        · obtain ⟨h1, h2⟩ := hstep₁ hr1
          exact mem_image.mpr ⟨.inl (rot a₀ r), mem_univ _, by simp [h1, h2]⟩
        · obtain ⟨h1, h2⟩ := hstep₂ (r - (k₁ + 1))
          have hadd : k₁ + 1 + (r - (k₁ + 1)) = r := by omega
          exact mem_image.mpr ⟨.inr (rot b₀ (r - (k₁ + 1))), mem_univ _, by
            simpa only [Sum.elim_inr, hadd] using (congrArg₂ Sym2.mk h1 h2).symm⟩
      · exact ⟨(i - a₀).val, by omega, by simpa only [hhit] using hstep₁ (i - a₀).isLt⟩
      · exact ⟨k₁ + 1 + (j - b₀).val, by omega, by simpa only [hhit] using hstep₂ (j - b₀).val⟩

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
      (two_le_card_filter_eq_of_no_singleton_fiber h)

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
  obtain ⟨b₀, hab₀⟩ : ∃ b₀ : Fin k₂, w₁ i₀ = w₂ b₀ := by
    rcases Sym2.mem_iff.mp (hij₀ ▸ Sym2.mem_mk_left _ _) with h1 | h2
    · exact ⟨j₀, h1⟩
    · exact ⟨finRotate k₂ j₀, h2⟩
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
  -- Exceeding `(k₁ + k₂) / 2` forces `#V = #N + 1` and `N = E`, so the shared edge `e₀` is nonloop.
  have hNE : N = E := eq_of_subset_of_card_le hpE (by omega)
  set e₀ := s(w₁ i₀, w₁ (finRotate k₁ i₀))
  have he₀E : e₀ ∈ E := mem_image.mpr ⟨.inl i₀, mem_univ _, rfl⟩
  have hEpos : 1 ≤ #E := card_pos.mpr ⟨e₀, he₀E⟩
  have he₀_noloop : ¬ e₀.IsDiag := by
    obtain ⟨r, hr, hre⟩ := mem_image.mp (hNE.symm ▸ he₀E)
    rw [← hre, Sym2.mk_isDiag_iff]
    exact (mem_filter.mp hr).2
  have hVN : #((range (k₁ + k₂ + 1)).image p) = #N + 1 := by rw [hpV]; omega
  obtain ⟨c, hc⟩ := exists_mod_two_color_of_card_image_eq p (k₁ + k₂) e₀ he₀_noloop hVN
  -- Both closed walks traverse `e₀` a positive even number of times, giving fiber size ≥ 4.
  have hmod₁ := card_filter_cyclic_edge_mod_two_eq_zero w₁ c e₀ fun i ↦
    let ⟨r, hr, h1, h2⟩ := hpw₁ i; by simpa only [h1, h2] using hc r hr
  have hmod₂ := card_filter_cyclic_edge_mod_two_eq_zero w₂ c e₀ fun j ↦
    let ⟨r, hr, h1, h2⟩ := hpw₂ j; by simpa only [h1, h2] using hc r hr
  have hpos₁ : 1 ≤ #{i | s(w₁ i, w₁ (finRotate k₁ i)) = e₀} := card_pos.mpr ⟨i₀, by simp [e₀]⟩
  have hpos₂ : 1 ≤ #{j | s(w₂ j, w₂ (finRotate k₂ j)) = e₀} :=
    card_pos.mpr ⟨j₀, by simp [e₀, hij₀]⟩
  have hsplit : #{t : Fin k₁ ⊕ Fin k₂ | stepEdge t = e₀} =
      #{i | s(w₁ i, w₁ (finRotate k₁ i)) = e₀} + #{j | s(w₂ j, w₂ (finRotate k₂ j)) = e₀} := by
    simp only [card_filter, Fintype.sum_sum_type, stepEdge, Sum.elim_inl, Sum.elim_inr]; congr 1
  have htotal : k₁ + k₂ = #{t | stepEdge t = e₀} + ∑ e ∈ E.erase e₀, #{t | stepEdge t = e} := by
    have hcard := card_eq_sum_card_image stepEdge (univ : Finset (Fin k₁ ⊕ Fin k₂))
    simpa only [card_univ, Fintype.card_sum, Fintype.card_fin, E] using
      hcard.trans (add_sum_erase _ _ he₀E).symm
  have herase : 2 * (#E - 1) ≤ ∑ e ∈ E.erase e₀, #{t | stepEdge t = e} := by
    simpa only [sum_const, smul_eq_mul, card_erase_of_mem he₀E, mul_comm] using
      sum_le_sum (s := E.erase e₀) fun e he ↦
        two_le_card_filter_eq_of_no_singleton_fiber h e (mem_of_mem_erase he)
  omega

/-- Over a finite alphabet `β`, at most `|β|^((k₁ + k₂) / 2) * ((k₁ + k₂) / 2)^(k₁ + k₂)`
pairs of cyclic words of lengths `k₁` and `k₂` share an unordered cyclic edge and have no
singleton unordered cyclic edge across `Fin k₁ ⊕ Fin k₂`. -/
theorem card_filter_shared_edge_and_no_singleton_edge_le {β : Type*} [Fintype β]
    [DecidableEq β] (k₁ k₂ : ℕ) :
    #{p : (Fin k₁ → β) × (Fin k₂ → β) |
        (∃ i j, s(p.1 i, p.1 (finRotate k₁ i)) = s(p.2 j, p.2 (finRotate k₂ j))) ∧
          ∀ t : Fin k₁ ⊕ Fin k₂, ∃ t' ≠ t,
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t' =
            Sum.elim (fun i ↦ s(p.1 i, p.1 (finRotate k₁ i)))
              (fun j ↦ s(p.2 j, p.2 (finRotate k₂ j))) t} ≤
      Fintype.card β ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) := by
  cases isEmpty_or_nonempty β with
  | inl hempty =>
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ ⟨⟨i, _, _⟩, _⟩ ↦
      isEmptyElim (p.1 i))]
    exact Nat.zero_le _
  | inr hne =>
    have hbound : #{p : (Fin k₁ → β) × (Fin k₂ → β) | #(univ.image p.1 ∪ univ.image p.2) ≤
        (k₁ + k₂) / 2} ≤ Fintype.card β ^ ((k₁ + k₂) / 2) * ((k₁ + k₂) / 2) ^ (k₁ + k₂) := by
      simpa using
        card_filter_card_image_union_le (ι₁ := Fin k₁) (ι₂ := Fin k₂) (β := β) ((k₁ + k₂) / 2)
    refine (card_le_card fun p hp ↦ ?_).trans hbound
    obtain ⟨-, hshare, hno⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_univ _,
      card_image_union_le_add_div_two_of_shared_edge_of_no_singleton_edge p.1 p.2 hshare hno⟩

end TauCeti
