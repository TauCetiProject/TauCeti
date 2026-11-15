/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
public import TauCeti.RepresentationTheory.LSPath.Linked

import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.RepresentationTheory.LSPath.Concatenation

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root, and write
`H(t) = ⟨π(t), αᵢ^∨⟩` for its running height, with minimum `h`. When `h ≤ -1`, Littelmann's raising
operator `e_αᵢ` reflects by `sᵢ` the single strictly falling piece of the path from the last time
`t₀` at height `h + 1` before the first time `t₁` at which `H = h` down to `t₁`, and keeps the rest
(`TauCeti.LSPath.exists_raise_toPLPath_eq`). This file proves Littelmann's theorem that the result
is again the path of an LS path of shape `λ` (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`),
that a single LS path realizes `e_αᵢ π` across any two ordered-field realizations
(`TauCeti.LSPath.exists_raise_toPLPath_eq_and_eq`), and that two LS paths with the same directions,
durations, and `αᵢ^∨`-orbit pairings raise to LS paths with the same directions and durations
(`TauCeti.LSPath.exists_dirDurations_eq_of_raise_of_dirDurations_eq`).

In terms of the directions `τ₀ > ⋯ > τ_l` and durations of `π`, with `t₀` inside the segment `j₀`
and `t₁` at the break `k₁`, the raised path runs along the list of directions
`τ₀, …, τ_{j₀}, sᵢ τ_{j₀}, …, sᵢ τ_{k₁ - 1}, τ_{k₁}, …, τ_l`, the segment `j₀` being cut at `t₀`.
This list is linked (`TauCeti.LSPath.Linked`), so it defines an LS path by
`TauCeti.LSPath.ofLinked`, which merges repeated directions. The chain conditions at its breaks
come from `TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain`:

* at `t₀` the height `h + 1` is an integer and `⟨τ_{j₀} λ, αᵢ^∨⟩ < 0`, so `u = sᵢ τ_{j₀}` has
  positive pairing and the cover `sᵢ τ_{j₀} ⋖ τ_{j₀}` is a `t₀`-chain;
* at a break `a` strictly inside `(t₀, t₁)` the height lies strictly between the integers `h` and
  `h + 1`, so the `a`-chain stays on the negative side of the wall of `αᵢ`, where `sᵢ` carries it
  to an `a`-chain;
* at `t₁` the height attains its global minimum `h`, so if `k₁ ≤ l` then
  `⟨τ_{k₁ - 1} λ, αᵢ^∨⟩ < 0 ≤ ⟨τ_{k₁} λ, αᵢ^∨⟩`, and an `a`-chain from `τ_{k₁ - 1}` down to
  `τ_{k₁}` gives one from `sᵢ τ_{k₁ - 1}` down to `τ_{k₁}`.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator preserves
  Lakshmibai–Seshadri paths**.
* `TauCeti.LSPath.exists_raise_toPLPath_eq_and_eq`: a single LS path realizes `e_αᵢ` across any two
  ordered-field realizations.
* `TauCeti.LSPath.exists_dirDurations_eq_of_raise_of_dirDurations_eq`: `e_αᵢ` preserves equality of
  `dirDurations` between dominant shapes with the same `αᵢ^∨`-orbit pairings.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Sections 1 and 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- **Reflecting a falling window of a linked list.** Let `[j₀ + 1, k₁]` be a window of entries of
a linked list along which the heights `⟨τ λ, αᵢ^∨⟩` of the directions are negative, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at the internal breaks `a`, preceded at `j₀` by an entry with the same
direction as `j₀ + 1` at a break `a` with `a ⟨τ λ, αᵢ^∨⟩` integral, and (if `k₁ + 1 < l.length`)
followed by a direction of nonnegative height. Replacing the directions `τ` in `[j₀ + 1, k₁]` by
`sᵢ τ` keeps the list linked. -/
private theorem Linked.mapIdx_simple_mul_falling (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ < l.length)
    (hneg : ∀ k (hk : k < l.length), j₀ + 1 ≤ k → k ≤ k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), j₀ + 1 < k → k ≤ k₁ →
      ¬∃ z : ℤ, (t + ((l.take k).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hright : ∀ k (hk : k < l.length), k = k₁ + 1 → 0 ≤ P.coroot' i (l[k].1 • lam))
    (hcut : (l[j₀ + 1]'(lt_of_le_of_lt hj₀k₁ hk₁)).1 = (l[j₀]'(lt_trans hj₀k₁ hk₁)).1)
    (hcutint : ∃ z : ℤ,
      (t + ((l.take (j₀ + 1)).map Prod.snd).sum) *
        P.coroot' i ((l[j₀]'(lt_trans hj₀k₁ hk₁)).1 • lam) = z) :
    Linked P b lam t (l.mapIdx fun k p ↦
      if j₀ + 1 ≤ k ∧ k ≤ k₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) := by
  set g : ℕ → P.weylGroup × ℚ → P.weylGroup × ℚ := fun k p ↦
    if j₀ + 1 ≤ k ∧ k ≤ k₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p
  have hsnd : (l.mapIdx g).map Prod.snd = l.map Prod.snd := by
    refine List.ext_getElem (by simp) fun k _ _ ↦ ?_
    simp only [g, List.getElem_map, List.getElem_mapIdx]
    split_ifs <;> rfl
  rw [linked_iff_getElem] at hl ⊢
  intro k hk
  rw [List.length_mapIdx] at hk
  rw [List.map_take, hsnd, ← List.map_take]
  obtain ⟨C, hhead, hlast, hC⟩ := hl k hk
  simp only [List.getElem_mapIdx, g]
  by_cases hk₁' : j₀ + 1 ≤ k ∧ k ≤ k₁ <;> by_cases hk₂' : j₀ + 1 ≤ k + 1 ∧ k + 1 ≤ k₁ <;>
    simp only [hk₁', hk₂', and_self, ↓reduceIte]
  · -- Both ends in `[j₀ + 1, k₁]`: the chain stays on the negative side and reflects.
    have hint_head : ¬∃ z : ℤ,
        (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (C.head.1 • lam) = z := by
      rintro ⟨z₁, hz₁⟩
      obtain ⟨z₂, hz₂⟩ := hC.exists_mul_sub_eq_intCast hlam (P.coroot' i)
      refine hint (k + 1) hk (by omega) hk₂'.2 ⟨z₁ - z₂, ?_⟩
      rw [← hlast]
      push_cast at hz₁ hz₂ ⊢
      linear_combination hz₁ - hz₂
    have hall := hC.coroot'_smul_neg hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁'.1 hk₁'.2) hint_head
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inr hall), ?_, ?_,
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
    · simp [hhead]
    · simp [hlast]
  · -- Leaving the window at `k₁`: Littelmann's chain at the end of a reflected piece of `e_αᵢ`.
    obtain ⟨D, hDhead, hDlast, hD⟩ := hC.exists_isAChain_simple_mul_head hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁'.1 hk₁'.2)
      (by rw [hlast]; exact hright (k + 1) hk (by omega))
    exact ⟨D, by rw [hDhead, hhead], by rw [hDlast, hlast], hD⟩
  · -- Entering the window at `j₀`: the cover `sᵢ τ ⋖ τ`.
    obtain rfl : j₀ = k := by omega
    have hj₀_lt : j₀ < l.length := lt_trans hj₀k₁ hk₁
    set s := (weylCoxeterSystem P b).simple i
    set u := s * (l[j₀]'hj₀_lt).1
    have hneg₀ : P.coroot' i ((l[j₀]'hj₀_lt).1 • lam) < 0 := by
      rw [← hcut]
      exact hneg (j₀ + 1) hk le_rfl hk₂'.2
    have hu : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) u :=
      isMinimalCosetRep_simple_mul_of_coroot'_ne_zero
        (hmin _ (List.getElem_mem hj₀_lt)) hneg₀.ne
    have hcoroot_u : P.coroot' i (u • lam) = -P.coroot' i ((l[j₀]'hj₀_lt).1 • lam) := by
      simp only [u]
      rw [simple_mul_smul_eq_reflection, coroot'_reflection_self]
    have hu_pos : 0 < P.coroot' i (u • lam) := by linarith
    have hu_int :
        ∃ z : ℤ, (t + ((l.take (j₀ + 1)).map Prod.snd).sum) * P.coroot' i (u • lam) = z := by
      obtain ⟨z, hz⟩ := hcutint
      refine ⟨-z, ?_⟩
      rw [hcoroot_u]
      push_cast at hz ⊢
      linear_combination -hz
    obtain ⟨D, hDhead, hDlast, hD⟩ :=
      exists_isAChain_simple_mul_of_coroot'_pos hlam hu hu_pos hu_int
    refine ⟨D, ?_, ?_, hD⟩
    · rw [hDhead]
      exact (weylCoxeterSystem P b).simple_mul_simple_cancel_left i
    · rw [hDlast, hcut]
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
/-- The directions and durations produced from `l` by Littelmann's raising operator along the
simple root `αᵢ`: the first part `(τ, θ d)` of `l[j₀] = (τ, d)` and earlier entries are kept, the
second part `(τ, (1 - θ) d)` and the entries `j₀ + 1, …, k₁ - 1` are reflected by `sᵢ`, and the
entries from `k₁` onwards are kept. -/
private noncomputable def raiseList (i : b.support) (l : List (P.weylGroup × ℚ)) (j₀ k₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  (l.take j₀ ++ [(τ, θ * d)]) ++
    ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).map
      (fun p ↦ ((weylCoxeterSystem P b).simple i * p.1, p.2)) ++
    l.drop k₁

private theorem nonneg_of_mem_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) {j₀ k₁ : ℕ} {τ : P.weylGroup} {d θ : ℚ} (hd : 0 ≤ d) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) {p : P.weylGroup × ℚ} (hp : p ∈ raiseList b i l j₀ k₁ τ d θ) : 0 ≤ p.2 := by
  simp only [raiseList, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ((hp | rfl) | ⟨q, rfl | hq, rfl⟩) | hp
  · exact hl p (List.mem_of_mem_take hp)
  · exact mul_nonneg hθ₀ hd
  · exact mul_nonneg (by linarith) hd
  · exact hl q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
  · exact hl p (List.mem_of_mem_drop hp)

private theorem sum_map_snd_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)} {j₀ k₁ : ℕ}
    (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ) :
    ((raiseList b i l j₀ k₁ (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1
      (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 θ).map Prod.snd).sum = (l.map Prod.snd).sum := by
  have hk₀take : j₀ < (l.take k₁).length := by simp; omega
  conv_rhs => rw [← List.take_append_drop k₁ l, ← List.take_append_drop j₀ (l.take k₁),
    List.drop_eq_getElem_cons hk₀take, List.take_take, min_eq_left hj₀k₁.le, List.getElem_take]
  simp only [raiseList, List.map_append, List.map_cons, List.map_map, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  ring

/-- **The raised list is linked.** Let `l` be a linked list of minimal coset representatives, let
`[j₀, k₁ - 1]` be a window along which `⟨-, αᵢ^∨⟩` is negative, with `a ⟨τ λ, αᵢ^∨⟩` nonintegral
at internal breaks `j₀ < k < k₁`, followed (if `k₁ < l.length`) by a direction of nonnegative
height, and let `θ` cut `l[j₀] = (τ, d)` at an `a`-integral time. Then `raiseList` is linked, and
its directions are minimal coset representatives. -/
private theorem linked_raiseList (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ)
    (hneg : ∀ k (hk : k < l.length), j₀ ≤ k → k < k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), j₀ < k → k < k₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i (l[k].1 • lam) = m)
    (hright : ∀ (hk : k₁ < l.length), 0 ≤ P.coroot' i (l[k₁].1 • lam))
    (hcut : ∃ m : ℤ,
      (((l.take j₀).map Prod.snd).sum + θ * (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2) *
        P.coroot' i ((l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1 • lam) = m) :
    Linked P b lam 0 (raiseList b i l j₀ k₁ (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1
      (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 θ) ∧
      ∀ p ∈ raiseList b i l j₀ k₁ (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1
          (l[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hj₀ : j₀ < l.length := lt_of_lt_of_le hj₀k₁ hk₁
  set τ := l[j₀].1
  set d := l[j₀].2
  set s := (weylCoxeterSystem P b).simple i
  have hτmin : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) τ :=
    hlmin _ (List.getElem_mem hj₀)
  -- Subdivide the entry `j₀` at the fraction `θ`; the list stays linked.
  set Dp : List (P.weylGroup × ℚ) :=
    l.take j₀ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₀ + 1) with hDp
  have hDp_linked : Linked P b lam 0 Dp := by
    have hsplit : l = l.take j₀ ++ (τ, θ * d + (1 - θ) * d) :: l.drop (j₀ + 1) := by
      rw [show θ * d + (1 - θ) * d = d by ring, ← List.drop_eq_getElem_cons hj₀,
        List.take_append_drop]
    rw [hsplit] at hl
    exact Linked.split hτmin hl
  have hDpmin : ∀ p ∈ Dp, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
    intro p hp
    simp only [Dp, List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | rfl | hp
    · exact hlmin p (List.mem_of_mem_take hp)
    · exact hτmin
    · exact hτmin
    · exact hlmin p (List.mem_of_mem_drop hp)
  have hlen_take : (l.take j₀).length = j₀ := by simp; omega
  have hDp_len : Dp.length = l.length + 1 := by simp [Dp]; omega
  have hDp_j₀ : Dp[j₀]'(by omega) = (τ, θ * d) := by
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  have hDp_j₀1 : Dp[j₀ + 1]'(by omega) = (τ, (1 - θ) * d) := by
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  have hDp_gt : ∀ k (hk : k < Dp.length), j₀ + 1 < k → Dp[k] = l[k - 1]'(by omega) := by
    intro k hk hkj
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    have hidx : k - (l.take j₀).length = (k - j₀ - 2) + 2 := by omega
    simp only [hidx, List.getElem_cons_succ, List.getElem_drop]
    congr 1
    omega
  have hDp_fst_ge : ∀ k (hk : k < Dp.length), j₀ + 1 ≤ k → Dp[k].1 = (l[k - 1]'(by omega)).1 := by
    intro k hk hkj
    rcases hkj.eq_or_lt with rfl | hkj
    · rw [hDp_j₀1]
      simp [τ]
    · rw [hDp_gt k hk hkj]
  have hcum_j₀1 : ((Dp.take (j₀ + 1)).map Prod.snd).sum =
      ((l.take j₀).map Prod.snd).sum + θ * d := by
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₀ + 1 - j₀ = 1 by omega]
    simp
  have hcum_gt : ∀ k, j₀ + 1 < k →
      ((Dp.take k).map Prod.snd).sum = ((l.take (k - 1)).map Prod.snd).sum := by
    intro k hkj
    have hl_split : l.take (k - 1) =
        l.take j₀ ++ (τ, d) :: (l.drop (j₀ + 1)).take (k - (j₀ + 2)) := by
      conv_lhs => rw [← List.take_append_drop j₀ l, List.drop_eq_getElem_cons hj₀]
      rw [List.take_append, List.take_of_length_le (by omega), hlen_take]
      have hsub : k - 1 - j₀ = (k - (j₀ + 2)) + 1 := by omega
      rw [hsub, List.take_succ_cons]
    have hDp_split : Dp.take k =
        l.take j₀ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: (l.drop (j₀ + 1)).take (k - (j₀ + 2)) := by
      simp only [Dp]
      rw [List.take_append, List.take_of_length_le (by omega), hlen_take]
      have hsub : k - j₀ = (k - (j₀ + 2)) + 2 := by omega
      rw [hsub, List.take_succ_cons, List.take_succ_cons]
    rw [hDp_split, hl_split]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring
  -- Reflect the window `[j₀ + 1, k₁]` of the subdivided list in `sᵢ`.
  have hW := Linked.mapIdx_simple_mul_falling hlam hDp_linked hDpmin i
    (j₀ := j₀) (k₁ := k₁) hj₀k₁ (by omega)
    (fun k hk hkj hkk₁ ↦ by
      rw [hDp_fst_ge k hk hkj]
      exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkj hkk₁ ↦ by
      rw [zero_add, hcum_gt k hkj, hDp_fst_ge k hk hkj.le]
      exact hint (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkk₁ ↦ by
      subst hkk₁
      rw [hDp_gt (k₁ + 1) hk (by omega)]
      simpa using hright (by omega))
    (by rw [hDp_j₀1, hDp_j₀])
    (by
      rw [zero_add, hcum_j₀1, hDp_j₀]
      exact hcut)
  -- The reflected subdivided list is the raised list.
  have hraise : raiseList b i l j₀ k₁ τ d θ =
      Dp.mapIdx fun k p ↦ if j₀ + 1 ≤ k ∧ k ≤ k₁ then (s * p.1, p.2) else p := by
    have hdrop : l.drop (j₀ + 1) = (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ := by
      conv_lhs => rw [← List.take_append_drop k₁ l]
      rw [List.drop_append, List.length_take_of_le hk₁,
        show j₀ + 1 - k₁ = 0 by omega, List.drop_zero]
    have hDp' : Dp = (l.take j₀ ++ [(τ, θ * d)]) ++
        ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
      simp [Dp, hdrop, List.append_assoc]
    have hA : (l.take j₀ ++ [(τ, θ * d)]).length = j₀ + 1 := by simp [hlen_take]
    have hB : ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by
      simp [List.length_take_of_le hk₁]
      omega
    rw [hDp']
    refine List.ext_getElem (by simp [raiseList]) fun k hk₁' hk₂' ↦ ?_
    simp only [raiseList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
      List.length_append, List.length_map, hA, hB]
    split_ifs <;> first | rfl | omega
  rw [hraise]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst_ge k hk' hw.1]
    exact (hneg (k - 1) (by omega) (by omega) (by omega)).ne
  · exact hDpmin _ (List.getElem_mem hk')

/-- Canonical additive evaluation of `M` into `N → ℚ` via the root pairing, used internally to
extract the rational cut data `(j₀, k₁, θ)` of a raising step without auxiliary hypotheses on `M`.
-/
private def evalRat (P : RootPairing ι ℤ M N) : M →+ (N → ℚ) where
  toFun m n := (P.toLinearMap m n : ℚ)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

private def projCoroot (P : RootPairing ι ℤ M N) (i : ι) : Module.Dual ℚ (N → ℚ) :=
  LinearMap.proj (P.coroot i)

private theorem preReflection_smul_apply {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (d : 𝕜) (w : P.weylGroup) :
    Module.preReflection (f (P.root i)) F (d • f (w • lam)) =
      d • f (((weylCoxeterSystem P b).simple i * w) • lam) := by
  rw [map_smul, ← P.map_reflection_eq_preReflection i hF, simple_mul_smul_eq_reflection]

/-- Given a shape `lam₂` whose `dirDurations` and `αᵢ^∨`-orbit pairings match those of `π`, any
form `F` inducing `⟨-, αᵢ^∨⟩` has the same minimum height `z` on `π₂.toPLPath` as `projCoroot P i`
has on `π.toPLPath ℚ (evalRat P)`. -/
private theorem minHeight_eq_of_dirDurations_eq {lam₂ : M} (π : LSPath P b lam)
    (π₂ : LSPath P b lam₂) (i : b.support)
    (hdir : π₂.dirDurations = π.dirDurations)
    (hcoroot : ∀ w : P.weylGroup, P.coroot' i (w • lam₂) = P.coroot' i (w • lam)) {z : ℤ}
    (hz₀ : (π.toPLPath ℚ (evalRat P)).minHeight (projCoroot P i) = z)
    {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    (π₂.toPLPath 𝕜 f).minHeight F = z := by
  set D := π.dirDurations
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
  have hHF₀ : ∀ k, projCoroot P i
      ((D.map fun p ↦ (p.2 : ℚ) • evalRat P (p.1 • lam)).take k).sum = hgt k := by
    intro k
    simp only [hgt, ← List.map_take, map_list_sum, List.map_map]
    congr 1
  have hHF₂ : ∀ k, F ((D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂)).take k).sum = (hgt k : 𝕜) := by
    intro k
    simp only [hgt, ← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
    congr 1
    refine List.map_congr_left fun p _ ↦ ?_
    simp [H, hF, hcoroot]
  have hm₀ : PLPath.listMinHeight (projCoroot P i)
      (D.map fun p ↦ (p.2 : ℚ) • evalRat P (p.1 • lam)) = z := by
    simpa only [toPLPath_def, map_snd_timed, Rat.cast_id, PLPath.minHeight_ofSegments] using hz₀
  rw [toPLPath_def, map_snd_timed, hdir, PLPath.minHeight_ofSegments]
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := projCoroot P i)
      (D.map fun p ↦ (p.2 : ℚ) • evalRat P (p.1 • lam))
    rw [hm₀, hHF₀] at hk
    have hb := PLPath.listMinHeight_le_apply_sum_take (f := F)
      (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂)) k
    rw [hHF₂, ← hk, Rat.cast_intCast] at hb
    exact hb
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F)
      (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂))
    have hb := PLPath.listMinHeight_le_apply_sum_take (f := projCoroot P i)
      (D.map fun p ↦ (p.2 : ℚ) • evalRat P (p.1 • lam)) k
    rw [hm₀, hHF₀] at hb
    rw [hk, hHF₂, ← Rat.cast_intCast]
    exact Rat.cast_le.mpr hb

/-- **The rational data of a raising step.** When the rational minimum height `z` of `π` along
`αᵢ^∨` satisfies `z ≤ -1`, there are a cut segment `j₀`, a first-minimum vertex `k₁ > j₀` and a
fraction `0 ≤ θ ≤ 1` satisfying the hypotheses of `linked_raiseList`. -/
private theorem exists_raiseList_data (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (i : b.support) {z : ℤ}
    (hz₀ : (π.toPLPath ℚ (evalRat P)).minHeight (projCoroot P i) = z)
    (hz : z ≤ -1) :
    ∃ (j₀ k₁ : ℕ) (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ π.dirDurations.length) (θ : ℚ),
      0 ≤ θ ∧ θ ≤ 1 ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ ≤ k → k < k₁ →
        P.coroot' i (π.dirDurations[k].1 • lam) < 0) ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ < k → k < k₁ →
        ¬∃ m : ℤ, ((π.dirDurations.take k).map Prod.snd).sum *
          P.coroot' i (π.dirDurations[k].1 • lam) = m) ∧
      (∀ (hk : k₁ < π.dirDurations.length), 0 ≤ P.coroot' i (π.dirDurations[k₁].1 • lam)) ∧
      (∃ m : ℤ, (((π.dirDurations.take j₀).map Prod.snd).sum +
          θ * (π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2) *
        P.coroot' i ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1 • lam) = m) ∧
      (((π.dirDurations.take k₁).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum = z) ∧
      (∀ k ≤ j₀, (z : ℚ) + 1 ≤
        ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum) ∧
      (∀ k, j₀ ≤ k → k < k₁ →
        ((π.dirDurations.take (k + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
          ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum) ∧
      (((π.dirDurations.take j₀).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum +
        θ * ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 *
          P.coroot' i ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1 • lam)) = z + 1) ∧
      (((π.dirDurations.take (j₀ + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum ≤
        z + 1) := by
  have h1 : (π.toPLPath ℚ (evalRat P)).minHeight (projCoroot P i) ≤ -1 := by
    rw [hz₀]
    exact_mod_cast hz
  obtain ⟨j₀', k₁, θ, hj₀k₁, hk₁s, hθ₀, hθlt, hmin, -, habove, hfall, hcross, -⟩ :=
    π.exists_raise_toPLPath_eq hlam (evalRat P) i (projCoroot P i) (fun _ ↦ rfl) 0 h1
  rw [map_snd_timed] at hmin habove hfall hcross
  simp only [Rat.cast_id] at hmin habove hfall hcross
  rw [hz₀] at hmin habove hcross
  set D := π.dirDurations
  set j₀ : ℕ := (j₀' : ℕ)
  have hlen : D.length = π.length + 1 := length_dirDurations π
  have hk₁D : k₁ ≤ D.length := by rwa [hlen]
  have hj₀lt : j₀ < D.length := lt_of_lt_of_le hj₀k₁ hk₁D
  set τ := (π.dir j₀').1
  set d := π.duration j₀'
  have hDj₀ : D[j₀] = (τ, d) := by rw [getElem_dirDurations]
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
  set cum : ℕ → ℚ := fun k ↦ ((D.take k).map Prod.snd).sum
  have hHF₀ : ∀ k, projCoroot P i
      ((D.map fun p ↦ (p.2 : ℚ) • evalRat P (p.1 • lam)).take k).sum = hgt k := by
    intro k
    simp only [hgt, ← List.map_take, map_list_sum, List.map_map]
    congr 1
  have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
    intro k hk
    simp only [hgt, List.map_take]
    rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
  have hgtk₁ : hgt k₁ = z := by rwa [hHF₀] at hmin
  have habove' : ∀ k ≤ j₀, (z : ℚ) + 1 ≤ hgt k := fun k hk ↦ by
    have := habove k hk
    rwa [hHF₀] at this
  have hfall' : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k := fun k hkj hkk₁ ↦ by
    have := hfall k hkj hkk₁
    rwa [hHF₀, hHF₀] at this
  have hcross' : hgt j₀ + θ * (d * H τ) = z + 1 := by
    have hc := hcross
    rw [hHF₀] at hc
    simpa [H, projCoroot, evalRat, RootPairing.coroot', mul_assoc] using hc
  have hmin_le : ∀ k, (z : ℚ) ≤ hgt k := by
    intro k
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := projCoroot P i)
      (D.map fun p ↦ p.2 • evalRat P (p.1 • lam)) k
    have hm : PLPath.listMinHeight (projCoroot P i)
        (D.map fun p ↦ p.2 • evalRat P (p.1 • lam)) = z := by
      simpa only [toPLPath_def, map_snd_timed, Rat.cast_id, PLPath.minHeight_ofSegments] using hz₀
    rwa [hm, hHF₀] at hle
  have hnegH : ∀ k (hk : k < D.length), j₀ ≤ k → k < k₁ → H D[k].1 < 0 := fun k hk hkj hkk₁ ↦ by
    have := hfall' k hkj hkk₁
    rw [hgt_succ k hk] at this
    exact neg_of_mul_neg_right (by linarith) (hdpos k hk).le
  have hHk₀₁ : hgt (j₀ + 1) < z + 1 := by
    have hdH : d * H τ < 0 := by
      have := hnegH j₀ hj₀lt le_rfl hj₀k₁
      rw [hDj₀] at this
      exact mul_neg_of_pos_of_neg (by simpa [d] using π.duration_pos j₀') this
    have hstep := hgt_succ j₀ hj₀lt
    rw [hDj₀] at hstep
    have hlt_mul : d * H τ < θ * (d * H τ) := by
      have : (1 - θ) * (d * H τ) < 0 := mul_neg_of_pos_of_neg (by linarith) hdH
      linarith
    linarith
  have hmono : ∀ m k, j₀ + 1 ≤ k → k + m ≤ k₁ → hgt (k + m) ≤ hgt k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro k hk hkm
      exact (hfall' (k + m) (by omega) (by omega)).le.trans (ih k hk (by omega))
  have hbetween : ∀ k, j₀ < k → k < k₁ → (z : ℚ) < hgt k ∧ hgt k < z + 1 := by
    intro k hkj hkk₁
    refine ⟨?_, ?_⟩
    · have h₁ := hfall' (k₁ - 1) (by omega) (by omega)
      have h₂ := hmono (k₁ - 1 - k) k (by omega) (by omega)
      rw [show k + (k₁ - 1 - k) = k₁ - 1 by omega] at h₂
      rw [show k₁ - 1 + 1 = k₁ by omega, hgtk₁] at h₁
      linarith
    · have h₂ := hmono (k - (j₀ + 1)) (j₀ + 1) le_rfl (by omega)
      rw [show j₀ + 1 + (k - (j₀ + 1)) = k by omega] at h₂
      linarith
  have hrightH : ∀ (hk : k₁ < D.length), 0 ≤ H D[k₁].1 := fun hk ↦ by
    have hle := hmin_le (k₁ + 1)
    rw [hgt_succ k₁ hk, hgtk₁] at hle
    exact nonneg_of_mul_nonneg_right (by linarith) (hdpos k₁ hk)
  have hcong : ∀ k (hk : k < D.length), ∃ m : ℤ, hgt k - cum k * H D[k].1 = m := fun k hk ↦
    π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
  refine ⟨j₀, k₁, hj₀k₁, hk₁D, θ, hθ₀, hθlt.le,
    fun k hk hkj hkk₁ ↦ ?_, fun k hk hkj hkk₁ ↦ ?_, fun hk ↦ ?_, ?_,
    hgtk₁, habove', hfall', ?_, hHk₀₁.le⟩
  · have h := hnegH k hk hkj hkk₁
    simp only [H] at h
    exact_mod_cast h
  · rintro ⟨m, hm⟩
    obtain ⟨m', hm'⟩ := hcong k hk
    obtain ⟨h₁, h₂⟩ := hbetween k hkj hkk₁
    have hk' : hgt k = ((m' + m : ℤ) : ℚ) := by
      simp only [H] at hm'
      push_cast
      linarith
    rw [hk'] at h₁ h₂
    have h₁' : z < m' + m := by exact_mod_cast h₁
    have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
    omega
  · have h := hrightH hk
    simp only [H] at h
    exact_mod_cast h
  · obtain ⟨m, hm⟩ := hcong j₀ hj₀lt
    refine ⟨z + 1 - m, ?_⟩
    rw [hDj₀] at hm ⊢
    simp only [H] at hm hcross'
    push_cast
    linear_combination hcross' - hm
  · rwa [hDj₀]

/-- Present `PLPath.raise` on any shape `lam₂` with the same `dirDurations` and `αᵢ^∨`-orbit
pairings as `π` using `raiseList`. -/
private theorem raise_toPLPath_eq_ofSegments_raiseList {𝕜 V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (π : LSPath P b lam) {lam₂ : M} (π₂ : LSPath P b lam₂) (i : b.support)
    (hdir : π₂.dirDurations = π.dirDurations)
    (hcoroot : ∀ w : P.weylGroup, P.coroot' i (w • lam₂) = P.coroot' i (w • lam))
    {z : ℤ} (hz₀ : (π.toPLPath ℚ (evalRat P)).minHeight (projCoroot P i) = z)
    {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ π.dirDurations.length) {θ : ℚ}
    (hgtk₁ : ((π.dirDurations.take k₁).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum = z)
    (habove : ∀ k ≤ j₀, (z : ℚ) + 1 ≤
      ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hfall : ∀ k, j₀ ≤ k → k < k₁ →
      ((π.dirDurations.take (k + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
        ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hcross : ((π.dirDurations.take j₀).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum +
      θ * ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 *
        P.coroot' i ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1 • lam)) = z + 1)
    (hHk₀₁ : ((π.dirDurations.take (j₀ + 1)).map fun p ↦
      p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum ≤ z + 1)
    (f : M →+ V) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    PLPath.raise F (f (P.root i)) (π₂.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
      ((raiseList b i π.dirDurations j₀ k₁
        (π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1
        (π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 θ).map
          fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂))) := by
  set D := π.dirDurations
  have hj₀lt : j₀ < D.length := lt_of_lt_of_le hj₀k₁ hk₁
  set seg₂ : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂)
  have hHF₂ : ∀ k, F ((D.map seg₂).take k).sum =
      (((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum : 𝕜) := by
    intro k
    simp only [← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
    congr 1
    refine List.map_congr_left fun p _ ↦ ?_
    simp [seg₂, hF, hcoroot]
  have hmin₂ : PLPath.listMinHeight F (D.map seg₂) = (z : 𝕜) := by
    rw [← PLPath.minHeight_ofSegments, ← hdir, ← map_snd_timed, ← toPLPath_def]
    exact minHeight_eq_of_dirDurations_eq π π₂ i hdir hcoroot hz₀ f F hF
  have hseg₂_j₀ : (D.map seg₂)[j₀]'(by simp only [List.length_map]; exact hj₀lt) =
      (D[j₀].2 : 𝕜) • f (D[j₀].1 • lam₂) := by
    rw [List.getElem_map]
  rw [toPLPath_def, map_snd_timed, hdir,
    PLPath.raise_ofSegments_eq_of_strictly_falling (k₀ := j₀) (k₁ := k₁) (θ := (θ : 𝕜))
      hj₀k₁ (by simp only [List.length_map]; exact hk₁)]
  · congr 2
    have hσ : ∀ (c : 𝕜) (w : P.weylGroup),
        c • f (((weylCoxeterSystem P b).simple i * w) • lam₂) =
          Module.preReflection (f (P.root i)) F (c • f (w • lam₂)) := fun c w ↦
      (preReflection_smul_apply f i F hF c w).symm
    simp only [raiseList, D, seg₂, hseg₂_j₀, List.map_append, List.map_cons, List.map_nil,
      List.map_map, List.map_take, List.map_drop, Function.comp_def, hσ, smul_smul,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  · rw [hHF₂, hgtk₁, hmin₂, Rat.cast_intCast]
  · intro k hk
    rw [hmin₂, hHF₂]
    exact_mod_cast habove k hk
  · intro k hkj hkk₁
    rw [hHF₂, hHF₂, Rat.cast_lt]
    exact hfall k hkj hkk₁
  · rw [hHF₂, hseg₂_j₀, hmin₂]
    simp only [map_smul, smul_eq_mul, hF, hcoroot]
    exact_mod_cast hcross
  · rw [hHF₂, hmin₂]
    exact_mod_cast hHk₀₁

/-- **Shape-invariance of `dirDurations` under raising.** If `π₁` (of dominant shape `λ₁`) and
`π₂` (of dominant shape `λ₂`) have the same `dirDurations` and the same `αᵢ^∨`-pairings along the
Weyl orbit, then in any two ordered-field realizations `(f₁, F₁)` and `(f₂, F₂)` inducing
`⟨-, αᵢ^∨⟩`, either `e_αᵢ` is `none` on both, or there exist `π₁' : LSPath P b λ₁` and
`π₂' : LSPath P b λ₂` with the same `dirDurations` realizing `e_αᵢ` on `π₁` and `π₂`. -/
theorem exists_dirDurations_eq_of_raise_of_dirDurations_eq
    {lam₁ lam₂ : M} {𝕜₁ V₁ 𝕜₂ V₂ : Type*}
    [Field 𝕜₁] [LinearOrder 𝕜₁] [IsStrictOrderedRing 𝕜₁] [AddCommGroup V₁] [Module 𝕜₁ V₁]
    [Field 𝕜₂] [LinearOrder 𝕜₂] [IsStrictOrderedRing 𝕜₂] [AddCommGroup V₂] [Module 𝕜₂ V₂]
    (π₁ : LSPath P b lam₁) (π₂ : LSPath P b lam₂)
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b) (i : b.support)
    (hdir : π₁.dirDurations = π₂.dirDurations)
    (hcoroot : ∀ w : P.weylGroup, P.coroot' i (w • lam₁) = P.coroot' i (w • lam₂))
    (f₁ : M →+ V₁) (F₁ : Module.Dual 𝕜₁ V₁) (hF₁ : ∀ m, F₁ (f₁ m) = (P.coroot' i m : 𝕜₁))
    (f₂ : M →+ V₂) (F₂ : Module.Dual 𝕜₂ V₂) (hF₂ : ∀ m, F₂ (f₂ m) = (P.coroot' i m : 𝕜₂)) :
    (PLPath.raise F₁ (f₁ (P.root i)) (π₁.toPLPath 𝕜₁ f₁) = none ∧
      PLPath.raise F₂ (f₂ (P.root i)) (π₂.toPLPath 𝕜₂ f₂) = none) ∨
    ∃ (π₁' : LSPath P b lam₁) (π₂' : LSPath P b lam₂),
      π₁'.dirDurations = π₂'.dirDurations ∧
      PLPath.raise F₁ (f₁ (P.root i)) (π₁.toPLPath 𝕜₁ f₁) = some (π₁'.toPLPath 𝕜₁ f₁) ∧
      PLPath.raise F₂ (f₂ (P.root i)) (π₂.toPLPath 𝕜₂ f₂) = some (π₂'.toPLPath 𝕜₂ f₂) := by
  obtain ⟨z, hz₀⟩ := π₁.exists_minHeight_eq_intCast hlam₁ (evalRat P) i (projCoroot P i)
    fun _ ↦ rfl
  by_cases hz : z ≤ -1
  · right
    obtain ⟨j₀, k₁, hj₀k₁, hk₁, θ, hθ₀, hθ₁, hneg, hint, hright, hcut,
      hgtk₁, habove, hfall, hcross, hHk₀₁⟩ := exists_raiseList_data π₁ hlam₁ i hz₀ hz
    have hj₀ : j₀ < π₁.dirDurations.length := lt_of_lt_of_le hj₀k₁ hk₁
    obtain ⟨hL₁, hLmin₁⟩ := linked_raiseList hlam₁ π₁.linked_dirDurations
      (fun _ hp ↦ π₁.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁ θ hneg hint hright hcut
    have hk₁₂ : k₁ ≤ π₂.dirDurations.length := hdir ▸ hk₁
    have hL₂_pair :
        Linked P b lam₂ 0 (raiseList b i π₁.dirDurations j₀ k₁
          (π₁.dirDurations[j₀]'hj₀).1 (π₁.dirDurations[j₀]'hj₀).2 θ) ∧
        ∀ p ∈ raiseList b i π₁.dirDurations j₀ k₁
            (π₁.dirDurations[j₀]'hj₀).1 (π₁.dirDurations[j₀]'hj₀).2 θ,
          (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam₂) p.1 := by
      have hLp := linked_raiseList hlam₂ π₂.linked_dirDurations
        (fun _ hp ↦ π₂.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁₂ θ
        (fun k hk hkj hkk₁ ↦ by
          have hk' : k < π₁.dirDurations.length := hdir ▸ hk
          have hget : π₂.dirDurations[k] = π₁.dirDurations[k] := by simp [hdir]
          rw [hget, ← hcoroot]
          exact hneg k hk' hkj hkk₁)
        (fun k hk hkj hkk₁ ↦ by
          have hk' : k < π₁.dirDurations.length := hdir ▸ hk
          have hget : π₂.dirDurations[k] = π₁.dirDurations[k] := by simp [hdir]
          rw [hget, ← hdir, ← hcoroot]
          exact hint k hk' hkj hkk₁)
        (fun hk ↦ by
          have hk' : k₁ < π₁.dirDurations.length := hdir ▸ hk
          have hget : π₂.dirDurations[k₁] = π₁.dirDurations[k₁] := by simp [hdir]
          rw [hget, ← hcoroot]
          exact hright hk')
        (by
          have hget : π₂.dirDurations[j₀]'(hdir ▸ hj₀) = π₁.dirDurations[j₀] := by simp [hdir]
          rw [hget, ← hdir, ← hcoroot]
          exact hcut)
      have hget₀ : π₂.dirDurations[j₀]'(hdir ▸ hj₀) = π₁.dirDurations[j₀] := by simp [hdir]
      rwa [hget₀, ← hdir] at hLp
    have hnonneg : ∀ p ∈ raiseList b i π₁.dirDurations j₀ k₁
        (π₁.dirDurations[j₀]'hj₀).1 (π₁.dirDurations[j₀]'hj₀).2 θ, 0 ≤ p.2 :=
      fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π₁.pos_of_mem_dirDurations hp).le)
        (π₁.pos_of_mem_dirDurations (List.getElem_mem hj₀)).le hθ₀ hθ₁ hp
    have hsum : ((raiseList b i π₁.dirDurations j₀ k₁
        (π₁.dirDurations[j₀]'hj₀).1 (π₁.dirDurations[j₀]'hj₀).2 θ).map Prod.snd).sum = 1 := by
      rw [sum_map_snd_raiseList i hj₀k₁ hk₁, sum_map_snd_dirDurations]
    refine ⟨ofLinked _ hLmin₁ hnonneg hsum hL₁,
      ofLinked _ hL₂_pair.2 hnonneg hsum hL₂_pair.1,
      dirDurations_ofLinked_eq _ hLmin₁ hL₂_pair.2 hnonneg hsum hL₁ hL₂_pair.1, ?_, ?_⟩
    · rw [toPLPath_ofLinked]
      exact raise_toPLPath_eq_ofSegments_raiseList π₁ π₁ i rfl (fun _ ↦ rfl) hz₀ hj₀k₁ hk₁
        hgtk₁ habove hfall hcross hHk₀₁ f₁ F₁ hF₁
    · rw [toPLPath_ofLinked]
      exact raise_toPLPath_eq_ofSegments_raiseList π₁ π₂ i hdir.symm (fun w ↦ (hcoroot w).symm)
        hz₀ hj₀k₁ hk₁ hgtk₁ habove hfall hcross hHk₀₁ f₂ F₂ hF₂
  · left
    have hz' : -1 < z := not_le.mp hz
    refine ⟨?_, ?_⟩
    · rw [PLPath.raise_eq_none_iff,
        minHeight_eq_of_dirDurations_eq π₁ π₁ i rfl (fun _ ↦ rfl) hz₀ f₁ F₁ hF₁]
      exact_mod_cast hz'
    · rw [PLPath.raise_eq_none_iff,
        minHeight_eq_of_dirDurations_eq π₁ π₂ i hdir.symm (fun w ↦ (hcoroot w).symm) hz₀ f₂ F₂ hF₂]
      exact_mod_cast hz'

/-- **Compatibility of Littelmann's raising operator across two realizations.** For a dominant
shape `λ`, an LS path `π`, and any two ordered-field realizations `(f₁, F₁)` and `(f₂, F₂)`
inducing `⟨-, αᵢ^∨⟩`, either `e_αᵢ` is `none` in both realizations, or a single LS path `π'` of
shape `λ` realizes `e_αᵢ π` in both realizations. -/
theorem exists_raise_toPLPath_eq_and_eq
    {𝕜₁ V₁ 𝕜₂ V₂ : Type*}
    [Field 𝕜₁] [LinearOrder 𝕜₁] [IsStrictOrderedRing 𝕜₁] [AddCommGroup V₁] [Module 𝕜₁ V₁]
    [Field 𝕜₂] [LinearOrder 𝕜₂] [IsStrictOrderedRing 𝕜₂] [AddCommGroup V₂] [Module 𝕜₂ V₂]
    (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (f₁ : M →+ V₁) (F₁ : Module.Dual 𝕜₁ V₁) (hF₁ : ∀ m, F₁ (f₁ m) = (P.coroot' i m : 𝕜₁))
    (f₂ : M →+ V₂) (F₂ : Module.Dual 𝕜₂ V₂) (hF₂ : ∀ m, F₂ (f₂ m) = (P.coroot' i m : 𝕜₂)) :
    (PLPath.raise F₁ (f₁ (P.root i)) (π.toPLPath 𝕜₁ f₁) = none ∧
      PLPath.raise F₂ (f₂ (P.root i)) (π.toPLPath 𝕜₂ f₂) = none) ∨
    ∃ π' : LSPath P b lam,
      PLPath.raise F₁ (f₁ (P.root i)) (π.toPLPath 𝕜₁ f₁) = some (π'.toPLPath 𝕜₁ f₁) ∧
      PLPath.raise F₂ (f₂ (P.root i)) (π.toPLPath 𝕜₂ f₂) = some (π'.toPLPath 𝕜₂ f₂) := by
  rcases exists_dirDurations_eq_of_raise_of_dirDurations_eq π π hlam hlam i rfl (fun _ ↦ rfl)
    f₁ F₁ hF₁ f₂ F₂ hF₂ with hnone | ⟨π₁', π₂', hdir', h₁, h₂⟩
  · exact Or.inl hnone
  · obtain rfl : π₁' = π₂' := dirDurations_injective hdir'
    exact Or.inr ⟨π₁', h₁, h₂⟩

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  rcases π.exists_raise_toPLPath_eq_and_eq hlam i f F hF f F hF with ⟨hnone, -⟩ | ⟨π', hsome, -⟩
  · rw [hnone] at hq
    cases hq
  · exact ⟨π', Option.some.inj (hsome.symm.trans hq)⟩

end TauCeti.LSPath
