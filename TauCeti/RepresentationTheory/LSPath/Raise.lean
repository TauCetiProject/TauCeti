/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Crystal.Basic
public import TauCeti.RepresentationTheory.LSPath.Lower

import TauCeti.Data.List.TakeDrop
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.LSPath.Weight

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root, and write
`H(t) = ⟨π(t), αᵢ^∨⟩` for its running height, with minimum `h`. When `h ≤ -1`, Littelmann's
raising operator `e_αᵢ` reflects by `sᵢ` the single piece of the path between the first time `t₁`
at which `H = h` and the last earlier time `t₀` at which `H = h + 1`, and keeps the rest
(`TauCeti.LSPath.exists_raise_toPLPath_eq`). This file proves Littelmann's theorem that the result
is again the path of an LS path of shape `λ` (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`),
the mirror image of `TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`.

In terms of the directions `τ₀ > ⋯ > τ_l` and durations of `π`, with `t₀` inside the segment `j₀`
and `t₁` a break, the raised path runs along the list of directions
`τ₀, …, τ_{j₀}, sᵢ τ_{j₀}, …, sᵢ τ_{k₁ - 1}, τ_{k₁}, …, τ_l`, the segment `j₀` being cut at `t₀`.
This list is linked (`TauCeti.LSPath.Linked`), so it defines an LS path by
`TauCeti.LSPath.ofLinked`, which merges repeated directions. The chain conditions at its breaks
are Littelmann's, proved in `TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain`:

* at `t₀` the height `h + 1` is an integer, so the cover `sᵢ τ_{j₀} ⋖ τ_{j₀}` is a `t₀`-chain;
* at a break `a` strictly inside the reflected piece the height lies strictly between the integers
  `h` and `h + 1`, so `a ⟨τ λ, αᵢ^∨⟩` is not an integer, and the `a`-chain stays on the negative
  side of the wall of `αᵢ`, where `sᵢ` carries it to an `a`-chain;
* at `t₁` the height has its first minimum, so `⟨τ_{k₁ - 1} λ, αᵢ^∨⟩ < 0 ≤ ⟨τ_{k₁} λ, αᵢ^∨⟩`, and
  an `a`-chain from `τ_{k₁ - 1}` down to `τ_{k₁}` gives one from `sᵢ τ_{k₁ - 1}`, possibly of
  length `0`.

With lowering stability, this makes the realized LS paths of a dominant shape an operator-closed
set of paths with lattice endpoints and integral minimal heights
(`TauCeti.LSPath.isCrystalSet_range_toPLPath`), which `TauCeti.PLPath.normalCrystalOn` turns
into a normal crystal when `f` is injective.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator
  preserves Lakshmibai–Seshadri paths**.
* `TauCeti.LSPath.isCrystalSet_range_toPLPath`: the realized LS paths of a dominant shape form a
  crystal-admissible set of paths (`TauCeti.PLPath.IsCrystalSet`).
* `TauCeti.LSPath.isIntegralPath_toPLPath`, `TauCeti.PLPath.isIntegralPath_straight`: realized
  LS paths of dominant shape and straight paths along arbitrary weights are integral in any
  compatible realization (`F i (f x) = (P.coroot' i x : 𝕜)`).

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

/-- **Reflecting a falling window of a linked list.** Let `[k₀, j₁]` be a window of entries of a
linked list along which the heights `⟨τ λ, αᵢ^∨⟩` of the directions are negative, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at the internal breaks `a`, entered from an entry with the same
direction as its first one, at a break `a` with `a ⟨τ λ, αᵢ^∨⟩` integral, and followed by a
direction of nonnegative height. Replacing the directions `τ` in the window by `sᵢ τ` keeps the
list linked. -/
private theorem Linked.mapIdx_simple_mul_of_neg (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {k₀ j₁ : ℕ}
    (hneg : ∀ k (hk : k < l.length), k₀ ≤ k → k ≤ j₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), k₀ < k → k ≤ j₁ →
      ¬∃ z : ℤ, (t + ((l.take k).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hright : ∀ k (hk : k < l.length), k = j₁ + 1 → 0 ≤ P.coroot' i (l[k].1 • lam))
    (hcut : ∀ k (hk : k + 1 < l.length), k + 1 = k₀ → l[k].1 = l[k + 1].1)
    (hcutint : ∀ k (hk : k + 1 < l.length), k + 1 = k₀ → ∃ z : ℤ,
      (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (l[k + 1].1 • lam) = z) :
    Linked P b lam t (l.mapIdx fun k p ↦
      if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) := by
  set g : ℕ → P.weylGroup × ℚ → P.weylGroup × ℚ := fun k p ↦
    if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p
  -- The reflection keeps the durations, hence the break times.
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
  by_cases hk₁ : k₀ ≤ k ∧ k ≤ j₁ <;> by_cases hk₂ : k₀ ≤ k + 1 ∧ k + 1 ≤ j₁ <;>
    simp only [hk₁, hk₂, and_self, ↓reduceIte]
  · -- Both ends in the window: the chain stays on the negative side and reflects.
    have hint' : ¬∃ z : ℤ,
        (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (C.head.val • lam) = z := by
      rintro ⟨z, hz⟩
      obtain ⟨z', hz'⟩ := hC.exists_mul_sub_eq_intCast hlam (P.coroot' i)
      refine hint (k + 1) hk (by omega) hk₂.2 ⟨z - z', ?_⟩
      rw [← hlast]
      push_cast at hz' ⊢
      linear_combination hz - hz'
    have hall := hC.coroot'_smul_neg hlam i (by rw [hhead]; exact hneg k (by omega) hk₁.1 hk₁.2)
      hint'
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inr hall), ?_, ?_,
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
    · simp [hhead]
    · simp [hlast]
  · -- Leaving the window at its end `j₁`: Littelmann's chain at the end of a reflected piece.
    obtain rfl : k = j₁ := by omega
    obtain ⟨D, hDhead, hDlast, hD⟩ := hC.exists_isAChain_simple_mul_head hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁.1 le_rfl)
      (by rw [hlast]; exact hright (k + 1) (by simpa using hk) rfl)
    exact ⟨D, by rw [hDhead, hhead], by rw [hDlast, hlast], hD⟩
  · -- Entering the window at `k₀`: the cover `sᵢ τ ⋖ τ`.
    have hkk : k + 1 = k₀ := by omega
    have hτ : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) l[k + 1].1 :=
      hmin _ (List.getElem_mem hk)
    have hneg' := hneg (k + 1) hk hk₂.1 hk₂.2
    rw [hcut k hk hkk]
    obtain ⟨z, hz⟩ := hcutint k hk hkk
    obtain ⟨D, hDhead, hDlast, hD⟩ := exists_isAChain_simple_mul_of_coroot'_pos hlam
      (isMinimalCosetRep_simple_mul_of_coroot'_ne_zero hτ hneg'.ne)
      (by rw [coroot'_simple_mul_smul_eq_neg]; exact neg_pos.mpr hneg')
      (a := t + ((l.take (k + 1)).map Prod.snd).sum)
      ⟨-z, by rw [coroot'_simple_mul_smul_eq_neg]; push_cast at hz ⊢; linear_combination -hz⟩
    exact ⟨D, by rw [hDhead, CoxeterSystem.simple_mul_simple_cancel_left], hDlast, hD⟩
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
/-- The directions and durations produced from `l` by Littelmann's raising operator along the
simple root `αᵢ`: the entries before `j₀` and the first part `(τ, θ d)` of the entry
`l[j₀] = (τ, d)` are kept, and the rest `(τ, (1 - θ) d)` of that entry and the entries
`j₀ + 1, …, k₁ - 1` are reflected by `sᵢ`, before the later entries. -/
private noncomputable def raiseList (i : b.support) (l : List (P.weylGroup × ℚ)) (j₀ k₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  l.take j₀ ++ (τ, θ * d) :: ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).map
      (fun p ↦ ((weylCoxeterSystem P b).simple i * p.1, p.2)) ++ l.drop k₁

private theorem nonneg_of_mem_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) {j₀ k₁ : ℕ} {τ : P.weylGroup} {d θ : ℚ} (hd : 0 ≤ d) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) {p : P.weylGroup × ℚ} (hp : p ∈ raiseList b i l j₀ k₁ τ d θ) : 0 ≤ p.2 := by
  simp only [raiseList, List.mem_append, List.mem_cons, List.map_cons, List.mem_map] at hp
  rcases hp with (hp | rfl | rfl | ⟨q, hq, rfl⟩) | hp
  · exact hl p (List.mem_of_mem_take hp)
  · exact mul_nonneg hθ₀ hd
  · exact mul_nonneg (by linarith) hd
  · exact hl q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
  · exact hl p (List.mem_of_mem_drop hp)

private theorem sum_map_snd_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)} {j₀ k₁ : ℕ}
    (hj₀ : j₀ < l.length) (hj₀k₁ : j₀ < k₁) (θ : ℚ) :
    ((raiseList b i l j₀ k₁ l[j₀].1 l[j₀].2 θ).map Prod.snd).sum = (l.map Prod.snd).sum := by
  have hsplit : l.drop j₀ = l[j₀] :: ((l.take k₁).drop (j₀ + 1) ++ l.drop k₁) := by
    rw [List.drop_eq_getElem_cons hj₀, List.drop_take_append_drop_of_le _ hj₀k₁]
  conv_rhs => rw [← List.take_append_drop j₀ l, hsplit]
  simp only [raiseList, List.map_append, List.map_cons, List.map_map, List.sum_append,
    List.sum_cons, Function.comp_def]
  ring

/-- **The raised list is linked.** Let `l` be a linked list of minimal coset representatives,
let `[j₀, k₁ - 1]` be a window along which the height `⟨-, αᵢ^∨⟩` of the directions is negative,
with `a ⟨τ λ, αᵢ^∨⟩` nonintegral at its internal breaks `a`, followed by a direction of
nonnegative height, and let `θ` cut the entry `l[j₀] = (τ, d)` at an `a`-integral time. Then the
list `TauCeti.LSPath.raiseList` produced by Littelmann's raising operator is linked, and its
directions are minimal coset representatives. -/
private theorem linked_raiseList (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ)
    (hneg : ∀ k (hk : k < l.length), j₀ ≤ k → k < k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), j₀ < k → k < k₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i (l[k].1 • lam) = m)
    (hright : ∀ k (hk : k < l.length), k = k₁ → 0 ≤ P.coroot' i (l[k].1 • lam))
    (hcut : ∃ m : ℤ, (((l.take j₀).map Prod.snd).sum + θ * (l[j₀]'(by omega)).2) *
      P.coroot' i ((l[j₀]'(by omega)).1 • lam) = m) :
    Linked P b lam 0 (raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ) ∧
      ∀ p ∈ raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hj₀ : j₀ < l.length := by omega
  set τ := l[j₀].1 with hτ
  set d := l[j₀].2 with hd
  set s := (weylCoxeterSystem P b).simple i with hs
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
  -- The entries and break times of the subdivided list.
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
  have hDp_fst : ∀ k (hk : k < Dp.length) (hkj : j₀ + 1 ≤ k),
      Dp[k].1 = (l[k - 1]'(by omega)).1 := by
    intro k hk hkj
    rcases hkj.eq_or_lt with rfl | hkj
    · rw [hDp_j₀1]
      simp [hτ]
    · simp only [Dp]
      rw [List.getElem_append_right (by omega)]
      obtain ⟨n, rfl⟩ : ∃ n, k = j₀ + 2 + n := ⟨k - (j₀ + 2), by omega⟩
      simp [hlen_take, show j₀ + 2 + n - j₀ = n + 2 by omega,
        show j₀ + 2 + n - 1 = j₀ + 1 + n by omega]
  have hcum_j₀1 : ((Dp.take (j₀ + 1)).map Prod.snd).sum =
      ((l.take j₀).map Prod.snd).sum + θ * d := by
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₀ + 1 - j₀ = 1 by omega]
    simp
  have hcum_ge : ∀ k, j₀ + 2 ≤ k →
      ((Dp.take k).map Prod.snd).sum = ((l.take (k - 1)).map Prod.snd).sum := by
    intro k hk₁
    have hl' : l.take (k - 1) = l.take j₀ ++ l[j₀] :: (l.drop (j₀ + 1)).take (k - j₀ - 2) := by
      rw [show k - 1 = j₀ + 1 + (k - j₀ - 2) by omega, List.take_add,
        List.take_succ_eq_append_getElem hj₀, List.append_assoc, List.singleton_append]
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show k - j₀ = k - j₀ - 2 + 1 + 1 by omega, List.take_succ_cons, List.take_succ_cons, hl']
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [show (l[j₀]).2 = d from rfl]
    ring
  -- Reflect the window `[j₀ + 1, k₁]` of the subdivided list in `sᵢ`.
  have hW := Linked.mapIdx_simple_mul_of_neg hlam hDp_linked hDpmin i (k₀ := j₀ + 1) (j₁ := k₁)
    (fun k hk hk₀ hkj ↦ by
      rw [hDp_fst k hk hk₀]
      exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hk₀ hkj ↦ by
      rw [zero_add, hcum_ge k (by omega), hDp_fst k hk (by omega)]
      exact hint (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkk ↦ by
      rw [hDp_fst k hk (by omega)]
      exact hright (k - 1) (by omega) (by omega))
    (fun k hk hkk ↦ by
      obtain rfl : k = j₀ := by omega
      rw [hDp_j₀, hDp_j₀1])
    (fun k hk hkk ↦ by
      obtain rfl : k = j₀ := by omega
      rw [zero_add, hcum_j₀1, hDp_j₀1]
      exact hcut)
  -- The reflected subdivided list is the raised list.
  have hraise : raiseList b i l j₀ k₁ τ d θ =
      Dp.mapIdx fun k p ↦ if j₀ + 1 ≤ k ∧ k ≤ k₁ then (s * p.1, p.2) else p := by
    have hDp' : Dp = l.take j₀ ++ [(τ, θ * d)] ++ ((τ, (1 - θ) * d) ::
        (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
      rw [hDp, ← List.drop_take_append_drop_of_le l hj₀k₁]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hA : (l.take j₀ ++ [(τ, θ * d)]).length = j₀ + 1 := by simp; omega
    have hB : ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by
      simp; omega
    rw [hDp']
    refine List.ext_getElem (by simp [raiseList]) fun k hk₁ hk₂ ↦ ?_
    simp only [raiseList, List.getElem_mapIdx, List.getElem_append, List.length_append, hA, hB,
      List.length_cons, List.length_map, hlen_take, List.getElem_cons, List.getElem_map]
    split_ifs <;> first | rfl | omega | congr 1; omega
  rw [hraise]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst k hk' hw.1]
    exact (hneg (k - 1) (by omega) (by omega) (by omega)).ne
  · exact hDpmin _ (List.getElem_mem hk')

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V]

/-- **The rational data of a raising step.** If Littelmann's raising operator `e_αᵢ` is defined on
the path of an LS path `π` of dominant shape, it is presented by the raised list
`TauCeti.LSPath.raiseList` of the directions and durations of `π`, for a window `[j₀, k₁ - 1]` and
a cut `θ` satisfying the hypotheses of `TauCeti.LSPath.linked_raiseList`. -/
private theorem exists_raise_toPLPath_eq_ofSegments_raiseList (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    (h1 : (π.toPLPath 𝕜 f).minHeight F ≤ -1) :
    ∃ (j₀ k₁ : ℕ) (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ π.dirDurations.length) (θ : ℚ),
      0 ≤ θ ∧ θ ≤ 1 ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ ≤ k → k < k₁ →
        P.coroot' i (π.dirDurations[k].1 • lam) < 0) ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ < k → k < k₁ →
        ¬∃ m : ℤ, ((π.dirDurations.take k).map Prod.snd).sum *
          P.coroot' i (π.dirDurations[k].1 • lam) = m) ∧
      (∀ k (hk : k < π.dirDurations.length), k = k₁ →
        0 ≤ P.coroot' i (π.dirDurations[k].1 • lam)) ∧
      (∃ m : ℤ, (((π.dirDurations.take j₀).map Prod.snd).sum +
        θ * (π.dirDurations[j₀]'(by omega)).2) *
          P.coroot' i ((π.dirDurations[j₀]'(by omega)).1 • lam) = m) ∧
      PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
        ((raiseList b i π.dirDurations j₀ k₁ (π.dirDurations[j₀]'(by omega)).1
          (π.dirDurations[j₀]'(by omega)).2 θ).map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))) := by
  obtain ⟨j₀', k₁, θ, hj₀k₁, hk₁s, hθ₀, hθ₁, hmin, hfall, hcross, -, hrai⟩ :=
    π.exists_raise_toPLPath_eq hlam f i F hF (f (P.root i)) h1
  obtain ⟨z, hz⟩ := π.exists_minHeight_eq_intCast hlam f i F hF
  have hminH : (π.toPLPath 𝕜 f).minHeight F =
      PLPath.listMinHeight F (π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) := by
    rw [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed]
  rw [map_snd_timed] at hmin hfall hcross hrai
  set D := π.dirDurations
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam) with hseg
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum with hhgt
  have hHdef : ∀ w, H w = (P.coroot' i (w • lam) : ℚ) := fun _ ↦ rfl
  set j₀ : ℕ := (j₀' : ℕ) with hj₀
  have hlen : D.length = π.length + 1 := length_dirDurations π
  have hj₀lt : j₀ < D.length := by rw [hlen]; exact j₀'.isLt
  have hk₁ : k₁ ≤ D.length := hlen ▸ hk₁s
  set τ := (π.dir j₀').val with hτ
  set d := π.duration j₀' with hd
  have hDj₀ : D[j₀] = (τ, d) := by rw [getElem_dirDurations]
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  -- Heights of the realization at the vertices are the rational heights of the encoding.
  have hHF : ∀ k, F ((D.map seg).take k).sum = (hgt k : 𝕜) :=
    apply_sum_take_map_smul D f F (P.coroot' i) hF
  have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
    intro k hk
    simp only [hgt, List.map_take]
    rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
  have hFseg : F ((d : 𝕜) • f (τ • lam)) = ((d * H τ : ℚ) : 𝕜) := by simp [H, hF]
  /- The rational heights: `hgt k₁ = z` is the minimum, the height falls strictly from `j₀` to
  `k₁`, and the piece reaches `z + 1` at the fraction `θ` of the segment `j₀`. -/
  have hgtk₁ : hgt k₁ = z := by
    rw [hHF, hz] at hmin
    exact_mod_cast hmin
  have hfall' : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k := fun k hj₀k hkk ↦ by
    have := hfall k hj₀k hkk
    rwa [hHF, hHF, Rat.cast_lt] at this
  have hnegH : ∀ k (hk : k < D.length), j₀ ≤ k → k < k₁ → H D[k].1 < 0 := fun k hk hj₀k hkk ↦ by
    have := hfall' k hj₀k hkk
    rw [hgt_succ k hk] at this
    exact neg_of_mul_neg_right (by linarith) (hdpos k hk).le
  have hdH : d * H τ < 0 := by
    have := hnegH j₀ hj₀lt le_rfl hj₀k₁
    rw [hDj₀] at this
    exact mul_neg_of_pos_of_neg (by rw [hd]; exact π.duration_pos _) this
  have hθd : θ * (d * H τ) = z + 1 - hgt j₀ := by
    rw [hHF, hz, hFseg] at hcross
    have hc : hgt j₀ + θ * (d * H τ) = z + 1 := by exact_mod_cast hcross
    linarith
  -- The heights strictly between `j₀` and `k₁` lie strictly between `z` and `z + 1`.
  have hanti : ∀ m k, j₀ ≤ k → k + m ≤ k₁ → hgt (k + m) ≤ hgt k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro k hk hkm
      exact (hfall' (k + m) (by omega) (by omega)).le.trans (ih k hk (by omega))
  have hbetween : ∀ k, j₀ < k → k < k₁ → (z : ℚ) < hgt k ∧ hgt k < z + 1 := by
    intro k hj₀k hkk
    refine ⟨?_, ?_⟩
    · have h₁ := hfall' (k₁ - 1) (by omega) (by omega)
      have h₂ := hanti (k₁ - 1 - k) k (by omega) (by omega)
      rw [show k + (k₁ - 1 - k) = k₁ - 1 by omega] at h₂
      rw [show k₁ - 1 + 1 = k₁ by omega, hgtk₁] at h₁
      linarith
    · have h₂ := hanti (k - (j₀ + 1)) (j₀ + 1) (by omega) (by omega)
      rw [show j₀ + 1 + (k - (j₀ + 1)) = k by omega, hgt_succ j₀ hj₀lt, hDj₀] at h₂
      nlinarith
  -- At the vertex `k₁` the height is minimal, so the segment after it does not fall.
  have hrightH : ∀ k (hk : k < D.length), k = k₁ → 0 ≤ H D[k].1 := fun k hk hkk ↦ by
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F) (D.map seg) (k + 1)
    rw [← hminH, hz, hHF] at hle
    have hle' : (z : ℚ) ≤ hgt (k + 1) := by exact_mod_cast hle
    have := hgt_succ k hk
    subst hkk
    rw [hgtk₁] at this
    exact nonneg_of_mul_nonneg_right (by linarith) (hdpos k hk)
  refine ⟨j₀, k₁, hj₀k₁, hk₁, θ, hθ₀, hθ₁.le, fun k hk hj₀k hkk ↦ ?_, fun k hk hj₀k hkk ↦ ?_,
    fun k hk hkk ↦ ?_, ?_, ?_⟩
  · have := hnegH k hk hj₀k hkk
    rw [hHdef] at this
    exact_mod_cast this
  · -- The height at the break is strictly between the integers `z` and `z + 1`.
    obtain ⟨h₁, h₂⟩ := hbetween k hj₀k hkk
    exact π.linked_dirDurations.not_exists_sum_take_mul_eq_intCast hlam (P.coroot' i) hk h₁ h₂
  · have := hrightH k hk hkk
    rw [hHdef] at this
    exact_mod_cast this
  · -- The height at the cut is the integer `z + 1`.
    have hcut : hgt j₀ + θ * (D[j₀].2 * H D[j₀].1) = ((z + 1 : ℤ) : ℚ) := by
      rw [hDj₀]
      push_cast
      linear_combination hθd
    exact π.linked_dirDurations.exists_sum_take_add_mul_mul_eq_intCast hlam (P.coroot' i) hj₀lt θ
      hcut
  · rw [hrai, hDj₀]
    congr 2
    simp only [raiseList, hseg, List.map_append, List.map_cons, List.map_map, List.map_take,
      List.map_drop, Function.comp_def, preReflection_smul_apply f i F hF, Rat.cast_mul,
      Rat.cast_sub, Rat.cast_one, D]

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  -- The raising operator is defined, so the minimal height is at most `-1`.
  have h1 : (π.toPLPath 𝕜 f).minHeight F ≤ -1 := by
    by_contra h
    have := (PLPath.raise_eq_none_iff (x := f (P.root i))).mpr (not_le.mp h)
    rw [hq] at this
    exact Option.some_ne_none _ this
  obtain ⟨j₀, k₁, hj₀k₁, hk₁, θ, hθ₀, hθ₁, hneg, hint, hright, hcut, hrai⟩ :=
    exists_raise_toPLPath_eq_ofSegments_raiseList π hlam f i F hF h1
  obtain ⟨hL, hLmin⟩ := linked_raiseList hlam π.linked_dirDurations
    (fun _ hp ↦ π.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁ θ hneg hint hright hcut
  refine ⟨ofLinked _ hLmin
    (fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π.pos_of_mem_dirDurations hp).le)
      (π.pos_of_mem_dirDurations (List.getElem_mem (by omega))).le hθ₀ hθ₁ hp)
    (by rw [sum_map_snd_raiseList i (by omega) hj₀k₁, sum_map_snd_dirDurations]) hL, ?_⟩
  rw [toPLPath_ofLinked]
  exact Option.some.inj (hrai.symm.trans hq)

/-- **The Lakshmibai–Seshadri paths of a dominant shape form a crystal-admissible set of paths.**
For dominant `λ`, a realization `f` of the weights and height forms `F i` inducing the simple
coroot pairings on `f(M)`, the realized paths of the LS paths of shape `λ` end in `f(M)`, have
integral minimal heights, and are closed under all the simple-root raising and lowering operators.
So, for injective `f`, `TauCeti.PLPath.normalCrystalOn` makes them a normal crystal. -/
theorem isCrystalSet_range_toPLPath (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    {F : b.support → Module.Dual 𝕜 V} (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) :
    PLPath.IsCrystalSet b f F (Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) where
  endpoint_mem_range := by
    rintro _ ⟨π, rfl⟩
    exact ⟨π.weight, π.apply_weight 𝕜 f⟩
  exists_minHeight_eq_intCast := by
    rintro _ ⟨π, rfl⟩ i
    exact π.exists_minHeight_eq_intCast hlam f i (F i) (hF i)
  mem_of_raise_eq_some := by
    rintro i _ q h ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_raise_eq_some hlam f i (F i) (hF i) h
  mem_of_lower_eq_some := by
    rintro i _ q h ⟨π, rfl⟩
    exact π.exists_toPLPath_eq_of_lower_eq_some hlam f i (F i) (hF i) h

/-- Every realized Lakshmibai–Seshadri path of dominant shape is an integral path in any compatible
realization (`∀ i x, F i (f x) = (P.coroot' i x : 𝕜)`). -/
theorem isIntegralPath_toPLPath (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ (i : b.support) (x : M), F i (f x) = (P.coroot' i x : 𝕜)) (π : LSPath P b lam) :
    PLPath.IsIntegralPath b f F (π.toPLPath 𝕜 f) :=
  (isCrystalSet_range_toPLPath hlam f hF).subset_isIntegralPath ⟨π, rfl⟩

end TauCeti.LSPath

namespace TauCeti.PLPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- The straight path along any weight `λ` is an integral path in any compatible realization
(`∀ i x, F i (f x) = (P.coroot' i x : 𝕜)`). -/
theorem isIntegralPath_straight (f : M →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ (i : b.support) (x : M), F i (f x) = (P.coroot' i x : 𝕜)) :
    IsIntegralPath b f F (straight 𝕜 (f lam)) := by
  have := P.flip_isReduced
  have := P.finite_weylGroup_of_base b
  obtain ⟨w, hw⟩ := P.exists_mem_dominantChamber_of_finite_weylGroup b lam
  obtain ⟨τ, ⟨hτmin, hτ⟩, -⟩ := existsUnique_isMinimalCosetRep_smul_eq hw w⁻¹
  have hsingle : (LSPath.single ⟨τ, hτmin⟩ : LSPath P b (w • lam)).toPLPath 𝕜 f =
      straight 𝕜 (f lam) := by
    rw [LSPath.toPLPath_single, hτ, inv_smul_smul]
  simpa only [hsingle] using LSPath.isIntegralPath_toPLPath hw f F hF (LSPath.single ⟨τ, hτmin⟩)

end TauCeti.PLPath
