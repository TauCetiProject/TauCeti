/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
import TauCeti.RepresentationTheory.LSPath.Concatenation
import TauCeti.RepresentationTheory.LSPath.Linked
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root, and write
`H(t) = ⟨π(t), αᵢ^∨⟩` for its running height, with minimum `h`. When `-h ≥ 1`, Littelmann's
raising operator `e_αᵢ` reflects by `sᵢ` the single piece of the path between the last time `t₀`
before the first minimum `t₁` at which `H = h + 1` and `t₁` itself, and keeps the rest
(`TauCeti.LSPath.exists_raise_toPLPath_eq`). This file proves Littelmann's theorem that the result
is again the path of an LS path of shape `λ` (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`),
produced by a single rational encoding independent of the chosen ordered-field realization
(`TauCeti.LSPath.raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some`).

In terms of the directions `τ₀ > ⋯ > τ_l` and durations of `π`, with `t₀` inside the segment `j₀`
and `t₁` at the vertex `k₁`, the raised path runs along the list of directions
`τ₀, …, τ_{j₀}, sᵢ τ_{j₀}, …, sᵢ τ_{k₁ - 1}, τ_{k₁}, …, τ_l`, the segment `j₀` being cut at `t₀`.
This list is linked (`TauCeti.LSPath.Linked`), so it defines an LS path by
`TauCeti.LSPath.ofLinked`, which drops zero-duration pieces and merges repeated directions. The
chain conditions at its breaks follow from `TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain`:

* at `t₀` the height `h + 1` is an integer and `⟨τ_{j₀} λ, αᵢ^∨⟩ < 0`, so `τ_{j₀} ⋗ sᵢ τ_{j₀}` is
  a `t₀`-chain;
* at a break `a` strictly inside the reflected piece the height lies strictly between the integers
  `h` and `h + 1`, so `a ⟨τ λ, αᵢ^∨⟩` is not an integer, and the `a`-chain stays on the negative
  side of the wall of `αᵢ`, where `sᵢ` carries it to an `a`-chain;
* at `t₁` the height attains its minimum, so `⟨τ_{k₁ - 1} λ, αᵢ^∨⟩ < 0 ≤ ⟨τ_{k₁} λ, αᵢ^∨⟩`, and an
  `a`-chain from `τ_{k₁ - 1}` down to `τ_{k₁}` gives one from `sᵢ τ_{k₁ - 1}` down to `τ_{k₁}`.

## Main results

* `TauCeti.LSPath.raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some`: **realization-independent
  action of Littelmann's raising operator on Lakshmibai–Seshadri encodings**.
* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator preserves
  Lakshmibai–Seshadri paths**.

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
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] [P.flip.IsReduced] {lam : M}

/-- **Reflecting a falling window of a linked list.** Let `[k₀, j₁]` be a window of entries of a
linked list along which the heights `⟨τ λ, αᵢ^∨⟩` of the directions are negative, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at the internal breaks `a` after `l[k]`, preceded by an entry with the
same direction as `l[k₀]` at a break `a` with `a ⟨τ λ, αᵢ^∨⟩` integral, and followed (if any entry
remains) by a direction of nonnegative height. Replacing the directions `τ` in the window by `sᵢ τ`
keeps the list linked. -/
private theorem Linked.mapIdx_simple_mul_neg (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {k₀ j₁ : ℕ} (hk₀ : 0 < k₀) (hk₀j₁ : k₀ ≤ j₁) (hj₁ : j₁ < l.length)
    (hneg : ∀ k (hk : k < l.length), k₀ ≤ k → k ≤ j₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), k₀ ≤ k → k < j₁ →
      ¬∃ z : ℤ, (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hright : ∀ k (hk : k < l.length), j₁ + 1 = k → 0 ≤ P.coroot' i (l[k].1 • lam))
    (hcut : (l[k₀ - 1]'(by omega)).1 = (l[k₀]'(by omega)).1)
    (hcutint : ∃ z : ℤ,
      (t + ((l.take k₀).map Prod.snd).sum) * P.coroot' i ((l[k₀]'(by omega)).1 • lam) = z) :
    Linked P b lam t (l.mapIdx fun k p ↦
      if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) := by
  set g : ℕ → P.weylGroup × ℚ → P.weylGroup × ℚ := fun k p ↦
    if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p
  have hsnd : (l.mapIdx g).map Prod.snd = l.map Prod.snd := by
    refine List.ext_getElem (by simp) fun k _ _ ↦ ?_
    simp only [g, List.getElem_map, List.getElem_mapIdx]
    split_ifs <;> rfl
  rw [linked_iff_getElem] at hl ⊢
  intro k hk
  have hk' : k + 1 < l.length := by simpa using hk
  rw [List.map_take, hsnd, ← List.map_take]
  obtain ⟨C, hhead, hlast, hC⟩ := hl k hk'
  simp only [List.getElem_mapIdx, g]
  by_cases hk₁ : k₀ ≤ k ∧ k ≤ j₁ <;> by_cases hk₂ : k₀ ≤ k + 1 ∧ k + 1 ≤ j₁ <;>
    simp only [hk₁, hk₂, and_self, ↓reduceIte]
  · -- Both ends in the window: the chain stays on the negative side and reflects.
    have hall := hC.coroot'_smul_neg hlam i (by rw [hhead]; exact hneg k (by omega) hk₁.1 hk₁.2)
      (by rw [hhead]; exact hint k (by omega) hk₁.1 (by omega))
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inr hall), ?_, ?_,
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
    · simp [hhead]
    · simp [hlast]
  · -- Leaving the window at its end `j₁`: Littelmann's chain at the end of a reflected piece.
    obtain ⟨D, hDhead, hDlast, hD⟩ := hC.exists_isAChain_simple_mul_head hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁.1 hk₁.2)
      (by rw [hlast]; exact hright (k + 1) hk' (by omega))
    exact ⟨D, by rw [hDhead, hhead], by rw [hDlast, hlast], hD⟩
  · -- Entering the window at `k₀`: the cover `sᵢ τ ⋖ τ`.
    obtain rfl : k₀ = k + 1 := by omega
    have hneg_k1 : P.coroot' i (l[k + 1].1 • lam) < 0 := hneg (k + 1) hk' le_rfl hk₂.2
    set u := (weylCoxeterSystem P b).simple i * l[k + 1].1
    have hu_min : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) u :=
      isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hmin _ (List.getElem_mem hk')) hneg_k1.ne
    have hu_pos : 0 < P.coroot' i (u • lam) := by
      rw [simple_mul_smul_eq_reflection, coroot'_reflection_self]
      exact neg_pos.mpr hneg_k1
    have hu_int :
        ∃ z : ℤ, (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (u • lam) = z := by
      obtain ⟨z, hz⟩ := hcutint
      refine ⟨-z, ?_⟩
      rw [simple_mul_smul_eq_reflection, coroot'_reflection_self]
      push_cast
      linear_combination -hz
    obtain ⟨D, hDhead, hDlast, hD⟩ :=
      exists_isAChain_simple_mul_of_coroot'_pos hlam hu_min hu_pos hu_int
    refine ⟨D, ?_, hDlast, hD⟩
    rw [hDhead, (weylCoxeterSystem P b).simple_mul_simple_cancel_left]
    exact hcut.symm
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
/-- The directions and durations produced from `l` by Littelmann's raising operator along the
simple root `αᵢ`: the first part `(τ, θ d)` of `l[j₀] = (τ, d)` is kept, the rest `(τ, (1 - θ) d)`
and the entries `j₀ + 1, …, k₁ - 1` are reflected by `sᵢ`, and the entries from `k₁` on are kept. -/
private noncomputable def raiseList (i : b.support) (l : List (P.weylGroup × ℚ)) (j₀ k₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  (l.take j₀ ++ [(τ, θ * d)]) ++
    ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).map
      (fun p ↦ ((weylCoxeterSystem P b).simple i * p.1, p.2)) ++
    l.drop k₁

omit [P.flip.IsReduced] in
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

omit [P.flip.IsReduced] in
private theorem sum_map_snd_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)} {j₀ k₁ : ℕ}
    (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ) :
    ((raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ).map Prod.snd).sum =
      (l.map Prod.snd).sum := by
  have hj₀_tk : j₀ < (l.take k₁).length := by simp; omega
  conv_rhs =>
    rw [← List.take_append_drop k₁ l, ← List.take_append_drop j₀ (l.take k₁),
      List.take_take, min_eq_left (by omega), List.drop_eq_getElem_cons hj₀_tk,
      List.getElem_take]
  simp only [raiseList, List.map_append, List.map_cons, List.map_map, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  ring

/-- **The raised list is linked.** Let `l` be a linked list of minimal coset representatives,
let `[j₀, k₁)` be a window along which the height `⟨-, αᵢ^∨⟩` of the directions is negative, with
`a_k ⟨τ_{k - 1} λ, αᵢ^∨⟩` nonintegral at its internal breaks `a_k`, followed (if `k₁ < l.length`) by
a direction of nonnegative height, and let `θ` cut the entry `l[j₀] = (τ, d)` at an `a`-integral
time. Then `TauCeti.LSPath.raiseList` is linked, and its directions are minimal coset
representatives. -/
private theorem linked_raiseList (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ)
    (hneg : ∀ k (hk : k < l.length), j₀ ≤ k → k < k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), j₀ < k → k < k₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i ((l[k - 1]'(by omega)).1 • lam) = m)
    (hright : ∀ (hk : k₁ < l.length), 0 ≤ P.coroot' i (l[k₁].1 • lam))
    (hcut : ∃ m : ℤ,
      (((l.take j₀).map Prod.snd).sum + θ * (l[j₀]'(by omega)).2) *
        P.coroot' i ((l[j₀]'(by omega)).1 • lam) = m) :
    Linked P b lam 0 (raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ) ∧
      ∀ p ∈ raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hj₀ : j₀ < l.length := by omega
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
    obtain ⟨r, rfl⟩ : ∃ r, k = j₀ + 2 + r := ⟨k - j₀ - 2, by omega⟩
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp only [hlen_take, show j₀ + 2 + r - j₀ = r + 2 by omega, List.getElem_cons_succ,
      List.getElem_drop]
    congr 1
    omega
  have hDp_fst_ge :
      ∀ k (hk : k < Dp.length), j₀ + 1 ≤ k → Dp[k].1 = (l[k - 1]'(by omega)).1 := by
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
  have hcum_ge : ∀ k, j₀ + 1 ≤ k →
      ((Dp.take (k + 1)).map Prod.snd).sum = ((l.take k).map Prod.snd).sum := by
    intro k hkj
    have hsplit : l.take k = l.take j₀ ++ l[j₀] :: (l.drop (j₀ + 1)).take (k - (j₀ + 1)) := by
      conv_lhs =>
        rw [show k = (j₀ + 1) + (k - (j₀ + 1)) by omega, List.take_add,
          ← List.take_append_drop j₀ (l.take (j₀ + 1)), List.take_take, min_eq_left (by omega)]
      have hj₀_tk1 : j₀ < (l.take (j₀ + 1)).length := by simp; omega
      rw [List.drop_eq_getElem_cons hj₀_tk1, List.getElem_take]
      have hnil : (l.take (j₀ + 1)).drop (j₀ + 1) = [] := by simp
      rw [hnil, List.append_assoc]
      rfl
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show k + 1 - j₀ = (k - (j₀ + 1)) + 2 by omega]
    simp only [List.take_succ_cons, hsplit, List.map_append, List.map_cons,
      List.sum_append, List.sum_cons]
    dsimp only [d]
    ring
  -- Reflect the window `[j₀ + 1, k₁]` of the subdivided list in `sᵢ`.
  have hW := Linked.mapIdx_simple_mul_neg hlam hDp_linked hDpmin i (k₀ := j₀ + 1) (j₁ := k₁)
    (by omega) (by omega) (by omega)
    (fun k hk hkj hkk₁ ↦ by
      rw [hDp_fst_ge k hk hkj]
      exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkj hkk₁ ↦ by
      rw [zero_add, hcum_ge k hkj, hDp_fst_ge k hk hkj]
      exact hint k (by omega) (by omega) hkk₁)
    (fun k hk hkk ↦ by
      subst hkk
      rw [hDp_gt (k₁ + 1) hk (by omega)]
      exact hright (by omega))
    (by simp only [Nat.add_sub_cancel, hDp_j₀, hDp_j₀1])
    (by
      rw [zero_add, hcum_j₀1, hDp_j₀1]
      exact hcut)
  -- Identify the reflected subdivided list with `raiseList`.
  have hraise : raiseList b i l j₀ k₁ τ d θ =
      Dp.mapIdx fun k p ↦ if j₀ + 1 ≤ k ∧ k ≤ k₁ then (s * p.1, p.2) else p := by
    have hDp' : Dp = (l.take j₀ ++ [(τ, θ * d)]) ++
        ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
      rw [hDp]
      have hdrop_split : l.drop (j₀ + 1) = (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ := by
        conv_lhs => rw [← List.take_append_drop k₁ l]
        rw [List.drop_append_of_le_length (by simp; omega)]
      rw [hdrop_split]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hA : (l.take j₀ ++ [(τ, θ * d)]).length = j₀ + 1 := by simp; omega
    have hB : ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by simp; omega
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

section Realization

omit [P.flip.IsReduced] in
/-- The reflection `s = Module.preReflection (f αᵢ) F`, for a form `F` inducing `⟨-, αᵢ^∨⟩`,
sends the segment `d • f (τ λ)` to `d • f ((sᵢ τ) λ)`. -/
private theorem preReflection_smul_apply {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (d : 𝕜) (w : P.weylGroup) :
    Module.preReflection (f (P.root i)) F (d • f (w • lam)) =
      d • f (((weylCoxeterSystem P b).simple i * w) • lam) := by
  rw [map_smul, ← P.map_reflection_eq_preReflection i hF, simple_mul_smul_eq_reflection]

omit [P.flip.IsReduced] in
private theorem apply_take_sum_dirDurations {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (π : LSPath P b lam) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (k : ℕ) :
    F (((π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take k)).sum =
      ((((π.dirDurations.take k).map fun p ↦
        p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum : ℚ) : 𝕜) := by
  simp only [← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
  congr 1
  refine List.map_congr_left fun p _ ↦ ?_
  simp [hF]

omit [P.flip.IsReduced] in
private theorem minHeight_toPLPath_eq_of_coroot' {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (π : LSPath P b lam) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    (f₀ : M →+ ℚ) (F₀ : Module.Dual ℚ ℚ) (hF₀ : ∀ m, F₀ (f₀ m) = (P.coroot' i m : ℚ)) :
    (π.toPLPath 𝕜 f).minHeight F =
      (PLPath.minHeight (𝕜 := ℚ) F₀ (π.toPLPath ℚ f₀) : 𝕜) := by
  rw [toPLPath_def, toPLPath_def, PLPath.minHeight_ofSegments, PLPath.minHeight_ofSegments,
    map_snd_timed, map_snd_timed]
  simp only [Rat.cast_id]
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F₀)
      (π.dirDurations.map fun p ↦ p.2 • f₀ (p.1 • lam))
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F)
      (π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) k
    have h0 := apply_take_sum_dirDurations π f₀ i F₀ hF₀ k
    simp only [Rat.cast_id] at h0
    rw [hk, h0]
    rwa [apply_take_sum_dirDurations π f i F hF k] at hle
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F)
      (π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F₀)
      (π.dirDurations.map fun p ↦ p.2 • f₀ (p.1 • lam)) k
    have h0 := apply_take_sum_dirDurations π f₀ i F₀ hF₀ k
    simp only [Rat.cast_id] at h0
    rw [h0] at hle
    rw [hk, apply_take_sum_dirDurations π f i F hF k]
    exact_mod_cast hle

omit [P.flip.IsReduced] in
private theorem raise_toPLPath_eq_some_of_raiseList {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (π : LSPath P b lam) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    (f₀ : M →+ ℚ) (F₀ : Module.Dual ℚ ℚ) (hF₀ : ∀ m, F₀ (f₀ m) = (P.coroot' i m : ℚ))
    {z : ℤ} (hz : PLPath.minHeight (𝕜 := ℚ) F₀ (π.toPLPath ℚ f₀) = (z : ℚ))
    {j₀ k₁ : ℕ} (hj₀lt : j₀ < π.dirDurations.length) (hj₀k₁ : j₀ < k₁)
    (hk₁D : k₁ ≤ π.dirDurations.length) {τ : P.weylGroup} {d θ : ℚ}
    (hDj₀ : π.dirDurations[j₀] = (τ, d))
    (habove' : ∀ k ≤ j₀,
      (z : ℚ) + 1 ≤ ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hfall' : ∀ k, j₀ ≤ k → k < k₁ →
      ((π.dirDurations.take (k + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
        ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hcross' : ((π.dirDurations.take j₀).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum +
      θ * (d * (P.coroot' i (τ • lam) : ℚ)) = z + 1)
    (hHj₀1 : ((π.dirDurations.take (j₀ + 1)).map fun p ↦
      p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum ≤ z + 1)
    (hgtk₁ : ((π.dirDurations.take k₁).map fun p ↦
      p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum = z)
    {π' : LSPath P b lam}
    (hπ' : π'.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((raiseList b i π.dirDurations j₀ k₁ (π.dirDurations[j₀]).1 (π.dirDurations[j₀]).2 θ).map
        fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))) :
    PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  set D := π.dirDurations
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum
  have hHF : ∀ k, F ((D.map seg).take k).sum = (hgt k : 𝕜) :=
    apply_take_sum_dirDurations π f i F hF
  have hminF : PLPath.listMinHeight F (D.map seg) = (z : 𝕜) := by
    have := minHeight_toPLPath_eq_of_coroot' π f i F hF f₀ F₀ hF₀
    rwa [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed, hz, Rat.cast_intCast] at this
  have hDj₀_seg : (D.map seg)[j₀]'(by rw [List.length_map]; exact hj₀lt) =
      (d : 𝕜) • f (τ • lam) := by
    simp [seg, D, hDj₀]
  rw [toPLPath_def, map_snd_timed, PLPath.raise_ofSegments_eq_of_strictly_falling
    (k₀ := j₀) (k₁ := k₁) (θ := (θ : 𝕜)) hj₀k₁ (by rw [List.length_map]; exact hk₁D)]
  · rw [hπ']
    congr 2
    have hσ : ∀ p : P.weylGroup × ℚ,
        (p.2 : 𝕜) • f (((weylCoxeterSystem P b).simple i * p.1) • lam) =
          Module.preReflection (f (P.root i)) F (seg p) := fun p ↦
      (preReflection_smul_apply f i F hF _ _).symm
    rw [show D[j₀] = (τ, d) from hDj₀]
    simp only [raiseList, seg, D, hDj₀_seg, List.map_append, List.map_cons, List.map_nil,
      List.map_map, List.map_take, List.map_drop, Function.comp_def, hσ, smul_smul,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
    rw [preReflection_smul_apply f i F hF]
  · intro k hkj
    rw [hminF, hHF]
    exact_mod_cast habove' k hkj
  · intro k hjk hkk₁
    rw [hHF, hHF, Rat.cast_lt]
    exact hfall' k hjk hkk₁
  · rw [hminF, hHF, hDj₀_seg, map_smul, hF, smul_eq_mul]
    exact_mod_cast hcross'
  · rw [hminF, hHF]
    exact_mod_cast hHj₀1
  · rw [hminF, hHF]
    exact_mod_cast hgtk₁

/-- **Realization-independent action of Littelmann's raising operator on Lakshmibai–Seshadri
encodings.** Given any two ordered-field simple-coroot realizations `(f₁, F₁)` and `(f₂, F₂)` (over
possibly different fields and universes), either `e_αᵢ` vanishes on `π` in both realizations, or a
single LS path `π'` of shape `λ` realizes `e_αᵢ π` in both realizations simultaneously. -/
theorem raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some {𝕜₁ V₁ 𝕜₂ V₂ : Type*}
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
  let f₀ : M →+ ℚ := (Int.castAddHom ℚ).comp (P.coroot' i).toAddMonoidHom
  let F₀ : Module.Dual ℚ ℚ := LinearMap.id
  have hF₀ : ∀ m, F₀ (f₀ m) = (P.coroot' i m : ℚ) := fun _ ↦ rfl
  by_cases h1₀ : 1 ≤ -(π.toPLPath ℚ f₀).minHeight F₀
  · right
    obtain ⟨j₀', k₁, θ, hj₀k₁, hk₁len, hθ₀, hθ₁, habove₀, hcross₀, hfall₀, hmin₀, -⟩ :=
      π.exists_raise_toPLPath_eq hlam f₀ i F₀ hF₀ (f₀ (P.root i)) h1₀
    obtain ⟨z, hz⟩ := π.exists_minHeight_eq_intCast hlam f₀ i F₀ hF₀
    rw [map_snd_timed] at habove₀ hcross₀ hfall₀ hmin₀
    simp only [Rat.cast_id] at habove₀ hcross₀ hfall₀ hmin₀
    set D := π.dirDurations
    set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
    set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
    set cum : ℕ → ℚ := fun k ↦ ((D.take k).map Prod.snd).sum
    set j₀ : ℕ := (j₀' : ℕ)
    have hlen : D.length = π.length + 1 := length_dirDurations π
    have hj₀lt : j₀ < D.length := by rw [hlen]; exact j₀'.2
    have hk₁D : k₁ ≤ D.length := by rw [hlen]; exact hk₁len
    set τ := (π.dir j₀').1
    set d := π.duration j₀'
    have hDj₀ : D[j₀] = (τ, d) := by rw [getElem_dirDurations]
    have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
      rw [getElem_dirDurations]; exact π.duration_pos _
    have hHF₀ : ∀ k, F₀ ((D.map fun p ↦ p.2 • f₀ (p.1 • lam)).take k).sum = hgt k := by
      intro k
      have := apply_take_sum_dirDurations π f₀ i F₀ hF₀ k
      simpa only [Rat.cast_id] using this
    have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
      intro k hk
      simp only [hgt, List.map_take]
      rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
    have hcum_succ : ∀ k (hk : k < D.length), cum (k + 1) = cum k + D[k].2 := by
      intro k hk
      simp only [cum, List.map_take]
      rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
    have hgtk₁ : hgt k₁ = z := by
      rw [hHF₀, hz] at hmin₀
      exact hmin₀
    have hfall' : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k := fun k hjk hkk₁ ↦ by
      have := hfall₀ k hjk hkk₁
      rwa [hHF₀, hHF₀] at this
    have habove' : ∀ k ≤ j₀, (z : ℚ) + 1 ≤ hgt k := fun k hkj ↦ by
      have := habove₀ k hkj
      rwa [hHF₀, hz] at this
    have hcross' : hgt j₀ + θ * (d * H τ) = z + 1 := by
      have hc := hcross₀
      rwa [hHF₀, hz, map_smul, smul_eq_mul, hF₀] at hc
    have hnegH : ∀ k (hk : k < D.length), j₀ ≤ k → k < k₁ → H D[k].1 < 0 := fun k hk hjk hkk₁ ↦ by
      have := hfall' k hjk hkk₁
      rw [hgt_succ k hk] at this
      exact neg_of_mul_neg_right (by linarith) (hdpos k hk).le
    have hmono : ∀ m k, j₀ ≤ k → k + m ≤ k₁ → hgt (k + m) ≤ hgt k := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro k hjk hkm
        exact (hfall' (k + m) (by omega) (by omega)).le.trans (ih k hjk (by omega))
    have hbetween : ∀ k, j₀ < k → k < k₁ → (z : ℚ) < hgt k ∧ hgt k < z + 1 := by
      intro k hjk hkk₁
      refine ⟨?_, ?_⟩
      · have h₁ := hfall' (k₁ - 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k₁), hgtk₁] at h₁
        have h₂ := hmono (k₁ - 1 - k) k (by omega) (by omega)
        rw [show k + (k₁ - 1 - k) = k₁ - 1 by omega] at h₂
        linarith
      · have hdH : d * H τ < 0 := by
          have := hnegH j₀ hj₀lt le_rfl hj₀k₁
          rw [hDj₀] at this
          exact mul_neg_of_pos_of_neg (by rw [show d = D[j₀].2 by rw [hDj₀]]; exact hdpos j₀ hj₀lt)
            this
        have hgt_j₀1 : hgt (j₀ + 1) < z + 1 := by
          rw [hgt_succ j₀ hj₀lt, hDj₀]
          have : (1 - θ) * (d * H τ) < 0 := mul_neg_of_pos_of_neg (by linarith) hdH
          linarith
        have h₂ := hmono (k - (j₀ + 1)) (j₀ + 1) (by omega) (by omega)
        rw [show j₀ + 1 + (k - (j₀ + 1)) = k by omega] at h₂
        linarith
    have hrightH : ∀ (hk : k₁ < D.length), 0 ≤ H D[k₁].1 := fun hk ↦ by
      have hle := PLPath.listMinHeight_le_apply_sum_take (f := F₀)
        (D.map fun p ↦ p.2 • f₀ (p.1 • lam)) (k₁ + 1)
      have hminH₀ : (π.toPLPath ℚ f₀).minHeight F₀ =
          PLPath.listMinHeight F₀ (D.map fun p ↦ p.2 • f₀ (p.1 • lam)) := by
        rw [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed]
        simp only [Rat.cast_id]
        rfl
      rw [← hminH₀, hz, hHF₀, hgt_succ k₁ hk, hgtk₁] at hle
      exact nonneg_of_mul_nonneg_right (by linarith) (hdpos k₁ hk)
    have hcong : ∀ k (hk : k < D.length), ∃ m : ℤ, hgt k - cum k * H D[k].1 = m := fun k hk ↦
      π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
    have hL_data := linked_raiseList hlam π.linked_dirDurations
      (fun _ hp ↦ π.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁D θ
      (fun k hk hjk hkk₁ ↦ by
        have := hnegH k hk hjk hkk₁
        dsimp only [H, D] at this
        exact_mod_cast this)
      (fun k hk hjk hkk₁ ⟨m, hm⟩ ↦ by
        obtain ⟨m', hm'⟩ := hcong (k - 1) (by omega)
        obtain ⟨h₁, h₂⟩ := hbetween k hjk hkk₁
        have hstep_gt := hgt_succ (k - 1) (by omega)
        have hstep_cum := hcum_succ (k - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hstep_gt hstep_cum
        have hk' : hgt k = ((m' + m : ℤ) : ℚ) := by
          simp only [H, cum, D] at hm' hstep_gt hstep_cum ⊢
          push_cast
          linear_combination hstep_gt -
            hstep_cum * (P.coroot' i (π.dirDurations[k - 1].1 • lam) : ℚ) + hm' + hm
        rw [hk'] at h₁ h₂
        have h₁' : z < m' + m := by exact_mod_cast h₁
        have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
        omega)
      (fun hk ↦ by
        have := hrightH hk
        dsimp only [H, D] at this
        exact_mod_cast this)
      (by
        obtain ⟨m, hm⟩ := hcong j₀ hj₀lt
        refine ⟨z + 1 - m, ?_⟩
        rw [hDj₀] at hm ⊢
        simp only [H, cum, D] at hm hcross' ⊢
        push_cast
        linear_combination hcross' - hm)
    let π' : LSPath P b lam := ofLinked _ hL_data.2
      (fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π.pos_of_mem_dirDurations hp).le)
        (π.pos_of_mem_dirDurations (List.getElem_mem hj₀lt)).le hθ₀ hθ₁.le hp)
      (by rw [sum_map_snd_raiseList i hj₀k₁ hk₁D, sum_map_snd_dirDurations]) hL_data.1
    have hHj₀1 : hgt (j₀ + 1) ≤ z + 1 := by
      rcases (Nat.add_one_le_iff.mpr hj₀k₁).eq_or_lt with heq | hlt
      · rw [heq, hgtk₁]
        linarith
      · exact (hbetween (j₀ + 1) (by omega) hlt).2.le
    exact ⟨π',
      raise_toPLPath_eq_some_of_raiseList π f₁ i F₁ hF₁ f₀ F₀ hF₀ hz hj₀lt hj₀k₁ hk₁D hDj₀
        habove' hfall' hcross' hHj₀1 hgtk₁ (toPLPath_ofLinked f₁ _ _ _ _ _),
      raise_toPLPath_eq_some_of_raiseList π f₂ i F₂ hF₂ f₀ F₀ hF₀ hz hj₀lt hj₀k₁ hk₁D hDj₀
        habove' hfall' hcross' hHj₀1 hgtk₁ (toPLPath_ofLinked f₂ _ _ _ _ _)⟩
  · left
    have hlt : (-1 : ℚ) < PLPath.minHeight (𝕜 := ℚ) F₀ (π.toPLPath ℚ f₀) := by linarith
    exact ⟨PLPath.raise_eq_none_iff.mpr
        (by rw [minHeight_toPLPath_eq_of_coroot' π f₁ i F₁ hF₁ f₀ F₀ hF₀]; exact_mod_cast hlt),
      PLPath.raise_eq_none_iff.mpr
        (by rw [minHeight_toPLPath_eq_of_coroot' π f₂ i F₂ hF₂ f₀ F₀ hF₀]; exact_mod_cast hlt)⟩

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
  rcases π.raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some hlam i f F hF f F hF with
    ⟨hnone, -⟩ | ⟨π', hsome, -⟩
  · rw [hnone] at hq
    cases hq
  · exact ⟨π', Option.some.inj (hsome.symm.trans hq)⟩

end Realization

end TauCeti.LSPath
