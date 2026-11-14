/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic
public import TauCeti.RepresentationTheory.LSPath.RootOperator

import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.RepresentationTheory.LSPath.Concatenation
import TauCeti.RepresentationTheory.LSPath.Integrality
import TauCeti.RepresentationTheory.LSPath.Linked

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root, and write
`H(t) = ⟨π(t), αᵢ^∨⟩` for its running height, with minimum `h`. When `h ≤ -1`, Littelmann's
raising operator `e_αᵢ` reflects by `sᵢ` the single falling piece of the path between the last
time `t₀` before the first minimum `t₁` at which `H = h + 1` and `t₁` itself, keeping the rest
(`TauCeti.LSPath.exists_raise_toPLPath_eq`). This file proves Littelmann's theorem that the result
is again the path of an LS path of shape `λ` (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`),
produced by a single encoding independent of the chosen linear realization
(`TauCeti.LSPath.exists_raise_toPLPath_eq_some_and_eq_some`).

In terms of the directions `τ₀ > ⋯ > τ_l` and durations of `π`, with `t₀` inside segment `j₀` and
`t₁` at vertex `k₁`, the raised path runs along the list of directions
`τ₀, …, τ_{j₀}, sᵢ τ_{j₀}, …, sᵢ τ_{k₁ - 1}, τ_{k₁}, …, τ_l`, segment `j₀` being cut at `t₀`.
This list is linked (`TauCeti.LSPath.Linked`), so `TauCeti.LSPath.ofLinked` produces an LS path:

* at `t₀` the height `h + 1` is an integer and `⟨τ_{j₀} λ, αᵢ^∨⟩ < 0`, so the cover
  `sᵢ τ_{j₀} ⋖ τ_{j₀}` is a `t₀`-chain (`TauCeti.exists_isAChain_simple_mul_of_coroot'_neg`);
* at a break `a` strictly inside `(t₀, t₁)` the height lies strictly between the integers `h` and
  `h + 1`, so `a ⟨τ λ, αᵢ^∨⟩` is nonintegral and the `a`-chain stays on the negative side of the
  wall of `αᵢ` (`TauCeti.IsAChain.coroot'_smul_neg`), where `sᵢ` reflects it to an `a`-chain;
* at `t₁` (when `t₁ < 1`) the height attains its minimum, so `⟨τ_{k₁ - 1} λ, αᵢ^∨⟩ < 0 ≤
  ⟨τ_{k₁} λ, αᵢ^∨⟩`, and `TauCeti.IsAChain.exists_isAChain_simple_mul_head` supplies a `t₁`-chain
  from `sᵢ τ_{k₁ - 1}` down to `τ_{k₁}`.

## Main results

* `TauCeti.LSPath.exists_raise_toPLPath_eq_some_and_eq_some`: **Littelmann's raising operator
  preserves Lakshmibai–Seshadri paths uniformly across realizations**.
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
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- **Reflecting a falling window of a linked list.** Let `[j₀ + 1, k₁]` be a window of entries of
a linked list along which the heights `⟨τ λ, αᵢ^∨⟩` of the directions are negative, preceded at
`j₀` by an entry with the same direction as `j₀ + 1` at an `a`-integral break, with nonintegral
`a ⟨τ λ, αᵢ^∨⟩` at internal breaks, and (if followed by an entry at `k₁ + 1`) leaving into a
direction of nonnegative height. Replacing `τ` by `sᵢ τ` on `[j₀ + 1, k₁]` keeps the list linked. -/
private theorem Linked.mapIdx_simple_mul_neg (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ < l.length)
    (hneg : ∀ k (hk : k < l.length), j₀ + 1 ≤ k → k ≤ k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k + 1 < l.length), j₀ + 1 ≤ k → k + 1 ≤ k₁ →
      ¬∃ z : ℤ, (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hright : ∀ k (hk : k + 1 < l.length), k = k₁ → 0 ≤ P.coroot' i (l[k + 1].1 • lam))
    (hcut : (l[j₀ + 1]'(by omega)).1 = (l[j₀]'(by omega)).1)
    (hcutint : ∃ z : ℤ,
      (t + ((l.take (j₀ + 1)).map Prod.snd).sum) * P.coroot' i ((l[j₀]'(by omega)).1 • lam) = z) :
    Linked P b lam t (l.mapIdx fun k p ↦
      if j₀ + 1 ≤ k ∧ k ≤ k₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) := by
  have := P.flip_isReduced
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
  by_cases hw₁ : j₀ + 1 ≤ k ∧ k ≤ k₁ <;> by_cases hw₂ : j₀ + 1 ≤ k + 1 ∧ k + 1 ≤ k₁ <;>
    simp only [hw₁, hw₂, and_self, ↓reduceIte]
  · -- Both ends in `[j₀ + 1, k₁]`: the chain stays on the negative side and reflects.
    have hall := hC.coroot'_smul_neg hlam i
      (by rw [hhead]; exact hneg k (by omega) hw₁.1 hw₁.2)
      (by rw [hhead]; exact hint k hk hw₁.1 hw₂.2)
    exact ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inr hall),
      by simp [hhead], by simp [hlast],
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
  · -- Leaving `[j₀ + 1, k₁]` at `k = k₁`.
    obtain ⟨D, hDhead, hDlast, hD⟩ := hC.exists_isAChain_simple_mul_head hlam i
      (by rw [hhead]; exact hneg k (by omega) hw₁.1 hw₁.2)
      (by rw [hlast]; exact hright k hk (by omega))
    exact ⟨D, by rw [hDhead, hhead], by rw [hDlast, hlast], hD⟩
  · -- Entering `[j₀ + 1, k₁]` at `k = j₀`: the cover `sᵢ τ ⋖ τ`.
    obtain rfl : k = j₀ := by omega
    rw [hcut]
    exact exists_isAChain_simple_mul_of_coroot'_neg hlam (hmin _ (List.getElem_mem _))
      (hcut ▸ hneg (k + 1) (by simpa using hk) le_rfl hw₂.2) hcutint
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
/-- The directions and durations produced from `l` by Littelmann's raising operator along the
simple root `αᵢ`: the first part `(τ, θ d)` of `l[j₀] = (τ, d)` is kept, the second part
`(τ, (1 - θ) d)` together with entries `j₀ + 1, …, k₁ - 1` are reflected by `sᵢ`, and the entries
from `k₁` on are kept. -/
private noncomputable def raiseList (i : b.support) (l : List (P.weylGroup × ℚ)) (j₀ k₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  l.take j₀ ++ [(τ, θ * d)] ++
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
    ((raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ).map Prod.snd).sum =
      (l.map Prod.snd).sum := by
  have hdrop : (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ = l.drop (j₀ + 1) := by
    have hlen₁ : j₀ + 1 ≤ (l.take k₁).length := by simp only [List.length_take]; omega
    conv_rhs => rw [← List.take_append_drop k₁ l, List.drop_append_of_le_length hlen₁]
  conv_rhs => rw [← List.take_append_drop j₀ l, List.drop_eq_getElem_cons (by omega), ← hdrop]
  simp only [raiseList, List.map_append, List.map_cons, List.map_map, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  ring

/-- Subdivide entry `j₀` of `l` into fractions `θ` and `1 - θ` with the same direction. -/
private def splitAt (l : List (P.weylGroup × ℚ)) (j₀ : ℕ) (hj₀ : j₀ < l.length) (θ : ℚ) :
    List (P.weylGroup × ℚ) :=
  l.take j₀ ++ (l[j₀].1, θ * l[j₀].2) :: (l[j₀].1, (1 - θ) * l[j₀].2) :: l.drop (j₀ + 1)

private theorem linked_splitAt {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    {j₀ : ℕ} (hj₀ : j₀ < l.length) (θ : ℚ) :
    Linked P b lam 0 (splitAt l j₀ hj₀ θ) ∧
      ∀ p ∈ splitAt l j₀ hj₀ θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hτmin := hlmin _ (List.getElem_mem hj₀)
  refine ⟨?_, fun p hp ↦ ?_⟩
  · have hsplit : l =
        l.take j₀ ++ (l[j₀].1, θ * l[j₀].2 + (1 - θ) * l[j₀].2) :: l.drop (j₀ + 1) := by
      rw [show θ * l[j₀].2 + (1 - θ) * l[j₀].2 = l[j₀].2 by ring,
        ← List.drop_eq_getElem_cons hj₀, List.take_append_drop]
    rw [hsplit] at hl
    exact Linked.split hτmin hl
  · simp only [splitAt, List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | rfl | hp
    · exact hlmin p (List.mem_of_mem_take hp)
    · exact hτmin
    · exact hτmin
    · exact hlmin p (List.mem_of_mem_drop hp)

omit [Finite ι] [P.IsReduced] in
private theorem getElem_splitAt_cut {l : List (P.weylGroup × ℚ)} {j₀ : ℕ} (hj₀ : j₀ < l.length)
    (θ : ℚ) :
    (splitAt l j₀ hj₀ θ).length = l.length + 1 ∧
      (splitAt l j₀ hj₀ θ)[j₀]'(by simp [splitAt]; omega) = (l[j₀].1, θ * l[j₀].2) ∧
      (splitAt l j₀ hj₀ θ)[j₀ + 1]'(by simp [splitAt]; omega) = (l[j₀].1, (1 - θ) * l[j₀].2) ∧
      ∀ k (hk : k < (splitAt l j₀ hj₀ θ).length), j₀ + 1 ≤ k →
        (splitAt l j₀ hj₀ θ)[k].1 = (l[k - 1]'(by simp [splitAt] at hk; omega)).1 := by
  have hlen_take : (l.take j₀).length = j₀ := by simp; omega
  have hDp_j₀ : (splitAt l j₀ hj₀ θ)[j₀]'(by simp [splitAt]; omega) = (l[j₀].1, θ * l[j₀].2) := by
    simp only [splitAt]; rw [List.getElem_append_right (by omega)]; simp [hlen_take]
  have hDp_j₀1 : (splitAt l j₀ hj₀ θ)[j₀ + 1]'(by simp [splitAt]; omega) =
      (l[j₀].1, (1 - θ) * l[j₀].2) := by
    simp only [splitAt]; rw [List.getElem_append_right (by omega)]; simp [hlen_take]
  refine ⟨by simp [splitAt]; omega, hDp_j₀, hDp_j₀1, fun k hk hkj ↦ ?_⟩
  rcases hkj.eq_or_lt with rfl | hkj
  · rw [hDp_j₀1]; rfl
  · have hDp_assoc : splitAt l j₀ hj₀ θ =
        (l.take j₀ ++ [(l[j₀].1, θ * l[j₀].2), (l[j₀].1, (1 - θ) * l[j₀].2)]) ++
          l.drop (j₀ + 1) := by simp [splitAt, List.append_assoc]
    have hlen2 :
        (l.take j₀ ++ [(l[j₀].1, θ * l[j₀].2), (l[j₀].1, (1 - θ) * l[j₀].2)]).length = j₀ + 2 := by
      simp [hlen_take]
    have hget : (splitAt l j₀ hj₀ θ)[k] =
        l[j₀ + 1 + (k - (j₀ + 2))]'(by simp [splitAt] at hk; omega) := by
      simp only [hDp_assoc]
      rw [List.getElem_append_right (by rw [hlen2]; omega), List.getElem_drop]
      simp only [hlen2]
    rw [hget]
    congr 2
    omega

omit [Finite ι] [P.IsReduced] in
private theorem sum_take_splitAt {l : List (P.weylGroup × ℚ)} {j₀ : ℕ} (hj₀ : j₀ < l.length)
    (θ : ℚ) :
    (((splitAt l j₀ hj₀ θ).take (j₀ + 1)).map Prod.snd).sum =
        ((l.take j₀).map Prod.snd).sum + θ * l[j₀].2 ∧
      ∀ k, j₀ + 1 ≤ k →
        (((splitAt l j₀ hj₀ θ).take (k + 1)).map Prod.snd).sum = ((l.take k).map Prod.snd).sum := by
  have hlen_take : (l.take j₀).length = j₀ := by simp; omega
  refine ⟨?_, fun k hkj ↦ ?_⟩
  · simp only [splitAt]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₀ + 1 - j₀ = 1 by omega]
    simp
  · have hDp_take : (splitAt l j₀ hj₀ θ).take (k + 1) =
        l.take j₀ ++ (l[j₀].1, θ * l[j₀].2) :: (l[j₀].1, (1 - θ) * l[j₀].2) ::
          (l.drop (j₀ + 1)).take (k - (j₀ + 1)) := by
      simp only [splitAt]
      rw [List.take_append, List.take_of_length_le (by omega), hlen_take]
      obtain ⟨r, hr⟩ : ∃ r, k + 1 - j₀ = r + 2 := ⟨k - (j₀ + 1), by omega⟩
      rw [hr]
      simp [show r = k - (j₀ + 1) by omega]
    have hl_take : l.take k =
        l.take j₀ ++ l[j₀] :: (l.drop (j₀ + 1)).take (k - (j₀ + 1)) := by
      conv_lhs => rw [← List.take_append_drop j₀ l]
      rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
        List.drop_eq_getElem_cons hj₀, show k - j₀ = (k - (j₀ + 1)) + 1 by omega,
        List.take_succ_cons]
    rw [hDp_take, hl_take]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    ring

private theorem raiseList_eq_mapIdx_splitAt (i : b.support) {l : List (P.weylGroup × ℚ)}
    {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ) :
    raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ =
      (splitAt l j₀ (by omega) θ).mapIdx fun k p ↦
        if j₀ + 1 ≤ k ∧ k ≤ k₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p := by
  have hj₀ : j₀ < l.length := lt_of_lt_of_le hj₀k₁ hk₁
  have hlen_take : (l.take j₀).length = j₀ := by simp; omega
  have hDp' : splitAt l j₀ hj₀ θ = (l.take j₀ ++ [(l[j₀].1, θ * l[j₀].2)]) ++
      ((l[j₀].1, (1 - θ) * l[j₀].2) :: (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
    have hdrop : (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ = l.drop (j₀ + 1) := by
      have hlen₁ : j₀ + 1 ≤ (l.take k₁).length := by simp only [List.length_take]; omega
      conv_rhs => rw [← List.take_append_drop k₁ l, List.drop_append_of_le_length hlen₁]
    simp only [splitAt, ← hdrop, List.append_assoc, List.cons_append, List.nil_append]
  have hA : (l.take j₀ ++ [(l[j₀].1, θ * l[j₀].2)]).length = j₀ + 1 := by simp [hlen_take]
  have hB :
      ((l[j₀].1, (1 - θ) * l[j₀].2) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by
    simp only [List.length_cons, List.length_drop, List.length_take]; omega
  rw [hDp']
  refine List.ext_getElem (by simp [raiseList]) fun k _ _ ↦ ?_
  simp only [raiseList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
    List.length_append, List.length_map, hA, hB]
  split_ifs <;> first | rfl | omega

/-- **The raised list is linked.** If `[j₀, k₁)` is a window of `l` along which `⟨-, αᵢ^∨⟩ < 0`,
`θ` cuts `l[j₀]` at an `a`-integral time, internal breaks are nonintegral, and any entry at `k₁`
has nonnegative height, then `TauCeti.LSPath.raiseList` is linked and consists of minimal coset
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
  have hj₀ : j₀ < l.length := lt_of_lt_of_le hj₀k₁ hk₁
  obtain ⟨hDp_linked, hDpmin⟩ := linked_splitAt hl hlmin hj₀ θ
  obtain ⟨hDp_len, hDp_j₀, hDp_j₀1, hDp_fst⟩ := getElem_splitAt_cut hj₀ θ
  obtain ⟨hcum_j₀1, hcum_ge⟩ := sum_take_splitAt hj₀ θ
  have hW := Linked.mapIdx_simple_mul_neg hlam hDp_linked hDpmin i hj₀k₁ (by omega)
    (fun k hk h1 h2 ↦ by rw [hDp_fst k hk h1]; exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk h1 h2 ↦ by
      rw [zero_add, hcum_ge k h1, hDp_fst k (by omega) h1]
      exact hint k (by omega) (by omega) (by omega))
    (fun k hk hkk ↦ by subst hkk; rw [hDp_fst (k + 1) hk (by omega)]; simpa using hright (by omega))
    (by rw [hDp_j₀1, hDp_j₀])
    (by rw [zero_add, hcum_j₀1, hDp_j₀]; exact hcut)
  rw [raiseList_eq_mapIdx_splitAt i hj₀k₁ hk₁ θ]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < (splitAt l j₀ hj₀ θ).length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst k hk' hw.1]
    exact (hneg (k - 1) (by omega) (by omega) (by omega)).ne
  · exact hDpmin _ (List.getElem_mem hk')

section Realization

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem preReflection_smul_apply (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (d : 𝕜) (w : P.weylGroup) :
    Module.preReflection (f (P.root i)) F (d • f (w • lam)) =
      d • f (((weylCoxeterSystem P b).simple i * w) • lam) := by
  rw [map_smul, ← P.map_reflection_eq_preReflection i hF, simple_mul_smul_eq_reflection]

private theorem apply_sum_take_map_dirDurations (π : LSPath P b lam)
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (k : ℕ) :
    F ((π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take k).sum =
      (((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum : 𝕜) := by
  simp only [← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
  exact congrArg _ (List.map_congr_left fun p _ ↦ by simp [hF])

/-- Evaluate `PLPath.raise` on `π.toPLPath 𝕜 f` from rational falling-piece data on
`π.dirDurations`. -/
private theorem raise_toPLPath_eq_ofSegments_raiseList (π : LSPath P b lam)
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {j₀ k₁ : ℕ} {θ : ℚ} {z : ℤ}
    (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ π.dirDurations.length)
    (hmin : (π.toPLPath 𝕜 f).minHeight F = z)
    (hgtk₁ : ((π.dirDurations.take k₁).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum = z)
    (hbefore : ∀ j ≤ j₀, (z : ℚ) + 1 ≤
      ((π.dirDurations.take j).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hfall : ∀ j, j₀ ≤ j → j < k₁ →
      ((π.dirDurations.take (j + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
        ((π.dirDurations.take j).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hθ : ((π.dirDurations.take j₀).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum +
      θ * ((π.dirDurations[j₀]'(by omega)).2 *
        (P.coroot' i ((π.dirDurations[j₀]'(by omega)).1 • lam) : ℚ)) = (z : ℚ) + 1)
    (hcut : ((π.dirDurations.take (j₀ + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum ≤
      (z : ℚ) + 1) :
    PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
      ((raiseList b i π.dirDurations j₀ k₁ (π.dirDurations[j₀]'(by omega)).1
        (π.dirDurations[j₀]'(by omega)).2 θ).map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))) := by
  set D := π.dirDurations
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)
  have hHF := apply_sum_take_map_dirDurations π f i F hF
  have hmin' : PLPath.listMinHeight F (D.map seg) = (z : 𝕜) := by
    rw [← hmin, toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed]
  have hj₀ : j₀ < D.length := lt_of_lt_of_le hj₀k₁ hk₁
  have hget : (D.map seg)[j₀]'(by simpa using hj₀) = seg D[j₀] := List.getElem_map _
  rw [toPLPath_def, map_snd_timed, PLPath.raise_ofSegments_eq_of_strictly_falling
    (k₀ := j₀) (k₁ := k₁) (θ := (θ : 𝕜)) hj₀k₁ (by simpa [D] using hk₁)]
  · congr 2
    have hσ : ∀ p : P.weylGroup × ℚ,
        (p.2 : 𝕜) • f (((weylCoxeterSystem P b).simple i * p.1) • lam) =
          Module.preReflection (f (P.root i)) F ((p.2 : 𝕜) • f (p.1 • lam)) := fun p ↦
      (preReflection_smul_apply f i F hF _ _).symm
    rw [hget]
    simp only [raiseList, seg, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.map_take, List.map_drop, Function.comp_def, hσ, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_one, smul_smul]
    rw [preReflection_smul_apply f i F hF]
  · rw [hHF, hmin']; exact_mod_cast hgtk₁
  · exact fun j hj ↦ by rw [hHF, hmin']; exact_mod_cast hbefore j hj
  · exact fun j hj₀j hjk₁ ↦ by rw [hHF, hHF, Rat.cast_lt]; exact hfall j hj₀j hjk₁
  · rw [hHF, hget, hmin']; simp only [seg, map_smul, smul_eq_mul, hF]; exact_mod_cast hθ
  · rw [hHF, hmin']; exact_mod_cast hcut

/-- Internal breaks strictly inside a strictly falling window `(j₀, k₁)` where the height stays in
`(z, z + 1)` cannot satisfy the `a`-integrality condition. -/
private theorem not_exists_intCast_of_falling_window (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (i : b.support) {j₀ k₁ : ℕ} {z : ℤ}
    (habove : ∀ j < k₁, (z : ℚ) <
      ((π.dirDurations.take j).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hfall : ∀ j, j₀ ≤ j → j < k₁ →
      ((π.dirDurations.take (j + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
        ((π.dirDurations.take j).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hstrict : ((π.dirDurations.take (j₀ + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum
      < (z : ℚ) + 1)
    {k : ℕ} (hk : k < π.dirDurations.length) (h1 : j₀ < k) (h2 : k < k₁) :
    ¬∃ m : ℤ, ((π.dirDurations.take k).map Prod.snd).sum *
      P.coroot' i ((π.dirDurations[k - 1]'(by omega)).1 • lam) = m := by
  have := P.flip_isReduced
  rintro ⟨m, hm⟩
  set D := π.dirDurations
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun j ↦ ((D.take j).map fun p ↦ p.2 * H p.1).sum
  set cum : ℕ → ℚ := fun j ↦ ((D.take j).map Prod.snd).sum
  have hmono_fall : ∀ m j, j₀ + 1 ≤ j → j + m ≤ k₁ → hgt (j + m) ≤ hgt j := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      intro j hj hjm
      exact (hfall (j + m) (by omega) (by omega)).le.trans (ih j hj (by omega))
  obtain ⟨m', hm'⟩ :=
    π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) (j := k - 1)
      (by omega)
  have hstep_cum : cum k = cum (k - 1) + (D[k - 1]'(by omega)).2 := by
    simp only [cum]; conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.sum_append]; simp
  have hstep_hgt : hgt k = hgt (k - 1) + (D[k - 1]'(by omega)).2 * H (D[k - 1]'(by omega)).1 := by
    simp only [hgt, List.map_take]; conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [List.sum_take_succ _ _ (by simp; omega), List.getElem_map]
  have hk_int : hgt k = ((m' + m : ℤ) : ℚ) := by
    dsimp only [hgt, cum, H, D] at hstep_hgt hstep_cum ⊢
    push_cast
    linear_combination hm' + hm + hstep_hgt -
      hstep_cum * (P.coroot' i ((π.dirDurations[k - 1]'(by omega)).1 • lam) : ℚ)
  have h₁ : (z : ℚ) < hgt k := habove k h2
  have h₂ : hgt k < z + 1 := by
    have hm1 := hmono_fall (k - (j₀ + 1)) (j₀ + 1) le_rfl (by omega)
    rw [show j₀ + 1 + (k - (j₀ + 1)) = k by omega] at hm1
    linarith
  rw [hk_int] at h₁ h₂
  have : z < m' + m := by exact_mod_cast h₁
  have : m' + m < z + 1 := by exact_mod_cast h₂
  omega

/-- **The rational data of a raising step.** When `(π.toPLPath 𝕜 f).minHeight F = z ≤ -1`, extract
the window `[j₀, k₁)` and cut fraction `θ ∈ [0, 1]` on `π.dirDurations` satisfying the hypotheses
of both `TauCeti.LSPath.linked_raiseList` and
`TauCeti.LSPath.raise_toPLPath_eq_ofSegments_raiseList`. -/
private theorem exists_rational_raise_data (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {z : ℤ}
    (hz : (π.toPLPath 𝕜 f).minHeight F = z) (hz1 : (π.toPLPath 𝕜 f).minHeight F ≤ -1) :
    ∃ (j₀ k₁ : ℕ) (θ : ℚ), ∃ (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ π.dirDurations.length),
      0 ≤ θ ∧ θ ≤ 1 ∧
      ((π.dirDurations.take k₁).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum = z ∧
      (∀ j ≤ j₀, (z : ℚ) + 1 ≤
        ((π.dirDurations.take j).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum) ∧
      (∀ j, j₀ ≤ j → j < k₁ →
        ((π.dirDurations.take (j + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
          ((π.dirDurations.take j).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum) ∧
      ((π.dirDurations.take j₀).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum +
        θ * ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2 *
          (P.coroot' i ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1 • lam) : ℚ)) =
        (z : ℚ) + 1 ∧
      ((π.dirDurations.take (j₀ + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum ≤
        (z : ℚ) + 1 ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ ≤ k → k < k₁ →
        P.coroot' i (π.dirDurations[k].1 • lam) < 0) ∧
      (∀ k (hk : k < π.dirDurations.length), j₀ < k → k < k₁ →
        ¬∃ m : ℤ, ((π.dirDurations.take k).map Prod.snd).sum *
          P.coroot' i ((π.dirDurations[k - 1]'(by omega)).1 • lam) = m) ∧
      (∀ (hk : k₁ < π.dirDurations.length), 0 ≤ P.coroot' i (π.dirDurations[k₁].1 • lam)) ∧
      ∃ m : ℤ, (((π.dirDurations.take j₀).map Prod.snd).sum +
        θ * (π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).2) *
          P.coroot' i ((π.dirDurations[j₀]'(lt_of_lt_of_le hj₀k₁ hk₁)).1 • lam) = m := by
  have := P.flip_isReduced
  obtain ⟨j₀', k₁, θ', hj₀k₁, hk₁s, hθ0', hθ1', hmin, habove_before, hbefore, hfall, hcross, -⟩ :=
    π.exists_raise_toPLPath_eq hlam f i F hF (f (P.root i)) hz1
  rw [map_snd_timed] at hmin habove_before hbefore hfall hcross
  set D := π.dirDurations
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
  set j₀ : ℕ := (j₀' : ℕ)
  have hk₁ : k₁ ≤ D.length := length_dirDurations π ▸ hk₁s
  have hj₀ : j₀ < D.length := lt_of_lt_of_le hj₀k₁ hk₁
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k _ ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  have hHF : ∀ k, F ((D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take k).sum = (hgt k : 𝕜) :=
    apply_sum_take_map_dirDurations π f i F hF
  have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := fun k hk ↦ by
    simp only [hgt, List.map_take]
    rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
  have hgtk₁ : hgt k₁ = z := by rw [hHF, hz] at hmin; exact_mod_cast hmin
  have habove' : ∀ j < k₁, (z : ℚ) < hgt j := fun j hj ↦ by
    have := habove_before j hj; rw [hHF, hz] at this; exact_mod_cast this
  have hbefore' : ∀ j ≤ j₀, (z : ℚ) + 1 ≤ hgt j := fun j hj ↦ by
    have := hbefore j hj; rw [hHF, hz] at this; exact_mod_cast this
  have hfall' : ∀ j, j₀ ≤ j → j < k₁ → hgt (j + 1) < hgt j := fun j h1 h2 ↦ by
    have := hfall j h1 h2; rwa [hHF, hHF, Rat.cast_lt] at this
  have hnegH : ∀ k (hk : k < D.length), j₀ ≤ k → k < k₁ → H D[k].1 < 0 := fun k hk h1 h2 ↦
    neg_of_mul_neg_right (by linarith [hfall' k h1 h2, hgt_succ k hk]) (hdpos k hk).le
  have hdH : D[j₀].2 * H D[j₀].1 < 0 :=
    mul_neg_of_pos_of_neg (hdpos j₀ hj₀) (hnegH j₀ hj₀ le_rfl hj₀k₁)
  set θ : ℚ := (z + 1 - hgt j₀) / (D[j₀].2 * H D[j₀].1) with hθ
  have hθd : θ * (D[j₀].2 * H D[j₀].1) = z + 1 - hgt j₀ := div_mul_cancel₀ _ hdH.ne
  have hθ' : θ' = θ := by
    have hFseg : F ((π.duration j₀' : 𝕜) • f ((π.dir j₀').1 • lam)) =
        ((D[j₀].2 * H D[j₀].1 : ℚ) : 𝕜) := by
      rw [show D[j₀] = ((π.dir j₀').1, π.duration j₀') by simp [D, j₀]]; simp [H, hF]
    rw [hHF, hz, hFseg] at hcross
    rw [hθ, Rat.cast_div, eq_div_iff (by exact_mod_cast hdH.ne),
      show θ' * ((D[j₀].2 * H D[j₀].1 : ℚ) : 𝕜) = ((z + 1 - hgt j₀ : ℚ) : 𝕜) by
        push_cast at hcross ⊢; linear_combination hcross]
  rw [hθ'] at hθ0' hθ1'
  have hθ1 : θ < 1 := by exact_mod_cast hθ1'
  have hstrict : hgt (j₀ + 1) < z + 1 := by
    rw [hgt_succ j₀ hj₀]; linarith [mul_lt_mul_of_neg_right hθ1 hdH]
  refine ⟨j₀, k₁, θ, hj₀k₁, hk₁, by exact_mod_cast hθ0', hθ1.le, hgtk₁, hbefore', hfall',
    by linarith [hθd], hstrict.le,
    fun k hk h1 h2 ↦ Int.cast_lt (R := ℚ) |>.mp (hnegH k hk h1 h2),
    fun k hk h1 h2 ↦ not_exists_intCast_of_falling_window π hlam i habove' hfall' hstrict
      hk h1 h2, fun hk ↦ ?_, ?_⟩
  · have hle := PLPath.listMinHeight_le_apply_sum_take
      (f := F) (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) (k₁ + 1)
    rw [show PLPath.listMinHeight F _ = (z : 𝕜) by
      rw [← hz, toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed], hHF] at hle
    have hle' : (z : ℚ) ≤ hgt (k₁ + 1) := by exact_mod_cast hle
    rw [hgt_succ k₁ hk, hgtk₁] at hle'
    exact Int.cast_nonneg_iff.mp (nonneg_of_mul_nonneg_right (by linarith) (hdpos k₁ hk))
  · obtain ⟨m, hm⟩ :=
      π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hj₀
    exact ⟨z + 1 - m, by simp only [H] at hm hθd; push_cast; linear_combination hθd - hm⟩

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths uniformly across
realizations.** If `e_αᵢ` is defined on `π.toPLPath 𝕜 f` in a realization `(𝕜, V, f, F)`, there is
an LS path `π'` of shape `λ` whose realization in `(𝕜, V, f)` is `e_αᵢ (π.toPLPath 𝕜 f)` and whose
realization in any other coroot-compatible realization `(𝕜', V', f', F')` is
`e_αᵢ (π.toPLPath 𝕜' f')`. -/
theorem exists_raise_toPLPath_eq_some_and_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (f : M →+ V) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    {𝕜' V' : Type*} [Field 𝕜'] [LinearOrder 𝕜'] [IsStrictOrderedRing 𝕜']
    [AddCommGroup V'] [Module 𝕜' V']
    (f' : M →+ V') (F' : Module.Dual 𝕜' V') (hF' : ∀ m, F' (f' m) = (P.coroot' i m : 𝕜'))
    {q : PLPath 𝕜 V} (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q ∧
      PLPath.raise F' (f' (P.root i)) (π.toPLPath 𝕜' f') = some (π'.toPLPath 𝕜' f') := by
  have hz1 : (π.toPLPath 𝕜 f).minHeight F ≤ -1 := by
    by_contra h
    have hnone := (PLPath.raise_eq_none_iff (x := f (P.root i))).mpr (not_le.mp h)
    rw [hq] at hnone
    exact Option.some_ne_none _ hnone
  obtain ⟨z, -, hz, hz'⟩ := π.exists_intCast_minHeight_eq_and_minHeight_eq hlam i f F hF f' F' hF'
  obtain ⟨j₀, k₁, θ, hj₀k₁, hk₁, hθ0, hθ1, hgtk₁, hbefore, hfall, hθ, hcut_le,
      hneg, hint, hright, hcut⟩ :=
    exists_rational_raise_data π hlam f i F hF hz hz1
  obtain ⟨hL, hLmin⟩ := linked_raiseList hlam π.linked_dirDurations
    (fun _ hp ↦ π.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁ θ hneg hint hright hcut
  have hj₀ : j₀ < π.dirDurations.length := lt_of_lt_of_le hj₀k₁ hk₁
  let π' : LSPath P b lam := ofLinked _ hLmin
    (fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π.pos_of_mem_dirDurations hp).le)
      (π.pos_of_mem_dirDurations (List.getElem_mem hj₀)).le hθ0 hθ1 hp)
    (by rw [sum_map_snd_raiseList i hj₀k₁ hk₁, sum_map_snd_dirDurations]) hL
  have hr₁ := raise_toPLPath_eq_ofSegments_raiseList π f i F hF hj₀k₁ hk₁ hz
    hgtk₁ hbefore hfall hθ hcut_le
  have hr₂ := raise_toPLPath_eq_ofSegments_raiseList π f' i F' hF' hj₀k₁ hk₁ hz'
    hgtk₁ hbefore hfall hθ hcut_le
  refine ⟨π', ?_, ?_⟩
  · dsimp only [π']
    rw [toPLPath_ofLinked]
    exact Option.some.inj (hr₁.symm.trans hq)
  · dsimp only [π']
    rw [hr₂, toPLPath_ofLinked]

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q :=
  let ⟨π', hπ', _⟩ := π.exists_raise_toPLPath_eq_some_and_eq_some hlam i f F hF f F hF hq
  ⟨π', hπ'⟩

end Realization

end TauCeti.LSPath
