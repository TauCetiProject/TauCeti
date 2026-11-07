/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
public import TauCeti.RepresentationTheory.LSPath.Linked
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray

/-!
# Littelmann's lowering operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root, and write
`H(t) = ⟨π(t), αᵢ^∨⟩` for its running height, with minimum `h`. When `H(1) - h ≥ 1`, Littelmann's
lowering operator `f_αᵢ` reflects by `sᵢ` the single piece of the path between the last time `t₀`
at which `H = h` and the first later time `t₁` at which `H = h + 1`, and keeps the rest
(`TauCeti.LSPath.exists_lower_toPLPath_eq`). This file proves Littelmann's theorem that the result
is again the path of an LS path of shape `λ` (`TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`).

In terms of the directions `τ₀ > ⋯ > τ_l` and durations of `π`, with `t₀` a break and `t₁` inside
the segment `j₁`, the lowered path runs along the list of directions
`τ₀, …, τ_{k₀ - 1}, sᵢ τ_{k₀}, …, sᵢ τ_{j₁}, τ_{j₁}, …, τ_l`, the segment `j₁` being cut at `t₁`.
This list is linked (`TauCeti.LSPath.Linked`), so it defines an LS path by
`TauCeti.LSPath.ofLinked`, which merges repeated directions. The chain conditions at its breaks
are Littelmann's, proved in `TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain`:

* at `t₀` the height has a local minimum, so `⟨τ_{k₀ - 1} λ, αᵢ^∨⟩ ≤ 0 < ⟨τ_{k₀} λ, αᵢ^∨⟩`, and an
  `a`-chain from `τ_{k₀ - 1}` down to `τ_{k₀}` gives one down to `sᵢ τ_{k₀}`, possibly of length
  `0`;
* at a break `a` strictly inside the reflected piece the height lies strictly between the integers
  `h` and `h + 1`, so `a ⟨τ λ, αᵢ^∨⟩` is not an integer, and the `a`-chain stays on the positive
  side of the wall of `αᵢ`, where `sᵢ` carries it to an `a`-chain;
* at `t₁` the height `h + 1` is an integer, so the cover `τ_{j₁} ⋖ sᵢ τ_{j₁}` is a `t₁`-chain.

The integrality statements use that the height at a break `a` before the direction `τ` differs from
`a ⟨τ λ, αᵢ^∨⟩` by an integer (`TauCeti.LSPath.Linked.exists_sum_take_sub_mul_eq_intCast`).

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`: **Littelmann's lowering operator
  preserves Lakshmibai–Seshadri paths**.

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

/-- **Reflecting a rising window of a linked list.** Let `[k₀, j₁]` be a window of entries of a
linked list along which the heights `⟨τ λ, αᵢ^∨⟩` of the directions are positive, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at the internal breaks `a`, entered from a direction of nonpositive
height, and followed by an entry with the same direction as its last one, at a break `a` with
`a ⟨τ λ, αᵢ^∨⟩` integral. Replacing the directions `τ` in the window by `sᵢ τ` keeps the list
linked. -/
private theorem Linked.mapIdx_simple_mul (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {k₀ j₁ : ℕ} (hj₁ : j₁ + 1 < l.length)
    (hpos : ∀ k (hk : k < l.length), k₀ ≤ k → k ≤ j₁ → 0 < P.coroot' i (l[k].1 • lam))
    (hint : ∀ k (hk : k < l.length), k₀ < k → k ≤ j₁ →
      ¬∃ z : ℤ, (t + ((l.take k).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hleft : ∀ k (hk : k + 1 < l.length), k + 1 = k₀ → P.coroot' i (l[k].1 • lam) ≤ 0)
    (hcut : l[j₁ + 1].1 = l[j₁].1)
    (hcutint : ∃ z : ℤ,
      (t + ((l.take (j₁ + 1)).map Prod.snd).sum) * P.coroot' i (l[j₁].1 • lam) = z) :
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
  · -- Both ends in the window: the chain stays on the positive side and reflects.
    have hall := hC.coroot'_smul_pos hlam i (by rw [hlast]; exact hpos (k + 1) hk hk₂.1 hk₂.2)
      (by rw [hlast]; exact hint (k + 1) hk (by omega) hk₂.2)
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inl hall), ?_, ?_,
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
    · simp [hhead]
    · simp [hlast]
  · -- Leaving the window at its end `j₁`: the cover `τ ⋖ sᵢ τ`.
    obtain rfl : k = j₁ := by omega
    rw [hcut]
    exact exists_isAChain_simple_mul_of_coroot'_pos hlam (hmin _ (List.getElem_mem _))
      (hpos k (by omega) hk₁.1 le_rfl) hcutint
  · -- Entering the window at `k₀`: Littelmann's chain at the start of a reflected piece.
    obtain ⟨D, hDhead, hDlast, hD⟩ := hC.exists_isAChain_simple_mul_last hlam i
      (by rw [hhead]; exact hleft k hk (by omega))
      (by rw [hlast]; exact hpos (k + 1) hk hk₂.1 hk₂.2)
    exact ⟨D, by rw [hDhead, hhead], by rw [hDlast, hlast], hD⟩
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
/-- The directions and durations produced from `l` by Littelmann's lowering operator along the
simple root `αᵢ`: the entries `k₀, …, j₁ - 1` and the first part `(τ, θ d)` of the entry
`l[j₁] = (τ, d)` are reflected by `sᵢ`, and the rest `(τ, (1 - θ) d)` of that entry and the later
entries are kept. -/
private noncomputable def lowerList (i : b.support) (l : List (P.weylGroup × ℚ)) (k₀ j₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  l.take k₀ ++ ((l.take j₁).drop k₀ ++ [(τ, θ * d)]).map
      (fun p ↦ ((weylCoxeterSystem P b).simple i * p.1, p.2)) ++
    (τ, (1 - θ) * d) :: l.drop (j₁ + 1)

omit [P.flip.IsReduced] in
private theorem nonneg_of_mem_lowerList (i : b.support) {l : List (P.weylGroup × ℚ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) {k₀ j₁ : ℕ} {τ : P.weylGroup} {d θ : ℚ} (hd : 0 ≤ d) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) {p : P.weylGroup × ℚ} (hp : p ∈ lowerList b i l k₀ j₁ τ d θ) : 0 ≤ p.2 := by
  simp only [lowerList, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with (hp | ⟨q, hq | rfl, rfl⟩) | rfl | hp
  · exact hl p (List.mem_of_mem_take hp)
  · exact hl q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
  · exact mul_nonneg hθ₀ hd
  · exact mul_nonneg (by linarith) hd
  · exact hl p (List.mem_of_mem_drop hp)

omit [P.flip.IsReduced] in
private theorem sum_map_snd_lowerList (i : b.support) {l : List (P.weylGroup × ℚ)} {k₀ j₁ : ℕ}
    (hj₁ : j₁ < l.length) (hk₀j₁ : k₀ ≤ j₁) (θ : ℚ) :
    ((lowerList b i l k₀ j₁ l[j₁].1 l[j₁].2 θ).map Prod.snd).sum = (l.map Prod.snd).sum := by
  conv_rhs => rw [← List.take_append_drop j₁ l, List.drop_eq_getElem_cons hj₁,
    ← List.take_append_drop k₀ (l.take j₁), List.take_take, min_eq_left hk₀j₁]
  simp only [lowerList, List.map_append, List.map_cons, List.map_map, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  ring

omit [P.flip.IsReduced] in
/-- Subdividing an entry `(τ, d)` of a linked list of minimal coset representatives at the fraction
`θ` of its duration keeps the list linked, and its directions are minimal coset representatives. -/
private theorem linked_subdivide {lam : M} {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    {j₁ : ℕ} (hj₁ : j₁ < l.length) {τ : P.weylGroup} {d : ℚ} (hτd : l[j₁] = (τ, d)) (θ : ℚ) :
    Linked P b lam 0 (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)) ∧
      ∀ p ∈ l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1),
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hτmin : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) τ := by
    have := hlmin _ (List.getElem_mem hj₁)
    rwa [hτd] at this
  refine ⟨?_, fun p hp ↦ ?_⟩
  · have hsplit : l = l.take j₁ ++ (τ, θ * d + (1 - θ) * d) :: l.drop (j₁ + 1) := by
      rw [show θ * d + (1 - θ) * d = d by ring, ← hτd, ← List.drop_eq_getElem_cons hj₁,
        List.take_append_drop]
    rw [hsplit] at hl
    exact Linked.split hτmin hl
  · simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | rfl | hp
    · exact hlmin p (List.mem_of_mem_take hp)
    · exact hτmin
    · exact hτmin
    · exact hlmin p (List.mem_of_mem_drop hp)

/-- Entries and partial sums of durations of the list obtained by subdividing the entry
`l[j₁] = (τ, d)` at the fraction `θ`: before the cut they are those of `l`, the entry at `j₁` is
`(τ, θ d)` and the one after it is `(τ, (1 - θ) d)`. -/
private theorem subdivide_getElem_and_sum_take {α : Type*} {l : List (α × ℚ)} {j₁ : ℕ}
    (hj₁ : j₁ < l.length) {τ : α} {d : ℚ} (hτd : l[j₁] = (τ, d)) (θ : ℚ)
    {Dp : List (α × ℚ)}
    (hDp : Dp = l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)) :
    Dp.length = l.length + 1 ∧
      (∀ k (hk : k < Dp.length) (hk' : k < l.length), k < j₁ → Dp[k] = l[k]) ∧
      (∀ h : j₁ < Dp.length, Dp[j₁] = (τ, θ * d)) ∧
      (∀ h : j₁ + 1 < Dp.length, Dp[j₁ + 1] = (τ, (1 - θ) * d)) ∧
      (∀ k (hk : k < Dp.length) (hk' : k < l.length), k ≤ j₁ → Dp[k].1 = l[k].1) ∧
      (∀ k ≤ j₁, ((Dp.take k).map Prod.snd).sum = ((l.take k).map Prod.snd).sum) ∧
      ((Dp.take (j₁ + 1)).map Prod.snd).sum = ((l.take j₁).map Prod.snd).sum + θ * d := by
  subst hDp
  have hlen_take : (l.take j₁).length = j₁ := by simp; omega
  have hlt : ∀ k (hk : k < (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)).length)
      (hk' : k < l.length), k < j₁ →
      (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1))[k] = l[k] := by
    intro k hk hk' hkj
    rw [List.getElem_append_left (by rw [hlen_take]; omega), List.getElem_take]
  have hj : ∀ h : j₁ < (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)).length,
      (l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1))[j₁] = (τ, θ * d) := by
    intro h
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  refine ⟨by simp; omega, hlt, hj, fun h ↦ ?_, fun k hk hk' hkj ↦ ?_, fun k hk ↦ ?_, ?_⟩
  · rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  · rcases hkj.lt_or_eq with hkj | rfl
    · rw [hlt k hk hk' hkj]
    · rw [hj hk, hτd]
  · rw [List.take_append_of_le_length (by omega), List.take_take, min_eq_left hk]
  · rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₁ + 1 - j₁ = 1 by omega]
    simp

omit [P.flip.IsReduced] in
/-- The list `TauCeti.LSPath.lowerList` is the subdivided list `Dp` with the directions in the
window `[k₀, j₁]` reflected by `sᵢ`. -/
private theorem lowerList_eq_mapIdx (i : b.support) {l : List (P.weylGroup × ℚ)} {k₀ j₁ : ℕ}
    (hj₁ : j₁ < l.length) (hk₀j₁ : k₀ ≤ j₁) (τ : P.weylGroup) (d θ : ℚ)
    {Dp : List (P.weylGroup × ℚ)}
    (hDp : Dp = l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)) :
    lowerList b i l k₀ j₁ τ d θ =
      Dp.mapIdx fun k p ↦
        if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p := by
  have hDp' : Dp = l.take k₀ ++ ((l.take j₁).drop k₀ ++ [(τ, θ * d)]) ++
      (τ, (1 - θ) * d) :: l.drop (j₁ + 1) := by
    rw [hDp]
    conv_lhs => rw [← List.take_append_drop k₀ (l.take j₁), List.take_take, min_eq_left hk₀j₁]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hA : (l.take k₀).length = k₀ := by simp; omega
  have hB : ((l.take j₁).drop k₀ ++ [(τ, θ * d)]).length = j₁ - k₀ + 1 := by simp; omega
  rw [hDp']
  refine List.ext_getElem (by simp [lowerList]) fun k hk₁ hk₂ ↦ ?_
  simp only [lowerList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
    List.length_append, List.length_map, hA, hB]
  split_ifs <;> first | rfl | omega

/-- **The reflected subdivided list is linked.** Subdivide the entry `l[j₁] = (τ, d)` of a linked
list `l` of minimal coset representatives at the fraction `θ`, and reflect by `sᵢ` the directions
of the window `[k₀, j₁]`, along which the height `⟨-, αᵢ^∨⟩` is positive. Under the hypotheses of
`TauCeti.LSPath.linked_lowerList`, the result is linked and its directions are minimal coset
representatives. -/
private theorem linked_mapIdx_subdivide (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {k₀ j₁ : ℕ} (hj₁ : j₁ < l.length) (hk₀j₁ : k₀ ≤ j₁) {τ : P.weylGroup} {d : ℚ}
    (hτd : l[j₁] = (τ, d)) (θ : ℚ)
    (hpos : ∀ k (hk : k < l.length), k₀ ≤ k → k ≤ j₁ → 0 < P.coroot' i (l[k].1 • lam))
    (hint : ∀ k (hk : k < l.length), k₀ < k → k ≤ j₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i (l[k].1 • lam) = m)
    (hleft : ∀ k (hk : k < l.length), k + 1 = k₀ → P.coroot' i (l[k].1 • lam) ≤ 0)
    (hcut : ∃ m : ℤ,
      (((l.take j₁).map Prod.snd).sum + θ * d) * P.coroot' i (τ • lam) = m)
    {Dp : List (P.weylGroup × ℚ)}
    (hDp : Dp = l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1)) :
    Linked P b lam 0 (Dp.mapIdx fun k p ↦
        if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) ∧
      ∀ p ∈ Dp.mapIdx (fun k p ↦
          if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p),
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  obtain ⟨hDp_len, hDp_lt, hDp_j₁, hDp_j₁1, hDp_fst, hcum_le, hcum_j₁1⟩ :=
    subdivide_getElem_and_sum_take hj₁ hτd θ hDp
  obtain ⟨hDp_linked, hDpmin⟩ := linked_subdivide hl hlmin hj₁ hτd θ
  rw [← hDp] at hDp_linked hDpmin
  -- Reflect the window `[k₀, j₁]` of the subdivided list in `sᵢ`.
  have hW := Linked.mapIdx_simple_mul hlam hDp_linked hDpmin i (k₀ := k₀) (j₁ := j₁)
    (by omega)
    (fun k hk hk₀ hkj ↦ by
      rw [hDp_fst k hk (by omega) hkj]
      exact hpos k (by omega) hk₀ hkj)
    (fun k hk hk₀ hkj ↦ by
      rw [zero_add, hcum_le k hkj, hDp_fst k hk (by omega) hkj]
      exact hint k (by omega) hk₀ hkj)
    (fun k hk hkk ↦ by
      rw [hDp_lt k (by omega) (by omega) (by omega)]
      exact hleft k (by omega) hkk)
    (by rw [hDp_j₁1 _, hDp_j₁ _])
    (by
      rw [zero_add, hcum_j₁1, hDp_j₁ _]
      exact hcut)
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst k hk' (by omega) hw.2]
    exact (hpos k (by omega) hw.1 hw.2).ne'
  · exact hDpmin _ (List.getElem_mem hk')

/-- **The lowered list is linked.** Let `l` be a linked list of minimal coset representatives,
let `[k₀, j₁]` be a window along which the height `⟨-, αᵢ^∨⟩` of the directions is positive, with
`a ⟨τ λ, αᵢ^∨⟩` nonintegral at its internal breaks `a`, entered from a direction of nonpositive
height, and let `θ` cut the entry `l[j₁] = (τ, d)` at an `a`-integral time. Then the list
`TauCeti.LSPath.lowerList` produced by Littelmann's lowering operator is linked, and its
directions are minimal coset representatives. -/
private theorem linked_lowerList (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {k₀ j₁ : ℕ} (hj₁ : j₁ < l.length) (hk₀j₁ : k₀ ≤ j₁) (θ : ℚ)
    (hpos : ∀ k (hk : k < l.length), k₀ ≤ k → k ≤ j₁ → 0 < P.coroot' i (l[k].1 • lam))
    (hint : ∀ k (hk : k < l.length), k₀ < k → k ≤ j₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i (l[k].1 • lam) = m)
    (hleft : ∀ k (hk : k < l.length), k + 1 = k₀ → P.coroot' i (l[k].1 • lam) ≤ 0)
    (hcut : ∃ m : ℤ,
      (((l.take j₁).map Prod.snd).sum + θ * l[j₁].2) * P.coroot' i (l[j₁].1 • lam) = m) :
    Linked P b lam 0 (lowerList b i l k₀ j₁ l[j₁].1 l[j₁].2 θ) ∧
      ∀ p ∈ lowerList b i l k₀ j₁ l[j₁].1 l[j₁].2 θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hlow := lowerList_eq_mapIdx i hj₁ hk₀j₁ l[j₁].1 l[j₁].2 θ rfl
  rw [hlow]
  exact linked_mapIdx_subdivide hlam hl hlmin i hj₁ hk₀j₁ rfl θ hpos hint hleft hcut rfl


variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V]
  [Module 𝕜 V]

omit [P.flip.IsReduced] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The reflection `s = Module.preReflection (f αᵢ) F`, for a form `F` inducing `⟨-, αᵢ^∨⟩`,
sends the segment `d • f (τ λ)` to `d • f ((sᵢ τ) λ)`. -/
private theorem preReflection_smul_apply (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (d : 𝕜) (w : P.weylGroup) :
    Module.preReflection (f (P.root i)) F (d • f (w • lam)) =
      d • f (((weylCoxeterSystem P b).simple i * w) • lam) := by
  rw [map_smul, ← P.map_reflection_eq_preReflection i hF, simple_mul_smul_eq_reflection]

/-- If a sequence rises strictly on the window `[k₀, j₁]`, starts at `z` there and stays below
`z + 1` at `j₁`, then its values strictly inside the window lie strictly between `z` and
`z + 1`. -/
private theorem lt_and_lt_add_one_of_lt_succ {hgt : ℕ → ℚ} {k₀ j₁ : ℕ} {z : ℚ}
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1)) (hk₀ : hgt k₀ = z)
    (hj₁ : hgt j₁ < z + 1) {k : ℕ} (hk₀k : k₀ < k) (hkj : k ≤ j₁) : z < hgt k ∧ hgt k < z + 1 := by
  have hmono : ∀ m k, k₀ ≤ k → k + m ≤ j₁ + 1 → hgt k ≤ hgt (k + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro k hk hkm
      exact (ih k hk (by omega)).trans (hrise (k + m) (by omega) (by omega)).le
  refine ⟨?_, ?_⟩
  · have h₁ := hrise k₀ le_rfl (by omega)
    have h₂ := hmono (k - (k₀ + 1)) (k₀ + 1) (by omega) (by omega)
    rw [show k₀ + 1 + (k - (k₀ + 1)) = k by omega] at h₂
    linarith
  · have h₂ := hmono (j₁ - k) k (by omega) (by omega)
    rw [show k + (j₁ - k) = j₁ by omega] at h₂
    linarith

/-- A rational strictly between two consecutive integers, congruent modulo integers to `c`, shows
that `c` is not an integer. -/
private theorem not_exists_intCast_of_lt_of_lt_add_one {x c : ℚ} {z : ℤ}
    (hx : ∃ m : ℤ, x - c = m) (h₁ : (z : ℚ) < x) (h₂ : x < z + 1) : ¬∃ m : ℤ, c = m := by
  rintro ⟨m, rfl⟩
  obtain ⟨m', hm'⟩ := hx
  have hk' : x = ((m' + m : ℤ) : ℚ) := by
    push_cast
    linarith
  rw [hk'] at h₁ h₂
  have h₁' : z < m' + m := by exact_mod_cast h₁
  have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
  omega

omit [P.flip.IsReduced] in
/-- The segments of the lowered list are those of `D`, with the window `[k₀, j₁]` and the cut piece
reflected by `Module.preReflection (f αᵢ) F`, for a form `F` inducing `⟨-, αᵢ^∨⟩`. -/
private theorem map_segments_lowerList (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (D : List (P.weylGroup × ℚ)) (k₀ j₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) :
    (lowerList b i D k₀ j₁ τ d θ).map (fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) =
      (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take k₀ ++
        ((((D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take j₁).drop k₀ ++
          [((θ : 𝕜) * d) • f (τ • lam)]).map (Module.preReflection (f (P.root i)) F)) ++
        ((1 - (θ : 𝕜)) * d) • f (τ • lam) ::
          (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).drop (j₁ + 1) := by
  have hσ : ∀ p : P.weylGroup × ℚ,
      (p.2 : 𝕜) • f (((weylCoxeterSystem P b).simple i * p.1) • lam) =
        Module.preReflection (f (P.root i)) F ((p.2 : 𝕜) • f (p.1 • lam)) := fun p ↦
    (preReflection_smul_apply f i F hF _ _).symm
  simp only [lowerList, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.map_take, List.map_drop, Function.comp_def, hσ]
  push_cast
  rw [preReflection_smul_apply f i F hF]

omit [Finite ι] [P.IsReduced] [P.flip.IsReduced] in
/-- The heights `F` of the vertices of the realization of the list `D` are the rational heights
`∑ dₖ ⟨τₖ λ, αᵢ^∨⟩`, for a form `F` inducing `⟨-, αᵢ^∨⟩`. -/
private theorem apply_sum_take_map_segments (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (D : List (P.weylGroup × ℚ)) (k : ℕ) :
    F ((D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take k).sum =
      (((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum : ℚ) := by
  simp only [← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
  congr 1
  refine List.map_congr_left fun p _ ↦ ?_
  simp [hF]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- If `x + θ y = z + 1` in a field `𝕜` of characteristic zero, with `x`, `y` rational and `y`
nonzero, then `θ` is the rational number `(z + 1 - x) / y`. -/
private theorem eq_cast_div_of_add_mul_eq [CharZero 𝕜] {x y : ℚ} {z : ℤ} {θ : 𝕜} (hy : y ≠ 0)
    (h : (x : 𝕜) + θ * y = z + 1) : θ = (((z + 1 - x) / y : ℚ) : 𝕜) := by
  push_cast
  rw [eq_div_iff (by exact_mod_cast hy)]
  linear_combination h

/-- Adding one more entry of a list adds its image to the partial sum of the images. -/
private theorem sum_take_succ_map {α β : Type*} [AddMonoid β] (g : α → β) (D : List α) {k : ℕ}
    (hk : k < D.length) : ((D.take (k + 1)).map g).sum = ((D.take k).map g).sum + g D[k] := by
  rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]

/-- Along a window where the rational heights `∑ dₖ c(τₖ)` rise strictly, the integers `c(τₖ)` are
positive, as the durations `dₖ` are. -/
private theorem coroot_pos_of_lt_succ {α : Type*} (c : α → ℤ) (D : List (α × ℚ))
    (hdpos : ∀ k (hk : k < D.length), 0 < D[k].2) {k₀ j₁ : ℕ} (hgt : ℕ → ℚ)
    (hhgt : ∀ k, hgt k = ((D.take k).map fun p ↦ p.2 * (c p.1 : ℚ)).sum)
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1)) :
    ∀ k (hk : k < D.length), k₀ ≤ k → k ≤ j₁ → 0 < c D[k].1 := fun k hk hk₀ hkj ↦ by
  have := hrise k hk₀ hkj
  rw [hhgt, hhgt, sum_take_succ_map _ D hk] at this
  have h : (0 : ℚ) < c D[k].1 := pos_of_mul_pos_right (by linarith) (hdpos k hk).le
  exact_mod_cast h

/-- **The integrality data of a window.** Let the rational heights `hgt k = ∑_{j<k} dⱼ c(τⱼ)` of a
list `D` start at the integer `z` at `k₀`, rise strictly up to `j₁`, and reach `z + 1` at the
fraction `θ` of the entry `j₁`, and let them be congruent modulo integers to `aₖ c(τₖ)` at the
break `aₖ`. Then `aₖ c(τₖ)` is not an integer strictly inside the window, `c(τₖ) ≤ 0` just before
it, and `(a_{j₁} + θ d_{j₁}) c(τ_{j₁})` is an integer. -/
private theorem window_facts_of_heights {α : Type*} (c : α → ℤ) (D : List (α × ℚ))
    (hdpos : ∀ k (hk : k < D.length), 0 < D[k].2) {k₀ j₁ : ℕ} (hk₀j₁ : k₀ ≤ j₁)
    (hj₁ : j₁ < D.length) (hgt : ℕ → ℚ)
    (hhgt : ∀ k, hgt k = ((D.take k).map fun p ↦ p.2 * (c p.1 : ℚ)).sum) {z : ℤ}
    (hk₀ : hgt k₀ = z) (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1))
    (hpos : ∀ k (hk : k < D.length), k₀ ≤ k → k ≤ j₁ → 0 < c D[k].1)
    (hmin : ∀ k, k + 1 = k₀ → (z : ℚ) ≤ hgt k)
    (hcong : ∀ k (hk : k < D.length),
      ∃ m : ℤ, hgt k - ((D.take k).map Prod.snd).sum * (c D[k].1 : ℚ) = m)
    {θ : ℚ} (hθpos : 0 < θ) (hθd : θ * (D[j₁].2 * (c D[j₁].1 : ℚ)) = z + 1 - hgt j₁) :
    (∀ k (hk : k < D.length), k₀ < k → k ≤ j₁ →
      ¬∃ m : ℤ, ((D.take k).map Prod.snd).sum * (c D[k].1 : ℚ) = m) ∧
    (∀ k (hk : k < D.length), k + 1 = k₀ → c D[k].1 ≤ 0) ∧
    ∃ m : ℤ, (((D.take j₁).map Prod.snd).sum + θ * D[j₁].2) * (c D[j₁].1 : ℚ) = m := by
  have hdH : 0 < D[j₁].2 * (c D[j₁].1 : ℚ) :=
    mul_pos (hdpos j₁ hj₁) (by exact_mod_cast hpos j₁ hj₁ hk₀j₁ le_rfl)
  refine ⟨fun k hk hk₀' hkj ↦ ?_, fun k hk hkk ↦ ?_, ?_⟩
  · have hlt := lt_and_lt_add_one_of_lt_succ hrise hk₀ (by nlinarith [mul_pos hθpos hdH]) hk₀' hkj
    exact not_exists_intCast_of_lt_of_lt_add_one (hcong k hk) hlt.1 hlt.2
  · have := hmin k hkk
    have hsucc := sum_take_succ_map (fun p : α × ℚ ↦ p.2 * (c p.1 : ℚ)) D hk
    rw [← hhgt, ← hhgt, hkk, hk₀] at hsucc
    have : (c D[k].1 : ℚ) ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) (hdpos k hk)
    exact_mod_cast this
  · obtain ⟨m, hm⟩ := hcong j₁ hj₁
    refine ⟨z + 1 - m, ?_⟩
    push_cast
    linear_combination hθd - hm

/-- **The rational data of a lowering step.** If Littelmann's lowering operator `f_αᵢ` is defined on
the path of an LS path `π` of dominant shape, it is presented by the lowered list
`TauCeti.LSPath.lowerList` of the directions and durations of `π`, for a window `[k₀, j₁]` and a
cut `θ` satisfying the hypotheses of `TauCeti.LSPath.linked_lowerList`. -/
private theorem exists_lower_toPLPath_eq_ofSegments_lowerList (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    (h1 : 1 ≤ F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F) :
    ∃ (k₀ j₁ : ℕ) (hj₁ : j₁ < π.dirDurations.length) (θ : ℚ), k₀ ≤ j₁ ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      (∀ k (hk : k < π.dirDurations.length), k₀ ≤ k → k ≤ j₁ →
        0 < P.coroot' i (π.dirDurations[k].1 • lam)) ∧
      (∀ k (hk : k < π.dirDurations.length), k₀ < k → k ≤ j₁ →
        ¬∃ m : ℤ, ((π.dirDurations.take k).map Prod.snd).sum *
          P.coroot' i (π.dirDurations[k].1 • lam) = m) ∧
      (∀ k (hk : k < π.dirDurations.length), k + 1 = k₀ →
        P.coroot' i (π.dirDurations[k].1 • lam) ≤ 0) ∧
      (∃ m : ℤ, (((π.dirDurations.take j₁).map Prod.snd).sum + θ * π.dirDurations[j₁].2) *
        P.coroot' i (π.dirDurations[j₁].1 • lam) = m) ∧
      PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
        ((lowerList b i π.dirDurations k₀ j₁ π.dirDurations[j₁].1 π.dirDurations[j₁].2 θ).map
          fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))) := by
  obtain ⟨k₀, j₁', θ', hk₀j₁, hθpos', hθle', hmin, hrise, hcross, -, hlow⟩ :=
    π.exists_lower_toPLPath_eq hlam f i F hF (f (P.root i)) h1
  obtain ⟨z, hz⟩ := π.exists_minHeight_eq_intCast hlam f i F hF
  have hminH : (π.toPLPath 𝕜 f).minHeight F =
      PLPath.listMinHeight F (π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)) := by
    rw [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed]
  rw [map_snd_timed] at hmin hrise hcross hlow
  set D := π.dirDurations with hD
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam) with hseg
  set hgt : ℕ → ℚ := fun k ↦
    ((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum with hhgt
  set j₁ : ℕ := (j₁' : ℕ) with hj₁
  have hj₁lt : j₁ < D.length := by rw [length_dirDurations]; exact j₁'.2
  set τ := (π.dir j₁').1 with hτ
  set d := π.duration j₁' with hd
  have hDj₁ : D[j₁] = (τ, d) := by rw [getElem_dirDurations]
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  -- Heights of the realization at the vertices are the rational heights of the encoding.
  have hHF : ∀ k, F ((D.map seg).take k).sum = (hgt k : 𝕜) := fun k ↦
    apply_sum_take_map_segments f i F hF D k
  have hgtk₀ : hgt k₀ = z := by
    rw [hHF, hz] at hmin
    exact_mod_cast hmin
  have hrise' : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1) := fun k hk₀ hkj ↦ by
    have := hrise k hk₀ hkj
    rwa [hHF, hHF, Rat.cast_lt] at this
  have hpos := coroot_pos_of_lt_succ (fun w ↦ P.coroot' i (w • lam)) D hdpos hgt (fun _ ↦ rfl)
    hrise'
  have hdH : 0 < d * (P.coroot' i (τ • lam) : ℚ) := by
    have := hpos j₁ hj₁lt hk₀j₁ le_rfl
    rw [hDj₁] at this
    exact mul_pos (by rw [hd]; exact π.duration_pos _) (by exact_mod_cast this)
  set θ : ℚ := (z + 1 - hgt j₁) / (d * P.coroot' i (τ • lam)) with hθ
  have hθ' : θ' = θ := by
    have hc := hcross
    rw [hHF, hz, show F ((d : 𝕜) • f (τ • lam)) = ((d * P.coroot' i (τ • lam) : ℚ) : 𝕜) by
      simp [hF]] at hc
    exact eq_cast_div_of_add_mul_eq hdH.ne' hc
  rw [hθ'] at hθpos' hθle' hlow
  have hθpos : 0 < θ := by exact_mod_cast hθpos'
  -- At the vertex `k₀` the height is minimal, so the segment before it does not rise.
  have hleftH : ∀ k, k + 1 = k₀ → (z : ℚ) ≤ hgt k := fun k _ ↦ by
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F) (D.map seg) k
    rw [← hminH, hz, hHF] at hle
    exact_mod_cast hle
  obtain ⟨hint, hleft, hcut⟩ := window_facts_of_heights (fun w ↦ P.coroot' i (w • lam)) D hdpos
    hk₀j₁ hj₁lt hgt (fun _ ↦ rfl) hgtk₀ hrise' hpos hleftH
    (fun k hk ↦ π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk)
    hθpos (by rw [hDj₁]; exact div_mul_cancel₀ _ hdH.ne')
  refine ⟨k₀, j₁, hj₁lt, θ, hk₀j₁, hθpos.le, by exact_mod_cast hθle', hpos, hint, hleft, hcut, ?_⟩
  rw [hlow, hDj₁, map_segments_lowerList f i F hF D k₀ j₁ τ d θ]

/-- **Littelmann's lowering operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the lowering operator `f_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_lower_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  -- The lowering operator is defined, so the height rises by at least one after its minimum.
  have h1 : 1 ≤ F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F := by
    by_contra h
    have := (PLPath.lower_eq_none_iff (x := f (P.root i))).mpr (not_le.mp h)
    rw [hq] at this
    exact Option.some_ne_none _ this
  obtain ⟨k₀, j₁, hj₁, θ, hk₀j₁, hθ₀, hθ₁, hpos, hint, hleft, hcut, hlow⟩ :=
    exists_lower_toPLPath_eq_ofSegments_lowerList π hlam f i F hF h1
  obtain ⟨hL, hLmin⟩ := linked_lowerList hlam π.linked_dirDurations
    (fun _ hp ↦ π.isMinimalCosetRep_of_mem_dirDurations hp) i hj₁ hk₀j₁ θ hpos hint hleft hcut
  refine ⟨ofLinked _ hLmin
    (fun _ hp ↦ nonneg_of_mem_lowerList i (fun _ hp ↦ (π.pos_of_mem_dirDurations hp).le)
      (π.pos_of_mem_dirDurations (List.getElem_mem hj₁)).le hθ₀ hθ₁ hp)
    (by rw [sum_map_snd_lowerList i hj₁ hk₀j₁, sum_map_snd_dirDurations]) hL, ?_⟩
  rw [toPLPath_ofLinked]
  exact Option.some.inj (hlow.symm.trans hq)

end TauCeti.LSPath
