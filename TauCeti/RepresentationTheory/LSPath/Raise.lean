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
that either `e_αᵢ` is undefined or a single LS path realizes `e_αᵢ π` across any two ordered-field
realizations (`TauCeti.LSPath.raise_toPLPath_eq_none_or_exists_eq_some_and_eq_some`), and that two
LS paths with the same directions, durations, and `αᵢ^∨`-orbit pairings either both have undefined
`e_αᵢ` or raise to LS paths with the same directions and durations
(`TauCeti.LSPath.raise_toPLPath_eq_none_or_exists_dirDurations_eq_of_dirDurations_eq`).

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
* `TauCeti.LSPath.raise_toPLPath_eq_none_or_exists_eq_some_and_eq_some`: either `e_αᵢ` is `none` in
  both realizations, or a single LS path realizes `e_αᵢ` across any two ordered-field realizations.
* `TauCeti.LSPath.raise_toPLPath_eq_none_or_exists_dirDurations_eq_of_dirDurations_eq`: `e_αᵢ`
  preserves equality of `dirDurations` between dominant shapes with the same `αᵢ^∨`-orbit pairings.

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

private theorem raiseList_eq_mapIdx_subdivide (i : b.support) {l : List (P.weylGroup × ℚ)}
    {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (τ : P.weylGroup) (d θ : ℚ) :
    raiseList b i l j₀ k₁ τ d θ =
      (subdivide l j₀ τ d θ).mapIdx fun k p ↦
        if j₀ + 1 ≤ k ∧ k ≤ k₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p := by
  have hj₀ : j₀ < l.length := lt_of_lt_of_le hj₀k₁ hk₁
  have htake : (l.take j₀).length = j₀ := by simp [Nat.min_eq_left hj₀.le]
  have hdrop : l.drop (j₀ + 1) = (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ := by
    conv_lhs => rw [← List.take_append_drop k₁ l]
    rw [List.drop_append, List.length_take_of_le hk₁,
      show j₀ + 1 - k₁ = 0 by omega, List.drop_zero]
  have hDp' : subdivide l j₀ τ d θ = (l.take j₀ ++ [(τ, θ * d)]) ++
      ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
    rw [subdivide_def, hdrop]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hA : (l.take j₀ ++ [(τ, θ * d)]).length = j₀ + 1 := by simp [htake]
  have hB : ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by
    simp [List.length_take_of_le hk₁]
    omega
  rw [hDp']
  refine List.ext_getElem (by simp [raiseList]) fun k _ _ ↦ ?_
  simp only [raiseList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
    List.length_append, List.length_map, hA, hB]
  split_ifs <;> first | rfl | omega

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
  have hτmin : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) l[j₀].1 :=
    hlmin _ (List.getElem_mem hj₀)
  -- Subdivide the entry `j₀` at fraction `θ` and reflect `[j₀ + 1, k₁]` in `sᵢ`.
  set Dp := subdivide l j₀ l[j₀].1 l[j₀].2 θ
  have hDp_linked : Linked P b lam 0 Dp := hl.subdivide hj₀ hτmin θ
  have hDpmin : ∀ p ∈ Dp, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 :=
    fun _ ↦ isMinimalCosetRep_of_mem_subdivide hlmin hτmin
  have hDp_len : Dp.length = l.length + 1 := length_subdivide hj₀ _ _ _
  have hW := Linked.mapIdx_simple_mul_falling hlam hDp_linked hDpmin i
    (j₀ := j₀) (k₁ := k₁) hj₀k₁ (by omega)
    (fun k hk hkj hkk₁ ↦ by
      rw [fst_getElem_subdivide_ge hj₀ hk hkj]
      exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkj hkk₁ ↦ by
      rw [zero_add, sum_map_snd_take_subdivide_gt hj₀ θ hkj,
        fst_getElem_subdivide_ge hj₀ hk hkj.le]
      exact hint (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkk₁ ↦ by
      subst hkk₁
      rw [getElem_subdivide_gt hj₀ _ _ _ hk (by omega)]
      simpa using hright (by omega))
    (by rw [getElem_subdivide_succ hj₀, getElem_subdivide_self hj₀])
    (by
      rw [zero_add, sum_map_snd_take_subdivide_succ hj₀, getElem_subdivide_self hj₀]
      exact hcut)
  rw [raiseList_eq_mapIdx_subdivide i hj₀k₁ hk₁]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [fst_getElem_subdivide_ge hj₀ hk' hw.1]
    exact (hneg (k - 1) (by omega) (by omega) (by omega)).ne
  · exact hDpmin _ (List.getElem_mem hk')

/-- Given a shape `lam₂` whose `dirDurations` and `αᵢ^∨`-orbit pairings match those of `π`, any
form `F` inducing `⟨-, αᵢ^∨⟩` has the same minimum height `z` on `π₂.toPLPath` as
`LinearMap.proj (P.coroot i)` has on `π.toPLPath ℚ (P.coweightEval ℚ)`. -/
private theorem minHeight_eq_of_dirDurations_eq {lam₂ : M} (π : LSPath P b lam)
    (π₂ : LSPath P b lam₂) (i : b.support)
    (hdir : π₂.dirDurations = π.dirDurations)
    (hcoroot : ∀ w : P.weylGroup, P.coroot' i (w • lam₂) = P.coroot' i (w • lam)) {z : ℤ}
    (hz₀ : (π.toPLPath ℚ (P.coweightEval ℚ)).minHeight
      (LinearMap.proj (R := ℚ) (P.coroot i)) = z)
    {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    (π₂.toPLPath 𝕜 f).minHeight F = z := by
  set D := π.dirDurations
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
  have hHF₀ : ∀ k, (LinearMap.proj (R := ℚ) (P.coroot i))
      ((D.map fun p ↦ (p.2 : ℚ) • P.coweightEval ℚ (p.1 • lam)).take k).sum = hgt k := by
    intro k
    simpa only [Rat.cast_id] using
      apply_sum_take_map_smul (P := P) (lam := lam) (𝕜 := ℚ) (P.coweightEval ℚ)
        (LinearMap.proj (R := ℚ) (P.coroot i)) H
        (fun w ↦ by simp [H]) D k
  have hHF₂ : ∀ k, F ((D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂)).take k).sum = (hgt k : 𝕜) :=
    apply_sum_take_map_smul f F H (fun w ↦ by rw [hF, hcoroot]; simp [H]) D
  have hm₀ : PLPath.listMinHeight (LinearMap.proj (R := ℚ) (P.coroot i))
      (D.map fun p ↦ (p.2 : ℚ) • P.coweightEval ℚ (p.1 • lam)) = z := by
    simpa only [toPLPath_def, map_snd_timed, Rat.cast_id, PLPath.minHeight_ofSegments] using hz₀
  rw [toPLPath_def, map_snd_timed, hdir, PLPath.minHeight_ofSegments]
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := LinearMap.proj (R := ℚ) (P.coroot i))
      (D.map fun p ↦ (p.2 : ℚ) • P.coweightEval ℚ (p.1 • lam))
    rw [hm₀, hHF₀] at hk
    have hb := PLPath.listMinHeight_le_apply_sum_take (f := F)
      (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂)) k
    rw [hHF₂, ← hk, Rat.cast_intCast] at hb
    exact hb
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F)
      (D.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam₂))
    have hb := PLPath.listMinHeight_le_apply_sum_take (f := LinearMap.proj (R := ℚ) (P.coroot i))
      (D.map fun p ↦ (p.2 : ℚ) • P.coweightEval ℚ (p.1 • lam)) k
    rw [hm₀, hHF₀] at hb
    rw [hk, hHF₂, ← Rat.cast_intCast]
    exact Rat.cast_le.mpr hb

/-- Along a sequence `hgt` strictly decreasing on `[j₀, k₁)` with `hgt (j₀ + 1) < c`, every
interior value `hgt k` (`j₀ < k < k₁`) satisfies `hgt k < c`. -/
private theorem lt_of_strictAnti_Ico {hgt : ℕ → ℚ} {j₀ k₁ : ℕ} {c : ℚ}
    (hfall : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k)
    (hc : hgt (j₀ + 1) < c) {k : ℕ} (hkj : j₀ < k) (hkk₁ : k < k₁) :
    hgt k < c := by
  have hmono : ∀ m, j₀ + 1 + m ≤ k₁ → hgt (j₀ + 1 + m) ≤ hgt (j₀ + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      exact (hfall (j₀ + 1 + m) (by omega) (by omega)).le.trans (ih (by omega))
  have hk := hmono (k - (j₀ + 1)) (by omega)
  rw [show j₀ + 1 + (k - (j₀ + 1)) = k by omega] at hk
  exact hk.trans_lt hc

/-- **The rational data of a raising step.** When the rational minimum height `z` of `π` along
`αᵢ^∨` satisfies `z ≤ -1`, there are a cut segment `j₀`, a first-minimum vertex `k₁ > j₀` and a
fraction `0 ≤ θ ≤ 1` satisfying the hypotheses of `linked_raiseList`. -/
private theorem exists_raiseList_data (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (i : b.support) {z : ℤ}
    (hz₀ : (π.toPLPath ℚ (P.coweightEval ℚ)).minHeight
      (LinearMap.proj (R := ℚ) (P.coroot i)) = z)
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
  -- Extract the strictly falling window `(j₀, k₁, θ)` in the canonical rational realization.
  let F₀ : Module.Dual ℚ (N → ℚ) := LinearMap.proj (R := ℚ) (P.coroot i)
  have h1 : (π.toPLPath ℚ (P.coweightEval ℚ)).minHeight F₀ ≤ -1 := by
    rw [hz₀]
    exact_mod_cast hz
  obtain ⟨j₀', k₁, θ, hj₀k₁, hk₁s, hθ₀, hθlt, hmin, habove_min, habove, hfall, hcross, -⟩ :=
    π.exists_raise_toPLPath_eq hlam (P.coweightEval ℚ) i F₀
      (P.proj_coroot_coweightEval ℚ i) 0 h1
  rw [map_snd_timed] at hmin habove_min habove hfall hcross
  simp only [Rat.cast_id] at hmin habove_min habove hfall hcross
  rw [hz₀] at hmin habove_min habove hcross
  set D := π.dirDurations
  set j₀ : ℕ := (j₀' : ℕ)
  have hk₁D : k₁ ≤ D.length := by rwa [length_dirDurations]
  have hj₀lt : j₀ < D.length := lt_of_lt_of_le hj₀k₁ hk₁D
  set τ := (π.dir j₀').1
  set d := π.duration j₀'
  have hDj₀ : D[j₀] = (τ, d) := by rw [getElem_dirDurations]
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  -- Express vertex heights via the shared rational prefix-sum helper.
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
  set cum : ℕ → ℚ := fun k ↦ ((D.take k).map Prod.snd).sum
  have hHF₀ : ∀ k, F₀ ((D.map fun p ↦ (p.2 : ℚ) • P.coweightEval ℚ (p.1 • lam)).take k).sum =
      hgt k := by
    intro k
    simpa only [Rat.cast_id] using
      apply_sum_take_map_smul (P := P) (lam := lam) (𝕜 := ℚ) (P.coweightEval ℚ) F₀ H
        (fun w ↦ by simp [F₀, H]) D k
  have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
    intro k hk
    simp only [hgt, List.map_take]
    rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
  have hgtk₁ : hgt k₁ = z := by rwa [hHF₀] at hmin
  have habove_min' : ∀ k < k₁, (z : ℚ) < hgt k := fun k hk ↦ by
    have := habove_min k hk
    rwa [hHF₀] at this
  have habove' : ∀ k ≤ j₀, (z : ℚ) + 1 ≤ hgt k := fun k hk ↦ by
    have := habove k hk
    rwa [hHF₀] at this
  have hfall' : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k := fun k hkj hkk₁ ↦ by
    have := hfall k hkj hkk₁
    rwa [hHF₀, hHF₀] at this
  have hcross' : hgt j₀ + θ * (d * H τ) = z + 1 := by
    have hc := hcross
    rw [hHF₀, map_smul, smul_eq_mul, ← mul_assoc] at hc
    simpa only [F₀, P.proj_coroot_coweightEval ℚ i, H, d, τ, mul_assoc] using hc
  -- Deduce direction signs and strict interior height bounds `(z, z + 1)` on `(j₀, k₁)`.
  have hmin_le : ∀ k, (z : ℚ) ≤ hgt k := by
    intro k
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F₀)
      (D.map fun p ↦ p.2 • P.coweightEval ℚ (p.1 • lam)) k
    have hm : PLPath.listMinHeight F₀ (D.map fun p ↦ p.2 • P.coweightEval ℚ (p.1 • lam)) = z := by
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
    have : (1 - θ) * (d * H τ) < 0 := mul_neg_of_pos_of_neg (by linarith) hdH
    linarith
  have hrightH : ∀ (hk : k₁ < D.length), 0 ≤ H D[k₁].1 := fun hk ↦ by
    have hle := hmin_le (k₁ + 1)
    rw [hgt_succ k₁ hk, hgtk₁] at hle
    exact nonneg_of_mul_nonneg_right (by linarith) (hdpos k₁ hk)
  -- Combine congruence modulo `ℤ` at breaks with `(z, z + 1)` to rule out interior integrality.
  have hcong : ∀ k (hk : k < D.length), ∃ m : ℤ, hgt k - cum k * H D[k].1 = m := fun k hk ↦
    π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
  refine ⟨j₀, k₁, hj₀k₁, hk₁D, θ, hθ₀, hθlt.le,
    fun k hk hkj hkk₁ ↦ ?_, fun k hk hkj hkk₁ ↦ ?_, fun hk ↦ ?_, ?_,
    hgtk₁, habove', hfall', ?_, hHk₀₁.le⟩
  · exact Int.cast_lt.mp (hnegH k hk hkj hkk₁)
  · rintro ⟨m, hm⟩
    obtain ⟨m', hm'⟩ := hcong k hk
    have h₁ := habove_min' k hkk₁
    have h₂ := lt_of_strictAnti_Ico hfall' hHk₀₁ hkj hkk₁
    have hk' : hgt k = ((m' + m : ℤ) : ℚ) := by
      simp only [H] at hm'
      push_cast
      linarith
    rw [hk'] at h₁ h₂
    have h₁' : z < m' + m := by exact_mod_cast h₁
    have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
    omega
  · have h := hrightH hk
    dsimp only [H] at h
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
    {z : ℤ} (hz₀ : (π.toPLPath ℚ (P.coweightEval ℚ)).minHeight
      (LinearMap.proj (R := ℚ) (P.coroot i)) = z)
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
      (((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum : 𝕜) :=
    apply_sum_take_map_smul f F (fun w ↦ (P.coroot' i (w • lam) : ℚ))
      (fun w ↦ by rw [hF, hcoroot]; simp) D
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
theorem raise_toPLPath_eq_none_or_exists_dirDurations_eq_of_dirDurations_eq
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
  obtain ⟨z, hz₀⟩ := π₁.exists_minHeight_eq_intCast hlam₁ (P.coweightEval ℚ) i
    (LinearMap.proj (R := ℚ) (P.coroot i)) (P.proj_coroot_coweightEval ℚ i)
  by_cases hz : z ≤ -1
  · -- When `z ≤ -1`, build both raised LS paths from the same `raiseList` on `π₁.dirDurations`.
    right
    obtain ⟨j₀, k₁, hj₀k₁, hk₁, θ, hθ₀, hθ₁, hneg, hint, hright, hcut,
      hgtk₁, habove, hfall, hcross, hHk₀₁⟩ := exists_raiseList_data π₁ hlam₁ i hz₀ hz
    have hj₀ : j₀ < π₁.dirDurations.length := lt_of_lt_of_le hj₀k₁ hk₁
    obtain ⟨hL₁, hLmin₁⟩ := linked_raiseList hlam₁ π₁.linked_dirDurations
      (fun _ hp ↦ π₁.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁ θ hneg hint hright hcut
    have hl₂ : Linked P b lam₂ 0 π₁.dirDurations := hdir ▸ π₂.linked_dirDurations
    have hlmin₂ : ∀ p ∈ π₁.dirDurations,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam₂) p.1 := by
      rw [hdir]
      exact fun _ hp ↦ π₂.isMinimalCosetRep_of_mem_dirDurations hp
    obtain ⟨hL₂, hLmin₂⟩ := linked_raiseList hlam₂ hl₂ hlmin₂ i hj₀k₁ hk₁ θ
      (fun k hk hkj hkk₁ ↦ hcoroot _ ▸ hneg k hk hkj hkk₁)
      (fun k hk hkj hkk₁ ↦ hcoroot _ ▸ hint k hk hkj hkk₁)
      (fun hk ↦ hcoroot _ ▸ hright hk)
      (hcoroot _ ▸ hcut)
    have hnonneg : ∀ p ∈ raiseList b i π₁.dirDurations j₀ k₁
        (π₁.dirDurations[j₀]'hj₀).1 (π₁.dirDurations[j₀]'hj₀).2 θ, 0 ≤ p.2 :=
      fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π₁.pos_of_mem_dirDurations hp).le)
        (π₁.pos_of_mem_dirDurations (List.getElem_mem hj₀)).le hθ₀ hθ₁ hp
    have hsum : ((raiseList b i π₁.dirDurations j₀ k₁
        (π₁.dirDurations[j₀]'hj₀).1 (π₁.dirDurations[j₀]'hj₀).2 θ).map Prod.snd).sum = 1 := by
      rw [sum_map_snd_raiseList i hj₀k₁ hk₁, sum_map_snd_dirDurations]
    refine ⟨ofLinked _ hLmin₁ hnonneg hsum hL₁,
      ofLinked _ hLmin₂ hnonneg hsum hL₂,
      dirDurations_ofLinked_eq _ hLmin₁ hLmin₂ hnonneg hsum hL₁ hL₂, ?_, ?_⟩
    · rw [toPLPath_ofLinked]
      exact raise_toPLPath_eq_ofSegments_raiseList π₁ π₁ i rfl (fun _ ↦ rfl) hz₀ hj₀k₁ hk₁
        hgtk₁ habove hfall hcross hHk₀₁ f₁ F₁ hF₁
    · rw [toPLPath_ofLinked]
      exact raise_toPLPath_eq_ofSegments_raiseList π₁ π₂ i hdir.symm (fun w ↦ (hcoroot w).symm)
        hz₀ hj₀k₁ hk₁ hgtk₁ habove hfall hcross hHk₀₁ f₂ F₂ hF₂
  · -- When `z > -1`, the minimum height exceeds `-1` in both realizations, so `raise` is `none`.
    left
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
theorem raise_toPLPath_eq_none_or_exists_eq_some_and_eq_some
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
  rcases raise_toPLPath_eq_none_or_exists_dirDurations_eq_of_dirDurations_eq π π hlam hlam i rfl
    (fun _ ↦ rfl) f₁ F₁ hF₁ f₂ F₂ hF₂ with hnone | ⟨π₁', π₂', hdir', h₁, h₂⟩
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
  rcases π.raise_toPLPath_eq_none_or_exists_eq_some_and_eq_some hlam i f F hF f F hF with
    ⟨hnone, -⟩ | ⟨π', hsome, -⟩
  · rw [hnone] at hq
    cases hq
  · exact ⟨π', Option.some.inj (hsome.symm.trans hq)⟩

end TauCeti.LSPath
