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
import TauCeti.Algebra.CharZero.RatCast
import TauCeti.Algebra.Order.Ring.Int.Cast

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
  have hA : (l.take k₀).length = k₀ := List.length_take_of_le (hk₀j₁.trans hj₁.le)
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
  have hDp_len : Dp.length = l.length + 1 := by simp [hDp]; omega
  have hDp_lt (k : ℕ) (hk : k < Dp.length) (hkj : k < j₁) : Dp[k] = l[k]'(by omega) := by
    simp [hDp, List.getElem_append_left, List.length_take_of_le hj₁.le, hkj]
  have hDp_j₁ (h : j₁ < Dp.length) : Dp[j₁] = (τ, θ * d) := by
    simp [hDp, List.length_take_of_le hj₁.le]
  have hDp_j₁1 (h : j₁ + 1 < Dp.length) : Dp[j₁ + 1] = (τ, (1 - θ) * d) := by
    simp [hDp, List.length_take_of_le hj₁.le]
  have hDp_fst (k : ℕ) (hk : k < Dp.length) (hkj : k ≤ j₁) :
      Dp[k].1 = (l[k]'(by omega)).1 := by
    rcases hkj.lt_or_eq with hkj | rfl
    · rw [hDp_lt k hk hkj]
    · rw [hDp_j₁ hk, hτd]
  have hcum_le (k : ℕ) (hk : k ≤ j₁) :
      ((Dp.take k).map Prod.snd).sum = ((l.take k).map Prod.snd).sum := by
    rw [hDp, List.take_append_of_le_length (hk.trans_eq (List.length_take_of_le hj₁.le).symm),
      List.take_take, min_eq_left hk]
  have hcum_j₁1 : ((Dp.take (j₁ + 1)).map Prod.snd).sum =
      ((l.take j₁).map Prod.snd).sum + θ * d := by
    simpa [show j₁ < Dp.length by omega, hDp_j₁ (by omega)] using
      congrArg (· + θ * d) (hcum_le j₁ le_rfl)
  obtain ⟨hDp_linked, hDpmin⟩ := Linked.subdivide hl hlmin hj₁ hτd θ
  rw [← hDp] at hDp_linked hDpmin
  -- Reflect the window `[k₀, j₁]` of the subdivided list in `sᵢ`.
  have hW := Linked.mapIdx_simple_mul hlam hDp_linked hDpmin i (k₀ := k₀) (j₁ := j₁)
    (by omega)
    (fun k hk hk₀ hkj ↦ by
      rw [hDp_fst k hk hkj]
      exact hpos k (by omega) hk₀ hkj)
    (fun k hk hk₀ hkj ↦ by
      rw [zero_add, hcum_le k hkj, hDp_fst k hk hkj]
      exact hint k (by omega) hk₀ hkj)
    (fun k hk hkk ↦ by
      rw [hDp_lt k (by omega) (by omega)]
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
    rw [hDp_fst k hk' hw.2]
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

/-! ### Heights along a rising window

For a list `D` and weights `f`, `g` of its entries, write `hₖ = ∑_{j<k} f(Dⱼ) g(Dⱼ)` for the
heights and `aₖ = ∑_{j<k} f(Dⱼ)` for the breaks. For the list of directions and durations of an LS
path, `f` is the duration and `g` the height `⟨τ λ, αᵢ^∨⟩` of the direction. -/

/-- Where the heights rise strictly at an entry `k` with `0 ≤ f(Dₖ)`, the weight `g(Dₖ)` is
positive. -/
private theorem pos_of_sum_map_mul_take_lt_sum_map_mul_take_succ {α R : Type*} [Semiring R]
    [LinearOrder R] [IsStrictOrderedRing R] (f g : α → R) (D : List α) {k : ℕ}
    (hk : k < D.length) (hd : 0 ≤ f D[k])
    (h : ((D.take k).map fun a ↦ f a * g a).sum < ((D.take (k + 1)).map fun a ↦ f a * g a).sum) :
    0 < g D[k] := by
  exact pos_of_mul_pos_right (by simpa [hk] using h) hd

/-- Where the heights do not rise at an entry `k` with `0 < f(Dₖ)`, the weight `g(Dₖ)` is
nonpositive. -/
private theorem nonpos_of_sum_map_mul_take_succ_le_sum_map_mul_take {α R : Type*} [Semiring R]
    [LinearOrder R] [IsStrictOrderedRing R] (f g : α → R) (D : List α) {k : ℕ}
    (hk : k < D.length) (hd : 0 < f D[k])
    (h : ((D.take (k + 1)).map fun a ↦ f a * g a).sum ≤ ((D.take k).map fun a ↦ f a * g a).sum) :
    g D[k] ≤ 0 := by
  exact nonpos_of_mul_nonpos_right (by simpa [hk] using h) hd

/-- **Non-integrality inside a rising window.** If the heights rise strictly on the window
`[k₀, j₁]`, are at least the integer `z` at `k₀` and below `z + 1` at `j₁`, and `hₖ` is congruent
to `aₖ g(Dₖ)` modulo integers, then `aₖ g(Dₖ)` is not an integer for `k₀ < k ≤ j₁`. -/
private theorem not_exists_sum_map_take_mul_eq_intCast {α K : Type*} [Ring K] [PartialOrder K]
    [IsStrictOrderedRing K] (f g : α → K) (D : List α) {k₀ j₁ k : ℕ} (hk : k < D.length)
    {z : ℤ} (hk₀ : (z : K) ≤ ((D.take k₀).map fun a ↦ f a * g a).sum)
    (hrise : ∀ m, k₀ ≤ m → m < j₁ →
      ((D.take m).map fun a ↦ f a * g a).sum < ((D.take (m + 1)).map fun a ↦ f a * g a).sum)
    (hj₁ : ((D.take j₁).map fun a ↦ f a * g a).sum < z + 1)
    (hcong : ∃ m : ℤ,
      ((D.take k).map fun a ↦ f a * g a).sum - ((D.take k).map f).sum * g D[k] = m)
    (hk₀k : k₀ < k) (hkj : k ≤ j₁) :
    ¬∃ m : ℤ, ((D.take k).map f).sum * g D[k] = m := by
  have hsm : StrictMonoOn (fun m ↦ ((D.take m).map fun a ↦ f a * g a).sum) (Set.Icc k₀ j₁) :=
    strictMonoOn_of_lt_add_one Set.ordConnected_Icc fun m _ hm hm' ↦
      hrise m hm.1 (by simp only [Set.mem_Icc] at hm'; omega)
  exact TauCeti.not_exists_eq_intCast_of_lt_of_lt_add_one hcong
    (hk₀.trans_lt (hsm ⟨le_rfl, by omega⟩ ⟨hk₀k.le, hkj⟩ hk₀k))
    ((hsm.monotoneOn ⟨hk₀k.le, hkj⟩ ⟨by omega, le_rfl⟩ hkj).trans_lt hj₁)

/-- **Integrality at the cut.** If `h - a w` is an integer and `θ (d w) = z - h` for an integer `z`,
then `(a + θ d) w` is an integer. -/
private theorem exists_add_mul_eq_intCast {R : Type*} [Ring R] {h a d w θ : R} {z : ℤ}
    (hcong : ∃ m : ℤ, h - a * w = m) (hθd : θ * (d * w) = z - h) :
    ∃ m : ℤ, (a + θ * d) * w = m := by
  obtain ⟨m, hm⟩ := hcong
  refine ⟨z - m, ?_⟩
  push_cast
  rw [← hm, add_mul, mul_assoc, hθd]
  abel

omit [P.flip.IsReduced] in
/-- **The window of a lowering step, from its heights.** Let `D` be a linked list of directions and
positive durations starting at time `0`, whose heights `hₖ = ∑_{j<k} dⱼ ⟨τⱼ λ, αᵢ^∨⟩` are at least
the integer `z = h_{k₀}`, rise strictly on the window `[k₀, j₁]`, and reach `z + 1` at the fraction
`θ > 0` of the entry `j₁`. Then the window satisfies the hypotheses of
`TauCeti.LSPath.linked_lowerList`: the heights `⟨τ λ, αᵢ^∨⟩` of its directions are positive,
`a ⟨τ λ, αᵢ^∨⟩` is not an integer at its internal breaks `a`, the direction entering it has
nonpositive height, and the cut is at a time `a` with `a ⟨τ λ, αᵢ^∨⟩` an integer. -/
private theorem lowerList_window_of_heights (hlam : lam ∈ dominantChamber P b)
    {D : List (P.weylGroup × ℚ)} (hD : Linked P b lam 0 D) (hdpos : ∀ p ∈ D, 0 < p.2)
    (i : b.support) {k₀ j₁ : ℕ} (hj₁ : j₁ < D.length) (hk₀j₁ : k₀ ≤ j₁) {z : ℤ} {θ : ℚ}
    (hθ : 0 < θ)
    (hmin : ∀ k, (z : ℚ) ≤ ((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hk₀ : ((D.take k₀).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum = z)
    (hrise : ∀ k, k₀ ≤ k → k ≤ j₁ →
      ((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum <
        ((D.take (k + 1)).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (hθd : θ * (D[j₁].2 * P.coroot' i (D[j₁].1 • lam)) =
      z + 1 - ((D.take j₁).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum) :
    (∀ k (hk : k < D.length), k₀ ≤ k → k ≤ j₁ → 0 < P.coroot' i (D[k].1 • lam)) ∧
      (∀ k (hk : k < D.length), k₀ < k → k ≤ j₁ →
        ¬∃ m : ℤ, ((D.take k).map Prod.snd).sum * P.coroot' i (D[k].1 • lam) = m) ∧
      (∀ k (hk : k < D.length), k + 1 = k₀ → P.coroot' i (D[k].1 • lam) ≤ 0) ∧
      ∃ m : ℤ,
        (((D.take j₁).map Prod.snd).sum + θ * D[j₁].2) * P.coroot' i (D[j₁].1 • lam) = m := by
  have hpos (k : ℕ) (hk : k < D.length) (hk₀k : k₀ ≤ k) (hkj : k ≤ j₁) :
      (0 : ℚ) < P.coroot' i (D[k].1 • lam) :=
    pos_of_sum_map_mul_take_lt_sum_map_mul_take_succ Prod.snd
      (fun p ↦ (P.coroot' i (p.1 • lam) : ℚ)) D hk (hdpos _ (List.getElem_mem hk)).le
      (hrise k hk₀k hkj)
  have hcong (k : ℕ) (hk : k < D.length) :=
    hD.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
  have hj₁z : ((D.take j₁).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum < z + 1 := by
    have : 0 < θ * (D[j₁].2 * P.coroot' i (D[j₁].1 • lam)) :=
      mul_pos hθ (mul_pos (hdpos _ (List.getElem_mem hj₁)) (hpos j₁ hj₁ hk₀j₁ le_rfl))
    linarith
  refine ⟨fun k hk hk₀k hkj ↦ by exact_mod_cast hpos k hk hk₀k hkj,
    fun k hk hk₀k hkj ↦ not_exists_sum_map_take_mul_eq_intCast Prod.snd
      (fun p ↦ (P.coroot' i (p.1 • lam) : ℚ)) D hk hk₀.ge (fun m hm hmj ↦ hrise m hm hmj.le) hj₁z
      (hcong k hk) hk₀k hkj,
    fun k hk hkk ↦ ?_,
    exists_add_mul_eq_intCast (z := z + 1) (hcong j₁ hj₁) (by push_cast; exact hθd)⟩
  have := nonpos_of_sum_map_mul_take_succ_le_sum_map_mul_take Prod.snd
    (fun p ↦ (P.coroot' i (p.1 • lam) : ℚ)) D hk (hdpos _ (List.getElem_mem hk))
    (by rw [hkk, hk₀]; exact hmin k)
  exact_mod_cast this

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
  set D := π.dirDurations
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)
  set hgt : ℕ → ℚ := fun k ↦
    ((D.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum with hhgt
  set j₁ : ℕ := (j₁' : ℕ) with hj₁
  have hj₁lt : j₁ < D.length := by rw [length_dirDurations]; exact j₁'.2
  set τ := (π.dir j₁').1 with hτ
  set d := π.duration j₁' with hd
  have hDj₁ : D[j₁] = (τ, d) := by rw [getElem_dirDurations]
  -- Heights of the realization at the vertices are the rational heights of the encoding.
  have hHF : ∀ k, F ((D.map seg).take k).sum = (hgt k : 𝕜) := fun k ↦
    apply_sum_take_map_segments f i F hF D k
  have hgtk₀ : hgt k₀ = z := by
    rw [hHF, hz] at hmin
    exact_mod_cast hmin
  have hrise' : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1) := fun k hk₀ hkj ↦ by
    have := hrise k hk₀ hkj
    rwa [hHF, hHF, Rat.cast_lt] at this
  -- The height rises along the entry `j₁`, so its segment has positive height.
  have hdH : 0 < d * (P.coroot' i (τ • lam) : ℚ) := by
    have := hrise' j₁ hk₀j₁ le_rfl
    simpa [hhgt, hj₁lt, hDj₁] using this
  set θ : ℚ := (z + 1 - hgt j₁) / (d * P.coroot' i (τ • lam)) with hθ
  have hθ' : θ' = θ := by
    have hc := hcross
    rw [hHF, hz, show F ((d : 𝕜) • f (τ • lam)) = ((d * P.coroot' i (τ • lam) : ℚ) : 𝕜) by
      simp [hF]] at hc
    exact eq_ratCast_div_of_add_mul_eq (r := (z : ℚ) + 1) hdH.ne' (by exact_mod_cast hc)
  rw [hθ'] at hθpos' hθle' hlow
  have hθpos : 0 < θ := by exact_mod_cast hθpos'
  -- The height is at least its minimum `z` at every vertex.
  have hzle : ∀ k, (z : ℚ) ≤ hgt k := fun k ↦ by
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F) (D.map seg) k
    rw [← hminH, hz, hHF] at hle
    exact_mod_cast hle
  have hθd : θ * (D[j₁].2 * (P.coroot' i (D[j₁].1 • lam) : ℚ)) = z + 1 - hgt j₁ := by
    rw [hDj₁]; exact div_mul_cancel₀ _ hdH.ne'
  obtain ⟨hpos, hint, hleft, hcut⟩ := lowerList_window_of_heights hlam π.linked_dirDurations
    (fun _ hp ↦ π.pos_of_mem_dirDurations hp) i hj₁lt hk₀j₁ hθpos hzle hgtk₀ hrise' hθd
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
