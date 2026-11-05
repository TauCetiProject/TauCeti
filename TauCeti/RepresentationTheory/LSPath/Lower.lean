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
  set τ := l[j₁].1 with hτ
  set d := l[j₁].2 with hd
  set s := (weylCoxeterSystem P b).simple i with hs
  have hτmin : (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) τ :=
    hlmin _ (List.getElem_mem hj₁)
  -- Subdivide the entry `j₁` at the fraction `θ`; the list stays linked.
  set Dp : List (P.weylGroup × ℚ) :=
    l.take j₁ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₁ + 1) with hDp
  have hDp_linked : Linked P b lam 0 Dp := by
    have hsplit : l = l.take j₁ ++ (τ, θ * d + (1 - θ) * d) :: l.drop (j₁ + 1) := by
      rw [show θ * d + (1 - θ) * d = d by ring, ← List.drop_eq_getElem_cons hj₁,
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
  -- The entries and break times of the subdivided list up to the cut.
  have hlen_take : (l.take j₁).length = j₁ := by simp; omega
  have hDp_len : Dp.length = l.length + 1 := by simp [Dp]; omega
  have hDp_lt : ∀ k (hk : k < Dp.length) (hkj : k < j₁), Dp[k] = l[k]'(by omega) := by
    intro k hk hkj
    simp only [Dp]
    rw [List.getElem_append_left (by rw [hlen_take]; omega), List.getElem_take]
  have hDp_j₁ : Dp[j₁]'(by omega) = (τ, θ * d) := by
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  have hDp_j₁1 : Dp[j₁ + 1]'(by omega) = (τ, (1 - θ) * d) := by
    simp only [Dp]
    rw [List.getElem_append_right (by omega)]
    simp [hlen_take]
  have hDp_fst : ∀ k (hk : k < Dp.length) (hkj : k ≤ j₁), Dp[k].1 = (l[k]'(by omega)).1 := by
    intro k hk hkj
    rcases hkj.lt_or_eq with hkj | rfl
    · rw [hDp_lt k hk hkj]
    · rw [hDp_j₁]
  have hcum_le : ∀ k ≤ j₁, ((Dp.take k).map Prod.snd).sum = ((l.take k).map Prod.snd).sum := by
    intro k hk
    simp only [Dp]
    rw [List.take_append_of_le_length (by omega), List.take_take, min_eq_left hk]
  have hcum_j₁1 : ((Dp.take (j₁ + 1)).map Prod.snd).sum =
      ((l.take j₁).map Prod.snd).sum + θ * d := by
    simp only [Dp]
    rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₁ + 1 - j₁ = 1 by omega]
    simp
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
    (by rw [hDp_j₁1, hDp_j₁])
    (by
      rw [zero_add, hcum_j₁1, hDp_j₁]
      exact hcut)
  -- The reflected subdivided list is the lowered list.
  have hlow : lowerList b i l k₀ j₁ τ d θ =
      Dp.mapIdx fun k p ↦ if k₀ ≤ k ∧ k ≤ j₁ then (s * p.1, p.2) else p := by
    have hDp' : Dp = l.take k₀ ++ ((l.take j₁).drop k₀ ++ [(τ, θ * d)]) ++
        (τ, (1 - θ) * d) :: l.drop (j₁ + 1) := by
      rw [hDp]
      conv_lhs => rw [← List.take_append_drop k₀ (l.take j₁), List.take_take,
        min_eq_left hk₀j₁]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hA : (l.take k₀).length = k₀ := by simp; omega
    have hB : ((l.take j₁).drop k₀ ++ [(τ, θ * d)]).length = j₁ - k₀ + 1 := by simp; omega
    rw [hDp']
    refine List.ext_getElem (by simp [lowerList]) fun k hk₁ hk₂ ↦ ?_
    simp only [lowerList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
      List.length_append, List.length_map, hA, hB]
    split_ifs <;> first | rfl | omega
  rw [hlow]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]
  split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst k hk' hw.2]
    exact (hpos k (by omega) hw.1 hw.2).ne'
  · exact hDpmin _ (List.getElem_mem hk')

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
  set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ) with hH
  set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum with hhgt
  set cum : ℕ → ℚ := fun k ↦ ((D.take k).map Prod.snd).sum with hcum
  have hHdef : ∀ w, H w = (P.coroot' i (w • lam) : ℚ) := fun _ ↦ rfl
  set j₁ : ℕ := (j₁' : ℕ) with hj₁
  have hlen : D.length = π.length + 1 := length_dirDurations π
  have hj₁lt : j₁ < D.length := by rw [hlen]; exact j₁'.2
  set τ := (π.dir j₁').1 with hτ
  set d := π.duration j₁' with hd
  have hDj₁ : D[j₁] = (τ, d) := by rw [getElem_dirDurations]
  have hdpos : ∀ k (hk : k < D.length), 0 < D[k].2 := fun k hk ↦ by
    rw [getElem_dirDurations]; exact π.duration_pos _
  -- Heights of the realization at the vertices are the rational heights of the encoding.
  have hHF : ∀ k, F ((D.map seg).take k).sum = (hgt k : 𝕜) := by
    intro k
    simp only [hgt, ← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
    congr 1
    refine List.map_congr_left fun p _ ↦ ?_
    simp [seg, H, hF]
  have hgt_succ : ∀ k (hk : k < D.length), hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
    intro k hk
    simp only [hgt, List.map_take]
    rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
  have hFseg : F ((d : 𝕜) • f (τ • lam)) = ((d * H τ : ℚ) : 𝕜) := by simp [H, hF]
  /- The rational heights: `hgt k₀ = z` is the minimum, the height rises strictly from `k₀` to past
  `j₁`, and the piece reaches `z + 1` at the fraction `θ` of the segment `j₁`. -/
  have hgtk₀ : hgt k₀ = z := by
    rw [hHF, hz] at hmin
    exact_mod_cast hmin
  have hrise' : ∀ k, k₀ ≤ k → k ≤ j₁ → hgt k < hgt (k + 1) := fun k hk₀ hkj ↦ by
    have := hrise k hk₀ hkj
    rwa [hHF, hHF, Rat.cast_lt] at this
  have hposH : ∀ k (hk : k < D.length), k₀ ≤ k → k ≤ j₁ → 0 < H D[k].1 := fun k hk hk₀ hkj ↦ by
    have := hrise' k hk₀ hkj
    rw [hgt_succ k hk] at this
    exact pos_of_mul_pos_right (by linarith) (hdpos k hk).le
  have hdH : 0 < d * H τ := by
    have := hposH j₁ hj₁lt hk₀j₁ le_rfl
    rw [hDj₁] at this
    exact mul_pos (by rw [hd]; exact π.duration_pos _) this
  set θ : ℚ := (z + 1 - hgt j₁) / (d * H τ) with hθ
  have hθd : θ * (d * H τ) = z + 1 - hgt j₁ := div_mul_cancel₀ _ hdH.ne'
  have hθ' : θ' = θ := by
    have hc := hcross
    rw [hHF, hz, hFseg] at hc
    have hc' : θ' * ((d * H τ : ℚ) : 𝕜) = ((z + 1 - hgt j₁ : ℚ) : 𝕜) := by
      push_cast at hc ⊢
      linear_combination hc
    rw [hθ, Rat.cast_div, eq_div_iff (by exact_mod_cast hdH.ne'), hc']
  rw [hθ'] at hθpos' hθle' hlow
  have hθpos : 0 < θ := by exact_mod_cast hθpos'
  have hθle : θ ≤ 1 := by exact_mod_cast hθle'
  -- The heights strictly between `k₀` and `j₁` lie strictly between `z` and `z + 1`.
  have hmono : ∀ m k, k₀ ≤ k → k + m ≤ j₁ + 1 → hgt k ≤ hgt (k + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro k hk hkm
      exact (ih k hk (by omega)).trans (hrise' (k + m) (by omega) (by omega)).le
  have hbetween : ∀ k, k₀ < k → k ≤ j₁ → (z : ℚ) < hgt k ∧ hgt k < z + 1 := by
    intro k hk₀ hkj
    refine ⟨?_, ?_⟩
    · have h₁ := hrise' k₀ le_rfl (by omega)
      have h₂ := hmono (k - (k₀ + 1)) (k₀ + 1) (by omega) (by omega)
      rw [show k₀ + 1 + (k - (k₀ + 1)) = k by omega] at h₂
      linarith
    · have h₂ := hmono (j₁ - k) k (by omega) (by omega)
      rw [show k + (j₁ - k) = j₁ by omega] at h₂
      nlinarith
  -- At the vertex `k₀` the height is minimal, so the segment before it does not rise.
  have hleftH : ∀ k (hk : k < D.length), k + 1 = k₀ → H D[k].1 ≤ 0 := fun k hk hkk ↦ by
    have hle := PLPath.listMinHeight_le_apply_sum_take (f := F) (D.map seg) k
    rw [← hminH, hz, hHF] at hle
    have hle' : (z : ℚ) ≤ hgt k := by exact_mod_cast hle
    have := hgt_succ k hk
    rw [hkk, hgtk₀] at this
    exact nonpos_of_mul_nonpos_right (by linarith) (hdpos k hk)
  -- Heights at breaks are congruent to `a_k ⟨τ_k λ, αᵢ^∨⟩` modulo integers.
  have hcong : ∀ k (hk : k < D.length), ∃ m : ℤ, hgt k - cum k * H D[k].1 = m := fun k hk ↦
    π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
  refine ⟨k₀, j₁, hj₁lt, θ, hk₀j₁, hθpos.le, hθle, fun k hk hk₀ hkj ↦ ?_, fun k hk hk₀ hkj ↦ ?_,
    fun k hk hkk ↦ ?_, ?_, ?_⟩
  · have := hposH k hk hk₀ hkj
    rw [hHdef] at this
    exact_mod_cast this
  · -- The height at the break is strictly between the integers `z` and `z + 1`.
    rintro ⟨m, hm⟩
    obtain ⟨m', hm'⟩ := hcong k hk
    obtain ⟨h₁, h₂⟩ := hbetween k hk₀ hkj
    have hk' : hgt k = ((m' + m : ℤ) : ℚ) := by
      simp only [H] at hm'
      push_cast
      linarith
    rw [hk'] at h₁ h₂
    have h₁' : z < m' + m := by exact_mod_cast h₁
    have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
    omega
  · have := hleftH k hk hkk
    rw [hHdef] at this
    exact_mod_cast this
  · -- The height at the cut is the integer `z + 1`.
    obtain ⟨m, hm⟩ := hcong j₁ hj₁lt
    refine ⟨z + 1 - m, ?_⟩
    rw [hDj₁] at hm ⊢
    simp only [H] at hm hθd
    push_cast
    linear_combination hθd - hm
  · rw [hlow, hDj₁]
    congr 2
    have hσ : ∀ p : P.weylGroup × ℚ,
        (p.2 : 𝕜) • f (((weylCoxeterSystem P b).simple i * p.1) • lam) =
          Module.preReflection (f (P.root i)) F ((p.2 : 𝕜) • f (p.1 • lam)) := fun p ↦
      (preReflection_smul_apply f i F hF _ _).symm
    simp only [lowerList, hseg, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.map_take, List.map_drop, Function.comp_def, hσ, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_one]
    rw [preReflection_smul_apply f i F hF]

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
