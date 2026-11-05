/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
import TauCeti.RepresentationTheory.LSPath.Concatenation

/-!
# Littelmann's lowering operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root. Littelmann's
lowering operator `f_{αᵢ}` acts on the realization of `π` by reflecting, in `sᵢ`, the piece of the
path between the last time `t₀` at which the height `⟨π(t), αᵢ^∨⟩` is minimal and the first later
time `t₁` at which it has risen by one (`TauCeti.LSPath.exists_lower_toPLPath_eq`). This file
proves that the result is again an LS path of shape `λ`: its directions are those of `π`, with the
directions `τ` of the reflected piece replaced by `sᵢ τ`, and its breaks are those of `π` and
`t₁`, except that `t₀` is dropped when `sᵢ τ` agrees with the direction before `t₀`.

The chain conditions of the new path are Littelmann's. The height does not increase just before
`t₀` and increases after it, so the chain from the direction before `t₀` can be continued to the
reflected direction after it (`TauCeti.IsAChain.exists_isAChain_simple_mul_last`). Strictly
between `t₀` and `t₁` the height at a break `a` is not an integer, so every chain at `a` lies on
the positive side of the wall of `αᵢ` and reflects in `sᵢ`. At `t₁` the height is an integer, so
`sᵢ τ ⋗ τ` is a `t₁`-chain.

To assemble the new path, it is convenient to allow **break data** more general than LS paths: a
sequence of directions `τ_k` and weakly increasing times `t_k` from `0` to `1`, where consecutive
directions may agree and segments may be stationary, subject to the chain conditions at every
break. Removing the stationary segments and merging the segments with repeated directions turns
break data into an LS path presenting the same piecewise-linear path
(`TauCeti.LSPath.exists_toPLPath_eq_ofSegments`).

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_ofSegments`: **break data present an LS path.**
* `TauCeti.LSPath.toPLPath_eq_ofSegments_natDir`: the realization of an LS path is presented by
  its break data `TauCeti.LSPath.natDir` and `TauCeti.LSPath.natTime`.
* `TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`: **Littelmann's lowering operator
  `f_{αᵢ}` sends an LS path of dominant shape `λ` to an LS path of shape `λ`** whenever it is
  defined.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### Break data with repeated directions and stationary pieces -/

/-- Splitting `range (k + 1 + n)` at `k`. -/
private theorem map_range_add_one_add {α : Type*} (g : ℕ → α) (k n : ℕ) :
    (List.range (k + 1 + n)).map g =
      (List.range k).map g ++ g k :: (List.range n).map fun m ↦ g (k + 1 + m) := by
  rw [List.range_add, List.range_succ, List.map_append, List.map_append, List.map_map]
  simp [Function.comp_def]

/-- Removing a stationary segment `g k = 0` from a segment list indexed by `range (s + 1)`. -/
private theorem ofSegments_map_range_of_eq_zero {g g' : ℕ → V} {s k : ℕ} (hk : k < s + 1)
    (hg : g k = 0) (hlt : ∀ n < k, g' n = g n) (hge : ∀ n, k ≤ n → g' n = g (n + 1)) :
    PLPath.ofSegments 𝕜 ((List.range (s + 1)).map g) =
      PLPath.ofSegments 𝕜 ((List.range s).map g') := by
  obtain ⟨n, rfl⟩ : ∃ n, s = k + n := ⟨s - k, by omega⟩
  rw [show k + n + 1 = k + 1 + n by omega, map_range_add_one_add, List.range_add,
    List.map_append, PLPath.ofSegments_append, PLPath.ofSegments_append,
    PLPath.ofSegments_cons, hg, PLPath.straight_zero, one_mul, List.map_map]
  congr 2
  · exact List.map_congr_left fun m hm ↦ (hlt m (List.mem_range.mp hm)).symm
  · refine List.map_congr_left fun m _ ↦ ?_
    simp only [Function.comp_apply, hge (k + m) (by omega)]
    congr 1
    omega

/-- Merging two adjacent segments `g k = a • u` and `g (k + 1) = c • u` along a common ray in a
segment list indexed by `range (s + 1)`. -/
private theorem ofSegments_map_range_of_smul {g g' : ℕ → V} {s k : ℕ} (hk : k + 1 < s + 1)
    {a c : 𝕜} {u : V} (ha : 0 ≤ a) (hc : 0 ≤ c) (hg₀ : g k = a • u) (hg₁ : g (k + 1) = c • u)
    (hg' : g' k = (a + c) • u) (hlt : ∀ n < k, g' n = g n)
    (hgt : ∀ n, k < n → g' n = g (n + 1)) :
    PLPath.ofSegments 𝕜 ((List.range (s + 1)).map g) =
      PLPath.ofSegments 𝕜 ((List.range s).map g') := by
  obtain ⟨n, rfl⟩ : ∃ n, s = k + 1 + n := ⟨s - k - 1, by omega⟩
  rw [show k + 1 + n + 1 = k + 1 + (0 + 1 + n) by omega, map_range_add_one_add,
    map_range_add_one_add (fun m ↦ g (k + 1 + m)) 0 n, map_range_add_one_add g' k n]
  simp only [List.range_zero, List.map_nil, List.nil_append, add_zero]
  rw [PLPath.ofSegments_append, PLPath.ofSegments_append, hg₀, hg₁,
    PLPath.ofSegments_smul_cons_smul_cons ha hc, hg']
  congr 2
  · exact List.map_congr_left fun m hm ↦ (hlt m (List.mem_range.mp hm)).symm
  · refine congrArg _ (List.map_congr_left fun m _ ↦ ?_)
    rw [hgt _ (by omega)]
    congr 1
    omega

variable (b) in
/-- Break data `(τ; t)` with `s` segments: the segment `k` runs along the orbit weight `τ k • λ`
from time `t k` to time `t (k + 1)`. Consecutive directions may agree and segments may be
stationary; the chain conditions are those of an LS path. -/
private structure IsBreakData (lam : M) (s : ℕ) (τ : ℕ → P.weylGroup) (t : ℕ → ℚ) : Prop where
  isMinimalCosetRep :
    ∀ k < s, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ k)
  time_zero : t 0 = 0
  time_last : t s = 1
  monotone : ∀ k < s, t k ≤ t (k + 1)
  chain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
    (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C

/-- Removing a stationary segment `k` from break data. -/
private theorem IsBreakData.removeAt {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ}
    (h : IsBreakData b lam (s + 1) τ t) {k : ℕ} (hk : k < s + 1) (hkt : t k = t (k + 1)) :
    IsBreakData b lam s (fun n ↦ if n < k then τ n else τ (n + 1))
      (fun n ↦ if n ≤ k then t n else t (n + 1)) where
  isMinimalCosetRep n hn := by
    split_ifs
    · exact h.isMinimalCosetRep n (by omega)
    · exact h.isMinimalCosetRep (n + 1) (by omega)
  time_zero := by simpa using h.time_zero
  time_last := by
    split_ifs with hs
    · obtain rfl : k = s := by omega
      rw [hkt, h.time_last]
    · exact h.time_last
  monotone n hn := by
    split_ifs with h₁ h₂ h₂
    · exact h.monotone n (by omega)
    · obtain rfl : n = k := by omega
      rw [hkt]
      exact h.monotone (n + 1) (by omega)
    · omega
    · exact h.monotone (n + 1) (by omega)
  chain n hn := by
    rcases lt_trichotomy (n + 1) k with hlt | heq | hgt
    · simpa only [show n < k by omega, hlt, hlt.le, ↓reduceIte] using h.chain n (by omega)
    · obtain ⟨C, hC₁, hC₂, hC⟩ := h.chain n (by omega)
      obtain ⟨D, hD₁, hD₂, hD⟩ := h.chain k (by omega)
      have hjoin : C.last = D.head := Subtype.ext (by rw [hC₂, hD₁, heq])
      refine ⟨C.smash D hjoin, ?_, ?_, (isAChain_smash_iff hjoin).mpr ⟨?_, ?_⟩⟩
      · simp [hC₁, show n < k by omega]
      · simp [hD₂, heq]
      · simpa only [heq.le, heq, le_refl, ↓reduceIte] using hC
      · simpa only [heq.le, heq, hkt, le_refl, ↓reduceIte] using hD
    · simpa only [show ¬n < k by omega, show ¬n + 1 < k by omega, show ¬n + 1 ≤ k by omega,
        ↓reduceIte] using h.chain (n + 1) (by omega)

/-- Merging the segments `k` and `k + 1` of break data with the same direction. -/
private theorem IsBreakData.mergeAt {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ}
    (h : IsBreakData b lam (s + 1) τ t) {k : ℕ} (hk : k + 1 < s + 1) (hkτ : τ k = τ (k + 1)) :
    IsBreakData b lam s (fun n ↦ if n ≤ k then τ n else τ (n + 1))
      (fun n ↦ if n ≤ k then t n else t (n + 1)) where
  isMinimalCosetRep n hn := by
    split_ifs
    · exact h.isMinimalCosetRep n (by omega)
    · exact h.isMinimalCosetRep (n + 1) (by omega)
  time_zero := by simpa using h.time_zero
  time_last := by
    simpa only [show ¬s ≤ k by omega, ↓reduceIte] using h.time_last
  monotone n hn := by
    split_ifs with h₁ h₂ h₂
    · exact h.monotone n (by omega)
    · obtain rfl : n = k := by omega
      exact (h.monotone n (by omega)).trans (h.monotone (n + 1) (by omega))
    · omega
    · exact h.monotone (n + 1) (by omega)
  chain n hn := by
    rcases lt_or_ge n k with hlt | hge
    · simpa only [hlt.le, show n + 1 ≤ k by omega, ↓reduceIte] using h.chain n (by omega)
    · rcases hge.eq_or_lt with rfl | hgt
      · simpa only [le_refl, show ¬k + 1 ≤ k by omega, ↓reduceIte, hkτ] using
          h.chain (k + 1) (by omega)
      · simpa only [show ¬n ≤ k by omega, show ¬n + 1 ≤ k by omega, ↓reduceIte] using
          h.chain (n + 1) (by omega)

/-- Break data with positive durations and no repeated direction is an LS path. -/
private theorem IsBreakData.exists_of_lt_of_ne {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ}
    (h : IsBreakData b lam (s + 1) τ t) (hpos : ∀ k < s + 1, t k < t (k + 1))
    (hne : ∀ k, k + 1 < s + 1 → τ k ≠ τ (k + 1)) :
    ∃ π : LSPath P b lam, ∀ f : M →+ V, π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((List.range (s + 1)).map fun k ↦ ((t (k + 1) - t k : ℚ) : 𝕜) • f (τ k • lam)) := by
  refine ⟨{
    length := s
    dir := fun j ↦ ⟨τ j, h.isMinimalCosetRep j j.2⟩
    time := fun j ↦ t j
    time_zero := by simpa using h.time_zero
    time_last := by simpa using h.time_last
    strictMono_time := Fin.strictMono_iff_lt_succ.mpr fun j ↦ by simpa using hpos j j.2
    dir_succ_ne := fun j he ↦ hne j (by omega) (by simpa using (congrArg Subtype.val he).symm)
    exists_isAChain := fun j ↦ by
      obtain ⟨C, h₁, h₂, hC⟩ := h.chain j (by omega)
      exact ⟨C, Subtype.ext (by simpa using h₁), Subtype.ext (by simpa using h₂),
        by simpa using hC⟩ }, fun f ↦ ?_⟩
  rw [toPLPath_def, timed_def, List.map_ofFn]
  congr 1
  refine List.ext_getElem (by simp) fun n h₁ h₂ ↦ ?_
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply,
    duration_def, Fin.val_succ, Fin.val_castSucc]

/-- Break data presents an LS path: remove the stationary segments and merge the segments with
repeated directions, one at a time. -/
private theorem IsBreakData.exists_toPLPath_eq {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ}
    (h : IsBreakData b lam s τ t) :
    ∃ π : LSPath P b lam, ∀ f : M →+ V, π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((List.range s).map fun k ↦ ((t (k + 1) - t k : ℚ) : 𝕜) • f (τ k • lam)) := by
  induction s generalizing τ t with
  | zero => exact absurd (h.time_zero.symm.trans h.time_last) zero_ne_one
  | succ s ih =>
    by_cases hz : ∃ k < s + 1, t k = t (k + 1)
    · obtain ⟨k, hk, hkt⟩ := hz
      obtain ⟨π, hπ⟩ := ih (h.removeAt hk hkt)
      refine ⟨π, fun f ↦ (hπ f).trans
        (ofSegments_map_range_of_eq_zero hk (by simp [hkt]) (fun n hn ↦ ?_) fun n hn ↦ ?_).symm⟩
      · simp [hn, hn.le, show n + 1 ≤ k by omega]
      · rcases hn.eq_or_lt with rfl | hn
        · simp [hkt]
        · simp [show ¬n < k by omega, show ¬n ≤ k by omega, show ¬n + 1 ≤ k by omega]
    by_cases hd : ∃ k, k + 1 < s + 1 ∧ τ k = τ (k + 1)
    · obtain ⟨k, hk, hkτ⟩ := hd
      obtain ⟨π, hπ⟩ := ih (h.mergeAt hk hkτ)
      refine ⟨π, fun f ↦ (hπ f).trans (ofSegments_map_range_of_smul hk
        (a := ((t (k + 1) - t k : ℚ) : 𝕜)) (c := ((t (k + 1 + 1) - t (k + 1) : ℚ) : 𝕜))
        (u := f (τ k • lam)) (Rat.cast_nonneg.mpr (sub_nonneg.mpr (h.monotone k (by omega))))
        (Rat.cast_nonneg.mpr (sub_nonneg.mpr (h.monotone (k + 1) hk))) rfl
        (by rw [hkτ]) ?_ (fun n hn ↦ ?_) fun n hn ↦ ?_).symm⟩
      · simp only [le_refl, show ¬k + 1 ≤ k by omega, ↓reduceIte]
        push_cast
        congr 1
        ring
      · simp [hn.le, show n + 1 ≤ k by omega]
      · simp [show ¬n ≤ k by omega, show ¬n + 1 ≤ k by omega]
    · push Not at hz hd
      exact h.exists_of_lt_of_ne (fun k hk ↦ lt_of_le_of_ne (h.monotone k hk) (hz k hk)) hd

/-- **Break data presents an LS path.** Let `τ₀, …, τ_{s-1}` be minimal coset representatives of
`W / W_λ` and `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_s = 1` rational times such that consecutive directions are
joined by a `t_{k+1}`-chain from `τ_k` down to `τ_{k+1}`. Consecutive directions may agree and
segments may be stationary. Then the segments `(t_{k+1} - t_k) τ_k λ` present an LS path of
shape `λ`, in every realization `f`. -/
theorem exists_toPLPath_eq_ofSegments {s : ℕ} {τ : ℕ → P.weylGroup} {t : ℕ → ℚ}
    (hτ : ∀ k < s, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (τ k))
    (ht₀ : t 0 = 0) (hts : t s = 1) (hmono : ∀ k < s, t k ≤ t (k + 1))
    (hchain : ∀ k, k + 1 < s → ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain
      (P.wallIndices b lam), C.head.1 = τ k ∧ C.last.1 = τ (k + 1) ∧ IsAChain (t (k + 1)) lam C) :
    ∃ π : LSPath P b lam, ∀ f : M →+ V, π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((List.range s).map fun k ↦ ((t (k + 1) - t k : ℚ) : 𝕜) • f (τ k • lam)) :=
  IsBreakData.exists_toPLPath_eq ⟨hτ, ht₀, hts, hmono, hchain⟩

/-! ### Lowering an LS path -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The segment list of Littelmann's lowering, as produced by
`TauCeti.PLPath.lower_ofSegments_eq_of_strictly_rising`, is again indexed by a range. -/
private theorem lowered_eq_map_range {g g' : ℕ → V} (r : V → V) {s k₀ k₁ : ℕ} (θ : 𝕜)
    (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ s) (h₁ : ∀ n < k₀, g' n = g n)
    (h₂ : ∀ n, k₀ ≤ n → n + 1 < k₁ → g' n = r (g n))
    (h₃ : g' (k₁ - 1) = r (θ • g (k₁ - 1))) (h₄ : g' k₁ = (1 - θ) • g (k₁ - 1))
    (h₅ : ∀ n, k₁ < n → g' n = g (n - 1)) (hL : k₁ - 1 < ((List.range s).map g).length) :
    ((List.range s).map g).take k₀ ++
        ((((List.range s).map g).take (k₁ - 1)).drop k₀ ++
          [θ • ((List.range s).map g)[k₁ - 1]]).map r ++
        (1 - θ) • ((List.range s).map g)[k₁ - 1] :: ((List.range s).map g).drop k₁ =
      (List.range (s + 1)).map g' := by
  refine List.ext_getElem (by simp; omega) fun n h h' ↦ ?_
  simp only [List.getElem_append, List.getElem_cons, List.getElem_map, List.getElem_take,
    List.getElem_drop, List.getElem_range, List.length_append, List.length_map, List.length_take,
    List.length_drop, List.length_range, List.length_cons, List.length_nil,
    min_eq_left (by omega : k₀ ≤ s), min_eq_left (by omega : k₁ - 1 ≤ s)]
  split_ifs
  · exact (h₁ n (by omega)).symm
  · rw [h₂ n (by omega) (by omega)]
    congr 2
    omega
  · rw [show n = k₁ - 1 by omega, h₃]
  · exfalso
    omega
  · rw [show n = k₁ by omega, h₄]
  · rw [h₅ n (by omega)]
    congr 1
    omega

/-- The realization of an LS path is presented by the segments `(a_{k+1} - a_k) τ_k λ`, read off
the sequences `TauCeti.LSPath.natTime` and `TauCeti.LSPath.natDir`. -/
theorem toPLPath_eq_ofSegments_natDir (π : LSPath P b lam) (f : M →+ V) :
    π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜 ((List.range (π.length + 1)).map fun k ↦
      ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam)) := by
  rw [toPLPath_def, timed_def, List.map_ofFn]
  congr 1
  refine List.ext_getElem (by simp) fun n h₁ h₂ ↦ ?_
  have hn : n < π.length + 1 := by simpa using h₁
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply,
    duration_def, π.natDir_of_le (by omega : n ≤ π.length),
    π.natTime_of_le (by omega : n + 1 ≤ π.length + 1),
    π.natTime_of_le (by omega : n ≤ π.length + 1), Fin.succ_mk, Fin.castSucc_mk]

omit [Finite ι] [P.IsReduced] in
/-- Vertex heights of a segment list indexed by a range. -/
private theorem apply_sum_take_map_range (f : M →+ V) (F : Module.Dual 𝕜 V)
    (g : Module.Dual ℤ M) (hF : ∀ m, F (f m) = (g m : 𝕜)) (s : ℕ) (τ : ℕ → P.weylGroup)
    (t : ℕ → ℚ) (j : ℕ) :
    F ((((List.range s).map fun k ↦ ((t (k + 1) - t k : ℚ) : 𝕜) • f (τ k • lam)).take j).sum) =
      ((∑ k ∈ Finset.range (min j s), (t (k + 1) - t k) * g (τ k • lam) : ℚ) : 𝕜) := by
  rw [← List.map_take, List.take_range]
  generalize min j s = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, map_add, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_smul,
      smul_eq_mul, hF]
    rw [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast]

variable [P.flip.IsReduced]

/-- The height of an LS path at the break `a_j`, minus `a_j` times the slope of the segment
starting there, is an integer. -/
private theorem exists_sum_sub_natTime_mul_eq_intCast (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (g : Module.Dual ℤ M) {j : ℕ} (hj : j < π.length + 1) :
    ∃ z : ℤ, ∑ k ∈ Finset.range j, (π.natTime (k + 1) - π.natTime k) * g (π.natDir k • lam) -
      π.natTime j * g (π.natDir j • lam) = z := by
  rcases j with _ | m
  · exact ⟨0, by simp [π.natTime_zero]⟩
  obtain ⟨z₁, hz₁⟩ := exists_sum_sub_mul_eq_intCast_of_isAChain hlam π.natTime_zero
    π.natDir_chain g (j := m) (by omega)
  obtain ⟨C, hh, hl, hC⟩ := π.natDir_chain m (by omega)
  obtain ⟨z₂, hz₂⟩ := hC.exists_mul_sub_eq_intCast hlam g
  rw [hh, hl] at hz₂
  exact ⟨z₁ + z₂, by push_cast at hz₁ hz₂ ⊢; linear_combination hz₁ + hz₂⟩

/-- The directions of an LS path after lowering at the vertices `k₀ < k₁`: the directions `τ_n`
with `k₀ ≤ n < k₁` are reflected by `sᵢ`, and `τ_{k₁ - 1}` is repeated after the new break. -/
private noncomputable def lowerDir (π : LSPath P b lam) (i : b.support) (k₀ k₁ n : ℕ) :
    P.weylGroup :=
  if n < k₀ then π.natDir n
  else if n < k₁ then (weylCoxeterSystem P b).simple i * π.natDir n else π.natDir (n - 1)

/-- The break times of an LS path after lowering, with the new break `t₁` inserted at `k₁`. -/
private def lowerTime (π : LSPath P b lam) (k₁ : ℕ) (t₁ : ℚ) (n : ℕ) : ℚ :=
  if n < k₁ then π.natTime n else if n = k₁ then t₁ else π.natTime (n - 1)

section LowerData

variable {π : LSPath P b lam} {i : b.support} {k₀ k₁ n : ℕ} {t₁ : ℚ}

omit [P.flip.IsReduced] in
private theorem lowerDir_of_lt (h : n < k₀) : lowerDir π i k₀ k₁ n = π.natDir n := by
  simp [lowerDir, h]

omit [P.flip.IsReduced] in
private theorem lowerDir_of_le_of_lt (h₀ : k₀ ≤ n) (h₁ : n < k₁) :
    lowerDir π i k₀ k₁ n = (weylCoxeterSystem P b).simple i * π.natDir n := by
  simp [lowerDir, h₁, show ¬n < k₀ by omega]

omit [P.flip.IsReduced] in
private theorem lowerDir_of_le (h₀ : k₀ < k₁) (h₁ : k₁ ≤ n) :
    lowerDir π i k₀ k₁ n = π.natDir (n - 1) := by
  simp [lowerDir, show ¬n < k₀ by omega, show ¬n < k₁ by omega]

omit [P.flip.IsReduced] in
private theorem lowerTime_of_lt (h : n < k₁) : lowerTime π k₁ t₁ n = π.natTime n := by
  simp [lowerTime, h]

omit [P.flip.IsReduced] in
private theorem lowerTime_self : lowerTime π k₁ t₁ k₁ = t₁ := by
  simp [lowerTime]

omit [P.flip.IsReduced] in
private theorem lowerTime_of_lt' (h : k₁ < n) : lowerTime π k₁ t₁ n = π.natTime (n - 1) := by
  simp [lowerTime, show ¬n < k₁ by omega, show n ≠ k₁ by omega]

end LowerData

/-- **The chains of a lowered LS path.** Let `H j` be the height `⟨π(a_j), αᵢ^∨⟩` of an LS path
at its vertex `j`, with an integral least value `H k₀`, rising strictly from `k₀` up to the vertex
`k₁` and staying below `H k₀ + 1` before `k₁`. Let `t₁` be the time at which the segment `k₁ - 1`
reaches the height `H k₀ + 1`. Then consecutive directions of the lowered break data are joined
by chains for the break between them. -/
private theorem lower_chain (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (i : b.support) (H : ℕ → ℚ) (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    {k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ π.length + 1) (hz : ∃ z : ℤ, H k₀ = z)
    (hleast : ∀ j ≤ π.length + 1, H k₀ ≤ H j)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1) {t₁ : ℚ}
    (ht₁ : (t₁ - π.natTime (k₁ - 1)) * P.coroot' i (π.natDir (k₁ - 1) • lam) =
      H k₀ + 1 - H (k₁ - 1))
    (n : ℕ) (hn : n + 1 < π.length + 2) :
    ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = lowerDir π i k₀ k₁ n ∧ C.last.1 = lowerDir π i k₀ k₁ (n + 1) ∧
        IsAChain (lowerTime π k₁ t₁ (n + 1)) lam C := by
  have hHs (k : ℕ) : H (k + 1) = H k +
      (π.natTime (k + 1) - π.natTime k) * P.coroot' i (π.natDir k • lam) := by
    rw [hH, hH, Finset.sum_range_succ]
  have hd (k : ℕ) (hk : k < π.length + 1) : 0 < π.natTime (k + 1) - π.natTime k :=
    sub_pos.mpr (π.natTime_strictMono k hk)
  -- The reflected directions lie strictly on the positive side of the wall of `αᵢ`.
  have hcpos (k : ℕ) (h₀ : k₀ ≤ k) (h₁ : k < k₁) : 0 < P.coroot' i (π.natDir k • lam) := by
    have hr := (hrise k h₀ h₁).1
    rw [hHs] at hr
    by_contra! hc
    nlinarith [hd k (by omega), (Int.cast_nonpos (R := ℚ)).mpr hc]
  obtain ⟨z, hz⟩ := hz
  rcases lt_trichotomy (n + 1) k₀ with h₁ | h₁ | h₁
  · -- Before `k₀` nothing changes.
    rw [lowerDir_of_lt (by omega), lowerDir_of_lt h₁, lowerTime_of_lt (by omega)]
    exact π.natDir_chain n (by omega)
  · -- At `k₀` the height stops decreasing: the chain ends at the reflected direction.
    obtain ⟨C, hh, hl, hC⟩ := π.natDir_chain n (by omega)
    have hneg : P.coroot' i (C.head.1 • lam) ≤ 0 := by
      have hle := hleast n (by omega)
      rw [← h₁, hHs] at hle
      rw [hh]
      by_contra! hc
      nlinarith [hd n (by omega), (Int.cast_pos (R := ℚ)).mpr hc]
    obtain ⟨D, hDh, hDl, hD⟩ := hC.exists_isAChain_simple_mul_last hlam i hneg
      (hl ▸ hcpos (n + 1) h₁.ge (by omega))
    refine ⟨D, by rw [hDh, hh, lowerDir_of_lt (by omega)], ?_, ?_⟩
    · rw [hDl, hl, lowerDir_of_le_of_lt h₁.ge (by omega)]
    · rwa [lowerTime_of_lt (by omega)]
  rcases lt_trichotomy (n + 1) k₁ with h₂ | h₂ | h₂
  · -- Strictly inside the reflected piece the height is not an integer, so the whole chain lies
    -- on the positive side and is reflected.
    obtain ⟨C, hh, hl, hC⟩ := π.natDir_chain n (by omega)
    have hint : ¬∃ z : ℤ, π.natTime (n + 1) * P.coroot' i (C.last.1 • lam) = z := by
      rintro ⟨z₁, hz₁⟩
      obtain ⟨z₂, hz₂⟩ := exists_sum_sub_natTime_mul_eq_intCast π hlam (P.coroot' i)
        (j := n + 1) (by omega)
      rw [← hH, ← hl] at hz₂
      have hlo : (z : ℚ) < z₁ + z₂ := by
        linarith [hleast n (by omega), (hrise n (by omega) (by omega)).1]
      have hhi : ((z₁ + z₂ : ℤ) : ℚ) < z + 1 := by
        push_cast
        linarith [(hrise (n + 1) (by omega) h₂).2]
      have : z < z₁ + z₂ := by exact_mod_cast hlo
      have : z₁ + z₂ < z + 1 := by exact_mod_cast hhi
      omega
    have hall := hC.coroot'_smul_pos hlam i (hl ▸ hcpos (n + 1) (by omega) h₂) hint
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inl hall), ?_, ?_,
      ?_⟩
    · rw [_root_.CoxeterSystem.MinimalCosetRepChain.head_simpleMul, hh,
        lowerDir_of_le_of_lt (by omega) (by omega)]
    · rw [_root_.CoxeterSystem.MinimalCosetRepChain.last_simpleMul, hl,
        lowerDir_of_le_of_lt (by omega) h₂]
    · rwa [lowerTime_of_lt h₂,
        _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff]
  · -- At the new break `t₁` the reflected direction `sᵢ τ` covers `τ`.
    obtain rfl : n = k₁ - 1 := by omega
    obtain ⟨z₂, hz₂⟩ := exists_sum_sub_natTime_mul_eq_intCast π hlam (P.coroot' i)
      (j := k₁ - 1) (by omega)
    rw [← hH] at hz₂
    obtain ⟨C, hh, hl, hC⟩ := exists_isAChain_simple_mul_of_coroot'_pos hlam
      (π.isMinimalCosetRep_natDir (k₁ - 1)) (hcpos (k₁ - 1) (by omega) (by omega))
      (a := t₁) ⟨z + 1 - z₂, by push_cast; linear_combination ht₁ + hz - hz₂⟩
    refine ⟨C, ?_, ?_, ?_⟩
    · rw [hh, lowerDir_of_le_of_lt (by omega) (by omega)]
    · rw [hl, h₂, lowerDir_of_le hk₀₁ le_rfl]
    · rwa [h₂, lowerTime_self]
  · -- After `t₁` nothing changes, up to the shift of indices.
    have hc := π.natDir_chain (n - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hc
    rwa [lowerDir_of_le hk₀₁ (by omega), lowerDir_of_le hk₀₁ (by omega), Nat.add_sub_cancel,
      lowerTime_of_lt' (by omega), Nat.add_sub_cancel]

/-- **The lowered break data present an LS path**, with the hypotheses of
`TauCeti.LSPath.lower_chain` and a cut time `t₁` inside the segment `k₁ - 1`. -/
private theorem exists_toPLPath_eq_lower (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (i : b.support) (H : ℕ → ℚ) (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    {k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ π.length + 1) (hz : ∃ z : ℤ, H k₀ = z)
    (hleast : ∀ j ≤ π.length + 1, H k₀ ≤ H j)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1) {t₁ : ℚ}
    (ht₁ : (t₁ - π.natTime (k₁ - 1)) * P.coroot' i (π.natDir (k₁ - 1) • lam) =
      H k₀ + 1 - H (k₁ - 1))
    (ht₁₀ : π.natTime (k₁ - 1) ≤ t₁) (ht₁₁ : t₁ ≤ π.natTime k₁) :
    ∃ π' : LSPath P b lam, ∀ f : M →+ V, π'.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((List.range (π.length + 1 + 1)).map fun n ↦
        ((lowerTime π k₁ t₁ (n + 1) - lowerTime π k₁ t₁ n : ℚ) : 𝕜) •
          f (lowerDir π i k₀ k₁ n • lam)) := by
  refine exists_toPLPath_eq_ofSegments (fun n hn ↦ ?_) ?_ ?_ (fun n hn ↦ ?_)
    (lower_chain π hlam i H hH hk₀₁ hk₁ hz hleast hrise ht₁)
  · -- The reflected directions are minimal coset representatives, off the wall of `αᵢ`.
    rcases lt_or_ge n k₀ with h₀ | h₀
    · rw [lowerDir_of_lt h₀]
      exact π.isMinimalCosetRep_natDir n
    rcases lt_or_ge n k₁ with h₁ | h₁
    · rw [lowerDir_of_le_of_lt h₀ h₁]
      refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (π.isMinimalCosetRep_natDir n)
        fun hc ↦ ?_
      have hr := (hrise n h₀ h₁).1
      rw [hH, hH, Finset.sum_range_succ, hc] at hr
      simp at hr
    · rw [lowerDir_of_le hk₀₁ h₁]
      exact π.isMinimalCosetRep_natDir (n - 1)
  · rw [lowerTime_of_lt (by omega), π.natTime_zero]
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, π.natTime_last]
  · -- The times increase weakly: the new break `t₁` lies in the segment `k₁ - 1`.
    have hmono (k : ℕ) (hk : k < π.length + 1) : π.natTime k ≤ π.natTime (k + 1) :=
      (π.natTime_strictMono k hk).le
    rcases lt_trichotomy (n + 1) k₁ with h₁ | h₁ | h₁
    · rw [lowerTime_of_lt (by omega), lowerTime_of_lt h₁]
      exact hmono n (by omega)
    · rw [lowerTime_of_lt (by omega), h₁, lowerTime_self, show n = k₁ - 1 by omega]
      exact ht₁₀
    · rcases (show n = k₁ ∨ k₁ < n by omega) with rfl | h₂
      · rw [lowerTime_self, lowerTime_of_lt' (by omega), Nat.add_sub_cancel]
        exact ht₁₁
      · rw [lowerTime_of_lt' h₂, lowerTime_of_lt' (by omega), Nat.add_sub_cancel]
        have := hmono (n - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this

omit [P.flip.IsReduced] in
/-- **The lowering of an LS path, computed on its presentation.** With the hypotheses of
`TauCeti.LSPath.lower_chain`, if the height `H k₁` is at least `H k₀ + 1` from `k₁` on and `t₁`
is the time at which the segment `k₁ - 1` reaches the height `H k₀ + 1`, then Littelmann's lowering
operator sends the realization of `π` to the path presented by the lowered break data. -/
private theorem lower_toPLPath_eq (π : LSPath P b lam) (f : M →+ V) (i : b.support)
    {F : Module.Dual 𝕜 V} (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (H : ℕ → ℚ)
    (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    {k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ π.length + 1)
    (hleast : ∀ j ≤ π.length + 1, H k₀ ≤ H j)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1)
    (habove : ∀ j, k₁ ≤ j → j ≤ π.length + 1 → H k₀ + 1 ≤ H j) {θ t₁ : ℚ}
    (hθ : θ * (H k₁ - H (k₁ - 1)) = H k₀ + 1 - H (k₁ - 1))
    (ht₁ : t₁ = π.natTime (k₁ - 1) + θ * (π.natTime k₁ - π.natTime (k₁ - 1))) :
    PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
      ((List.range (π.length + 1 + 1)).map fun n ↦
        ((lowerTime π k₁ t₁ (n + 1) - lowerTime π k₁ t₁ n : ℚ) : 𝕜) •
          f (lowerDir π i k₀ k₁ n • lam))) := by
  set s := π.length + 1
  set L := (List.range s).map fun k ↦
    ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam) with hL
  set j₁ := k₁ - 1 with hj₁
  have hk₁' : j₁ + 1 = k₁ := by omega
  have hHk₁ : H k₁ = H j₁ +
      (π.natTime k₁ - π.natTime j₁) * (P.coroot' i (π.natDir j₁ • lam) : ℚ) := by
    rw [hH, hH, ← hk₁', Finset.sum_range_succ]
  have hrj := hrise j₁ (by omega) (by omega)
  rw [hk₁'] at hrj
  -- The vertex heights of `L` are the heights `H`, with minimum `H k₀`.
  have hFL (j : ℕ) : F (L.take j).sum = (H (min j s) : 𝕜) := by
    rw [hH]
    exact apply_sum_take_map_range f F (P.coroot' i) hF s _ _ j
  have hFLj (j : ℕ) (hj : j ≤ s) : F (L.take j).sum = (H j : 𝕜) := by rw [hFL, min_eq_left hj]
  have hmin : PLPath.listMinHeight F L = (H k₀ : 𝕜) := by
    refine le_antisymm ?_ ?_
    · have := PLPath.listMinHeight_le_apply_sum_take (f := F) L k₀
      rwa [hFLj k₀ (by omega)] at this
    · obtain ⟨m, hm⟩ := PLPath.exists_listMinHeight_eq (f := F) L
      rw [hm, hFL]
      exact_mod_cast hleast _ (Nat.min_le_right _ _)
  have hgetL : L[k₁ - 1]'(by simp [hL]; omega) =
      ((π.natTime k₁ - π.natTime j₁ : ℚ) : 𝕜) • f (π.natDir j₁ • lam) := by
    simp only [hL, List.getElem_map, List.getElem_range, Nat.sub_add_cancel (by omega : 1 ≤ k₁)]
    rw [hj₁]
  -- Littelmann's lowering of `L` reflects the rising piece from `k₀` to the cut in `k₁ - 1`.
  rw [π.toPLPath_eq_ofSegments_natDir f, PLPath.lower_ofSegments_eq_of_strictly_rising
    (θ := (θ : 𝕜)) hk₀₁ (by simp; omega)
    (by rw [hmin, hFLj k₀ (by omega)])
    (fun j h₀ h₁ ↦ by
      rw [hFLj j (by omega), hFLj (j + 1) (by omega)]
      exact_mod_cast (hrise j h₀ h₁).1)
    (by
      rw [hFLj _ (by omega), hgetL, map_smul, hF, hmin, smul_eq_mul]
      have : H j₁ + θ * ((π.natTime k₁ - π.natTime j₁) *
          (P.coroot' i (π.natDir j₁ • lam) : ℚ)) = H k₀ + 1 := by
        linear_combination hθ - θ * hHk₁
      exact_mod_cast this)
    (by
      rw [hFLj _ (by omega), hmin]
      exact_mod_cast hrj.2.le)
    (fun j hj ↦ by
      rw [hFL, hmin]
      exact_mod_cast habove _ (le_min hj hk₁) (Nat.min_le_right _ _))]
  -- The lowered presentation is the presentation of the lowered break data.
  congr 2
  refine (lowered_eq_map_range (Module.preReflection (f (P.root i)) F) (θ : 𝕜) hk₀₁ hk₁
    (fun n hn ↦ ?_) (fun n h₀ h₁ ↦ ?_) ?_ ?_ (fun n hn ↦ ?_) (by simp; omega))
  · rw [lowerTime_of_lt (by omega), lowerTime_of_lt (by omega), lowerDir_of_lt hn]
  · rw [lowerTime_of_lt (by omega), lowerTime_of_lt (by omega),
      lowerDir_of_le_of_lt h₀ (by omega), simple_mul_smul_eq_reflection,
      P.map_reflection_eq_preReflection i hF, LinearMap.map_smul]
  · rw [hk₁', lowerTime_self, lowerTime_of_lt (by omega),
      lowerDir_of_le_of_lt (by omega) (by omega), simple_mul_smul_eq_reflection,
      P.map_reflection_eq_preReflection i hF, LinearMap.map_smul, LinearMap.map_smul, smul_smul]
    congr 1
    push_cast [ht₁]
    ring
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, lowerTime_self,
      lowerDir_of_le hk₀₁ le_rfl, hk₁', smul_smul]
    congr 1
    push_cast [ht₁]
    ring
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, lowerTime_of_lt' hn,
      lowerDir_of_le hk₀₁ hn.le, Nat.sub_add_cancel (by omega : 1 ≤ n)]

/-- **Littelmann's lowering operator preserves LS paths.** Let `π` be an LS path of dominant shape
`λ`, realized in `V` by `f`, and let `F` be a form on `V` inducing the simple coroot pairing
`⟨-, αᵢ^∨⟩`. If the lowering operator `f_{αᵢ}` along the realized simple root `f αᵢ` is defined
on `π`, then `f_{αᵢ} π` is the realization of an LS path of shape `λ`. Its directions are those
of `π` with the directions `τ` of the lowered piece replaced by `sᵢ τ`. -/
theorem exists_toPLPath_eq_of_lower_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  set s := π.length + 1
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j,
    (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ) with hH
  -- The final height exceeds the minimal height by at least one.
  have hgap : ∃ j ≤ s, H j + 1 ≤ H s := by
    set L := (List.range s).map fun k ↦
      ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam) with hL
    have hFL (j : ℕ) : F (L.take j).sum = (H (min j s) : 𝕜) :=
      apply_sum_take_map_range f F (P.coroot' i) hF s _ _ j
    obtain ⟨m, hm⟩ := PLPath.exists_listMinHeight_eq (f := F) L
    have h1 : ¬F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F < 1 := fun h ↦ by
      rw [PLPath.lower_eq_none_iff.mpr h] at hq
      cases hq
    have hπ : π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜 L := π.toPLPath_eq_ofSegments_natDir f
    rw [hπ, PLPath.endpoint_ofSegments, PLPath.minHeight_ofSegments, hm, hFL,
      ← List.take_length (l := L), hFL, show L.length = s by simp [hL], min_self] at h1
    have h2 : ((H (min m s) + 1 : ℚ) : 𝕜) ≤ (H s : 𝕜) := by
      push_cast
      linarith [not_lt.mp h1]
    exact ⟨min m s, Nat.min_le_right _ _, by exact_mod_cast h2⟩
  -- The rising piece: the last vertex `k₀` of minimal height, an integer, and the first vertex
  -- `k₁` after it of height at least `H k₀ + 1`.
  have hs₁ : ∃ z : ℤ, π.natTime s = z := ⟨1, by rw [π.natTime_last, Int.cast_one]⟩
  obtain ⟨k₀, k₁, hk₀₁, hk₁, hleast, hrise, habove⟩ := exists_strictly_rising_of_isAChain hlam
    π.natTime_zero π.natDir_chain π.natTime_strictMono hs₁ i hgap
  obtain ⟨z, hz⟩ := exists_isLeast_sum_coroot'_eq_intCast_of_isAChain hlam π.natTime_zero
    π.natDir_chain π.natTime_strictMono hs₁ i
  have hleast' (j : ℕ) (hj : j ≤ s) : H k₀ ≤ H j := hleast.2 ⟨j, hj, rfl⟩
  -- The segment `j₁ = k₁ - 1`, of duration `d`, reaches the height `H k₀ + 1` after the
  -- fraction `θ` of it, at the time `t₁`.
  set j₁ := k₁ - 1
  have hk₁' : j₁ + 1 = k₁ := by omega
  have hHk₁ : H k₁ = H j₁ +
      (π.natTime k₁ - π.natTime j₁) * (P.coroot' i (π.natDir j₁ • lam) : ℚ) := by
    rw [← hk₁']
    simp only [hH, Finset.sum_range_succ]
  have hrj := hrise j₁ (by omega) (by omega)
  rw [hk₁'] at hrj
  have hab := habove k₁ le_rfl hk₁
  set θ : ℚ := (H k₀ + 1 - H j₁) / (H k₁ - H j₁)
  have hθmul : θ * (H k₁ - H j₁) = H k₀ + 1 - H j₁ := div_mul_cancel₀ _ (by linarith)
  have hθ₀ : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ₁ : θ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  set d := π.natTime k₁ - π.natTime j₁
  have hd₀ : 0 < d := by
    have := π.natTime_strictMono j₁ (by omega)
    rw [hk₁'] at this
    linarith
  set t₁ := π.natTime j₁ + θ * d with ht₁
  obtain ⟨π', hπ'⟩ := exists_toPLPath_eq_lower (𝕜 := 𝕜) (V := V) π hlam i H (fun _ ↦ rfl) hk₀₁
    hk₁ ⟨z, hleast.unique hz⟩ hleast' hrise (t₁ := t₁) (by rw [← hθmul, hHk₁]; ring)
    (by nlinarith) (by nlinarith)
  refine ⟨π', (hπ' f).trans (Option.some.inj ?_)⟩
  rw [← hq, lower_toPLPath_eq π f i hF H (fun _ ↦ rfl) hk₀₁ hk₁ hleast' hrise habove hθmul ht₁]

end TauCeti.LSPath
