/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic

/-!
# Break data of Lakshmibai–Seshadri paths

An LS path `π = (τ₀, …, τ_l; a₀, …, a_{l+1})` is read here as **break data**: a sequence of
directions `τ_k` and times `t_k` indexed by `ℕ`, so that its realization is presented by the
segments `(t_{k+1} - t_k) τ_k λ`. The sequences `TauCeti.LSPath.natDir` and
`TauCeti.LSPath.natTime` extend the directions and the break times of `π` constantly past their
last entries, in the form taken by the chain-height lemmas of
`TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond`.

Conversely, more general break data present LS paths: weakly increasing times `t_k` from `0` to
`1` and minimal coset representatives `τ_k`, where consecutive directions may agree and segments
may be stationary, subject to the chain conditions at every break. Removing the stationary
segments and merging the segments with repeated directions turns break data into an LS path
presenting the same piecewise-linear path.

## Main definitions

* `TauCeti.LSPath.natDir`, `TauCeti.LSPath.natTime`: the directions and break times of an LS
  path as sequences indexed by `ℕ`.

## Main results

* `TauCeti.LSPath.natDir_chain`: consecutive directions are joined by chains for the break
  between them.
* `TauCeti.LSPath.toPLPath_eq_ofSegments_natDir`: the realization of an LS path is presented by
  its break data.
* `TauCeti.LSPath.apply_sum_take_map_range`: the vertex heights of break data.
* `TauCeti.LSPath.exists_toPLPath_eq_ofSegments`: **break data present an LS path.**

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

/-! ### Directions and break times indexed by `ℕ` -/

/-- The directions `τ₀, …, τ_l` of an LS path as a sequence indexed by `ℕ`, extended constantly
past its last entry, in the form taken by the chain-height lemmas of
`TauCeti.LinearAlgebra.RootSystem.Weyl.ChainBond`. -/
def natDir (π : LSPath P b lam) (k : ℕ) : P.weylGroup :=
  (π.dir ⟨min k π.length, by omega⟩).1

/-- The break times `a₀, …, a_{l+1}` of an LS path as a sequence indexed by `ℕ`, extended
constantly past its last entry. -/
def natTime (π : LSPath P b lam) (k : ℕ) : ℚ :=
  π.time ⟨min k (π.length + 1), by omega⟩

theorem natDir_of_le (π : LSPath P b lam) {k : ℕ} (hk : k ≤ π.length) :
    π.natDir k = (π.dir ⟨k, Nat.lt_succ_of_le hk⟩).1 := by
  simp only [natDir, min_eq_left hk]

theorem natTime_of_le (π : LSPath P b lam) {k : ℕ} (hk : k ≤ π.length + 1) :
    π.natTime k = π.time ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp only [natTime, min_eq_left hk]

theorem natDir_of_length_le (π : LSPath P b lam) {k : ℕ} (hk : π.length ≤ k) :
    π.natDir k = (π.dir (Fin.last _)).1 := by
  simp only [natDir, min_eq_right hk, Fin.last]

theorem natTime_of_length_lt (π : LSPath P b lam) {k : ℕ} (hk : π.length < k) :
    π.natTime k = 1 := by
  simpa only [natTime, min_eq_right (Nat.succ_le_of_lt hk), Fin.last] using π.time_last

theorem isMinimalCosetRep_natDir (π : LSPath P b lam) (k : ℕ) :
    (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) (π.natDir k) :=
  (π.dir _).2

@[simp]
theorem natTime_zero (π : LSPath P b lam) : π.natTime 0 = 0 :=
  π.time_zero

@[simp]
theorem natTime_last (π : LSPath P b lam) : π.natTime (π.length + 1) = 1 := by
  simpa only [natTime, min_self, Fin.last] using π.time_last

theorem natTime_lt_natTime_succ (π : LSPath P b lam) (k : ℕ) (hk : k < π.length + 1) :
    π.natTime k < π.natTime (k + 1) := by
  apply π.strictMono_time
  simp only [Fin.mk_lt_mk, min_eq_left (by omega : k ≤ π.length + 1),
    min_eq_left (by omega : k + 1 ≤ π.length + 1)]
  omega

/-- Consecutive directions of an LS path are joined by chains for the break between them. -/
theorem natDir_chain (π : LSPath P b lam) (k : ℕ) (hk : k + 1 < π.length + 1) :
    ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = π.natDir k ∧ C.last.1 = π.natDir (k + 1) ∧
        IsAChain (π.natTime (k + 1)) lam C := by
  obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain ⟨k, by omega⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simpa [natDir, min_eq_left (by omega : k ≤ π.length)] using congrArg Subtype.val hhead
  · simpa [natDir, min_eq_left (by omega : k + 1 ≤ π.length)] using congrArg Subtype.val hlast
  · simpa [natTime, min_eq_left (by omega : k + 1 ≤ π.length + 1)] using hC

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The segments of the distinguished timed presentation of an LS path are the segments
`(a_{k+1} - a_k) τ_k λ`, read off the sequences `TauCeti.LSPath.natTime` and
`TauCeti.LSPath.natDir`. -/
theorem map_snd_timed (π : LSPath P b lam) (f : M →+ V) :
    (π.timed 𝕜 f).map Prod.snd = (List.range (π.length + 1)).map fun k ↦
      ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam) := by
  rw [timed_def, List.map_ofFn]
  refine List.ext_getElem (by simp) fun n h₁ h₂ ↦ ?_
  have hn : n < π.length + 1 := by simpa using h₁
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply,
    duration_def, π.natDir_of_le (by omega : n ≤ π.length),
    π.natTime_of_le (by omega : n + 1 ≤ π.length + 1),
    π.natTime_of_le (by omega : n ≤ π.length + 1), Fin.succ_mk, Fin.castSucc_mk]

/-- The realization of an LS path is presented by the segments `(a_{k+1} - a_k) τ_k λ`, read off
the sequences `TauCeti.LSPath.natTime` and `TauCeti.LSPath.natDir`. -/
theorem toPLPath_eq_ofSegments_natDir (π : LSPath P b lam) (f : M →+ V) :
    π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜 ((List.range (π.length + 1)).map fun k ↦
      ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam)) := by
  rw [toPLPath_def, map_snd_timed]

omit [Finite ι] [P.IsReduced] in
/-- The vertex heights of break data: under a height form `F` agreeing with an integral form `g`
on the lattice, the height of the `j`-th vertex of the segments `(t_{k+1} - t_k) τ_k λ` is
`∑_{k < j} (t_{k+1} - t_k) g (τ_k λ)`. -/
theorem apply_sum_take_map_range (f : M →+ V) (F : Module.Dual 𝕜 V)
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

/-! ### Break data with repeated directions and stationary pieces -/

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
        (PLPath.ofSegments_map_range_of_eq_zero hk (by simp [hkt]) (fun n hn ↦ ?_)
          fun n hn ↦ ?_).symm⟩
      · simp [hn, hn.le, show n + 1 ≤ k by omega]
      · rcases hn.eq_or_lt with rfl | hn
        · simp [hkt]
        · simp [show ¬n < k by omega, show ¬n ≤ k by omega, show ¬n + 1 ≤ k by omega]
    by_cases hd : ∃ k, k + 1 < s + 1 ∧ τ k = τ (k + 1)
    · obtain ⟨k, hk, hkτ⟩ := hd
      obtain ⟨π, hπ⟩ := ih (h.mergeAt hk hkτ)
      refine ⟨π, fun f ↦ (hπ f).trans (PLPath.ofSegments_map_range_of_smul hk
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

end TauCeti.LSPath
