/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Combinatorics.Additive.NoRelation

/-!
# Orbits meeting the powers of an element along a set with no short relation

Let `α₀` be an element of a group `G` and `T ⊆ ℤ`. We bound how many points `y * h ^ i` of the
orbit of `y` under right multiplication by `h` lie in the left translate
`u₀ • ((α₀ ^ ·) '' T)`, for arbitrary `y h u₀ : G`.

Two such points `y * h ^ i = u₀ * α₀ ^ s` and `y * h ^ i' = u₀ * α₀ ^ s'` give
`h ^ (i' - i) = α₀ ^ (s' - s)`.

* Three distinct such points, with `a = i₁ - i₀` and `b = i₂ - i₀`, give
  `α₀ ^ (b (s₁ - s₀)) = h ^ (a b) = α₀ ^ (a (s₂ - s₀))`, so `orderOf α₀` divides
  `b (s₁ - s₀) - a (s₂ - s₀)`. If `|a|, |b| ≤ L` and `2 L |s - s'| < orderOf α₀` for all
  `s, s' ∈ T`, this difference has absolute value less than `orderOf α₀`, hence vanishes: a
  relation of length `L` among the distinct `s₀, s₁, s₂`. So if `T` has no relation of length
  `L`, at most two points `y * h ^ i` with `i` in a set of indices of diameter at most `L` lie in
  the translate.
* If `orderOf h * |s - s'| < orderOf α₀` for all `s, s' ∈ T`, the whole orbit meets the
  translate in at most one point: for `orderOf h ≠ 0`, `α₀ ^ ((s' - s) orderOf h) = 1` forces
  `s = s'`; for `h` of infinite order, `h ^ ((i' - i) orderOf α₀) = 1` forces `i = i'`.

## Main results

* `TauCeti.NoRelation.encard_image_inter_le_two`: if `T` has no relation of length `L` and
  `2 L |s - s'| < orderOf α₀` on `T`, then for every set `I ⊆ ℤ` of diameter at most `L`, at most
  two of the points `y * h ^ i`, `i ∈ I`, lie in `u₀ • ((α₀ ^ ·) '' T)`.
* `TauCeti.NoRelation.encard_setOf_mem_le_two`: the same bound for the indices `i ∈ I` with
  `y * h ^ i ∈ u₀ • ((α₀ ^ ·) '' T)`, when `h ^ n ≠ 1` for `0 < n ≤ L`.
* `TauCeti.subsingleton_smul_zpowers_inter_smul_image_zpow`: if `orderOf h * |s - s'| < orderOf α₀`
  on `T`, the orbit `y • zpowers h` contains at most one point of `u₀ • ((α₀ ^ ·) '' T)`.
* `TauCeti.NoRelation.encard_setOf_mem_Ico_le_two`,
  `TauCeti.subsingleton_smul_zpowers_inter_smul_image_zpow_of_orderOf_le`: the two bounds for
  `T ⊆ [0, orderOf α₀ / (4 L))`, with `4 L < orderOf h` for `L` consecutive positions and
  `orderOf h ≤ 4 L` for the whole orbit. Such sets `T` are given by `TauCeti.exists_noRelation`.

## References

* L. Alpöge et al., Lean formalization of the Riemann hypothesis for Dirichlet L-functions,
  https://github.com/leanprover-community/riemann-hypothesis: both bounds, on cyclic hosts, are
  `Formalism.HC.Frame.hostThickOrbit`, the source of the statements here.
* `TauCeti.NoRelation` and `TauCeti.exists_noRelation` are in
  `TauCeti.Combinatorics.Additive.NoRelation`.
-/

public section

open Set
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G] {L : ℕ} {T : Set ℤ} {α₀ h : G}

/-- Two points `y * h ^ i = u₀ * α₀ ^ s` and `y * h ^ i' = u₀ * α₀ ^ s'` give
`h ^ (i' - i) = α₀ ^ (s' - s)`. -/
private lemma zpow_sub_eq_zpow_sub {y u₀ : G} {i i' s s' : ℤ} (e : u₀ * α₀ ^ s = y * h ^ i)
    (e' : u₀ * α₀ ^ s' = y * h ^ i') : h ^ (i' - i) = α₀ ^ (s' - s) := by
  have key : h ^ (i' - i) = (y * h ^ i)⁻¹ * (y * h ^ i') := by group
  rw [key, ← e, ← e']
  group

/-- Three distinct points `y * h ^ iₖ = u₀ * α₀ ^ sₖ` with `sₖ ∈ T` and `|iₖ - i₀| ≤ L` give a
relation of length `L` in `T` when `2 L |s - s'| < orderOf α₀` on `T`. -/
private lemma false_of_three {y u₀ : G} (hT : NoRelation L T)
    (hdiam : ∀ s ∈ T, ∀ s' ∈ T, 2 * L * |s - s'| < orderOf α₀) {i₀ i₁ i₂ s₀ s₁ s₂ : ℤ}
    (hs₀ : s₀ ∈ T) (hs₁ : s₁ ∈ T) (hs₂ : s₂ ∈ T) (hi₁ : |i₁ - i₀| ≤ L) (hi₂ : |i₂ - i₀| ≤ L)
    (e₀ : u₀ * α₀ ^ s₀ = y * h ^ i₀) (e₁ : u₀ * α₀ ^ s₁ = y * h ^ i₁)
    (e₂ : u₀ * α₀ ^ s₂ = y * h ^ i₂) (h₀₁ : y * h ^ i₀ ≠ y * h ^ i₁)
    (h₀₂ : y * h ^ i₀ ≠ y * h ^ i₂) (h₁₂ : y * h ^ i₁ ≠ y * h ^ i₂) : False := by
  have hpow : α₀ ^ ((s₁ - s₀) * (i₂ - i₀)) = α₀ ^ ((s₂ - s₀) * (i₁ - i₀)) := by
    rw [zpow_mul, zpow_mul, ← zpow_sub_eq_zpow_sub e₀ e₁, ← zpow_sub_eq_zpow_sub e₀ e₂,
      ← zpow_mul, ← zpow_mul, mul_comm]
  have hlt : |(s₂ - s₀) * (i₁ - i₀) - (s₁ - s₀) * (i₂ - i₀)| < orderOf α₀ :=
    calc |(s₂ - s₀) * (i₁ - i₀) - (s₁ - s₀) * (i₂ - i₀)|
        ≤ |(s₂ - s₀) * (i₁ - i₀)| + |(s₁ - s₀) * (i₂ - i₀)| := abs_sub _ _
      _ ≤ |s₂ - s₀| * L + |s₁ - s₀| * L := by rw [abs_mul, abs_mul]; gcongr
      _ < orderOf α₀ := by linarith [hdiam s₂ hs₂ s₀ hs₀, hdiam s₁ hs₁ s₀ hs₀]
  have hrel := Int.eq_zero_of_abs_lt_dvd (zpow_eq_zpow_iff_modEq.1 hpow).dvd hlt
  refine noRelation_iff.1 hT s₀ hs₀ s₁ hs₁ s₂ hs₂ (fun hs => h₀₁ (by rw [← e₀, ← e₁, hs]))
    (fun hs => h₀₂ (by rw [← e₀, ← e₂, hs])) (fun hs => h₁₂ (by rw [← e₁, ← e₂, hs]))
    (i₁ - i₀) (i₂ - i₀) (fun hi => h₁₂ (by rw [sub_left_inj.1 hi]))
    (abs_pos.2 (sub_ne_zero.2 fun hi => h₀₁ (by rw [hi]))) hi₁
    (abs_pos.2 (sub_ne_zero.2 fun hi => h₀₂ (by rw [hi]))) hi₂ (by linear_combination -hrel)

/-- **Few points of an orbit window in a translate.** Let `T ⊆ ℤ` have no relation of length `L`
and satisfy `2 L |s - s'| < orderOf α₀` for all `s, s' ∈ T`. For every set of indices `I ⊆ ℤ` of
diameter at most `L` and all `y h u₀ : G`, at most two of the points `y * h ^ i`, `i ∈ I`, lie in
`u₀ • ((α₀ ^ ·) '' T)`. No hypothesis on `h` is needed; `I` may be `Finset.Ico i₀ (i₀ + L)`, the
indices of `L` consecutive points of the orbit, or `Finset.Icc i₀ (i₀ + L)`. -/
theorem NoRelation.encard_image_inter_le_two (hT : NoRelation L T)
    (hdiam : ∀ s ∈ T, ∀ s' ∈ T, 2 * L * |s - s'| < orderOf α₀) {I : Set ℤ}
    (hI : ∀ i ∈ I, ∀ i' ∈ I, |i - i'| ≤ L) (y h u₀ : G) :
    ((fun i => y * h ^ i) '' I ∩ u₀ • ((fun s => α₀ ^ s) '' T)).encard ≤ 2 := by
  by_contra hlt
  obtain ⟨f, hf, hinj⟩ := (le_encard_iff_exists_fin_injective _ 3).1
    (Order.add_one_le_of_lt (not_le.1 hlt))
  have hmem (k : Fin 3) : ∃ i ∈ I, ∃ s ∈ T, u₀ * α₀ ^ s = y * h ^ i ∧ y * h ^ i = f k := by
    obtain ⟨⟨i, hi, hik⟩, _, ⟨s, hs, rfl⟩, hsk⟩ := hf k
    exact ⟨i, hi, s, hs, hsk.trans hik.symm, hik⟩
  obtain ⟨i₀, hi₀, s₀, hs₀, e₀, f₀⟩ := hmem 0
  obtain ⟨i₁, hi₁, s₁, hs₁, e₁, f₁⟩ := hmem 1
  obtain ⟨i₂, hi₂, s₂, hs₂, e₂, f₂⟩ := hmem 2
  exact false_of_three hT hdiam hs₀ hs₁ hs₂ (hI _ hi₁ _ hi₀) (hI _ hi₂ _ hi₀) e₀ e₁ e₂
    (by rw [f₀, f₁]; exact hinj.ne (by decide)) (by rw [f₀, f₂]; exact hinj.ne (by decide))
    (by rw [f₁, f₂]; exact hinj.ne (by decide))

/-- **Few marked positions in an orbit window.** Let `T ⊆ ℤ` have no relation of length `L` and
satisfy `2 L |s - s'| < orderOf α₀` for all `s, s' ∈ T`, and let `h ^ n ≠ 1` for `0 < n ≤ L` (for
instance `L < orderOf h`, or `h` of infinite order). For every set of indices `I ⊆ ℤ` of diameter
at most `L` and all `y u₀ : G`, at most two indices `i ∈ I` satisfy
`y * h ^ i ∈ u₀ • ((α₀ ^ ·) '' T)`. -/
theorem NoRelation.encard_setOf_mem_le_two (hT : NoRelation L T)
    (hdiam : ∀ s ∈ T, ∀ s' ∈ T, 2 * L * |s - s'| < orderOf α₀) {I : Set ℤ}
    (hI : ∀ i ∈ I, ∀ i' ∈ I, |i - i'| ≤ L) (hh : ∀ n : ℕ, 0 < n → n ≤ L → h ^ n ≠ 1)
    (y u₀ : G) : {i ∈ I | y * h ^ i ∈ u₀ • ((fun s => α₀ ^ s) '' T)}.encard ≤ 2 := by
  have hinj : InjOn (fun i => y * h ^ i) {i ∈ I | y * h ^ i ∈ u₀ • ((fun s => α₀ ^ s) '' T)} := by
    intro i hi i' hi' e
    by_contra hne
    have hle := hI i hi.1 i' hi'.1
    rw [Int.abs_eq_natAbs] at hle
    exact hh _ (Int.natAbs_pos.2 (sub_ne_zero.2 hne)) (by exact_mod_cast hle)
      (pow_natAbs_eq_one.2 (by rw [zpow_sub, mul_left_cancel e, mul_inv_cancel]))
  rw [← hinj.encard_image]
  refine (encard_le_encard ?_).trans (hT.encard_image_inter_le_two hdiam hI y h u₀)
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨mem_image_of_mem _ hi.1, hi.2⟩

/-- **An orbit meets a translate at most once.** If `orderOf h * |s - s'| < orderOf α₀` for all
`s, s' ∈ T`, then for all `y u₀ : G` the left coset `y • zpowers h` (the orbit `y ⟨h⟩`) contains
at most one point of `u₀ • ((α₀ ^ ·) '' T)`. This covers `h` of infinite order
(`orderOf h = 0`), where the hypothesis only asks `orderOf α₀ ≠ 0` when `T` is nonempty. -/
theorem subsingleton_smul_zpowers_inter_smul_image_zpow
    (hdiam : ∀ s ∈ T, ∀ s' ∈ T, orderOf h * |s - s'| < orderOf α₀) (y u₀ : G) :
    (y • (Subgroup.zpowers h : Set G) ∩ u₀ • ((fun s => α₀ ^ s) '' T)).Subsingleton := by
  rintro _ ⟨⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨s, hs, rfl⟩, e⟩ _ ⟨⟨_, ⟨i', rfl⟩, rfl⟩, _, ⟨s', hs', rfl⟩, e'⟩
  have hg := zpow_sub_eq_zpow_sub e e'
  have hA : α₀ ^ ((s' - s) * orderOf h) = 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := h)).1 (dvd_mul_left _ (i' - i))
    rwa [zpow_mul, hg, ← zpow_mul] at this
  have hH : h ^ ((i' - i) * orderOf α₀) = 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := α₀)).1 (dvd_mul_left _ (s' - s))
    rwa [zpow_mul, ← hg, ← zpow_mul] at this
  have hlt : |(s' - s) * orderOf h| < orderOf α₀ := by
    rw [abs_mul, Nat.abs_cast, mul_comm, abs_sub_comm]
    exact hdiam s hs s' hs'
  have h1 : h ^ (i' - i) = 1 := by
    rcases mul_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd (orderOf_dvd_iff_zpow_eq_one.2 hA) hlt)
      with hs0 | hm
    · rw [hg, hs0, zpow_zero]
    · have hM : (orderOf α₀ : ℤ) ≠ 0 := by
        have := hdiam s hs s' hs'
        rw [hm, zero_mul] at this
        exact this.ne'
      have hd := orderOf_dvd_iff_zpow_eq_one.2 hH
      rw [hm, zero_dvd_iff, mul_eq_zero, or_iff_left hM] at hd
      rw [hd, zpow_zero]
  dsimp only
  rw [smul_eq_mul, smul_eq_mul, ← sub_add_cancel i' i, zpow_add, h1, one_mul]

/-! ### The bounds for `T ⊆ [0, orderOf α₀ / (4 L))` -/

/-- For `s, s' ∈ [0, M / (4 L))` and `c ≤ 4 L`, `c |s - s'| < M`. -/
private lemma mul_abs_sub_lt {M c : ℕ} (hc : c ≤ 4 * L) {s s' : ℤ}
    (hs : 0 ≤ s ∧ (s : ℝ) < M / (4 * L)) (hs' : 0 ≤ s' ∧ (s' : ℝ) < M / (4 * L)) :
    c * |s - s'| < M := by
  have hL : (0 : ℝ) < 4 * L := by
    by_contra hL
    have h0 : (4 * L : ℝ) = 0 := le_antisymm (not_lt.1 hL) (by positivity)
    rw [h0, div_zero] at hs
    exact absurd hs.2 (not_lt.2 (by exact_mod_cast hs.1))
  have h1 : |(s : ℝ) - s'| < M / (4 * L) :=
    abs_sub_lt_of_nonneg_of_lt (by exact_mod_cast hs.1) hs.2 (by exact_mod_cast hs'.1) hs'.2
  have h2 : (c : ℝ) * |(s : ℝ) - s'| < M :=
    calc (c : ℝ) * |(s : ℝ) - s'| ≤ 4 * L * |(s : ℝ) - s'| := by gcongr; exact_mod_cast hc
      _ < M := by rwa [lt_div_iff₀' hL] at h1
  exact_mod_cast h2

/-- **Part (a) for `T ⊆ [0, orderOf α₀ / (4 L))`.** If `T ⊆ [0, orderOf α₀ / (4 L))` has no
relation of length `L` and `4 L < orderOf h`, then among the `L` consecutive positions
`i₀ ≤ i < i₀ + L` at most two satisfy `y * h ^ i ∈ u₀ • ((α₀ ^ ·) '' T)`; these positions give
distinct points. A special case of `TauCeti.NoRelation.encard_setOf_mem_le_two`. -/
theorem NoRelation.encard_setOf_mem_Ico_le_two (hT : NoRelation L T)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf α₀ / (4 * L)) (hh : 4 * L < orderOf h)
    (y u₀ : G) (i₀ : ℤ) :
    {i ∈ Ico i₀ (i₀ + L) | y * h ^ i ∈ u₀ • ((fun s => α₀ ^ s) '' T)}.encard ≤ 2 := by
  have hdiam (s : ℤ) (hs : s ∈ T) (s' : ℤ) (hs' : s' ∈ T) : 2 * L * |s - s'| < orderOf α₀ := by
    exact_mod_cast mul_abs_sub_lt (c := 2 * L) (by omega) (hTM s hs) (hTM s' hs')
  exact hT.encard_setOf_mem_le_two hdiam
    (fun i hi i' hi' => abs_le.2 ⟨by linarith [hi.1, hi'.2], by linarith [hi.2, hi'.1]⟩)
    (fun n hn hnL => pow_ne_one_of_lt_orderOf hn.ne' (by omega)) y u₀

/-- **Part (b) for `T ⊆ [0, orderOf α₀ / (4 L))`.** If `T ⊆ [0, orderOf α₀ / (4 L))` and
`orderOf h ≤ 4 L`, the orbit `y • zpowers h` contains at most one point of
`u₀ • ((α₀ ^ ·) '' T)`. A special case of
`TauCeti.subsingleton_smul_zpowers_inter_smul_image_zpow`. -/
theorem subsingleton_smul_zpowers_inter_smul_image_zpow_of_orderOf_le
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf α₀ / (4 * L)) (hh : orderOf h ≤ 4 * L)
    (y u₀ : G) :
    (y • (Subgroup.zpowers h : Set G) ∩ u₀ • ((fun s => α₀ ^ s) '' T)).Subsingleton :=
  subsingleton_smul_zpowers_inter_smul_image_zpow
    (fun s hs s' hs' => mul_abs_sub_lt hh (hTM s hs) (hTM s' hs')) y u₀

end TauCeti
