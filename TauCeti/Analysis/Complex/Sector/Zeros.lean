/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Complex.Conformal.Rouche
import TauCeti.Analysis.Complex.Sector.Bounds

/-!
# Polar-ordered enumeration of zeros in complex sectors

Complex zeros in an open angular sector `θ₁ < arg z < θ₂` do not carry the linear order of `ℝ`,
so enumerating them requires fixing a tie-breaking order on equal-modulus circles. Because
`Complex.ext_norm_arg` recovers every complex number from its norm and principal argument in
`(-π, π]`, the polar-lexicographic relation `Complex.polarLt` (`‖w‖ < ‖z‖`, or equal norms and
`arg w < arg z`) is a strict total order on `ℂ` (`IsStrictTotalOrder ℂ Complex.polarLt`).

Whenever a function `f : ℂ → ℂ` has only finitely many sector zeros in each closed disc
`Metric.closedBall 0 R` — in particular whenever `f` is entire and not identically zero — every
`polarLt`-initial segment of its sector zero set `{z | θ₁ < arg z ∧ arg z < θ₂ ∧ f z = 0}` is
finite. This makes the 1-indexed epsilon selector `TauCeti.sectorZero θ₁ θ₂ f k` canonical:

* every zero `z` of `f` in `θ₁ < arg z < θ₂` equals `sectorZero θ₁ θ₂ f k` at rank
  `k = {w | ... ∧ w.polarLt z}.ncard + 1`, with no hypothesis that the sector contains infinitely
  many zeros (`TauCeti.exists_sectorZero_eq`);
* when the sector zero set has cardinality at least `k`, and unconditionally for all `k ≥ 1` when
  it is infinite, `sectorZero θ₁ θ₂ f k` attains its defining predicate, is strictly monotone with
  respect to `Complex.polarLt`, has nondecreasing norms, and satisfies
  `‖sectorZero θ₁ θ₂ f k‖ → ∞` as `k → ∞`;
* when Rouché or annular comparison discs `Metric.ball (c n) (r n)` in strictly separated annuli
  `‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1)` isolate single zeros inside the sector and exhaust all
  sector zeros of norm at least `R₀ ≤ ‖c 0‖ - r 0`, the enumeration lands inside those discs from
  index `k₀ = {w | ... ∧ ‖w‖ < R₀}.ncard + 1` onward and its norms are strictly increasing for all
  `k ≥ k₀` (`TauCeti.sectorZero_mem_ball_of_annular_discs`,
  `TauCeti.sectorZero_mem_ball_of_rouche`).

The last section evaluates `sectorZero` and exercises the Rouché annular localization on rotated
cosines `z ↦ cos (exp (-i θ) * z)` along any ray `0 ≤ θ₁ < θ < θ₂ ≤ π`.
-/

public section

open Complex Metric Set Filter

/-! ### The polar-lexicographic strict total order on `ℂ` -/

namespace Complex

/-- Polar-lexicographic strict order on `ℂ`: `w.polarLt z` holds when `‖w‖ < ‖z‖`, or when
`‖w‖ = ‖z‖` and `w.arg < z.arg`. -/
def polarLt (w z : ℂ) : Prop :=
  ‖w‖ < ‖z‖ ∨ ‖w‖ = ‖z‖ ∧ w.arg < z.arg

/-- Unfolding lemma for `Complex.polarLt`. -/
theorem polarLt_def (w z : ℂ) :
    w.polarLt z ↔ ‖w‖ < ‖z‖ ∨ ‖w‖ = ‖z‖ ∧ w.arg < z.arg := Iff.rfl

/-- `Complex.polarLt` is a strict total order on `ℂ`. -/
instance instIsStrictTotalOrderPolarLt : IsStrictTotalOrder ℂ polarLt where
  irrefl z hz := by
    rcases hz with h | ⟨_, h⟩ <;> exact lt_irrefl _ h
  trans a b c hab hbc := by
    rcases hab with hab | ⟨hab_n, hab_a⟩ <;> rcases hbc with hbc | ⟨hbc_n, hbc_a⟩
    · exact .inl (hab.trans hbc)
    · exact .inl (hab.trans_eq hbc_n)
    · exact .inl (hab_n.trans_lt hbc)
    · exact .inr ⟨hab_n.trans hbc_n, hab_a.trans hbc_a⟩
  trichotomous w z hwz hzw := by
    have hn : ‖w‖ = ‖z‖ := le_antisymm
      (not_lt.mp fun h => hzw (.inl h))
      (not_lt.mp fun h => hwz (.inl h))
    have ha : w.arg = z.arg := le_antisymm
      (not_lt.mp fun h => hzw (.inr ⟨hn.symm, h⟩))
      (not_lt.mp fun h => hwz (.inr ⟨hn, h⟩))
    exact ext_norm_arg hn ha

/-- Strict norm inequality implies `Complex.polarLt`. -/
theorem polarLt_of_norm_lt {w z : ℂ} (h : ‖w‖ < ‖z‖) : w.polarLt z := .inl h

/-- Equal norms and strict argument inequality imply `Complex.polarLt`. -/
theorem polarLt_of_norm_eq_of_arg_lt {w z : ℂ} (hn : ‖w‖ = ‖z‖) (ha : w.arg < z.arg) :
    w.polarLt z := .inr ⟨hn, ha⟩

/-- `Complex.polarLt` is compatible with nondecreasing norms. -/
theorem polarLt.norm_le {w z : ℂ} (h : w.polarLt z) : ‖w‖ ≤ ‖z‖ :=
  h.elim le_of_lt fun h' => h'.1.le

/-- Nothing precedes `0` in `Complex.polarLt`. -/
@[simp]
theorem not_polarLt_zero (w : ℂ) : ¬ w.polarLt 0 := by
  rintro (h | ⟨hn, ha⟩)
  · exact (norm_nonneg w).not_gt (by simpa using h)
  · rw [norm_zero, norm_eq_zero] at hn
    subst hn
    exact lt_irrefl _ ha

/-- `0` precedes every nonzero complex number in `Complex.polarLt`. -/
@[simp]
theorem zero_polarLt_iff {z : ℂ} : (0 : ℂ).polarLt z ↔ z ≠ 0 := by
  refine ⟨fun h hz => not_polarLt_zero 0 (hz ▸ h), fun hz => .inl ?_⟩
  simpa using norm_pos_iff.mpr hz

/-- Along a single ray (`w.arg = z.arg`), `Complex.polarLt` reduces to strict norm comparison. -/
theorem polarLt_iff_of_arg_eq {w z : ℂ} (h : w.arg = z.arg) : w.polarLt z ↔ ‖w‖ < ‖z‖ :=
  ⟨fun hp => hp.elim id fun ⟨_, ha⟩ => absurd (h ▸ ha) (lt_irrefl _), .inl⟩

/-- On a circle (`‖w‖ = ‖z‖`), `Complex.polarLt` reduces to strict argument comparison. -/
theorem polarLt_iff_of_norm_eq {w z : ℂ} (h : ‖w‖ = ‖z‖) : w.polarLt z ↔ w.arg < z.arg :=
  ⟨fun hp => hp.elim (fun hn => absurd (h ▸ hn) (lt_irrefl _)) And.right, fun ha => .inr ⟨h, ha⟩⟩

end Complex

/-! ### Polar-ordered enumeration of zeros in an open sector -/

namespace TauCeti

/-- The `k`-th zero (`k ≥ 1`) of `f : ℂ → ℂ` in the open sector `θ₁ < arg z < θ₂`, ordered
primarily by norm and secondarily by principal argument via `Classical.epsilon`. -/
noncomputable def sectorZero (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon fun z : ℂ =>
    (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
        (‖w‖ < ‖z‖ ∨ ‖w‖ = ‖z‖ ∧ w.arg < z.arg)}.ncard = k - 1

/-- Defining expression for `TauCeti.sectorZero`. -/
theorem sectorZero_def (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) (k : ℕ) :
    sectorZero θ₁ θ₂ f k =
      Classical.epsilon fun z : ℂ =>
        (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧
          {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
            (‖w‖ < ‖z‖ ∨ ‖w‖ = ‖z‖ ∧ w.arg < z.arg)}.ncard = k - 1 := (rfl)

/-- An entire function that is not identically zero has only finitely many zeros of norm at most
`R` in any sector. -/
theorem finite_sectorZeros_of_differentiable {θ₁ θ₂ : ℝ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : ∃ z₀ : ℂ, f z₀ ≠ 0) (R : ℝ) :
    {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hA : AnalyticOnNhd ℂ f univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  refine (hA.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (mem_univ z₀) hz₀
    (isCompact_closedBall 0 R) (subset_univ _)).subset fun z hz => ?_
  exact ⟨mem_closedBall_zero_iff.mpr hz.2, hz.1.2.2⟩

section LocallyFinite

variable {θ₁ θ₂ : ℝ} {f : ℂ → ℂ}

/-- Every `Complex.polarLt`-initial segment of a locally norm-finite sector zero set is finite. -/
theorem finite_sectorZeroInit
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite) (z : ℂ) :
    {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.Finite :=
  (hfin ‖z‖).subset fun _ hw => ⟨hw.1, hw.2.norm_le⟩

/-- Strict `Complex.polarLt` inequality between two sector zeros gives strict inequality between
the cardinalities of their initial segments. -/
theorem ncard_sectorZeroInit_lt
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z₁ z₂ : ℂ} (hz₁ : θ₁ < z₁.arg ∧ z₁.arg < θ₂ ∧ f z₁ = 0)
    (h12 : z₁.polarLt z₂) :
    {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₁}.ncard <
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₂}.ncard := by
  refine Set.ncard_lt_ncard ⟨fun w hw => ⟨hw.1, IsTrans.trans _ _ _ hw.2 h12⟩, ?_⟩
    (finite_sectorZeroInit hfin z₂)
  intro hsub
  exact irrefl z₁ (hsub ⟨hz₁, h12⟩).2

/-- Two zeros in the same sector with equal initial-segment cardinalities coincide. -/
theorem eq_of_mem_sectorZeros_of_ncard_eq
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z₁ z₂ : ℂ} (hz₁ : θ₁ < z₁.arg ∧ z₁.arg < θ₂ ∧ f z₁ = 0)
    (hz₂ : θ₁ < z₂.arg ∧ z₂.arg < θ₂ ∧ f z₂ = 0)
    (hcard : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₁}.ncard =
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₂}.ncard) :
    z₁ = z₂ :=
  Std.Trichotomous.trichotomous (r := Complex.polarLt) z₁ z₂
    (fun h12 => (ncard_sectorZeroInit_lt hfin hz₁ h12).ne hcard)
    (fun h21 => (ncard_sectorZeroInit_lt hfin hz₂ h21).ne hcard.symm)

/-- If `z` is a zero of `f` in `θ₁ < arg z < θ₂` whose `polarLt`-initial segment has cardinality
`k - 1` (`1 ≤ k`), then `sectorZero θ₁ θ₂ f k = z`. -/
theorem sectorZero_eq_of_ncard
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z : ℂ} {k : ℕ} (hz : θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0)
    (hcard : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1) :
    sectorZero θ₁ θ₂ f k = z := by
  let P : ℂ → Prop := fun u =>
    (θ₁ < u.arg ∧ u.arg < θ₂ ∧ f u = 0) ∧
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt u}.ncard = k - 1
  have hPz : P z := ⟨hz, hcard⟩
  have hPe : P (sectorZero θ₁ θ₂ f k) := Classical.epsilon_spec ⟨z, hPz⟩
  exact eq_of_mem_sectorZeros_of_ncard_eq hfin hPe.1 hz (hPe.2.trans hcard.symm)

/-- **Unconditional completeness of `sectorZero`.** Every zero `z` of `f` in `θ₁ < arg z < θ₂`
appears in the sequence `sectorZero θ₁ θ₂ f k` at a positive index `k ≥ 1`, without assuming that
`f` has infinitely many zeros in the sector. -/
theorem exists_sectorZero_eq
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z : ℂ} (h₁ : θ₁ < z.arg) (h₂ : z.arg < θ₂) (hfz : f z = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ sectorZero θ₁ θ₂ f k = z :=
  ⟨{w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard + 1,
    Nat.le_add_left 1 _,
    sectorZero_eq_of_ncard hfin ⟨h₁, h₂, hfz⟩ rfl⟩

/-- When `1 ≤ k` and the sector zero set has extended cardinality at least `k`, some zero in the
sector has initial-segment cardinality `k - 1`. -/
private theorem exists_mem_sectorZeros_ncard_eq
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard) :
    ∃ z : ℂ, (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1 := by
  classical
  set S : Set ℂ := {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}
  obtain ⟨t, hts, hte⟩ := Set.exists_subset_encard_eq hle
  have ht_fin : t.Finite := Set.encard_lt_top_iff.mp (hte ▸ WithTop.coe_lt_top k)
  obtain ⟨R, htR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp ht_fin.isBounded
  set F : Finset ℂ := (hfin R).toFinset
  have htF : t ⊆ (F : Set ℂ) := fun z hz =>
    (hfin R).mem_toFinset.mpr ⟨hts hz, mem_closedBall_zero_iff.mp (htR hz)⟩
  have hk_le : k ≤ F.card := by
    have h1 : t.encard ≤ (F : Set ℂ).encard := Set.encard_mono htF
    rw [hte, Set.encard_coe_eq_coe_finsetCard] at h1
    exact Nat.cast_le.mp h1
  let rk : ℂ → ℕ := fun z => {w ∈ S | w.polarLt z}.ncard
  have hmaps : Set.MapsTo rk (F : Set ℂ) (Finset.range F.card : Set ℕ) := by
    intro z hz
    have hzR : z ∈ S ∧ ‖z‖ ≤ R := (hfin R).mem_toFinset.mp (Finset.mem_coe.mp hz)
    have hss : {w ∈ S | w.polarLt z} ⊂ (F : Set ℂ) :=
      ⟨fun w hw => Finset.mem_coe.mpr ((hfin R).mem_toFinset.mpr ⟨hw.1, hw.2.norm_le.trans hzR.2⟩),
        fun hsub => irrefl z (hsub hz).2⟩
    have hlt := Set.ncard_lt_ncard hss F.finite_toSet
    rw [Set.ncard_coe_finset] at hlt
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr hlt)
  have hinj : Set.InjOn rk (F : Set ℂ) := fun z₁ hz₁ z₂ hz₂ hEq =>
    eq_of_mem_sectorZeros_of_ncard_eq hfin
      ((hfin R).mem_toFinset.mp (Finset.mem_coe.mp hz₁)).1
      ((hfin R).mem_toFinset.mp (Finset.mem_coe.mp hz₂)).1 hEq
  have hsurj := Finset.surjOn_of_injOn_of_card_le rk hmaps hinj (by simp)
  have hk_mem : k - 1 ∈ (Finset.range F.card : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
  obtain ⟨z, hzF, hz_rk⟩ := hsurj hk_mem
  exact ⟨z, ((hfin R).mem_toFinset.mp (Finset.mem_coe.mp hzF)).1, hz_rk⟩

/-- When `1 ≤ k` and `(k : ℕ∞) ≤ {z | θ₁ < arg z ∧ arg z < θ₂ ∧ f z = 0}.encard`, the epsilon
`sectorZero θ₁ θ₂ f k` attains its defining predicate. -/
theorem sectorZero_spec_of_le_encard
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard) :
    (θ₁ < (sectorZero θ₁ θ₂ f k).arg ∧ (sectorZero θ₁ θ₂ f k).arg < θ₂ ∧
        f (sectorZero θ₁ θ₂ f k) = 0) ∧
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
        w.polarLt (sectorZero θ₁ θ₂ f k)}.ncard = k - 1 :=
  Classical.epsilon_spec (exists_mem_sectorZeros_ncard_eq hfin hk hle)

/-! ### Properties when the sector zero set is infinite -/

/-- When `f` has infinitely many zeros in `θ₁ < arg z < θ₂` (and locally finitely many by norm),
`sectorZero θ₁ θ₂ f k` attains its defining predicate for every `k ≥ 1`. -/
theorem sectorZero_spec_of_infinite
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    (θ₁ < (sectorZero θ₁ θ₂ f k).arg ∧ (sectorZero θ₁ θ₂ f k).arg < θ₂ ∧
        f (sectorZero θ₁ θ₂ f k) = 0) ∧
      {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
        w.polarLt (sectorZero θ₁ θ₂ f k)}.ncard = k - 1 :=
  sectorZero_spec_of_le_encard hfin hk (by simp [hinf.encard_eq])

/-- Under `Infinite`, `sectorZero θ₁ θ₂ f` is strictly increasing with respect to
`Complex.polarLt` on `{k | 1 ≤ k}`. -/
theorem polarLt_sectorZero_of_lt
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    (sectorZero θ₁ θ₂ f j).polarLt (sectorZero θ₁ θ₂ f k) := by
  have hspec_j := sectorZero_spec_of_infinite hfin hinf hj
  have hspec_k := sectorZero_spec_of_infinite hfin hinf (hj.trans hjk.le)
  by_contra hnot
  rcases eq_or_ne (sectorZero θ₁ θ₂ f j) (sectorZero θ₁ θ₂ f k) with hEq | hNe
  · have : j - 1 = k - 1 := by rw [← hspec_j.2, hEq, hspec_k.2]
    omega
  · have hkj : (sectorZero θ₁ θ₂ f k).polarLt (sectorZero θ₁ θ₂ f j) := by
      by_contra hnot'
      exact hNe (Std.Trichotomous.trichotomous _ _ hnot hnot')
    have hlt := ncard_sectorZeroInit_lt hfin hspec_k.1 hkj
    rw [hspec_k.2, hspec_j.2] at hlt
    omega

/-- Under `Infinite`, `sectorZero θ₁ θ₂ f` is injective on `Set.Ici 1`. -/
theorem injOn_sectorZero_Ici
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite) :
    Set.InjOn (sectorZero θ₁ θ₂ f) (Set.Ici 1) := by
  intro j hj k hk hEq
  rcases lt_trichotomy j k with hlt | rfl | hgt
  · exact absurd (hEq ▸ polarLt_sectorZero_of_lt hfin hinf hj hlt) (irrefl _)
  · rfl
  · exact absurd (hEq ▸ polarLt_sectorZero_of_lt hfin hinf hk hgt) (irrefl _)

/-- Under `Infinite`, every zero `z` of `f` in `θ₁ < arg z < θ₂` appears at a *unique* positive
index `k ≥ 1`. -/
theorem existsUnique_sectorZero_eq_of_infinite
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {z : ℂ} (h₁ : θ₁ < z.arg) (h₂ : z.arg < θ₂) (hfz : f z = 0) :
    ∃! k : ℕ, 1 ≤ k ∧ sectorZero θ₁ θ₂ f k = z := by
  obtain ⟨k, hk, hk_eq⟩ := exists_sectorZero_eq hfin h₁ h₂ hfz
  exact ⟨k, ⟨hk, hk_eq⟩, fun m ⟨hm, hm_eq⟩ =>
    injOn_sectorZero_Ici hfin hinf hm hk (hm_eq.trans hk_eq.symm)⟩

/-- Under `Infinite`, the norms `‖sectorZero θ₁ θ₂ f k‖` are nondecreasing for `k ≥ 1`. -/
theorem norm_sectorZero_le_norm_sectorZero
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖sectorZero θ₁ θ₂ f j‖ ≤ ‖sectorZero θ₁ θ₂ f k‖ := by
  rcases hjk.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (polarLt_sectorZero_of_lt hfin hinf hj hlt).norm_le

/-- Stepwise norm monotonicity `‖sectorZero θ₁ θ₂ f k‖ ≤ ‖sectorZero θ₁ θ₂ f (k + 1)‖` for
`k ≥ 1`. -/
theorem norm_sectorZero_le_succ
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖sectorZero θ₁ θ₂ f k‖ ≤ ‖sectorZero θ₁ θ₂ f (k + 1)‖ :=
  norm_sectorZero_le_norm_sectorZero hfin hinf hk (Nat.le_succ k)

/-- Under `Infinite` and local norm-finiteness, `‖sectorZero θ₁ θ₂ f k‖ → ∞` as `k → ∞`. -/
theorem tendsto_norm_sectorZero_atTop
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite) :
    Tendsto (fun k : ℕ => ‖sectorZero θ₁ θ₂ f k‖) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  let B := {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}
  refine ⟨B.ncard + 2, fun k hk => ?_⟩
  by_contra! hlt
  have hspec := sectorZero_spec_of_infinite hfin hinf (by omega : 1 ≤ k)
  have hsub : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
      w.polarLt (sectorZero θ₁ θ₂ f k)} ⊂ B := by
    refine ⟨fun w hw => ⟨hw.1, hw.2.norm_le.trans hlt.le⟩, fun hB => ?_⟩
    exact irrefl _ (hB ⟨hspec.1, hlt.le⟩).2
  have hcard := Set.ncard_lt_ncard hsub (hfin R)
  rw [hspec.2] at hcard
  omega

/-! ### Annular disc and Rouché localization -/

/-- Norm bounds for a point in `Metric.ball c r`. -/
private theorem norm_bounds_of_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) :
    ‖c‖ - r < ‖z‖ ∧ ‖z‖ < ‖c‖ + r := by
  have h := mem_ball_iff_norm.mp hz
  have h1 := norm_sub_norm_le z c
  have h2 := norm_sub_norm_le c z
  rw [norm_sub_rev] at h2
  exact ⟨by linarith, by linarith⟩

/-- Monotonicity of inner annular radii `‖c n‖ - r n` under `0 < r n` and annular separation. -/
private theorem annular_inner_mono {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    {m n : ℕ} (hmn : m ≤ n) :
    ‖c m‖ - r m ≤ ‖c n‖ - r n :=
  Nat.le_induction le_rfl (fun k _ ih => ih.trans (by linarith [hr k, hsep k])) n hmn

/-- Strict separation `‖c m‖ + r m < ‖c n‖ - r n` for `m < n`. -/
private theorem annular_outer_lt_inner {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    {m n : ℕ} (hmn : m < n) :
    ‖c m‖ + r m < ‖c n‖ - r n :=
  (hsep m).trans_le (annular_inner_mono hr hsep hmn)

/-- A sequence of annularly separated discs inside `θ₁ < arg z < θ₂`, each containing a zero of `f`,
forces `f` to have infinitely many zeros in that sector. -/
theorem infinite_sectorZeros_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hex : ∀ n, ∃ z ∈ ball (c n) (r n), f z = 0) :
    {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite := by
  choose zSeq hz_ball hz_zero using hex
  have hr : ∀ n, 0 < r n := fun n => pos_of_mem_ball (hz_ball n)
  have hstrict : StrictMono fun n => ‖zSeq n‖ := fun m n hmn =>
    (norm_bounds_of_mem_ball (hz_ball m)).2.trans <|
      (annular_outer_lt_inner hr hsep hmn).trans (norm_bounds_of_mem_ball (hz_ball n)).1
  have hinj : Function.Injective zSeq := fun m n hEq => hstrict.injective (congrArg norm hEq)
  exact (Set.infinite_range_of_injective hinj).mono <| by
    rintro _ ⟨n, rfl⟩
    exact ⟨(hsub n _ (hz_ball n)).1, (hsub n _ (hz_ball n)).2, hz_zero n⟩

/-- **Annular disc localization of `sectorZero`.** Suppose `ball (c n) (r n)` lies in the sector
`θ₁ < arg z < θ₂`, satisfies `‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1)`, contains a unique zero of
`f`, and that every sector zero of norm at least `R₀` (`R₀ ≤ ‖c 0‖ - r 0`) belongs to one of these
discs. Setting `k₀ = {w | (θ₁ < arg w ∧ arg w < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1`, the
`(k₀ + n)`-th sector zero lies in `ball (c n) (r n)` for every `n : ℕ`. -/
theorem sectorZero_mem_ball_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, θ₁ < z.arg → z.arg < θ₂ → f z = 0 → R₀ ≤ ‖z‖ → ∃ n, z ∈ ball (c n) (r n))
    (n : ℕ) :
    sectorZero θ₁ θ₂ f
      ({w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1 + n) ∈
        ball (c n) (r n) := by
  let zSeq : ℕ → ℂ := fun m => Classical.choose (huniq m)
  have hz_spec : ∀ m, (zSeq m ∈ ball (c m) (r m) ∧ f (zSeq m) = 0) ∧
      ∀ y, y ∈ ball (c m) (r m) ∧ f y = 0 → y = zSeq m :=
    fun m => Classical.choose_spec (huniq m)
  have hr : ∀ m, 0 < r m := fun m => pos_of_mem_ball (hz_spec m).1.1
  have hzS : ∀ m, θ₁ < (zSeq m).arg ∧ (zSeq m).arg < θ₂ ∧ f (zSeq m) = 0 := fun m =>
    ⟨(hsub m _ (hz_spec m).1.1).1, (hsub m _ (hz_spec m).1.1).2, (hz_spec m).1.2⟩
  have hnorm_lt : ∀ {i j}, i < j → ‖zSeq i‖ < ‖zSeq j‖ := fun hlt =>
    (norm_bounds_of_mem_ball (hz_spec _).1.1).2.trans <|
      (annular_outer_lt_inner hr hsep hlt).trans (norm_bounds_of_mem_ball (hz_spec _).1.1).1
  have hR₀_lt : ∀ m, R₀ < ‖zSeq m‖ := fun m =>
    (hR₀.trans (annular_inner_mono hr hsep (Nat.zero_le m))).trans_lt
      (norm_bounds_of_mem_ball (hz_spec m).1.1).1
  set A : Set ℂ := {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}
  set B : Set ℂ := zSeq '' (Finset.range n : Set ℕ)
  have hInit_eq : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt (zSeq n)} = A ∪ B := by
    ext w
    constructor
    · rintro ⟨hwS, hwp⟩
      rcases lt_or_ge ‖w‖ R₀ with hwR | hwR
      · exact .inl ⟨hwS, hwR⟩
      · obtain ⟨m, hwm⟩ := hexh w hwS.1 hwS.2.1 hwS.2.2 hwR
        have hweq : w = zSeq m := (hz_spec m).2 w ⟨hwm, hwS.2.2⟩
        subst hweq
        refine .inr ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), rfl⟩
        by_contra! hnm
        rcases hnm.eq_or_lt with rfl | hlt
        · exact irrefl _ hwp
        · exact (hnorm_lt hlt).not_ge hwp.norm_le
    · rintro (⟨hwS, hwR⟩ | ⟨m, hm, rfl⟩)
      · exact ⟨hwS, .inl (hwR.trans (hR₀_lt n))⟩
      · exact ⟨hzS m, .inl (hnorm_lt (Finset.mem_range.mp (Finset.mem_coe.mp hm)))⟩
  have hdisj : Disjoint A B := Set.disjoint_left.mpr fun _ hwA ⟨m, _, hwm⟩ =>
    (hwm ▸ hwA.2).not_gt (hR₀_lt m)
  have hA_fin : A.Finite := (hfin R₀).subset fun _ hw => ⟨hw.1, hw.2.le⟩
  have hB_fin : B.Finite := (Finset.range n).finite_toSet.image zSeq
  have hinj : Function.Injective zSeq := fun i j hij => by
    rcases lt_trichotomy i j with h | rfl | h
    · exact absurd (congrArg norm hij) (hnorm_lt h).ne
    · rfl
    · exact absurd (congrArg norm hij) (hnorm_lt h).ne'
  have hcard : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt (zSeq n)}.ncard =
      A.ncard + n := by
    rw [hInit_eq, Set.ncard_union_eq hdisj hA_fin hB_fin,
      Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]
  have hEq := sectorZero_eq_of_ncard hfin (k := A.ncard + 1 + n) (hzS n) (by omega)
  exact hEq.symm ▸ (hz_spec n).1.1

/-- Under the hypotheses of `TauCeti.sectorZero_mem_ball_of_annular_discs`, the norms
`‖sectorZero θ₁ θ₂ f k‖` are **strictly** increasing from `k₀` onward. -/
theorem norm_sectorZero_lt_succ_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, θ₁ < z.arg → z.arg < θ₂ → f z = 0 → R₀ ≤ ‖z‖ → ∃ n, z ∈ ball (c n) (r n))
    {k : ℕ}
    (hk : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1 ≤ k) :
    ‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖ := by
  set k₀ := {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1
  set n := k - k₀
  have hk_eq : k = k₀ + n := (Nat.add_sub_of_le hk).symm
  have hmem₀ := sectorZero_mem_ball_of_annular_discs hfin hsub hsep huniq hR₀ hexh n
  have hmem₁ := sectorZero_mem_ball_of_annular_discs hfin hsub hsep huniq hR₀ hexh (n + 1)
  rw [hk_eq, Nat.add_assoc k₀ n 1]
  exact (norm_bounds_of_mem_ball hmem₀).2.trans <|
    (hsep n).trans (norm_bounds_of_mem_ball hmem₁).1

/-- **Rouché annular localization of `sectorZero`.** Let `g` be a comparison function having a
unique zero in each disc `ball (c n) (r n)` with nonvanishing derivative there, and let `f` satisfy
the symmetric Rouché bound `‖f z - g z‖ < ‖f z‖ + ‖g z‖` on each circle `sphere (c n) (r n)`. If
the discs lie in `θ₁ < arg z < θ₂`, sit in strictly separated annuli, and cover all sector zeros of
`f` of norm at least `R₀ ≤ ‖c 0‖ - r 0`, then from index
`k₀ = {w | (θ₁ < arg w ∧ arg w < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1` onward,
`sectorZero θ₁ θ₂ f (k₀ + n)` lies in `ball (c n) (r n)`, is a simple zero (`deriv f · ≠ 0`), and
`‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖` for all `k ≥ k₀`. -/
theorem sectorZero_mem_ball_of_rouche {g : ℂ → ℂ} {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z : ℂ | (θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hf_an : ∀ n, AnalyticOnNhd ℂ f (closedBall (c n) (r n)))
    (hg_an : ∀ n, AnalyticOnNhd ℂ g (closedBall (c n) (r n)))
    (hs : ∀ n, ∀ z ∈ sphere (c n) (r n), ‖f z - g z‖ < ‖f z‖ + ‖g z‖)
    (hg_uniq : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ g z = 0) ∧
      ∀ z ∈ ball (c n) (r n), g z = 0 → deriv g z ≠ 0)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, θ₁ < z.arg → z.arg < θ₂ → f z = 0 → R₀ ≤ ‖z‖ → ∃ n, z ∈ ball (c n) (r n)) :
    let k₀ := {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1
    (∀ n, sectorZero θ₁ θ₂ f (k₀ + n) ∈ ball (c n) (r n)) ∧
      (∀ n, deriv f (sectorZero θ₁ θ₂ f (k₀ + n)) ≠ 0) ∧
      ∀ k, k₀ ≤ k → ‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖ := by
  have hf_simple : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ f z = 0) ∧
      ∀ z ∈ ball (c n) (r n), f z = 0 → deriv f z ≠ 0 := fun n =>
    (rouche_symm_existsUnique_eq_zero_and_deriv_ne_zero_iff
      (hf_an n) (hg_an n) (hs n)).mpr (hg_uniq n)
  have hf_uniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0 := fun n => (hf_simple n).1
  have hinf : {z : ℂ | θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite :=
    infinite_sectorZeros_of_annular_discs hsub hsep fun n =>
      let ⟨z, hz, _⟩ := hf_uniq n; ⟨z, hz.1, hz.2⟩
  intro k₀
  have hmem : ∀ n, sectorZero θ₁ θ₂ f (k₀ + n) ∈ ball (c n) (r n) :=
    sectorZero_mem_ball_of_annular_discs hfin hsub hsep hf_uniq hR₀ hexh
  refine ⟨hmem, fun n => ?_, fun k hk =>
    norm_sectorZero_lt_succ_of_annular_discs hfin hsub hsep hf_uniq hR₀ hexh hk⟩
  have hspec := sectorZero_spec_of_infinite hfin hinf (by dsimp [k₀]; omega : 1 ≤ k₀ + n)
  exact (hf_simple n).2 _ (hmem n) hspec.1.2.2

end LocallyFinite

/-! ### Explicit evaluation on rotated cosines in an upper-half-plane subsector -/

section RotatedCosine

/-- The `n`-th positive-ray zero `((n + 1/2) π) exp(i θ)` of `z ↦ cos (exp (-i θ) * z)`. -/
private noncomputable def rotatedCosZero (θ : ℝ) (n : ℕ) : ℂ :=
  Complex.ofReal (((n : ℝ) + 1 / 2) * Real.pi) * Complex.exp (θ * Complex.I)

private theorem norm_rotatedCosZero (θ : ℝ) (n : ℕ) :
    ‖rotatedCosZero θ n‖ = ((n : ℝ) + 1 / 2) * Real.pi := by
  have hpos : 0 < ((n : ℝ) + 1 / 2) * Real.pi := mul_pos (by positivity) Real.pi_pos
  rw [rotatedCosZero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    mul_comm (θ : ℂ), Complex.norm_exp_I_mul_ofReal, mul_one]

private theorem arg_rotatedCosZero {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ ≤ Real.pi) (n : ℕ) :
    (rotatedCosZero θ n).arg = θ := by
  have hpos : 0 < ((n : ℝ) + 1 / 2) * Real.pi := mul_pos (by positivity) Real.pi_pos
  rw [rotatedCosZero, Complex.arg_real_mul _ hpos, Complex.arg_exp_mul_I]
  exact toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith [Real.pi_pos], by linarith⟩

/-- Classification of the sector zeros of `z ↦ cos (exp (-i θ) * z)` when
`0 ≤ θ₁ < θ < θ₂ ≤ π`: they are precisely `rotatedCosZero θ n` for `n : ℕ`. -/
private theorem mem_sectorZeros_cos_iff {θ₁ θ₂ θ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (h₁ : θ₁ < θ) (h₂ : θ < θ₂) (hθ₂ : θ₂ ≤ Real.pi) {z : ℂ} :
    (θ₁ < z.arg ∧ z.arg < θ₂ ∧ Complex.cos (Complex.exp (-(θ * Complex.I)) * z) = 0) ↔
      ∃ n : ℕ, z = rotatedCosZero θ n := by
  have hθ_pos : 0 < θ := hθ₁.trans_lt h₁
  have hθ_lt_pi : θ < Real.pi := h₂.trans_le hθ₂
  constructor
  · rintro ⟨hz₁, _, hcos⟩
    obtain ⟨m, hm⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hz_eq : z =
        Complex.ofReal ((2 * (m : ℝ) + 1) * Real.pi / 2) * Complex.exp (θ * Complex.I) := by
      have hmul : z = (Complex.exp (-(θ * Complex.I)) * z) * Complex.exp (θ * Complex.I) := by
        rw [mul_comm _ (Complex.exp (θ * Complex.I)), ← mul_assoc, ← Complex.exp_add]
        simp
      rw [hmul, hm]
      push_cast
      ring
    rcases le_or_gt 0 m with hm0 | hm_neg
    · lift m to ℕ using hm0
      refine ⟨m, ?_⟩
      rw [hz_eq, rotatedCosZero]
      congr 1
      push_cast
      ring
    · exfalso
      have hcoeff_neg : (2 * (m : ℝ) + 1) * Real.pi / 2 < 0 := by
        have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm_neg
        nlinarith [Real.pi_pos]
      have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
      have him_neg : z.im < 0 := by
        rw [hz_eq, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
        exact mul_neg_of_neg_of_pos hcoeff_neg hsin_pos
      have harg_neg : z.arg < 0 := Complex.arg_neg_iff.mpr him_neg
      linarith
  · rintro ⟨n, rfl⟩
    rw [arg_rotatedCosZero hθ_pos hθ_lt_pi.le n]
    refine ⟨h₁, h₂, Complex.cos_eq_zero_iff.mpr ⟨n, ?_⟩⟩
    rw [rotatedCosZero, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    simp
    ring

private theorem exists_int_norm_sub_rotatedCosZero {θ : ℝ} {z : ℂ}
    (hcos : Complex.cos (Complex.exp (-(θ * Complex.I)) * z) = 0) (n : ℕ) :
    ∃ m : ℤ, z = Complex.ofReal ((2 * (m : ℝ) + 1) * Real.pi / 2) * Complex.exp (θ * Complex.I) ∧
      ‖z - rotatedCosZero θ n‖ = |(m : ℝ) - (n : ℝ)| * Real.pi := by
  obtain ⟨m, hm⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hz_eq : z =
      Complex.ofReal ((2 * (m : ℝ) + 1) * Real.pi / 2) * Complex.exp (θ * Complex.I) := by
    have hmul : z = (Complex.exp (-(θ * Complex.I)) * z) * Complex.exp (θ * Complex.I) := by
      rw [mul_comm _ (Complex.exp (θ * Complex.I)), ← mul_assoc, ← Complex.exp_add]
      simp
    rw [hmul, hm]
    push_cast
    ring
  refine ⟨m, hz_eq, ?_⟩
  rw [hz_eq, rotatedCosZero, ← sub_mul, norm_mul, mul_comm (θ : ℂ),
    Complex.norm_exp_I_mul_ofReal, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have hsub_eq : |(2 * (m : ℝ) + 1) * Real.pi / 2 - ((n : ℝ) + 1 / 2) * Real.pi| =
      |((m : ℝ) - (n : ℝ)) * Real.pi| := by
    congr 1
    ring
  rw [hsub_eq, abs_mul, abs_of_pos Real.pi_pos]

private theorem existsUnique_rotatedCosZero_mem_ball {θ r₀ : ℝ}
    (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < Real.pi / 2) (n : ℕ) :
    let g : ℂ → ℂ := fun z => Complex.cos (Complex.exp (-(θ * Complex.I)) * z)
    ((∃! z, z ∈ ball (rotatedCosZero θ n) r₀ ∧ g z = 0) ∧
      ∀ z ∈ ball (rotatedCosZero θ n) r₀, g z = 0 → deriv g z ≠ 0) ∧
      ∀ z ∈ sphere (rotatedCosZero θ n) r₀, g z ≠ 0 := by
  intro g
  have hcn_zero : g (rotatedCosZero θ n) = 0 := by
    refine Complex.cos_eq_zero_iff.mpr ⟨n, ?_⟩
    rw [rotatedCosZero, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    simp
    ring
  have honly : ∀ z ∈ ball (rotatedCosZero θ n) r₀, g z = 0 → z = rotatedCosZero θ n := by
    intro z hz hgz
    obtain ⟨m, hz_eq, hdiff⟩ := exists_int_norm_sub_rotatedCosZero hgz n
    have hlt : |(m : ℝ) - (n : ℝ)| * Real.pi < Real.pi / 2 := by
      have := mem_ball_iff_norm.mp hz
      linarith
    have hmn : m = (n : ℤ) := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
      nlinarith [Real.pi_pos]
    subst hmn
    rw [hz_eq, rotatedCosZero]
    congr 1
    push_cast
    ring
  have hderiv_ne : deriv g (rotatedCosZero θ n) ≠ 0 := by
    have hd : HasDerivAt g
        (-Complex.sin (Complex.exp (-(θ * Complex.I)) * rotatedCosZero θ n) *
          (Complex.exp (-(θ * Complex.I)) * 1)) (rotatedCosZero θ n) :=
      (Complex.hasDerivAt_cos (Complex.exp (-(θ * Complex.I)) * rotatedCosZero θ n)).comp
        (rotatedCosZero θ n)
        ((hasDerivAt_id (rotatedCosZero θ n)).const_mul (Complex.exp (-(θ * Complex.I))))
    rw [hd.deriv, mul_one]
    refine mul_ne_zero (neg_ne_zero.mpr ?_) (Complex.exp_ne_zero _)
    intro hsin0
    rcases Complex.sin_eq_zero_iff_cos_eq.mp hsin0 with h1 | h1 <;>
      simp [g] at hcn_zero <;> norm_num [hcn_zero] at h1
  have hsph_ne : ∀ z ∈ sphere (rotatedCosZero θ n) r₀, g z ≠ 0 := by
    intro z hz hgz
    obtain ⟨m, _, hdiff⟩ := exists_int_norm_sub_rotatedCosZero hgz n
    have hsph : ‖z - rotatedCosZero θ n‖ = r₀ := mem_sphere_iff_norm.mp hz
    rw [hsph] at hdiff
    rcases eq_or_ne m (n : ℤ) with rfl | hne
    · simp at hdiff; linarith
    · have h1 : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
      nlinarith [Real.pi_pos]
  exact ⟨⟨⟨rotatedCosZero θ n, ⟨mem_ball_self hr₀_pos, hcn_zero⟩,
      fun z ⟨hz, hgz⟩ => honly z hz hgz⟩,
    fun z hz hgz => honly z hz hgz ▸ hderiv_ne⟩, hsph_ne⟩

private theorem exists_radius_rotatedCosZero_sector {θ₁ θ₂ θ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (h₁ : θ₁ < θ) (h₂ : θ < θ₂) (hθ₂ : θ₂ ≤ Real.pi) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < Real.pi / 2 ∧
      (∀ n, ∀ z ∈ ball (rotatedCosZero θ n) r₀, θ₁ < z.arg ∧ z.arg < θ₂) ∧
      ∀ n, ‖rotatedCosZero θ n‖ + r₀ < ‖rotatedCosZero θ (n + 1)‖ - r₀ := by
  set δ : ℝ := min (Real.pi / 2) (min (θ - θ₁) (θ₂ - θ))
  have hδ_pos : 0 < δ := by positivity [sub_pos.mpr h₁, sub_pos.mpr h₂, Real.pi_pos]
  have hsin_pos : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ_pos
    (lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos]))
  set r₀ : ℝ := (Real.pi / 4) * Real.sin δ
  have hr₀_pos : 0 < r₀ := mul_pos (by positivity [Real.pi_pos]) hsin_pos
  have hr₀_lt : r₀ < Real.pi / 2 := by
    have hsin_le : Real.sin δ ≤ 1 := Real.sin_le_one δ
    dsimp [r₀]
    nlinarith [Real.pi_pos]
  have hc_arg : ∀ n, (rotatedCosZero θ n).arg = θ :=
    arg_rotatedCosZero (hθ₁.trans_lt h₁) (h₂.trans_le hθ₂).le
  have hc_ne : ∀ n, rotatedCosZero θ n ≠ 0 := fun n h0 => by
    have := norm_rotatedCosZero θ n; rw [h0, norm_zero] at this; nlinarith [Real.pi_pos]
  refine ⟨r₀, hr₀_pos, hr₀_lt, fun n z hz => ?_, fun n => ?_⟩
  · refine Complex.arg_mem_Ioo_of_mem_ball (by linarith [Real.pi_pos]) hθ₂ (hc_ne n)
      hδ_pos (min_le_left _ _)
      (by rw [hc_arg n]; exact (min_le_right _ _).trans (min_le_left _ _))
      (by rw [hc_arg n]; exact (min_le_right _ _).trans (min_le_right _ _)) ?_ hz
    rw [norm_rotatedCosZero]
    exact mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hsin_pos.le
  · simp only [norm_rotatedCosZero]; push_cast; nlinarith [Real.pi_pos]

/-- **Explicit sector-zero enumeration for a rotated cosine.** For `0 ≤ θ₁ < θ < θ₂ ≤ π` and
every `k ≥ 1`, the `k`-th zero of `z ↦ cos (exp (-i θ) * z)` in `θ₁ < arg z < θ₂` is
`((k - 1 / 2) * π) * exp (i θ)` — proved via `TauCeti.sectorZero_mem_ball_of_rouche` and
`Complex.arg_mem_Ioo_of_mem_ball`. -/
theorem sectorZero_cos_mul_cexp_neg_mul_I {θ₁ θ₂ θ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (h₁ : θ₁ < θ) (h₂ : θ < θ₂) (hθ₂ : θ₂ ≤ Real.pi)
    {k : ℕ} (hk : 1 ≤ k) :
    sectorZero θ₁ θ₂ (fun z => Complex.cos (Complex.exp (-(θ * Complex.I)) * z)) k =
      (((k : ℝ) - 1 / 2) * Real.pi : ℂ) * Complex.exp (θ * Complex.I) := by
  set g : ℂ → ℂ := fun z => Complex.cos (Complex.exp (-(θ * Complex.I)) * z)
  have hg_diff : Differentiable ℂ g := by unfold g; fun_prop
  have hfin := finite_sectorZeros_of_differentiable (θ₁ := θ₁) (θ₂ := θ₂) hg_diff ⟨0, by simp [g]⟩
  obtain ⟨r₀, hr₀_pos, hr₀_lt, hsub, hsep⟩ := exists_radius_rotatedCosZero_sector hθ₁ h₁ h₂ hθ₂
  have hdisc := existsUnique_rotatedCosZero_mem_ball (θ := θ) hr₀_pos hr₀_lt
  have hhs : ∀ n, ∀ z ∈ sphere (rotatedCosZero θ n) r₀, ‖g z - g z‖ < ‖g z‖ + ‖g z‖ :=
    fun n z hz => by
      have hne := (hdisc n).2 z hz
      simpa using add_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hne)
  have hg_an : ∀ n, AnalyticOnNhd ℂ g (closedBall (rotatedCosZero θ n) r₀) := fun _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg_diff).mono (subset_univ _)
  have hexh : ∀ z, θ₁ < z.arg → z.arg < θ₂ → g z = 0 → ‖rotatedCosZero θ 0‖ - r₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (rotatedCosZero θ n) r₀ := fun z hz₁ hz₂ hgz _ => by
    obtain ⟨n, rfl⟩ := (mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂).mp ⟨hz₁, hz₂, hgz⟩
    exact ⟨n, mem_ball_self hr₀_pos⟩
  have hrouche := sectorZero_mem_ball_of_rouche hfin hg_an hg_an hhs (fun n => (hdisc n).1)
    hsub hsep le_rfl hexh
  have hk₀_eq : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ g w = 0) ∧
      ‖w‖ < ‖rotatedCosZero θ 0‖ - r₀}.ncard + 1 = 1 := by
    suffices h_emp : {w : ℂ | (θ₁ < w.arg ∧ w.arg < θ₂ ∧ g w = 0) ∧
        ‖w‖ < ‖rotatedCosZero θ 0‖ - r₀} = ∅ by simp [h_emp]
    ext w
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hwS hw_lt
    obtain ⟨n, rfl⟩ := (mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂).mp hwS
    simp only [norm_rotatedCosZero] at hw_lt
    nlinarith [Real.pi_pos, hr₀_pos]
  set n := k - 1
  have hk_n : k = 1 + n := by omega
  have hmem := hrouche.1 n
  rw [hk₀_eq, ← hk_n] at hmem
  have hinf := infinite_sectorZeros_of_annular_discs hsub hsep fun m =>
    let ⟨z, hz, _⟩ := (hdisc m).1.1; ⟨z, hz.1, hz.2⟩
  have hspec := sectorZero_spec_of_infinite hfin hinf hk
  have h_eq : sectorZero θ₁ θ₂ g k = rotatedCosZero θ n :=
    (hdisc n).1.1.unique ⟨hmem, hspec.1.2.2⟩
      ⟨mem_ball_self hr₀_pos, ((mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂).mpr ⟨n, rfl⟩).2.2⟩
  rw [h_eq, rotatedCosZero]
  congr 1
  have hk_cast : (k : ℂ) = (n : ℂ) + 1 := by exact_mod_cast hk_n.trans (Nat.add_comm 1 n)
  push_cast
  rw [hk_cast]
  ring

end RotatedCosine

end TauCeti
