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

/-!
# Polar-ordered enumeration of zeros in complex sectors

Complex zeros in an open angular sector `z ≠ 0`, `θ₁ < arg z < θ₂` do not carry the linear order of
`ℝ`, so enumerating them requires fixing a tie-breaking order on equal-modulus circles. Because
`Complex.ext_norm_arg` recovers every complex number from its norm and principal argument in
`(-π, π]`, the polar-lexicographic relation `Complex.polarLt` (`‖w‖ < ‖z‖`, or equal norms and
`arg w < arg z`) is a strict total order on `ℂ` (`IsStrictTotalOrder ℂ Complex.polarLt`).

Whenever a function `f : ℂ → ℂ` has only finitely many sector zeros in each closed disc
`Metric.closedBall 0 R` — in particular whenever `f` is entire and not identically zero — every
`polarLt`-initial segment of its sector zero set
`{z | z ≠ 0 ∧ θ₁ < arg z ∧ arg z < θ₂ ∧ f z = 0}` is finite. This makes the 1-indexed epsilon
selector `TauCeti.sectorZero θ₁ θ₂ f k` canonical:

* under local norm-finiteness, every zero `z ≠ 0` of `f` in `θ₁ < arg z < θ₂` equals
  `sectorZero θ₁ θ₂ f k` at rank `k = {w | ... ∧ w.polarLt z}.ncard + 1`, with no hypothesis that
  the sector contains infinitely many zeros (`TauCeti.exists_sectorZero_eq`);
* under local norm-finiteness, for `1 ≤ k` with
  `(k : ℕ∞) ≤ {z | z ≠ 0 ∧ θ₁ < arg z ∧ arg z < θ₂ ∧ f z = 0}.encard`, `sectorZero θ₁ θ₂ f k`
  attains its defining predicate (`TauCeti.sectorZero_spec_of_le_encard`), is strictly
  `Complex.polarLt`-monotone and injective on such indices
  (`TauCeti.polarLt_sectorZero_of_lt_of_le_encard`, `TauCeti.injOn_sectorZero`), and has
  nondecreasing norms (`TauCeti.norm_sectorZero_le_norm_sectorZero_of_le_encard`);
* when the sector zero set is additionally infinite, these properties hold for all `k ≥ 1`, every
  sector zero appears at a unique positive index (`TauCeti.existsUnique_sectorZero_eq_of_infinite`),
  and `‖sectorZero θ₁ θ₂ f k‖ → ∞` as `k → ∞` (`TauCeti.tendsto_norm_sectorZero_atTop`);
* when Rouché or annular comparison discs `Metric.ball (c n) (r n)` in strictly separated annuli
  `‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1)` isolate single zeros inside the open sector
  `z ≠ 0 ∧ θ₁ < arg z ∧ arg z < θ₂` and exhaust all sector zeros of norm at least
  `R₀ ≤ ‖c 0‖ - r 0`, the enumeration lands inside those discs from index
  `k₀ = {w | ... ∧ ‖w‖ < R₀}.ncard + 1` onward and its norms are strictly increasing for all
  `k ≥ k₀` (`TauCeti.sectorZero_mem_ball_of_annular_discs`,
  `TauCeti.sectorZero_mem_ball_of_rouche`).

The last section evaluates `sectorZero` explicitly on the ray comparison model
`z ↦ cos (exp (-i θ) * z)` along any ray `-π ≤ θ₁ < θ < θ₂ ≤ π` whose open sector excludes the
opposite ray (`θ - θ₁ ≤ π`, `θ₂ - θ ≤ π`) (`TauCeti.sectorZero_cos_cexp_neg_mul_I_mul`).
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
@[grind =]
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

/-- `Complex.polarLt` is irreflexive. -/
@[simp]
theorem not_polarLt_self (z : ℂ) : ¬ z.polarLt z := irrefl z

/-- `Complex.polarLt` is transitive. -/
theorem polarLt.trans {a b c : ℂ} (hab : a.polarLt b) (hbc : b.polarLt c) : a.polarLt c :=
  IsTrans.trans a b c hab hbc

/-- `Complex.polarLt` is asymmetric. -/
theorem polarLt.asymm {w z : ℂ} (h : w.polarLt z) : ¬ z.polarLt w :=
  fun h' => not_polarLt_self w (h.trans h')

/-- `Complex.polarLt`-comparable complex numbers are distinct. -/
theorem polarLt.ne {w z : ℂ} (h : w.polarLt z) : w ≠ z :=
  fun hEq => not_polarLt_self w (hEq ▸ h)

/-- Trichotomy for `Complex.polarLt`. -/
theorem polarLt_trichotomy (w z : ℂ) : w.polarLt z ∨ w = z ∨ z.polarLt w := by
  by_cases h1 : w.polarLt z
  · exact .inl h1
  · by_cases h2 : z.polarLt w
    · exact .inr (.inr h2)
    · exact .inr (.inl (Std.Trichotomous.trichotomous w z h1 h2))

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

/-- The `k`-th zero (`k ≥ 1`) of `f : ℂ → ℂ` in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`, ordered
by `Complex.polarLt` via `Classical.epsilon`. -/
noncomputable def sectorZero (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon fun z : ℂ =>
    (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1

/-- Defining expression for `TauCeti.sectorZero`. -/
theorem sectorZero_def (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) (k : ℕ) :
    sectorZero θ₁ θ₂ f k =
      Classical.epsilon fun z : ℂ =>
        (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧
          {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1 :=
  (rfl)

/-- An entire function that is not identically zero has only finitely many zeros of norm at most
`R` in any open sector `z ≠ 0`, `θ₁ < arg z < θ₂`. -/
theorem finite_sectorZeros_of_differentiable {θ₁ θ₂ : ℝ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : ∃ z₀ : ℂ, f z₀ ≠ 0) (R : ℝ) :
    {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hA : AnalyticOnNhd ℂ f univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  refine (hA.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (mem_univ z₀) hz₀
    (isCompact_closedBall 0 R) (subset_univ _)).subset fun z hz => ?_
  exact ⟨mem_closedBall_zero_iff.mpr hz.2, hz.1.2.2.2⟩

section LocallyFinite

variable {θ₁ θ₂ : ℝ} {f : ℂ → ℂ}

/-- Every `Complex.polarLt`-initial segment of a locally norm-finite sector zero set is finite. -/
theorem finite_sectorZeroInit
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (z : ℂ) :
    {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.Finite :=
  (hfin ‖z‖).subset fun _ hw => ⟨hw.1, hw.2.norm_le⟩

/-- Under local norm-finiteness, strict `Complex.polarLt` inequality between two sector zeros gives
strict inequality between the cardinalities of their initial segments. -/
theorem ncard_sectorZeroInit_lt
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0 ∧ θ₁ < z₁.arg ∧ z₁.arg < θ₂ ∧ f z₁ = 0)
    (h12 : z₁.polarLt z₂) :
    {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₁}.ncard <
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₂}.ncard := by
  refine Set.ncard_lt_ncard ⟨fun w hw => ⟨hw.1, hw.2.trans h12⟩, ?_⟩
    (finite_sectorZeroInit hfin z₂)
  intro hsub
  exact Complex.not_polarLt_self z₁ (hsub ⟨hz₁, h12⟩).2

/-- Under local norm-finiteness, two zeros in the same open sector with equal initial-segment
cardinalities coincide. -/
theorem eq_of_mem_sectorZeros_of_ncard_eq
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0 ∧ θ₁ < z₁.arg ∧ z₁.arg < θ₂ ∧ f z₁ = 0)
    (hz₂ : z₂ ≠ 0 ∧ θ₁ < z₂.arg ∧ z₂.arg < θ₂ ∧ f z₂ = 0)
    (hcard : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₁}.ncard =
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z₂}.ncard) :
    z₁ = z₂ := by
  rcases Complex.polarLt_trichotomy z₁ z₂ with h12 | rfl | h21
  · exact absurd hcard (ncard_sectorZeroInit_lt hfin hz₁ h12).ne
  · rfl
  · exact absurd hcard.symm (ncard_sectorZeroInit_lt hfin hz₂ h21).ne

/-- Under local norm-finiteness, if `z ≠ 0` is a zero of `f` in `θ₁ < arg z < θ₂` whose
`polarLt`-initial segment has cardinality `k - 1`, then `sectorZero θ₁ θ₂ f k = z`. -/
theorem sectorZero_eq_of_ncard
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z : ℂ} {k : ℕ} (hz : z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0)
    (hcard : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1) :
    sectorZero θ₁ θ₂ f k = z := by
  let P : ℂ → Prop := fun u =>
    (u ≠ 0 ∧ θ₁ < u.arg ∧ u.arg < θ₂ ∧ f u = 0) ∧
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt u}.ncard = k - 1
  have hPz : P z := ⟨hz, hcard⟩
  have hPe : P (sectorZero θ₁ θ₂ f k) := Classical.epsilon_spec ⟨z, hPz⟩
  exact eq_of_mem_sectorZeros_of_ncard_eq hfin hPe.1 hz (hPe.2.trans hcard.symm)

/-- **Completeness of `sectorZero` under local norm-finiteness.** When `f` has finitely many sector
zeros in every closed ball, every zero `z ≠ 0` of `f` in `θ₁ < arg z < θ₂` appears in the sequence
`sectorZero θ₁ θ₂ f k` at a positive index `k ≥ 1`, without assuming that `f` has infinitely many
zeros in the sector. -/
theorem exists_sectorZero_eq
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {z : ℂ} (hz₀ : z ≠ 0) (h₁ : θ₁ < z.arg) (h₂ : z.arg < θ₂) (hfz : f z = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ sectorZero θ₁ θ₂ f k = z :=
  ⟨{w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard + 1,
    Nat.le_add_left 1 _,
    sectorZero_eq_of_ncard hfin ⟨hz₀, h₁, h₂, hfz⟩ rfl⟩

/-- When `1 ≤ k` and the sector zero set has extended cardinality at least `k`, some zero in the
sector has initial-segment cardinality `k - 1`. -/
private theorem exists_mem_sectorZeros_ncard_eq
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard) :
    ∃ z : ℂ, (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1 := by
  classical
  set S : Set ℂ := {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}
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
        fun hsub => Complex.not_polarLt_self z (hsub hz).2⟩
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

/-- Under local norm-finiteness, when `1 ≤ k` and
`(k : ℕ∞) ≤ {z | z ≠ 0 ∧ θ₁ < arg z ∧ arg z < θ₂ ∧ f z = 0}.encard`, the epsilon
`sectorZero θ₁ θ₂ f k` attains its defining predicate. -/
theorem sectorZero_spec_of_le_encard
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard) :
    (sectorZero θ₁ θ₂ f k ≠ 0 ∧ θ₁ < (sectorZero θ₁ θ₂ f k).arg ∧
        (sectorZero θ₁ θ₂ f k).arg < θ₂ ∧ f (sectorZero θ₁ θ₂ f k) = 0) ∧
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
        w.polarLt (sectorZero θ₁ θ₂ f k)}.ncard = k - 1 :=
  Classical.epsilon_spec (exists_mem_sectorZeros_ncard_eq hfin hk hle)

/-- Under local norm-finiteness, `sectorZero θ₁ θ₂ f` is strictly increasing with respect to
`Complex.polarLt` for `1 ≤ j < k` whenever `(k : ℕ∞)` is at most the sector zero cardinality. -/
theorem polarLt_sectorZero_of_lt_of_le_encard
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard) :
    (sectorZero θ₁ θ₂ f j).polarLt (sectorZero θ₁ θ₂ f k) := by
  have hspec_j := sectorZero_spec_of_le_encard hfin hj ((Nat.cast_le.mpr hjk.le).trans hle)
  have hspec_k := sectorZero_spec_of_le_encard hfin (hj.trans hjk.le) hle
  rcases Complex.polarLt_trichotomy (sectorZero θ₁ θ₂ f j) (sectorZero θ₁ θ₂ f k) with
    h | hEq | hkj
  · exact h
  · have : j - 1 = k - 1 := by rw [← hspec_j.2, hEq, hspec_k.2]
    omega
  · have hlt := ncard_sectorZeroInit_lt hfin hspec_k.1 hkj
    rw [hspec_k.2, hspec_j.2] at hlt
    omega

/-- Under local norm-finiteness, `sectorZero θ₁ θ₂ f` is injective on positive indices at most the
extended cardinality of the sector zero set. -/
theorem injOn_sectorZero
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite) :
    Set.InjOn (sectorZero θ₁ θ₂ f)
      {k : ℕ | 1 ≤ k ∧ (k : ℕ∞) ≤ {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard} := by
  intro j hj k hk hEq
  rcases lt_trichotomy j k with hlt | rfl | hgt
  · exact absurd (hEq ▸ polarLt_sectorZero_of_lt_of_le_encard hfin hj.1 hlt hk.2)
      (Complex.not_polarLt_self _)
  · rfl
  · exact absurd (hEq ▸ polarLt_sectorZero_of_lt_of_le_encard hfin hk.1 hgt hj.2)
      (Complex.not_polarLt_self _)

/-- Under local norm-finiteness, the norms `‖sectorZero θ₁ θ₂ f ·‖` are nondecreasing for
`1 ≤ j ≤ k` whenever `(k : ℕ∞)` is at most the sector zero cardinality. -/
theorem norm_sectorZero_le_norm_sectorZero_of_le_encard
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.encard) :
    ‖sectorZero θ₁ θ₂ f j‖ ≤ ‖sectorZero θ₁ θ₂ f k‖ := by
  rcases hjk.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (polarLt_sectorZero_of_lt_of_le_encard hfin hj hlt hle).norm_le

/-! ### Properties when the sector zero set is infinite -/

/-- When `f` has infinitely many zeros in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂` (and locally
finitely many by norm), `sectorZero θ₁ θ₂ f k` attains its defining predicate for every `k ≥ 1`. -/
theorem sectorZero_spec_of_infinite
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    (sectorZero θ₁ θ₂ f k ≠ 0 ∧ θ₁ < (sectorZero θ₁ θ₂ f k).arg ∧
        (sectorZero θ₁ θ₂ f k).arg < θ₂ ∧ f (sectorZero θ₁ θ₂ f k) = 0) ∧
      {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
        w.polarLt (sectorZero θ₁ θ₂ f k)}.ncard = k - 1 :=
  sectorZero_spec_of_le_encard hfin hk (by simp [hinf.encard_eq])

/-- Under local norm-finiteness and `Infinite`, `sectorZero θ₁ θ₂ f` is strictly increasing with
respect to `Complex.polarLt` on `{k | 1 ≤ k}`. -/
theorem polarLt_sectorZero_of_lt
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    (sectorZero θ₁ θ₂ f j).polarLt (sectorZero θ₁ θ₂ f k) :=
  polarLt_sectorZero_of_lt_of_le_encard hfin hj hjk (by simp [hinf.encard_eq])

/-- Under local norm-finiteness and `Infinite`, `sectorZero θ₁ θ₂ f` is injective on `Set.Ici 1`. -/
theorem injOn_sectorZero_Ici
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite) :
    Set.InjOn (sectorZero θ₁ θ₂ f) (Set.Ici 1) := by
  refine (injOn_sectorZero hfin).mono fun k hk => ?_
  exact ⟨hk, by simp [hinf.encard_eq]⟩

/-- Under local norm-finiteness and `Infinite`, every zero `z ≠ 0` of `f` in `θ₁ < arg z < θ₂`
appears at a *unique* positive index `k ≥ 1`. -/
theorem existsUnique_sectorZero_eq_of_infinite
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {z : ℂ} (hz₀ : z ≠ 0) (h₁ : θ₁ < z.arg) (h₂ : z.arg < θ₂) (hfz : f z = 0) :
    ∃! k : ℕ, 1 ≤ k ∧ sectorZero θ₁ θ₂ f k = z := by
  obtain ⟨k, hk, hk_eq⟩ := exists_sectorZero_eq hfin hz₀ h₁ h₂ hfz
  exact ⟨k, ⟨hk, hk_eq⟩, fun m ⟨hm, hm_eq⟩ =>
    injOn_sectorZero_Ici hfin hinf hm hk (hm_eq.trans hk_eq.symm)⟩

/-- Under local norm-finiteness and `Infinite`, the norms `‖sectorZero θ₁ θ₂ f k‖` are
nondecreasing for `k ≥ 1`. -/
theorem norm_sectorZero_le_norm_sectorZero
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖sectorZero θ₁ θ₂ f j‖ ≤ ‖sectorZero θ₁ θ₂ f k‖ :=
  norm_sectorZero_le_norm_sectorZero_of_le_encard hfin hj hjk (by simp [hinf.encard_eq])

/-- Under local norm-finiteness and `Infinite`, stepwise norm monotonicity
`‖sectorZero θ₁ θ₂ f k‖ ≤ ‖sectorZero θ₁ θ₂ f (k + 1)‖` holds for `k ≥ 1`. -/
theorem norm_sectorZero_le_succ
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖sectorZero θ₁ θ₂ f k‖ ≤ ‖sectorZero θ₁ θ₂ f (k + 1)‖ :=
  norm_sectorZero_le_norm_sectorZero hfin hinf hk (Nat.le_succ k)

/-- Under local norm-finiteness and `Infinite`, `‖sectorZero θ₁ θ₂ f k‖ → ∞` as `k → ∞`. -/
theorem tendsto_norm_sectorZero_atTop
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite) :
    Tendsto (fun k : ℕ => ‖sectorZero θ₁ θ₂ f k‖) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  let B := {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}
  refine ⟨B.ncard + 2, fun k hk => ?_⟩
  by_contra! hlt
  have hspec := sectorZero_spec_of_infinite hfin hinf (by omega : 1 ≤ k)
  have hsub : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧
      w.polarLt (sectorZero θ₁ θ₂ f k)} ⊂ B := by
    refine ⟨fun w hw => ⟨hw.1, hw.2.norm_le.trans hlt.le⟩, fun hB => ?_⟩
    exact Complex.not_polarLt_self _ (hB ⟨hspec.1, hlt.le⟩).2
  have hcard := Set.ncard_lt_ncard hsub (hfin R)
  rw [hspec.2] at hcard
  omega

/-! ### Annular disc and Rouché localization -/

/-- Points chosen from annularly separated open balls have strictly increasing norms. -/
private theorem strictMono_norm_of_mem_annular_balls {c : ℕ → ℂ} {r : ℕ → ℝ} {zSeq : ℕ → ℂ}
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hz : ∀ n, zSeq n ∈ ball (c n) (r n)) :
    StrictMono fun n => ‖zSeq n‖ :=
  strictMono_nat_of_lt_succ fun n =>
    (norm_lt_of_mem_ball (hz n)).trans <|
      (hsep n).trans (sub_lt_iff_lt_add.mpr (norm_lt_of_mem_ball (mem_ball_comm.mp (hz (n + 1)))))

/-- A sequence of annularly separated discs inside the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`, each
containing a zero of `f`, forces `f` to have infinitely many zeros in that sector. -/
theorem infinite_sectorZeros_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hex : ∀ n, ∃ z ∈ ball (c n) (r n), f z = 0) :
    {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite := by
  choose zSeq hz_ball hz_zero using hex
  have hstrict := strictMono_norm_of_mem_annular_balls hsep hz_ball
  have hinj : Function.Injective zSeq := Function.Injective.of_comp (f := norm) hstrict.injective
  exact (Set.infinite_range_of_injective hinj).mono <| by
    rintro _ ⟨n, rfl⟩
    exact ⟨(hsub n _ (hz_ball n)).1, (hsub n _ (hz_ball n)).2.1, (hsub n _ (hz_ball n)).2.2,
      hz_zero n⟩

/-- **Annular disc localization of `sectorZero`.** Under local norm-finiteness, suppose
`ball (c n) (r n)` lies in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`, satisfies
`‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1)`, contains a unique zero of `f`, and that every sector zero
of norm at least `R₀` (`R₀ ≤ ‖c 0‖ - r 0`) belongs to one of these discs. Setting
`k₀ = {w | (w ≠ 0 ∧ θ₁ < arg w ∧ arg w < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1`, the `(k₀ + n)`-th
sector zero lies in `ball (c n) (r n)` for every `n : ℕ`. -/
theorem sectorZero_mem_ball_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, z ≠ 0 → θ₁ < z.arg → z.arg < θ₂ → f z = 0 → R₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (c n) (r n))
    (n : ℕ) :
    sectorZero θ₁ θ₂ f
      ({w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1 + n) ∈
        ball (c n) (r n) := by
  let zSeq : ℕ → ℂ := fun m => Classical.choose (huniq m)
  have hz_spec : ∀ m, (zSeq m ∈ ball (c m) (r m) ∧ f (zSeq m) = 0) ∧
      ∀ y, y ∈ ball (c m) (r m) ∧ f y = 0 → y = zSeq m :=
    fun m => Classical.choose_spec (huniq m)
  have hzS : ∀ m, zSeq m ≠ 0 ∧ θ₁ < (zSeq m).arg ∧ (zSeq m).arg < θ₂ ∧ f (zSeq m) = 0 := fun m =>
    ⟨(hsub m _ (hz_spec m).1.1).1, (hsub m _ (hz_spec m).1.1).2.1,
      (hsub m _ (hz_spec m).1.1).2.2, (hz_spec m).1.2⟩
  have hstrict := strictMono_norm_of_mem_annular_balls hsep (fun m => (hz_spec m).1.1)
  have hR₀_lt : ∀ m, R₀ < ‖zSeq m‖ := fun m =>
    (hR₀.trans_lt (sub_lt_iff_lt_add.mpr
      (norm_lt_of_mem_ball (mem_ball_comm.mp (hz_spec 0).1.1)))).trans_le
      (hstrict.monotone (Nat.zero_le m))
  set A : Set ℂ := {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}
  set B : Set ℂ := zSeq '' (Finset.range n : Set ℕ)
  have hInit_eq : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt (zSeq n)} =
      A ∪ B := by
    ext w
    constructor
    · rintro ⟨hwS, hwp⟩
      rcases lt_or_ge ‖w‖ R₀ with hwR | hwR
      · exact .inl ⟨hwS, hwR⟩
      · obtain ⟨m, hwm⟩ := hexh w hwS.1 hwS.2.1 hwS.2.2.1 hwS.2.2.2 hwR
        have hweq : w = zSeq m := (hz_spec m).2 w ⟨hwm, hwS.2.2.2⟩
        subst hweq
        refine .inr ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr ?_), rfl⟩
        by_contra! hnm
        rcases hnm.eq_or_lt with rfl | hlt
        · exact Complex.not_polarLt_self _ hwp
        · exact (hstrict hlt).not_ge hwp.norm_le
    · rintro (⟨hwS, hwR⟩ | ⟨m, hm, rfl⟩)
      · exact ⟨hwS, .inl (hwR.trans (hR₀_lt n))⟩
      · exact ⟨hzS m, .inl (hstrict (Finset.mem_range.mp (Finset.mem_coe.mp hm)))⟩
  have hdisj : Disjoint A B := Set.disjoint_left.mpr fun _ hwA ⟨m, _, hwm⟩ =>
    (hwm ▸ hwA.2).not_gt (hR₀_lt m)
  have hA_fin : A.Finite := (hfin R₀).subset fun _ hw => ⟨hw.1, hw.2.le⟩
  have hB_fin : B.Finite := (Finset.range n).finite_toSet.image zSeq
  have hinj : Function.Injective zSeq := Function.Injective.of_comp (f := norm) hstrict.injective
  have hcard : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ w.polarLt (zSeq n)}.ncard =
      A.ncard + n := by
    rw [hInit_eq, Set.ncard_union_eq hdisj hA_fin hB_fin,
      Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]
  have hEq := sectorZero_eq_of_ncard hfin (k := A.ncard + 1 + n) (hzS n) (by omega)
  exact hEq.symm ▸ (hz_spec n).1.1

/-- Under the hypotheses of `TauCeti.sectorZero_mem_ball_of_annular_discs`, the norms
`‖sectorZero θ₁ θ₂ f k‖` are **strictly** increasing from `k₀` onward. -/
theorem norm_sectorZero_lt_succ_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, z ≠ 0 → θ₁ < z.arg → z.arg < θ₂ → f z = 0 → R₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (c n) (r n))
    {k : ℕ}
    (hk : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1 ≤ k) :
    ‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖ := by
  set k₀ := {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1
  set n := k - k₀
  have hk_eq : k = k₀ + n := (Nat.add_sub_of_le hk).symm
  have hmem₀ := sectorZero_mem_ball_of_annular_discs hfin hsub hsep huniq hR₀ hexh n
  have hmem₁ := sectorZero_mem_ball_of_annular_discs hfin hsub hsep huniq hR₀ hexh (n + 1)
  rw [hk_eq, Nat.add_assoc k₀ n 1]
  exact (norm_lt_of_mem_ball hmem₀).trans <|
    (hsep n).trans (sub_lt_iff_lt_add.mpr (norm_lt_of_mem_ball (mem_ball_comm.mp hmem₁)))

/-- **Rouché annular localization of `sectorZero`.** Under local norm-finiteness, let `g` be a
comparison function having a unique zero in each disc `ball (c n) (r n)` with nonvanishing
derivative there, and let `f` satisfy the symmetric Rouché bound `‖f z - g z‖ < ‖f z‖ + ‖g z‖` on
each circle `sphere (c n) (r n)`. If the discs lie in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`,
sit in strictly separated annuli, and cover all sector zeros of `f` of norm at least
`R₀ ≤ ‖c 0‖ - r 0`, then from index
`k₀ = {w | (w ≠ 0 ∧ θ₁ < arg w ∧ arg w < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1` onward,
`sectorZero θ₁ θ₂ f (k₀ + n)` lies in `ball (c n) (r n)`, is a simple zero (`deriv f · ≠ 0`), and
`‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖` for all `k ≥ k₀`. -/
theorem sectorZero_mem_ball_of_rouche {g : ℂ → ℂ} {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z : ℂ | (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hf_an : ∀ n, AnalyticOnNhd ℂ f (closedBall (c n) (r n)))
    (hg_an : ∀ n, AnalyticOnNhd ℂ g (closedBall (c n) (r n)))
    (hs : ∀ n, ∀ z ∈ sphere (c n) (r n), ‖f z - g z‖ < ‖f z‖ + ‖g z‖)
    (hg_uniq : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ g z = 0) ∧
      ∀ z ∈ ball (c n) (r n), g z = 0 → deriv g z ≠ 0)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, z ≠ 0 → θ₁ < z.arg → z.arg < θ₂ → f z = 0 → R₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (c n) (r n)) :
    let k₀ := {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1
    (∀ n, sectorZero θ₁ θ₂ f (k₀ + n) ∈ ball (c n) (r n)) ∧
      (∀ n, deriv f (sectorZero θ₁ θ₂ f (k₀ + n)) ≠ 0) ∧
      ∀ k, k₀ ≤ k → ‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖ := by
  have hf_simple : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ f z = 0) ∧
      ∀ z ∈ ball (c n) (r n), f z = 0 → deriv f z ≠ 0 := fun n =>
    (rouche_symm_existsUnique_eq_zero_and_deriv_ne_zero_iff
      (hf_an n) (hg_an n) (hs n)).mpr (hg_uniq n)
  have hf_uniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0 := fun n => (hf_simple n).1
  have hinf : {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}.Infinite :=
    infinite_sectorZeros_of_annular_discs hsub hsep fun n =>
      let ⟨z, hz, _⟩ := hf_uniq n; ⟨z, hz.1, hz.2⟩
  intro k₀
  have hmem : ∀ n, sectorZero θ₁ θ₂ f (k₀ + n) ∈ ball (c n) (r n) :=
    sectorZero_mem_ball_of_annular_discs hfin hsub hsep hf_uniq hR₀ hexh
  refine ⟨hmem, fun n => ?_, fun k hk =>
    norm_sectorZero_lt_succ_of_annular_discs hfin hsub hsep hf_uniq hR₀ hexh hk⟩
  have hspec := sectorZero_spec_of_infinite hfin hinf (by dsimp [k₀]; omega : 1 ≤ k₀ + n)
  exact (hf_simple n).2 _ (hmem n) hspec.1.2.2.2

end LocallyFinite

/-! ### Explicit evaluation on rotated cosines -/

section RotatedCosine

/-- The `n`-th positive-ray zero `((n + 1/2) π) exp(i θ)` of `z ↦ cos (exp (-i θ) * z)`. -/
private noncomputable def rotatedCosZero (θ : ℝ) (n : ℕ) : ℂ :=
  Complex.ofReal (((n : ℝ) + 1 / 2) * Real.pi) * Complex.exp (θ * Complex.I)

private theorem norm_rotatedCosZero (θ : ℝ) (n : ℕ) :
    ‖rotatedCosZero θ n‖ = ((n : ℝ) + 1 / 2) * Real.pi := by
  have hpos : 0 < ((n : ℝ) + 1 / 2) * Real.pi := mul_pos (by positivity) Real.pi_pos
  rw [rotatedCosZero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    mul_comm (θ : ℂ), Complex.norm_exp_I_mul_ofReal, mul_one]

private theorem rotatedCosZero_ne_zero (θ : ℝ) (n : ℕ) : rotatedCosZero θ n ≠ 0 := by
  intro h0
  have := norm_rotatedCosZero θ n
  rw [h0, norm_zero] at this
  nlinarith [Real.pi_pos]

private theorem arg_rotatedCosZero {θ : ℝ} (hθ₀ : -Real.pi < θ) (hθ₁ : θ ≤ Real.pi) (n : ℕ) :
    (rotatedCosZero θ n).arg = θ := by
  have hpos : 0 < ((n : ℝ) + 1 / 2) * Real.pi := mul_pos (by positivity) Real.pi_pos
  rw [rotatedCosZero, Complex.arg_ofReal_mul hpos, Complex.arg_exp_mul_I]
  exact toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith, by linarith⟩

/-- Classification of the sector zeros of `z ↦ cos (exp (-i θ) * z)` when
`-π ≤ θ₁ < θ < θ₂ ≤ π` with `θ - θ₁ ≤ π` and `θ₂ - θ ≤ π`: they are precisely
`rotatedCosZero θ n` for `n : ℕ`. -/
private theorem mem_sectorZeros_cos_iff {θ₁ θ₂ θ : ℝ}
    (hθ₁ : -Real.pi ≤ θ₁) (h₁ : θ₁ < θ) (h₂ : θ < θ₂) (hθ₂ : θ₂ ≤ Real.pi)
    (hlo : θ - θ₁ ≤ Real.pi) (hhi : θ₂ - θ ≤ Real.pi) {z : ℂ} :
    (z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ Complex.cos (Complex.exp (-(θ * Complex.I)) * z) = 0) ↔
      ∃ n : ℕ, z = rotatedCosZero θ n := by
  have hθ_gt : -Real.pi < θ := hθ₁.trans_lt h₁
  have hθ_lt : θ < Real.pi := h₂.trans_le hθ₂
  constructor
  · rintro ⟨_, hz₁, hz₂, hcos⟩
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
      have hneg : 0 < -((2 * (m : ℝ) + 1) * Real.pi / 2) := by
        have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm_neg
        nlinarith [Real.pi_pos]
      rcases le_or_gt θ 0 with hθ_le | hθ_pos
      · have hz_neg : z = Complex.ofReal (-((2 * (m : ℝ) + 1) * Real.pi / 2)) *
            Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) := by
          rw [hz_eq, Complex.ofReal_neg, Complex.ofReal_add,
            add_mul (θ : ℂ) (Real.pi : ℂ) Complex.I, Complex.exp_add, Complex.exp_pi_mul_I]
          ring
        have hz_arg : z.arg = θ + Real.pi := by
          rw [hz_neg, Complex.arg_ofReal_mul hneg, Complex.arg_exp_mul_I]
          exact toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith [Real.pi_pos], by linarith⟩
        linarith
      · have hz_neg : z = Complex.ofReal (-((2 * (m : ℝ) + 1) * Real.pi / 2)) *
            Complex.exp (((θ - Real.pi : ℝ) : ℂ) * Complex.I) := by
          rw [hz_eq, Complex.ofReal_neg, Complex.ofReal_sub,
            sub_mul (θ : ℂ) (Real.pi : ℂ) Complex.I, Complex.exp_sub, Complex.exp_pi_mul_I]
          ring
        have hz_arg : z.arg = θ - Real.pi := by
          rw [hz_neg, Complex.arg_ofReal_mul hneg, Complex.arg_exp_mul_I]
          exact toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith, by linarith [Real.pi_pos]⟩
        linarith
  · rintro ⟨n, rfl⟩
    rw [arg_rotatedCosZero hθ_gt hθ_lt.le n]
    refine ⟨rotatedCosZero_ne_zero θ n, h₁, h₂, Complex.cos_eq_zero_iff.mpr ⟨n, ?_⟩⟩
    rw [rotatedCosZero, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    simp
    ring

/-- **Explicit sector-zero enumeration for a rotated cosine.** For `-π ≤ θ₁ < θ < θ₂ ≤ π` with
`θ - θ₁ ≤ π` and `θ₂ - θ ≤ π`, and for every `k ≥ 1`, the `k`-th zero of
`z ↦ cos (exp (-i θ) * z)` in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂` is
`((k - 1 / 2) * π) * exp (i θ)`. -/
theorem sectorZero_cos_cexp_neg_mul_I_mul {θ₁ θ₂ θ : ℝ}
    (hθ₁ : -Real.pi ≤ θ₁) (h₁ : θ₁ < θ) (h₂ : θ < θ₂) (hθ₂ : θ₂ ≤ Real.pi)
    (hlo : θ - θ₁ ≤ Real.pi) (hhi : θ₂ - θ ≤ Real.pi)
    {k : ℕ} (hk : 1 ≤ k) :
    sectorZero θ₁ θ₂ (fun z => Complex.cos (Complex.exp (-(θ * Complex.I)) * z)) k =
      (((k : ℝ) - 1 / 2) * Real.pi : ℂ) * Complex.exp (θ * Complex.I) := by
  set g : ℂ → ℂ := fun z => Complex.cos (Complex.exp (-(θ * Complex.I)) * z)
  have hg_diff : Differentiable ℂ g := by unfold g; fun_prop
  have hfin := finite_sectorZeros_of_differentiable (θ₁ := θ₁) (θ₂ := θ₂) hg_diff ⟨0, by simp [g]⟩
  have hθ_gt : -Real.pi < θ := hθ₁.trans_lt h₁
  have hθ_lt : θ < Real.pi := h₂.trans_le hθ₂
  have hstrict : StrictMono fun m => ‖rotatedCosZero θ m‖ := fun i j hij => by
    simp only [norm_rotatedCosZero]
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    nlinarith [Real.pi_pos]
  have hinj : Function.Injective (rotatedCosZero θ) :=
    Function.Injective.of_comp (f := norm) hstrict.injective
  set n := k - 1
  have hmem_n : rotatedCosZero θ n ≠ 0 ∧ θ₁ < (rotatedCosZero θ n).arg ∧
      (rotatedCosZero θ n).arg < θ₂ ∧ g (rotatedCosZero θ n) = 0 :=
    (mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂ hlo hhi).mpr ⟨n, rfl⟩
  have hInit : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ g w = 0) ∧
      w.polarLt (rotatedCosZero θ n)} = rotatedCosZero θ '' (Finset.range n : Set ℕ) := by
    ext w
    constructor
    · rintro ⟨hwS, hwp⟩
      obtain ⟨m, rfl⟩ := (mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂ hlo hhi).mp hwS
      have hlt : ‖rotatedCosZero θ m‖ < ‖rotatedCosZero θ n‖ :=
        (Complex.polarLt_iff_of_arg_eq
          (by rw [arg_rotatedCosZero hθ_gt hθ_lt.le, arg_rotatedCosZero hθ_gt hθ_lt.le])).mp hwp
      exact ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr (hstrict.lt_iff_lt.mp hlt)), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨(mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂ hlo hhi).mpr ⟨m, rfl⟩,
        Complex.polarLt_of_norm_lt (hstrict (Finset.mem_range.mp (Finset.mem_coe.mp hm)))⟩
  have hcard : {w : ℂ | (w ≠ 0 ∧ θ₁ < w.arg ∧ w.arg < θ₂ ∧ g w = 0) ∧
      w.polarLt (rotatedCosZero θ n)}.ncard = k - 1 := by
    rw [hInit, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]
  have hEq : sectorZero θ₁ θ₂ g k = rotatedCosZero θ n :=
    sectorZero_eq_of_ncard hfin hmem_n hcard
  rw [hEq, rotatedCosZero]
  congr 1
  have hk_cast : (k : ℂ) = (n : ℂ) + 1 := by exact_mod_cast (by omega : k = n + 1)
  push_cast
  rw [hk_cast]
  ring

end RotatedCosine

end TauCeti
