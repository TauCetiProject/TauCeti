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
import TauCeti.Analysis.Normed.Group.BallSphere
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Order.Northcott.Enumeration

/-!
# Polar-ordered enumeration of zeros in complex sectors

Complex zeros in an open angular sector `z ≠ 0`, `θ₁ < arg z < θ₂` do not carry the linear order of
`ℝ`, so enumerating them requires fixing a tie-breaking order on equal-modulus circles. Because
`Complex.ext_norm_arg` recovers every complex number from its norm and principal argument in
`(-π, π]`, the polar-lexicographic relation `Complex.polarLt` (`‖w‖ < ‖z‖`, or equal norms and
`arg w < arg z`) is a strict total order on `ℂ` (`IsStrictTotalOrder ℂ Complex.polarLt`).

Whenever a function `f : ℂ → ℂ` has only finitely many sector zeros
`TauCeti.sectorZeros θ₁ θ₂ f` in each closed disc `Metric.closedBall 0 R` — in particular whenever
`f` is entire and not identically zero — every `polarLt`-initial segment of
`sectorZeros θ₁ θ₂ f` is finite. This makes the 1-indexed epsilon selector
`TauCeti.sectorZero θ₁ θ₂ f k` canonical:

* under local norm-finiteness, every `z ∈ sectorZeros θ₁ θ₂ f` equals `sectorZero θ₁ θ₂ f k` at
  rank `k = {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard + 1`, with no hypothesis that the sector
  contains infinitely many zeros (`TauCeti.exists_sectorZero_eq`);
* under local norm-finiteness, for `1 ≤ k` with `(k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard`,
  `sectorZero θ₁ θ₂ f k` attains its defining predicate (`TauCeti.sectorZero_spec_of_le_encard`),
  is strictly `Complex.polarLt`-monotone and bijective onto `sectorZeros θ₁ θ₂ f` on such
  indices (`TauCeti.polarLt_sectorZero_of_lt_of_le_encard`, `TauCeti.injOn_sectorZero`,
  `TauCeti.bijOn_sectorZero`), and has nondecreasing norms
  (`TauCeti.norm_sectorZero_le_norm_sectorZero_of_le_encard`);
* when `sectorZeros θ₁ θ₂ f` is additionally infinite, these properties hold for all `k ≥ 1`, every
  sector zero appears at a unique positive index (`TauCeti.existsUnique_sectorZero_eq_of_infinite`),
  and `‖sectorZero θ₁ θ₂ f k‖ → ∞` as `k → ∞` (`TauCeti.tendsto_norm_sectorZero_atTop`);
* when Rouché or annular comparison discs `Metric.ball (c n) (r n)` in strictly separated annuli
  `‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1)` isolate single zeros inside the open sector
  `z ≠ 0 ∧ θ₁ < arg z < θ₂` and exhaust all sector zeros of norm at least
  `R₀ ≤ ‖c 0‖ - r 0`, the enumeration lands inside those discs as zeros of `f` from index
  `k₀ = {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1` onward and its norms are strictly
  increasing for all `k ≥ k₀` (`TauCeti.sectorZero_mem_ball_of_annular_discs`,
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
  toLex (‖w‖, w.arg) < toLex (‖z‖, z.arg)

/-- Unfolding lemma for `Complex.polarLt`. -/
@[grind =]
theorem polarLt_def (w z : ℂ) :
    w.polarLt z ↔ ‖w‖ < ‖z‖ ∨ ‖w‖ = ‖z‖ ∧ w.arg < z.arg :=
  Prod.Lex.toLex_lt_toLex

/-- `Complex.polarLt` is a strict total order on `ℂ`. -/
instance instIsStrictTotalOrderPolarLt : IsStrictTotalOrder ℂ polarLt :=
  toLex_norm_arg_injective.isStrictTotalOrder_onFun (· < ·)

/-- Strict norm inequality implies `Complex.polarLt`. -/
theorem polarLt_of_norm_lt {w z : ℂ} (h : ‖w‖ < ‖z‖) : w.polarLt z :=
  Prod.Lex.toLex_lt_toLex.mpr (.inl h)

/-- Equal norms and strict argument inequality imply `Complex.polarLt`. -/
theorem polarLt_of_norm_eq_of_arg_lt {w z : ℂ} (hn : ‖w‖ = ‖z‖) (ha : w.arg < z.arg) :
    w.polarLt z :=
  Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨hn, ha⟩)

/-- `Complex.polarLt` is compatible with nondecreasing norms. -/
theorem polarLt.norm_le {w z : ℂ} (h : w.polarLt z) : ‖w‖ ≤ ‖z‖ :=
  ((polarLt_def w z).mp h).elim le_of_lt fun h' => h'.1.le

/-- Nothing precedes `0` in `Complex.polarLt`. -/
@[simp]
theorem not_polarLt_zero (w : ℂ) : ¬ w.polarLt 0 := by
  rw [polarLt_def]
  rintro (h | ⟨hn, ha⟩)
  · exact (norm_nonneg w).not_gt (by simpa using h)
  · rw [norm_zero, norm_eq_zero] at hn
    subst hn
    exact lt_irrefl _ ha

/-- `0` precedes every nonzero complex number in `Complex.polarLt`. -/
@[simp]
theorem zero_polarLt_iff {z : ℂ} : (0 : ℂ).polarLt z ↔ z ≠ 0 :=
  ⟨fun h hz => not_polarLt_zero 0 (hz ▸ h),
    fun hz => polarLt_of_norm_lt (by simpa using norm_pos_iff.mpr hz)⟩

/-- Along a single ray (`w.arg = z.arg`), `Complex.polarLt` reduces to strict norm comparison. -/
theorem polarLt_iff_of_arg_eq {w z : ℂ} (h : w.arg = z.arg) : w.polarLt z ↔ ‖w‖ < ‖z‖ :=
  ⟨fun hp => ((polarLt_def w z).mp hp).elim id fun ⟨_, ha⟩ => absurd (h ▸ ha) (lt_irrefl _),
    polarLt_of_norm_lt⟩

/-- On a circle (`‖w‖ = ‖z‖`), `Complex.polarLt` reduces to strict argument comparison. -/
theorem polarLt_iff_of_norm_eq {w z : ℂ} (h : ‖w‖ = ‖z‖) : w.polarLt z ↔ w.arg < z.arg :=
  ⟨fun hp => ((polarLt_def w z).mp hp).elim (fun hn => absurd (h ▸ hn) (lt_irrefl _)) And.right,
    polarLt_of_norm_eq_of_arg_lt h⟩

end Complex

/-! ### Polar-ordered enumeration of zeros in an open sector -/

namespace TauCeti

/-- The set of nonzero zeros of `f : ℂ → ℂ` in the open angular sector `θ₁ < arg z < θ₂`. -/
def sectorZeros (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0}

/-- Membership criterion for `TauCeti.sectorZeros`. -/
@[simp]
theorem mem_sectorZeros_iff {θ₁ θ₂ : ℝ} {f : ℂ → ℂ} {z : ℂ} :
    z ∈ sectorZeros θ₁ θ₂ f ↔ z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂ ∧ f z = 0 :=
  Iff.rfl

/-- The `k`-th zero (`k ≥ 1`) of `f : ℂ → ℂ` in `sectorZeros θ₁ θ₂ f`, ordered by `Complex.polarLt`
via `Classical.epsilon`. -/
noncomputable def sectorZero (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon fun z : ℂ =>
    z ∈ sectorZeros θ₁ θ₂ f ∧ {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard = k - 1

/-- Defining expression for `TauCeti.sectorZero`. -/
theorem sectorZero_def (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) (k : ℕ) :
    sectorZero θ₁ θ₂ f k =
      Classical.epsilon fun z : ℂ =>
        z ∈ sectorZeros θ₁ θ₂ f ∧ {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard = k - 1 :=
  (rfl)

/-- An entire function that is not identically zero has only finitely many sector zeros of norm at
most `R` in any open sector `z ≠ 0`, `θ₁ < arg z < θ₂`. -/
theorem finite_sectorZeros_of_differentiable {θ₁ θ₂ : ℝ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : ∃ z₀ : ℂ, f z₀ ≠ 0) (R : ℝ) :
    {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hA : AnalyticOnNhd ℂ f univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  refine (hA.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (mem_univ z₀) hz₀
    (isCompact_closedBall 0 R) (subset_univ _)).subset fun z hz => ?_
  exact ⟨mem_closedBall_zero_iff.mpr hz.2, (mem_sectorZeros_iff.mp hz.1).2.2.2⟩

section LocallyFinite

variable {θ₁ θ₂ : ℝ} {f : ℂ → ℂ}

/-- Every `Complex.polarLt`-initial segment of a locally norm-finite sector zero set is finite. -/
theorem finite_sectorZeroInit
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (z : ℂ) :
    {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.Finite :=
  (hfin ‖z‖).subset fun _ hw => ⟨hw.1, hw.2.norm_le⟩

@[instance_reducible]
private noncomputable def sectorZerosLinearOrder (θ₁ θ₂ : ℝ) (f : ℂ → ℂ) :
    LinearOrder (sectorZeros θ₁ θ₂ f) :=
  LinearOrder.lift' (fun w : sectorZeros θ₁ θ₂ f => toLex (‖w.val‖, w.val.arg))
    (Complex.toLex_norm_arg_injective.comp Subtype.val_injective)

private theorem ncard_Iio_sectorZeros_eq (z : sectorZeros θ₁ θ₂ f) :
    let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
    (Set.Iio z).ncard = {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z.val}.ncard := by
  let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
  have himg : Subtype.val '' Set.Iio z = {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z.val} := by
    ext w
    constructor
    · rintro ⟨⟨w, hw⟩, hlt, rfl⟩
      exact ⟨hw, hlt⟩
    · rintro ⟨hw, hlt⟩
      exact ⟨⟨w, hw⟩, hlt, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

private theorem finite_Iio_sectorZeros
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (z : sectorZeros θ₁ θ₂ f) :
    let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
    (Set.Iio z).Finite :=
  ((finite_sectorZeroInit hfin z.val).preimage Subtype.val_injective.injOn).subset
    fun w hw => ⟨w.property, hw⟩

/-- Under local norm-finiteness, strict `Complex.polarLt` inequality between two sector zeros gives
strict inequality between the cardinalities of their initial segments. -/
theorem ncard_sectorZeroInit_lt
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ sectorZeros θ₁ θ₂ f) (h12 : z₁.polarLt z₂) :
    {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z₁}.ncard <
      {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z₂}.ncard := by
  refine Set.ncard_lt_ncard
    ⟨fun w hw => ⟨hw.1, trans_of Complex.polarLt hw.2 h12⟩, fun hsub => ?_⟩
    (finite_sectorZeroInit hfin z₂)
  exact irrefl_of Complex.polarLt z₁ (hsub ⟨hz₁, h12⟩).2

/-- Under local norm-finiteness, two zeros in the same open sector with equal initial-segment
cardinalities coincide. -/
theorem eq_of_mem_sectorZeros_of_ncard_eq
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ sectorZeros θ₁ θ₂ f) (hz₂ : z₂ ∈ sectorZeros θ₁ θ₂ f)
    (hcard : {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z₁}.ncard =
      {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z₂}.ncard) :
    z₁ = z₂ := by
  let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
  let r := ncardIioOrderEmbedding (finite_Iio_sectorZeros hfin)
  have hEq : (⟨z₁, hz₁⟩ : sectorZeros θ₁ θ₂ f) = ⟨z₂, hz₂⟩ := by
    apply r.injective
    simpa [r, ncardIioOrderEmbedding_apply, ncard_Iio_sectorZeros_eq] using hcard
  exact congrArg Subtype.val hEq

/-- Under local norm-finiteness, if `z ∈ sectorZeros θ₁ θ₂ f` has initial-segment cardinality
`k - 1`, then `sectorZero θ₁ θ₂ f k = z`. -/
theorem sectorZero_eq_of_ncard
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {z : ℂ} {k : ℕ} (hz : z ∈ sectorZeros θ₁ θ₂ f)
    (hcard : {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard = k - 1) :
    sectorZero θ₁ θ₂ f k = z := by
  let P : ℂ → Prop := fun u =>
    u ∈ sectorZeros θ₁ θ₂ f ∧ {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt u}.ncard = k - 1
  have hPz : P z := ⟨hz, hcard⟩
  have hPe : P (sectorZero θ₁ θ₂ f k) := Classical.epsilon_spec ⟨z, hPz⟩
  exact eq_of_mem_sectorZeros_of_ncard_eq hfin hPe.1 hz (hPe.2.trans hcard.symm)

/-- **Completeness of `sectorZero` under local norm-finiteness.** When `f` has finitely many sector
zeros in every closed ball, every `z ∈ sectorZeros θ₁ θ₂ f` appears in the sequence
`sectorZero θ₁ θ₂ f k` at a positive index `k ≥ 1`, without assuming that `f` has infinitely many
zeros in the sector. -/
theorem exists_sectorZero_eq
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {z : ℂ} (hz : z ∈ sectorZeros θ₁ θ₂ f) :
    ∃ k : ℕ, 1 ≤ k ∧ sectorZero θ₁ θ₂ f k = z :=
  ⟨{w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard + 1,
    Nat.le_add_left 1 _,
    sectorZero_eq_of_ncard hfin hz rfl⟩

/-- When `1 ≤ k` and the sector zero set has extended cardinality at least `k`, some zero in the
sector has initial-segment cardinality `k - 1`. -/
private theorem exists_mem_sectorZeros_ncard_eq
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard) :
    ∃ z ∈ sectorZeros θ₁ θ₂ f,
      {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard = k - 1 := by
  let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
  have hlt : ((k - 1 : ℕ) : ℕ∞) < ENat.card (sectorZeros θ₁ θ₂ f) := by
    rw [ENat.card_coe_set_eq]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hk Nat.zero_lt_one) hle
  obtain ⟨z, hz⟩ := exists_ncard_Iio_eq_of_finite_Iio (finite_Iio_sectorZeros hfin) hlt
  exact ⟨z.val, z.property, by simpa [ncard_Iio_sectorZeros_eq] using hz⟩

/-- Under local norm-finiteness, when `1 ≤ k` and `(k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard`,
the epsilon `sectorZero θ₁ θ₂ f k` attains its defining predicate. -/
theorem sectorZero_spec_of_le_encard
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard) :
    sectorZero θ₁ θ₂ f k ∈ sectorZeros θ₁ θ₂ f ∧
      {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt (sectorZero θ₁ θ₂ f k)}.ncard = k - 1 :=
  Classical.epsilon_spec (exists_mem_sectorZeros_ncard_eq hfin hk hle)

/-- Under local norm-finiteness, `sectorZero θ₁ θ₂ f` is strictly increasing with respect to
`Complex.polarLt` for `1 ≤ j < k` whenever `(k : ℕ∞)` is at most the sector zero cardinality. -/
theorem polarLt_sectorZero_of_lt_of_le_encard
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    (hle : (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard) :
    (sectorZero θ₁ θ₂ f j).polarLt (sectorZero θ₁ θ₂ f k) := by
  have hspec_j := sectorZero_spec_of_le_encard hfin hj ((Nat.cast_le.mpr hjk.le).trans hle)
  have hspec_k := sectorZero_spec_of_le_encard hfin (hj.trans hjk.le) hle
  let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
  let r := ncardIioOrderEmbedding (finite_Iio_sectorZeros hfin)
  change (⟨sectorZero θ₁ θ₂ f j, hspec_j.1⟩ : sectorZeros θ₁ θ₂ f) <
    ⟨sectorZero θ₁ θ₂ f k, hspec_k.1⟩
  rw [← r.lt_iff_lt]
  simp only [r, ncardIioOrderEmbedding_apply, ncard_Iio_sectorZeros_eq, hspec_j.2, hspec_k.2]
  omega

/-- Under local norm-finiteness, `sectorZero θ₁ θ₂ f` is injective on positive indices at most the
extended cardinality of the sector zero set. -/
theorem injOn_sectorZero
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite) :
    Set.InjOn (sectorZero θ₁ θ₂ f)
      {k : ℕ | 1 ≤ k ∧ (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard} := by
  let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
  let S : Set ℕ := {k : ℕ | 1 ≤ k ∧ (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard}
  let g : S → sectorZeros θ₁ θ₂ f := fun k =>
    ⟨sectorZero θ₁ θ₂ f k.val, (sectorZero_spec_of_le_encard hfin k.property.1 k.property.2).1⟩
  have hg : StrictMonoOn g Set.univ := fun j _ k _ hjk =>
    polarLt_sectorZero_of_lt_of_le_encard hfin j.property.1 hjk k.property.2
  intro j hj k hk hEq
  exact congrArg Subtype.val
    (hg.injOn (Set.mem_univ ⟨j, hj⟩) (Set.mem_univ ⟨k, hk⟩) (Subtype.ext hEq))

/-- Under local norm-finiteness, `sectorZero θ₁ θ₂ f` restricts to a bijection from
`{k : ℕ | 1 ≤ k ∧ (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard}` onto `sectorZeros θ₁ θ₂ f`. -/
theorem bijOn_sectorZero
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite) :
    Set.BijOn (sectorZero θ₁ θ₂ f)
      {k : ℕ | 1 ≤ k ∧ (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard}
      (sectorZeros θ₁ θ₂ f) := by
  refine ⟨fun _ hk => (sectorZero_spec_of_le_encard hfin hk.1 hk.2).1, injOn_sectorZero hfin,
    fun z hz => ?_⟩
  refine ⟨{w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard + 1, ⟨Nat.le_add_left 1 _, ?_⟩,
    sectorZero_eq_of_ncard hfin hz rfl⟩
  have hI_fin : {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.Finite :=
    finite_sectorZeroInit hfin z
  have hz_not : z ∉ {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z} :=
    fun h => irrefl_of Complex.polarLt z h.2
  have hsub : insert z {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z} ⊆ sectorZeros θ₁ θ₂ f :=
    Set.insert_subset_iff.mpr ⟨hz, fun _ hw => hw.1⟩
  calc
    (({w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.ncard + 1 : ℕ) : ℕ∞)
        = {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}.encard + 1 := by
          rw [Nat.cast_add, Nat.cast_one, hI_fin.cast_ncard_eq]
    _ = (insert z {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt z}).encard :=
          (Set.encard_insert_of_notMem hz_not).symm
    _ ≤ (sectorZeros θ₁ θ₂ f).encard := Set.encard_le_encard hsub

/-- Under local norm-finiteness, the norms `‖sectorZero θ₁ θ₂ f ·‖` are nondecreasing for
`1 ≤ j ≤ k` whenever `(k : ℕ∞)` is at most the sector zero cardinality. -/
theorem norm_sectorZero_le_norm_sectorZero_of_le_encard
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hle : (k : ℕ∞) ≤ (sectorZeros θ₁ θ₂ f).encard) :
    ‖sectorZero θ₁ θ₂ f j‖ ≤ ‖sectorZero θ₁ θ₂ f k‖ := by
  rcases hjk.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (polarLt_sectorZero_of_lt_of_le_encard hfin hj hlt hle).norm_le

/-! ### Properties when the sector zero set is infinite -/

/-- When `sectorZeros θ₁ θ₂ f` is infinite (and locally finite by norm), `sectorZero θ₁ θ₂ f k`
attains its defining predicate for every `k ≥ 1`. -/
theorem sectorZero_spec_of_infinite
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    sectorZero θ₁ θ₂ f k ∈ sectorZeros θ₁ θ₂ f ∧
      {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt (sectorZero θ₁ θ₂ f k)}.ncard = k - 1 :=
  sectorZero_spec_of_le_encard hfin hk (by simp [hinf.encard_eq])

/-- Under local norm-finiteness and `Infinite`, `sectorZero θ₁ θ₂ f` is strictly increasing with
respect to `Complex.polarLt` on `{k | 1 ≤ k}`. -/
theorem polarLt_sectorZero_of_lt
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    (sectorZero θ₁ θ₂ f j).polarLt (sectorZero θ₁ θ₂ f k) :=
  polarLt_sectorZero_of_lt_of_le_encard hfin hj hjk (by simp [hinf.encard_eq])

/-- Under local norm-finiteness and `Infinite`, `sectorZero θ₁ θ₂ f` is injective on `Set.Ici 1`. -/
theorem injOn_sectorZero_Ici
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite) :
    Set.InjOn (sectorZero θ₁ θ₂ f) (Set.Ici 1) := by
  refine (injOn_sectorZero hfin).mono fun k hk => ?_
  exact ⟨hk, by simp [hinf.encard_eq]⟩

/-- Under local norm-finiteness and `Infinite`, every `z ∈ sectorZeros θ₁ θ₂ f` appears at a
*unique* positive index `k ≥ 1`. -/
theorem existsUnique_sectorZero_eq_of_infinite
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite)
    {z : ℂ} (hz : z ∈ sectorZeros θ₁ θ₂ f) :
    ∃! k : ℕ, 1 ≤ k ∧ sectorZero θ₁ θ₂ f k = z := by
  obtain ⟨k, hk, hk_eq⟩ := exists_sectorZero_eq hfin hz
  exact ⟨k, ⟨hk, hk_eq⟩, fun m ⟨hm, hm_eq⟩ =>
    injOn_sectorZero_Ici hfin hinf hm hk (hm_eq.trans hk_eq.symm)⟩

/-- Under local norm-finiteness and `Infinite`, the norms `‖sectorZero θ₁ θ₂ f k‖` are
nondecreasing for `k ≥ 1`. -/
theorem norm_sectorZero_le_norm_sectorZero
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖sectorZero θ₁ θ₂ f j‖ ≤ ‖sectorZero θ₁ θ₂ f k‖ :=
  norm_sectorZero_le_norm_sectorZero_of_le_encard hfin hj hjk (by simp [hinf.encard_eq])

/-- Under local norm-finiteness and `Infinite`, stepwise norm monotonicity
`‖sectorZero θ₁ θ₂ f k‖ ≤ ‖sectorZero θ₁ θ₂ f (k + 1)‖` holds for `k ≥ 1`. -/
theorem norm_sectorZero_le_succ
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖sectorZero θ₁ θ₂ f k‖ ≤ ‖sectorZero θ₁ θ₂ f (k + 1)‖ :=
  norm_sectorZero_le_norm_sectorZero hfin hinf hk (Nat.le_succ k)

/-- Under local norm-finiteness and `Infinite`, `‖sectorZero θ₁ θ₂ f k‖ → ∞` as `k → ∞`. -/
theorem tendsto_norm_sectorZero_atTop
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hinf : (sectorZeros θ₁ θ₂ f).Infinite) :
    Tendsto (fun k : ℕ => ‖sectorZero θ₁ θ₂ f k‖) atTop atTop := by
  let e : ℕ → sectorZeros θ₁ θ₂ f := fun n =>
    ⟨sectorZero θ₁ θ₂ f (n + 1), (sectorZero_spec_of_infinite hfin hinf (Nat.succ_pos n)).1⟩
  have he : Function.Injective e := fun m n h =>
    Nat.succ.inj <| injOn_sectorZero_Ici hfin hinf (Nat.succ_pos m) (Nat.succ_pos n)
      (congrArg Subtype.val h)
  have hsub : ∀ R : ℝ, {z : sectorZeros θ₁ θ₂ f | ‖z.val‖ ≤ R}.Finite := fun R =>
    ((hfin R).preimage Subtype.val_injective.injOn).subset fun z hz => ⟨z.property, hz⟩
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp
    (tendsto_comp_atTop_of_finite_setOf_le (f := fun z : sectorZeros θ₁ θ₂ f => ‖z.val‖) hsub he)

/-! ### Annular disc and Rouché localization -/

private theorem sectorZero_add_eq_of_tail
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    {A : Set ℂ} (hA_fin : A.Finite) (hA_sub : A ⊆ sectorZeros θ₁ θ₂ f)
    {zSeq : ℕ → ℂ} (hzS : ∀ m, zSeq m ∈ sectorZeros θ₁ θ₂ f)
    (hstrict : ∀ {i j}, i < j → (zSeq i).polarLt (zSeq j))
    (hA_lt : ∀ w ∈ A, ∀ m, w.polarLt (zSeq m))
    (hexh : ∀ w ∈ sectorZeros θ₁ θ₂ f, w ∈ A ∨ ∃ m, w = zSeq m)
    (n : ℕ) :
    sectorZero θ₁ θ₂ f (A.ncard + 1 + n) = zSeq n := by
  let : LinearOrder (sectorZeros θ₁ θ₂ f) := sectorZerosLinearOrder θ₁ θ₂ f
  let A' : Set (sectorZeros θ₁ θ₂ f) := Subtype.val ⁻¹' A
  let zSub : ℕ → sectorZeros θ₁ θ₂ f := fun m => ⟨zSeq m, hzS m⟩
  have hA'_fin : A'.Finite := hA_fin.preimage Subtype.val_injective.injOn
  have hA'_card : A'.ncard = A.ncard := by
    rw [← Set.ncard_image_of_injective A' Subtype.val_injective,
      Set.image_preimage_eq_iff.mpr (by rw [Subtype.range_coe]; exact hA_sub)]
  have hrank := ncard_Iio_eq_ncard_add_of_strictMono hA'_fin
    (z := zSub) (fun _ _ h => hstrict h)
    (fun w hw m => hA_lt w.val hw m)
    (fun w => (hexh w.val w.property).imp id fun ⟨m, hm⟩ => ⟨m, Subtype.ext hm⟩) n
  have hcard : {w ∈ sectorZeros θ₁ θ₂ f | w.polarLt (zSeq n)}.ncard = A.ncard + 1 + n - 1 := by
    rw [← ncard_Iio_sectorZeros_eq (zSub n), hrank, hA'_card]
    omega
  exact sectorZero_eq_of_ncard hfin (hzS n) hcard

/-- A sequence of annularly separated discs inside the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`, each
containing a zero of `f`, forces `sectorZeros θ₁ θ₂ f` to be infinite. -/
theorem infinite_sectorZeros_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hex : ∀ n, ∃ z ∈ ball (c n) (r n), f z = 0) :
    (sectorZeros θ₁ θ₂ f).Infinite := by
  choose zSeq hz_ball hz_zero using hex
  have hstrict := strictMono_norm_of_forall_mem_ball hsep hz_ball
  have hinj : Function.Injective zSeq := Function.Injective.of_comp (f := norm) hstrict.injective
  exact (Set.infinite_range_of_injective hinj).mono <| by
    rintro _ ⟨n, rfl⟩
    exact ⟨(hsub n _ (hz_ball n)).1, (hsub n _ (hz_ball n)).2.1, (hsub n _ (hz_ball n)).2.2,
      hz_zero n⟩

/-- **Annular disc localization of `sectorZero`.** Under local norm-finiteness, suppose
`ball (c n) (r n)` lies in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`, satisfies
`‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1)`, contains a unique zero of `f`, and that every zero in
`sectorZeros θ₁ θ₂ f` of norm at least `R₀` (`R₀ ≤ ‖c 0‖ - r 0`) belongs to one of these discs.
Setting `k₀ = {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1`, the `(k₀ + n)`-th sector zero lies
in `ball (c n) (r n)` and satisfies `f (...) = 0` for every `n : ℕ`. -/
theorem sectorZero_mem_ball_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z ∈ sectorZeros θ₁ θ₂ f, R₀ ≤ ‖z‖ → ∃ n, z ∈ ball (c n) (r n))
    (n : ℕ) :
    sectorZero θ₁ θ₂ f ({w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1 + n) ∈
      ball (c n) (r n) ∧
      f (sectorZero θ₁ θ₂ f ({w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1 + n)) = 0 := by
  let zSeq : ℕ → ℂ := fun m => Classical.choose (huniq m)
  have hz_spec : ∀ m, (zSeq m ∈ ball (c m) (r m) ∧ f (zSeq m) = 0) ∧
      ∀ y, y ∈ ball (c m) (r m) ∧ f y = 0 → y = zSeq m :=
    fun m => Classical.choose_spec (huniq m)
  have hzS : ∀ m, zSeq m ∈ sectorZeros θ₁ θ₂ f := fun m =>
    ⟨(hsub m _ (hz_spec m).1.1).1, (hsub m _ (hz_spec m).1.1).2.1,
      (hsub m _ (hz_spec m).1.1).2.2, (hz_spec m).1.2⟩
  have hstrict := strictMono_norm_of_forall_mem_ball hsep (fun m => (hz_spec m).1.1)
  have hR₀_lt : ∀ m, R₀ < ‖zSeq m‖ := fun m =>
    (hR₀.trans_lt (sub_lt_iff_lt_add.mpr
      (norm_lt_of_mem_ball (mem_ball_comm.mp (hz_spec 0).1.1)))).trans_le
      (hstrict.monotone (Nat.zero_le m))
  set A : Set ℂ := {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}
  have hA_fin : A.Finite := (hfin R₀).subset fun _ hw => ⟨hw.1, hw.2.le⟩
  have hEq := sectorZero_add_eq_of_tail hfin hA_fin (fun _ hw => hw.1) hzS
    (fun hij => Complex.polarLt_of_norm_lt (hstrict hij))
    (fun _ hwA m => Complex.polarLt_of_norm_lt (hwA.2.trans (hR₀_lt m)))
    (fun w hwS => (lt_or_ge ‖w‖ R₀).imp (fun hwR => ⟨hwS, hwR⟩) fun hwR =>
      let ⟨m, hwm⟩ := hexh w hwS hwR
      ⟨m, (hz_spec m).2 w ⟨hwm, (mem_sectorZeros_iff.mp hwS).2.2.2⟩⟩) n
  exact hEq.symm ▸ (hz_spec n).1

/-- Under the hypotheses of `TauCeti.sectorZero_mem_ball_of_annular_discs`, the norms
`‖sectorZero θ₁ θ₂ f k‖` are **strictly** increasing from `k₀` onward. -/
theorem norm_sectorZero_lt_succ_of_annular_discs {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z ∈ sectorZeros θ₁ θ₂ f, R₀ ≤ ‖z‖ → ∃ n, z ∈ ball (c n) (r n))
    {k : ℕ} (hk : {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1 ≤ k) :
    ‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖ := by
  set k₀ := {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1
  set n := k - k₀
  have hk_eq : k = k₀ + n := (Nat.add_sub_of_le hk).symm
  have hstrict := strictMono_norm_of_forall_mem_ball hsep fun m =>
    (sectorZero_mem_ball_of_annular_discs hfin hsub hsep huniq hR₀ hexh m).1
  rw [hk_eq, Nat.add_assoc k₀ n 1]
  exact hstrict (Nat.lt_succ_self n)

/-- **Rouché annular localization of `sectorZero`.** Under local norm-finiteness, let `g` be a
comparison function having a unique zero in each disc `ball (c n) (r n)` with nonvanishing
derivative there, and let `f` satisfy the symmetric Rouché bound `‖f z - g z‖ < ‖f z‖ + ‖g z‖` on
each circle `sphere (c n) (r n)`. If the discs lie in the open sector `z ≠ 0`, `θ₁ < arg z < θ₂`,
sit in strictly separated annuli, and cover all zeros in `sectorZeros θ₁ θ₂ f` of norm at least
`R₀ ≤ ‖c 0‖ - r 0`, then from index `k₀ = {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1`
onward, `sectorZero θ₁ θ₂ f (k₀ + n)` lies in `ball (c n) (r n)`, satisfies `f (...) = 0` and
`deriv f (...) ≠ 0`, and `‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖` for all
`k ≥ k₀`. -/
theorem sectorZero_mem_ball_of_rouche {g : ℂ → ℂ} {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hfin : ∀ R : ℝ, {z ∈ sectorZeros θ₁ θ₂ f | ‖z‖ ≤ R}.Finite)
    (hf_an : ∀ n, AnalyticOnNhd ℂ f (closedBall (c n) (r n)))
    (hg_an : ∀ n, AnalyticOnNhd ℂ g (closedBall (c n) (r n)))
    (hs : ∀ n, ∀ z ∈ sphere (c n) (r n), ‖f z - g z‖ < ‖f z‖ + ‖g z‖)
    (hg_uniq : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ g z = 0) ∧
      ∀ z ∈ ball (c n) (r n), g z = 0 → deriv g z ≠ 0)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), z ≠ 0 ∧ θ₁ < z.arg ∧ z.arg < θ₂)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z ∈ sectorZeros θ₁ θ₂ f, R₀ ≤ ‖z‖ → ∃ n, z ∈ ball (c n) (r n)) :
    let k₀ := {w ∈ sectorZeros θ₁ θ₂ f | ‖w‖ < R₀}.ncard + 1
    (∀ n, sectorZero θ₁ θ₂ f (k₀ + n) ∈ ball (c n) (r n)) ∧
      (∀ n, f (sectorZero θ₁ θ₂ f (k₀ + n)) = 0) ∧
      (∀ n, deriv f (sectorZero θ₁ θ₂ f (k₀ + n)) ≠ 0) ∧
      ∀ k, k₀ ≤ k → ‖sectorZero θ₁ θ₂ f k‖ < ‖sectorZero θ₁ θ₂ f (k + 1)‖ := by
  have hf_simple : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ f z = 0) ∧
      ∀ z ∈ ball (c n) (r n), f z = 0 → deriv f z ≠ 0 := fun n =>
    (rouche_symm_existsUnique_eq_zero_and_deriv_ne_zero_iff
      (hf_an n) (hg_an n) (hs n)).mpr (hg_uniq n)
  have hf_uniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0 := fun n => (hf_simple n).1
  intro k₀
  have hball : ∀ n, sectorZero θ₁ θ₂ f (k₀ + n) ∈ ball (c n) (r n) ∧
      f (sectorZero θ₁ θ₂ f (k₀ + n)) = 0 :=
    sectorZero_mem_ball_of_annular_discs hfin hsub hsep hf_uniq hR₀ hexh
  exact ⟨fun n => (hball n).1, fun n => (hball n).2,
    fun n => (hf_simple n).2 _ (hball n).1 (hball n).2,
    fun k hk => norm_sectorZero_lt_succ_of_annular_discs hfin hsub hsep hf_uniq hR₀ hexh hk⟩

end LocallyFinite

/-! ### Explicit evaluation on rotated cosines -/

section RotatedCosine

/-- The `n`-th positive-ray zero `((n + 1/2) π) exp(i θ)` of `z ↦ cos (exp (-i θ) * z)`. -/
private noncomputable def rotatedCosZero (θ : ℝ) (n : ℕ) : ℂ :=
  circleMap 0 (((n : ℝ) + 1 / 2) * Real.pi) θ

private theorem norm_rotatedCosZero (θ : ℝ) (n : ℕ) :
    ‖rotatedCosZero θ n‖ = ((n : ℝ) + 1 / 2) * Real.pi := by
  rw [rotatedCosZero, norm_circleMap_zero, abs_of_pos (mul_pos (by positivity) Real.pi_pos)]

private theorem rotatedCosZero_ne_zero (θ : ℝ) (n : ℕ) : rotatedCosZero θ n ≠ 0 :=
  circleMap_ne_center (mul_pos (by positivity) Real.pi_pos).ne'

private theorem arg_rotatedCosZero {θ : ℝ} (hθ₀ : -Real.pi < θ) (hθ₁ : θ ≤ Real.pi) (n : ℕ) :
    (rotatedCosZero θ n).arg = θ := by
  have hpos : 0 < ((n : ℝ) + 1 / 2) * Real.pi := mul_pos (by positivity) Real.pi_pos
  rw [rotatedCosZero, circleMap_zero, Complex.arg_ofReal_mul hpos, Complex.arg_exp_mul_I]
  exact toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith, by linarith⟩

/-- Classification of the sector zeros of `z ↦ cos (exp (-i θ) * z)` when
`-π ≤ θ₁ < θ < θ₂ ≤ π` with `θ - θ₁ ≤ π` and `θ₂ - θ ≤ π`: they are precisely
`rotatedCosZero θ n` for `n : ℕ`. -/
private theorem mem_sectorZeros_cos_iff {θ₁ θ₂ θ : ℝ}
    (hθ₁ : -Real.pi ≤ θ₁) (h₁ : θ₁ < θ) (h₂ : θ < θ₂) (hθ₂ : θ₂ ≤ Real.pi)
    (hlo : θ - θ₁ ≤ Real.pi) (hhi : θ₂ - θ ≤ Real.pi) {z : ℂ} :
    z ∈ sectorZeros θ₁ θ₂ (fun w => Complex.cos (Complex.exp (-(θ * Complex.I)) * w)) ↔
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
      rw [hz_eq, rotatedCosZero, circleMap_zero]
      congr 1
      push_cast
      ring
    · exfalso
      have hpos : 0 < -((2 * (m : ℝ) + 1) * Real.pi / 2) := by
        have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm_neg
        nlinarith [Real.pi_pos]
      have hz_pos : z = Complex.ofReal (-((2 * (m : ℝ) + 1) * Real.pi / 2)) *
          Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) := by
        rw [hz_eq]
        push_cast
        rw [add_mul (θ : ℂ) Real.pi Complex.I, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      have hz_arg : z.arg = toIocMod Real.two_pi_pos (-Real.pi) (θ + Real.pi) := by
        rw [hz_pos, Complex.arg_ofReal_mul hpos, Complex.arg_exp_mul_I]
      rcases le_or_gt θ 0 with hθ_le | hθ_pos
      · rw [toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith, by linarith⟩] at hz_arg
        linarith
      · rw [← toIocMod_sub Real.two_pi_pos (-Real.pi) (θ + Real.pi),
          show θ + Real.pi - 2 * Real.pi = θ - Real.pi by ring,
          toIocMod_eq_self Real.two_pi_pos |>.mpr ⟨by linarith, by linarith⟩] at hz_arg
        linarith
  · rintro ⟨n, rfl⟩
    rw [mem_sectorZeros_iff, arg_rotatedCosZero hθ_gt hθ_lt.le n]
    refine ⟨rotatedCosZero_ne_zero θ n, h₁, h₂, Complex.cos_eq_zero_iff.mpr ⟨n, ?_⟩⟩
    rw [rotatedCosZero, circleMap_zero, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
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
  have hstrict : StrictMono fun m => ‖rotatedCosZero θ m‖ := fun i j hij => by
    simp only [norm_rotatedCosZero]
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    nlinarith [Real.pi_pos]
  set n := k - 1
  have hEq := sectorZero_add_eq_of_tail hfin Set.finite_empty (Set.empty_subset _)
    (fun m => (mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂ hlo hhi).mpr ⟨m, rfl⟩)
    (fun hij => Complex.polarLt_of_norm_lt (hstrict hij))
    (fun _ hwA _ => False.elim hwA)
    (fun w hwS => .inr ((mem_sectorZeros_cos_iff hθ₁ h₁ h₂ hθ₂ hlo hhi).mp hwS)) n
  simp only [Set.ncard_empty, zero_add] at hEq
  rw [show 1 + n = k by omega] at hEq
  rw [hEq, rotatedCosZero, circleMap_zero]
  congr 1
  have hk_cast : (k : ℂ) = (n : ℂ) + 1 := by exact_mod_cast (by omega : k = n + 1)
  push_cast
  rw [hk_cast]
  ring

end RotatedCosine

end TauCeti
