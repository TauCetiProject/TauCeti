/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.UnitBall
public import TauCeti.Topology.Algebra.Valued.Integer
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Discrete and dense value groups of nonarchimedean normed fields

Let `K` be an ultrametric normed field with closed unit ball `K° = Subring.unitClosedBall K` and
open-ball maximal ideal `K°° = TauCeti.unitBallIdeal K`. This file characterizes when `K°` is
noetherian, or a discrete valuation ring when the norm is nontrivial, and gives the uniform scalar
approximation of ideals of `K°` that persists when `K°` is not noetherian.

Any finitely generated ideal of `K°` is bounded in norm by a generator of largest norm, so finite
generation of `K°°` produces a strict norm gap `ρ < 1` above `K°°`. Conversely, if some `ρ < 1`
bounds all norms strictly below `1`, either `K°° = ⊥` and `K°` is a field, or the supremum of
`{‖a‖ | 0 < ‖a‖ < 1}` is attained by an element `π` whose integer powers exhaust all nonzero norms
of `K`. In either case `K°` is a principal ideal ring, hence noetherian, and when `K` is
nontrivially normed both `K°` and the valuation ring `𝒪[K]` are discrete valuation rings.

Without a norm gap below `1`, `K°°` is not finitely generated. Every ideal `I` of `K°` is
nevertheless *almost principal*: for each `0 < ε < 1`, an element `x ∈ I` whose norm exceeds
`ε · sup_{y ∈ I} ‖y‖` spans a principal ideal `x K° ≤ I` containing `c • I` for every `c ∈ K°`
with `‖c‖ ≤ ε`. In particular, for `I = K°°` and any `x ∈ K` with `ε < ‖x‖ < 1`, the principal
ideal `x K°` lies in `K°°` and contains `c • K°°` whenever `‖c‖ ≤ ε`. This is the zero-variable
case of Kiehl's almost noetherianity theorem.

## Main definitions

* `TauCeti.integerUnitClosedBallEquiv`: the identity ring equivalence `𝒪[K] ≃+* K°` for a
  nontrivially normed ultrametric field `K`.

## Main results

* `TauCeti.exists_norm_eq_zpow_of_forall_norm_le`: if `K` is nontrivially normed and some `ρ < 1`
  bounds every norm strictly below `1`, then some `π` with `0 < ‖π‖ < 1` generates all nonzero
  norms of `K` as integer powers `‖π‖ ^ k`.
* `TauCeti.fg_unitBallIdeal_iff_exists_forall_norm_le`,
  `TauCeti.isNoetherianRing_unitClosedBall_iff_fg_unitBallIdeal`,
  `TauCeti.isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le`: for any ultrametric normed
  field `K`, `K°` is noetherian if and only if `K°°` is finitely generated, if and only if there is
  a norm gap `ρ < 1` above `{‖a‖ < 1}`, and in that case `K°` is a principal ideal ring
  (`TauCeti.isPrincipalIdealRing_unitClosedBall_of_forall_norm_le`).
* `TauCeti.isDiscreteValuationRing_unitClosedBall_iff_isNoetherianRing`,
  `TauCeti.isDiscreteValuationRing_integer_iff_isNoetherianRing`,
  `TauCeti.isDiscreteValuationRing_integer_iff_exists_forall_norm_le`: when `K` is nontrivially
  normed, `K°` and `𝒪[K]` are discrete valuation rings exactly under these equivalent conditions.
* `Ideal.exists_span_singleton_le_forall_smul_mem_unitClosedBall`: for every ideal `I` of `K°` and
  every `0 < ε < 1`, some `x ∈ I` spans a principal ideal `≤ I` containing `c • I` for all
  `c ∈ K°` with `‖c‖ ≤ ε`.
* `TauCeti.smul_mem_span_singleton_of_mem_unitBallIdeal`,
  `TauCeti.smul_mem_span_singleton_of_mem_maximalIdeal_integer`: explicit principal containment
  `c • y ∈ Ideal.span {x}` for `y` in the open unit ball whenever `‖c‖ ≤ ε < ‖x‖ ≤ 1`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5, Satz 5.1.
* [S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §1.2.
-/

public section

open Filter Topology IsLocalRing
open scoped NormedField Valued

namespace TauCeti

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
/-- If every norm strictly below `1` is at most `‖π‖` with `0 < ‖π‖ < 1`, then every nonzero
element of norm at most `1` has norm a natural power of `‖π‖`. -/
theorem exists_norm_eq_pow_of_le_one {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hmax : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖) {u : K} (hu0 : u ≠ 0) (hu1 : ‖u‖ ≤ 1) :
    ∃ n : ℕ, ‖u‖ = ‖π‖ ^ n := by
  classical
  have hex : ∃ m : ℕ, ‖π‖ ^ (m + 1) < ‖u‖ := by
    have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1
    obtain ⟨m, hm⟩ := (eventually_atTop.mp
      (htend.eventually (gt_mem_nhds (norm_pos_iff.mpr hu0))))
    exact ⟨m, hm (m + 1) (Nat.le_succ m)⟩
  set n := Nat.find hex
  have hn_lt : ‖π‖ ^ (n + 1) < ‖u‖ := Nat.find_spec hex
  have hle : ‖u‖ ≤ ‖π‖ ^ n := by
    rcases eq_or_ne n 0 with h0 | hpos
    · simpa [h0] using hu1
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos
      have hmin := Nat.find_min hex (hk ▸ Nat.lt_succ_self k)
      simpa [hk] using not_lt.mp hmin
  have hq_le : ‖u / π ^ n‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ hle (pow_nonneg hπ0.le n)
  have hq_gt : ‖π‖ < ‖u / π ^ n‖ := by
    rw [norm_div, norm_pow, lt_div_iff₀ (pow_pos hπ0 n), ← pow_succ']
    exact hn_lt
  have hq_eq : ‖u / π ^ n‖ = 1 :=
    hq_le.antisymm (not_lt.mp fun hlt ↦ (hmax _ hlt).not_gt hq_gt)
  refine ⟨n, ?_⟩
  rw [norm_div, norm_pow, div_eq_one_iff_eq (pow_ne_zero n hπ0.ne')] at hq_eq
  exact hq_eq

omit [IsUltrametricDist K] in
/-- If some `ρ < 1` bounds every norm strictly below `1`, and `K` has an element of norm strictly
between `0` and `1`, then the supremum of `{‖a‖ | 0 < ‖a‖ < 1}` is attained by an element `π` whose
integer powers exhaust all nonzero norms of `K`. -/
private theorem exists_uniformizer_of_exists_norm_lt_one {ρ : ℝ} (hρ1 : ρ < 1)
    (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) {c : K} (hc0 : 0 < ‖c‖) (hc1 : ‖c‖ < 1) :
    ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ (∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖) ∧
      ∀ x : K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  set S : Set ℝ := (fun a : K ↦ ‖a‖) '' {a : K | 0 < ‖a‖ ∧ ‖a‖ < 1}
  have hSne : S.Nonempty := ⟨‖c‖, c, ⟨hc0, hc1⟩, rfl⟩
  have hSbdd : BddAbove S := ⟨ρ, by rintro _ ⟨a, ha, rfl⟩; exact hρ a ha.2⟩
  set μ := sSup S
  have hμ_pos : 0 < μ := hc0.trans_le (le_csSup hSbdd ⟨c, ⟨hc0, hc1⟩, rfl⟩)
  have hμ_le_ρ : μ ≤ ρ := csSup_le hSne (by rintro _ ⟨a, ha, rfl⟩; exact hρ a ha.2)
  have hμ_lt_one : μ < 1 := hμ_le_ρ.trans_lt hρ1
  -- Since `0 < μ < 1`, `μ ^ 2 < μ = sSup S`; any `π` with `μ ^ 2 < ‖π‖ ≤ μ` attains `μ`.
  have hsq_lt : μ * μ < μ := mul_lt_of_lt_one_left hμ_pos hμ_lt_one
  obtain ⟨_, ⟨π, ⟨hπ0, hπ1⟩, rfl⟩, hπsq⟩ := (lt_csSup_iff hSbdd hSne).mp hsq_lt
  have hmax (a : K) (ha1 : ‖a‖ < 1) : ‖a‖ ≤ ‖π‖ := by
    by_contra! hlt
    have ha0 : 0 < ‖a‖ := hπ0.trans hlt
    have haμ : ‖a‖ ≤ μ := le_csSup hSbdd ⟨a, ⟨ha0, ha1⟩, rfl⟩
    have hdiv0 : 0 < ‖π / a‖ := by rw [norm_div]; exact div_pos hπ0 ha0
    have hdiv1 : ‖π / a‖ < 1 := by rw [norm_div]; exact (div_lt_one ha0).mpr hlt
    have hdivμ : ‖π / a‖ ≤ μ := le_csSup hSbdd ⟨π / a, ⟨hdiv0, hdiv1⟩, rfl⟩
    rw [norm_div, div_le_iff₀ ha0] at hdivμ
    exact (hdivμ.trans (mul_le_mul_of_nonneg_left haμ hμ_pos.le)).not_gt hπsq
  refine ⟨π, hπ0, hπ1, hmax, fun x hx0 ↦ ?_⟩
  rcases le_or_gt ‖x‖ 1 with hx1 | hx1
  · obtain ⟨n, hn⟩ := exists_norm_eq_pow_of_le_one hπ0 hπ1 hmax hx0 hx1
    exact ⟨n, by simpa using hn⟩
  · have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hinv1 : ‖x⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hx1.le
    obtain ⟨n, hn⟩ := exists_norm_eq_pow_of_le_one hπ0 hπ1 hmax hinv0 hinv1
    refine ⟨-(n : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← hn, norm_inv, inv_inv]

/-- **Principal ideal property from a norm gap.** If some `ρ < 1` bounds every norm strictly below
`1` in an ultrametric normed field `K`, then `Subring.unitClosedBall K` is a principal ideal ring:
either `K` is trivially normed and `K°` is a field, or `K` is discretely valued. -/
theorem isPrincipalIdealRing_unitClosedBall_of_forall_norm_le {ρ : ℝ} (hρ1 : ρ < 1)
    (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsPrincipalIdealRing (Subring.unitClosedBall K) := by
  by_cases hex : ∃ c : K, 0 < ‖c‖ ∧ ‖c‖ < 1
  · obtain ⟨c, hc0, hc1⟩ := hex
    obtain ⟨π, hπ0, hπ1, -, hdisc⟩ := exists_uniformizer_of_exists_norm_lt_one hρ1 hρ hc0 hc1
    exact isPrincipalIdealRing_unitClosedBall_of_norm_eq_zpow hπ0 hπ1 hdisc
  · push Not at hex
    -- Every nonzero element of `K°` has norm `1`, hence is a unit, so `K°` is a field.
    have hfield : IsField (Subring.unitClosedBall K) := by
      refine IsLocalRing.isField_iff_maximalIdeal_eq.mpr ?_
      rw [maximalIdeal_unitClosedBall, Submodule.eq_bot_iff]
      intro x hx
      rw [mem_unitBallIdeal] at hx
      ext
      by_contra hx0
      exact (hex x (norm_pos_iff.mpr hx0)).not_gt hx
    let := hfield.toField
    infer_instance

/-- **Finite generation of the open-ball ideal is equivalent to a norm gap below `1`.** -/
theorem fg_unitBallIdeal_iff_exists_forall_norm_le :
    (unitBallIdeal K).FG ↔ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ := by
  refine ⟨fun hfg ↦ ?_, fun ⟨ρ, hρ1, hρ⟩ ↦ ?_⟩
  · obtain ⟨π, hπ1, hπ⟩ := exists_norm_lt_one_forall_norm_le_of_fg hfg
    exact ⟨‖π‖, hπ1, hπ⟩
  · have := isPrincipalIdealRing_unitClosedBall_of_forall_norm_le hρ1 hρ
    exact IsNoetherian.noetherian _

/-- **The closed unit ball of an ultrametric normed field is noetherian if and only if its
open-ball ideal is finitely generated.** -/
theorem isNoetherianRing_unitClosedBall_iff_fg_unitBallIdeal :
    IsNoetherianRing (Subring.unitClosedBall K) ↔ (unitBallIdeal K).FG := by
  refine ⟨fun _ ↦ IsNoetherian.noetherian _, fun hfg ↦ ?_⟩
  obtain ⟨ρ, hρ1, hρ⟩ := fg_unitBallIdeal_iff_exists_forall_norm_le.mp hfg
  have := isPrincipalIdealRing_unitClosedBall_of_forall_norm_le hρ1 hρ
  infer_instance

/-- **The closed unit ball of an ultrametric normed field is noetherian if and only if some
`ρ < 1` bounds all norms strictly below `1`.** -/
theorem isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le :
    IsNoetherianRing (Subring.unitClosedBall K) ↔
      ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ :=
  isNoetherianRing_unitClosedBall_iff_fg_unitBallIdeal.trans
    fg_unitBallIdeal_iff_exists_forall_norm_le

/-- **Ideals of `K°` are almost principal.** For every ideal `I` of `Subring.unitClosedBall K` and
every `0 < ε < 1`, there is an element `x ∈ I` such that `c • y ∈ Ideal.span {x}` for all
`c ∈ Subring.unitClosedBall K` with `‖(c : K)‖ ≤ ε` and all `y ∈ I`. -/
theorem _root_.Ideal.exists_span_singleton_le_forall_smul_mem_unitClosedBall
    (I : Ideal (Subring.unitClosedBall K)) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ x ∈ I, ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε →
      ∀ y ∈ I, c • y ∈ Ideal.span {x} := by
  set S : Set ℝ := (fun y : Subring.unitClosedBall K ↦ ‖(y : K)‖) '' (I : Set _)
  have hSne : S.Nonempty := ⟨0, 0, I.zero_mem, by simp⟩
  have hSbdd : BddAbove S := ⟨1, by rintro _ ⟨y, -, rfl⟩; exact Subring.mem_unitClosedBall.mp y.2⟩
  set α := sSup S
  have hα0 : 0 ≤ α := le_csSup_of_le hSbdd ⟨0, I.zero_mem, rfl⟩ (by simp)
  rcases hα0.eq_or_lt with hα | hα
  · refine ⟨0, I.zero_mem, fun c _ y hy ↦ ?_⟩
    have hy0 : ‖(y : K)‖ ≤ 0 := hα ▸ le_csSup hSbdd ⟨y, hy, rfl⟩
    have hy_eq : y = 0 := Subtype.ext (norm_le_zero_iff.mp hy0)
    simp [hy_eq]
  · have hεα : ε * α < α := mul_lt_of_lt_one_left hα hε1
    obtain ⟨_, ⟨x, hxI, rfl⟩, hxgt⟩ := (lt_csSup_iff hSbdd hSne).mp hεα
    have hx0 : (x : K) ≠ 0 := norm_pos_iff.mp ((mul_pos hε0 hα).trans hxgt)
    refine ⟨x, hxI, fun c hc y hy ↦ ?_⟩
    have hyα : ‖(y : K)‖ ≤ α := le_csSup hSbdd ⟨y, hy, rfl⟩
    have hcy : ‖(c : K) * (y : K)‖ ≤ ‖(x : K)‖ := by
      rw [norm_mul]
      exact (mul_le_mul hc hyα (norm_nonneg _) hε0.le).trans hxgt.le
    refine Ideal.mem_span_singleton'.mpr
      ⟨⟨((c : K) * (y : K)) / (x : K), Subring.mem_unitClosedBall.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]
      exact div_le_one_of_le₀ hcy (norm_nonneg _)
    · simp [smul_eq_mul, div_mul_cancel₀ _ hx0]

/-- **Explicit principal containment for the open unit ball `K°°`.** For any `x : K` with
`ε < ‖x‖ ≤ 1` (lying in `unitBallIdeal K` when `‖x‖ < 1`), the principal ideal of
`Subring.unitClosedBall K` spanned by `x` contains `c • y` whenever `‖(c : K)‖ ≤ ε` and
`y ∈ unitBallIdeal K`. -/
theorem smul_mem_span_singleton_of_mem_unitBallIdeal {ε : ℝ} {x : K}
    (hxε : ε < ‖x‖) (hx1 : ‖x‖ ≤ 1) {c : Subring.unitClosedBall K} (hc : ‖(c : K)‖ ≤ ε)
    {y : Subring.unitClosedBall K} (hy : y ∈ unitBallIdeal K) :
    c • y ∈ Ideal.span {(⟨x, Subring.mem_unitClosedBall.mpr hx1⟩ : Subring.unitClosedBall K)} := by
  rw [mem_unitBallIdeal] at hy
  by_cases hc0 : (c : K) = 0
  · have hc_zero : c = 0 := Subtype.ext hc0
    simp [hc_zero]
  · have hpos : 0 < ‖(c : K)‖ := norm_pos_iff.mpr hc0
    have hx_pos : 0 < ‖x‖ := hpos.trans_le (hc.trans hxε.le)
    have hx0 : x ≠ 0 := norm_pos_iff.mp hx_pos
    have hcy : ‖(c : K) * (y : K)‖ ≤ ‖x‖ := by
      rw [norm_mul]
      exact ((mul_le_of_le_one_right hpos.le hy.le).trans hc).trans hxε.le
    refine Ideal.mem_span_singleton'.mpr
      ⟨⟨((c : K) * (y : K)) / x, Subring.mem_unitClosedBall.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]
      exact div_le_one_of_le₀ hcy hx_pos.le
    · simp [smul_eq_mul, div_mul_cancel₀ _ hx0]

end NormedField

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **The valuation ring `𝒪[K]` and the closed unit ball `K°` have the same underlying subring.**
This is the identity ring equivalence `𝒪[K] ≃+* Subring.unitClosedBall K`. -/
noncomputable def integerUnitClosedBallEquiv : 𝒪[K] ≃+* Subring.unitClosedBall K :=
  RingEquiv.subringCongr <| Subring.ext fun _ ↦
    Valued.integer.mem_iff.trans Subring.mem_unitClosedBall.symm

@[simp]
theorem coe_integerUnitClosedBallEquiv (x : 𝒪[K]) :
    (integerUnitClosedBallEquiv x : K) = x := by
  simp [integerUnitClosedBallEquiv]

@[simp]
theorem coe_integerUnitClosedBallEquiv_symm (x : Subring.unitClosedBall K) :
    (integerUnitClosedBallEquiv.symm x : K) = x := by
  simp [integerUnitClosedBallEquiv]

omit [IsUltrametricDist K] in
/-- **Uniformizer from a norm gap.** In a nontrivially normed ultrametric field `K`, if some
`ρ < 1` bounds every norm strictly below `1`, then there exists `π : K` with `0 < ‖π‖ < 1` whose
norm bounds every norm strictly below `1` and whose integer powers give all nonzero norms of `K`. -/
theorem exists_norm_eq_zpow_of_forall_norm_le {ρ : ℝ} (hρ1 : ρ < 1)
    (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    ∃ π : K, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ (∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖) ∧
      ∀ x : K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  exact exists_uniformizer_of_exists_norm_lt_one hρ1 hρ hc0 hc1

/-- **Over a nontrivially normed ultrametric field, `Subring.unitClosedBall K` is a discrete
valuation ring if and only if it is noetherian.** -/
theorem isDiscreteValuationRing_unitClosedBall_iff_isNoetherianRing :
    IsDiscreteValuationRing (Subring.unitClosedBall K) ↔
      IsNoetherianRing (Subring.unitClosedBall K) := by
  refine ⟨fun _ ↦ inferInstance, fun hnoeth ↦ ?_⟩
  obtain ⟨ρ, hρ1, hρ⟩ := isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mp hnoeth
  have : IsPrincipalIdealRing (Subring.unitClosedBall K) :=
    isPrincipalIdealRing_unitClosedBall_of_forall_norm_le hρ1 hρ
  refine { not_a_field' := ?_ }
  rw [maximalIdeal_unitClosedBall]
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  intro hbot
  have hc : (⟨c, Subring.mem_unitClosedBall.mpr hc1.le⟩ : Subring.unitClosedBall K) ∈
      unitBallIdeal K := mem_unitBallIdeal.mpr hc1
  rw [hbot, Ideal.mem_bot] at hc
  exact hc0.ne' (by simpa using congrArg (fun x : Subring.unitClosedBall K ↦ ‖(x : K)‖) hc)

/-- **Over a nontrivially normed ultrametric field, `𝒪[K]` is a discrete valuation ring if and only
if it is noetherian.** -/
theorem isDiscreteValuationRing_integer_iff_isNoetherianRing :
    IsDiscreteValuationRing 𝒪[K] ↔ IsNoetherianRing 𝒪[K] := by
  refine ⟨fun _ ↦ inferInstance, fun hnoeth ↦ ?_⟩
  have hball : IsNoetherianRing (Subring.unitClosedBall K) :=
    isNoetherianRing_of_ringEquiv 𝒪[K] (integerUnitClosedBallEquiv (K := K))
  have : IsDiscreteValuationRing (Subring.unitClosedBall K) :=
    isDiscreteValuationRing_unitClosedBall_iff_isNoetherianRing.mpr hball
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (integerUnitClosedBallEquiv (K := K)).symm

/-- **Over a nontrivially normed ultrametric field, `𝒪[K]` is a discrete valuation ring if and only
if some `ρ < 1` bounds every norm strictly below `1`.** -/
theorem isDiscreteValuationRing_integer_iff_exists_forall_norm_le :
    IsDiscreteValuationRing 𝒪[K] ↔ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ := by
  rw [isDiscreteValuationRing_integer_iff_isNoetherianRing,
    ← isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le]
  exact ⟨fun _ ↦ isNoetherianRing_of_ringEquiv 𝒪[K] (integerUnitClosedBallEquiv (K := K)),
    fun _ ↦ isNoetherianRing_of_ringEquiv _ (integerUnitClosedBallEquiv (K := K)).symm⟩

/-- **Explicit principal containment for the maximal ideal `𝓂[K]` of `𝒪[K]`.** For any `x : K`
with `ε < ‖x‖ ≤ 1` (lying in `maximalIdeal 𝒪[K]` when `‖x‖ < 1`), the principal ideal of `𝒪[K]`
spanned by `x` contains `c • y` whenever `‖(c : K)‖ ≤ ε` and `y ∈ maximalIdeal 𝒪[K]`. -/
theorem smul_mem_span_singleton_of_mem_maximalIdeal_integer {ε : ℝ} {x : K}
    (hxε : ε < ‖x‖) (hx1 : ‖x‖ ≤ 1) {c : 𝒪[K]} (hc : ‖(c : K)‖ ≤ ε)
    {y : 𝒪[K]} (hy : y ∈ maximalIdeal 𝒪[K]) :
    c • y ∈ Ideal.span {(⟨x, Valued.integer.mem_iff.mpr hx1⟩ : 𝒪[K])} := by
  have hy' : integerUnitClosedBallEquiv y ∈ unitBallIdeal K := by
    rw [mem_unitBallIdeal, coe_integerUnitClosedBallEquiv]
    exact Valued.integer.mem_maximalIdeal_iff.mp hy
  have hc' : ‖(integerUnitClosedBallEquiv c : K)‖ ≤ ε := by
    rwa [coe_integerUnitClosedBallEquiv]
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp
    (smul_mem_span_singleton_of_mem_unitBallIdeal hxε hx1 hc' hy')
  refine Ideal.mem_span_singleton'.mpr ⟨integerUnitClosedBallEquiv.symm q, Subtype.ext ?_⟩
  have hq' := congrArg (fun z : Subring.unitClosedBall K ↦ (z : K)) hq
  simpa [smul_eq_mul] using hq'

end NontriviallyNormedField

end TauCeti
