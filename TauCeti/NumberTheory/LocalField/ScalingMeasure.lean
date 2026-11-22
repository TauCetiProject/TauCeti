/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.NumberTheory.LocalField.HaarCharacter
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.NumberTheory.LocalField.NormedField

/-!
# The `β`-scaling measure of a nonarchimedean local field

Let `K` be a nonarchimedean local field whose residue field has `q` elements, with normalized
absolute value `|x|_K` and an additive Haar measure `μ`. For a real exponent `β`, this file
introduces the density

`scalingDensity K β x = (1 - q ^ (-β)) / (1 - q⁻¹) * |x|_K ^ (β - 1)` for `x ≠ 0`,

with value `0` at `x = 0`, and studies the measure `μ.withDensity (scalingDensity K β)`. Up to the
constant, this is the measure `|x|_K ^ (β - 1) dx`; the constant is chosen so that, for `β > 0`,
the measure gives `𝒪[K]` the same mass as `μ` does. When `μ` is the Haar measure normalized by
`μ 𝒪[K] = 1`, its restriction to `𝒪[K]` is then a probability measure.

Multiplication by `a ∈ K` scales the measure by `|a|_K ^ β` (Haar measure itself is the case
`β = 1`), and the shell `|x|_K = q ^ (-k)` of elements of valuation `k` has mass
`(1 - q ^ (-β)) q ^ (-kβ) μ(𝒪[K])`. At a prime `p` and `K = ℚ_[p]` these are the local factors of
Neshveyev's measure `μ_β` on the finite adeles, the measure whose rational scaling law
`μ_β(q⁻¹ E) = q ^ β μ_β(E)` underlies the classification of the KMS states of the Bost–Connes
system.

## Main definitions

* `TauCeti.scalingDensity`: the normalized density `|x|_K ^ (β - 1)`, vanishing at `0`.

## Main results

* `MeasureTheory.Measure.withDensity_scalingDensity_setOf_eq_zpow`: the shell `|x|_K = q ^ (-k)`
  has mass `(1 - q ^ (-β)) q ^ (-kβ) μ(𝒪[K])`, for every integer `k`.
* `MeasureTheory.Measure.withDensity_scalingDensity_integer`: for `β > 0`, the ring of integers
  has mass `μ(𝒪[K])`.
* `MeasureTheory.Measure.withDensity_scalingDensity_smul` and
  `MeasureTheory.Measure.map_smul_withDensity_scalingDensity`: multiplication by `a` scales the
  measure by `|a|_K ^ β`, and pushes it forward to `|a|_K ^ (-β)` times itself.
* `MeasureTheory.Measure.withDensity_scalingDensity_one`: at `β = 1` the measure is `μ`.
* `MeasureTheory.Measure.isFiniteMeasureOnCompacts_withDensity_scalingDensity`: compact sets have
  finite mass.

## References

* S. Neshveyev, *Ergodicity of the action of the positive rationals on the group of finite adeles
  and the Bost–Connes phase transition theorem*, Proc. Amer. Math. Soc. **130** (2002),
  2999–3003, arXiv:math/0002141, pp. 1–2.
-/

public section

open MeasureTheory Measure ValuativeRel
open scoped NNReal ENNReal Pointwise

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open scoped Classical in
variable (K) in
/-- The normalized `β`-scaling density on a nonarchimedean local field `K`: the function
`x ↦ (1 - q ^ (-β)) / (1 - q⁻¹) * |x|_K ^ (β - 1)` away from `0`, with value `0` at `0`, where
`q` is the cardinality of the residue field. For `β ≤ 0` the constant is not positive, and the
density vanishes identically. -/
noncomputable def scalingDensity (β : ℝ) (x : K) : ℝ≥0∞ :=
  if x = 0 then 0 else
    ENNReal.ofReal ((1 - (Nat.card 𝓀[K] : ℝ) ^ (-β)) / (1 - (Nat.card 𝓀[K] : ℝ)⁻¹) *
      (normalizedAbsoluteValue K x : ℝ) ^ (β - 1))

variable {β : ℝ}

/-- The density vanishes at `0`. -/
@[simp]
theorem scalingDensity_apply_zero (β : ℝ) : scalingDensity K β 0 = 0 := by
  simp [scalingDensity]

/-- Away from `0`, the density is `(1 - q ^ (-β)) / (1 - q⁻¹) * |x|_K ^ (β - 1)`. -/
theorem scalingDensity_apply_of_ne_zero {x : K} (hx : x ≠ 0) :
    scalingDensity K β x =
      ENNReal.ofReal ((1 - (Nat.card 𝓀[K] : ℝ) ^ (-β)) / (1 - (Nat.card 𝓀[K] : ℝ)⁻¹) *
        (normalizedAbsoluteValue K x : ℝ) ^ (β - 1)) := by
  simp [scalingDensity, hx]

/-- The density is homogeneous of degree `β - 1`: `f(a x) = |a|_K ^ (β - 1) f(x)` for `a ≠ 0`. -/
theorem scalingDensity_mul {a : K} (ha : a ≠ 0) (x : K) :
    scalingDensity K β (a * x) =
      ENNReal.ofReal ((normalizedAbsoluteValue K a : ℝ) ^ (β - 1)) * scalingDensity K β x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [scalingDensity_apply_of_ne_zero (mul_ne_zero ha hx), scalingDensity_apply_of_ne_zero hx,
    ← ENNReal.ofReal_mul (by positivity), map_mul, NNRat.cast_mul,
    Real.mul_rpow (by positivity) (by positivity)]
  ring_nf

/-- For `β ≤ 0` the normalizing constant `(1 - q ^ (-β)) / (1 - q⁻¹)` is not positive, so the
density vanishes identically. -/
theorem scalingDensity_eq_zero_of_nonpos (hβ : β ≤ 0) : scalingDensity K β = 0 := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hq : (1 : ℝ) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  rw [scalingDensity_apply_of_ne_zero hx, Pi.zero_apply, ENNReal.ofReal_eq_zero]
  refine mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg ?_ ?_) (by positivity)
  · linarith [Real.one_le_rpow hq.le (neg_nonneg.2 hβ)]
  · linarith [inv_lt_one_of_one_lt₀ hq]

/-- At `β = 1` the density is the indicator function of `K ∖ {0}`. -/
theorem scalingDensity_one : scalingDensity K 1 = ({0}ᶜ : Set K).indicator 1 := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hq : (1 : ℝ) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  rw [scalingDensity_apply_of_ne_zero hx, Set.indicator_of_mem (by simpa using hx),
    Real.rpow_neg_one, div_self (by linarith [inv_lt_one_of_one_lt₀ hq]), sub_self,
    Real.rpow_zero, one_mul, ENNReal.ofReal_one, Pi.one_apply]

theorem measurable_scalingDensity [MeasurableSpace K] [OpensMeasurableSpace K] (β : ℝ) :
    Measurable (scalingDensity K β) := by
  refine measurable_of_continuousOn_compl_singleton 0 fun x hx ↦ ?_
  -- Away from `0` the normalized absolute value, hence the density, is locally constant.
  have hx : x ≠ 0 := hx
  refine ((continuousAt_const (y := scalingDensity K β x)).congr ?_).continuousWithinAt
  filter_upwards [(Valuation.locally_const (v := valuation K) (by simpa using hx))] with y hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hy.symm)
  have habs : normalizedAbsoluteValue K y = normalizedAbsoluteValue K x :=
    le_antisymm ((normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff _ _).2 hy.le)
      ((normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff _ _).2 hy.ge)
  rw [scalingDensity_apply_of_ne_zero hx, scalingDensity_apply_of_ne_zero hy0, habs]

private theorem measurableSet_setOf_normalizedAbsoluteValue_eq [MeasurableSpace K]
    [OpensMeasurableSpace K] (r : ℚ≥0) :
    MeasurableSet {x : K | normalizedAbsoluteValue K x = r} := by
  simp_rw [← NNRat.cast_inj (α := ℝ)]
  exact (isClosed_eq continuous_normalizedAbsoluteValue continuous_const).measurableSet

/-- The ring of integers is `{0}` together with the shells `|x|_K = q ^ (-n)`, `n : ℕ`. -/
private theorem integer_eq_union_iUnion_setOf_normalizedAbsoluteValue_eq :
    (𝒪[K] : Set K) = {0} ∪
      ⋃ n : ℕ, {x | normalizedAbsoluteValue K x = (Nat.card 𝓀[K] : ℚ≥0) ^ (-(n : ℤ))} := by
  have hq : (1 : ℚ≥0) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  ext x
  simp only [SetLike.mem_coe, mem_integer_iff_normalizedAbsoluteValue_le_one,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl rfl
    rw [normalizedAbsoluteValue_apply_ne_zero x hx0] at hx ⊢
    rw [zpow_le_one_iff_right₀ hq, neg_nonpos] at hx
    exact Or.inr ⟨_, by rw [Int.toNat_of_nonneg hx]⟩
  · rintro (rfl | ⟨n, hn⟩)
    · simp
    rw [hn]
    exact zpow_le_one_of_nonpos₀ hq.le (by simp)

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

/-- **Mass of a valuation shell.** For every additive Haar measure `μ` and every integer `k`, the
shell `|x|_K = q ^ (-k)` of elements of normalized valuation `k` has mass
`(1 - q ^ (-β)) q ^ (-kβ) μ(𝒪[K])` for the `β`-scaling measure. -/
theorem withDensity_scalingDensity_setOf_eq_zpow (β : ℝ) (k : ℤ) :
    μ.withDensity (scalingDensity K β)
        {x | normalizedAbsoluteValue K x = (Nat.card 𝓀[K] : ℚ≥0) ^ (-k)} =
      ENNReal.ofReal ((1 - (Nat.card 𝓀[K] : ℝ) ^ (-β)) * (Nat.card 𝓀[K] : ℝ) ^ (-(k * β))) *
        μ 𝒪[K] := by
  have hq : (1 : ℝ) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have hq0 : (0 : ℝ) < Nat.card 𝓀[K] := zero_lt_one.trans hq
  -- Write the shell as the sphere `|x|_K = |a|_K` through `a = ϖ ^ k`; the density is constant
  -- on it.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set a : K := (ϖ : K) ^ k with ha_def
  have ha0 : a ≠ 0 := zpow_ne_zero _ fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have ha : normalizedAbsoluteValue K a = (Nat.card 𝓀[K] : ℚ≥0) ^ (-k) := by
    rw [ha_def, map_zpow₀, normalizedAbsoluteValue_irreducible hϖ, inv_zpow', zpow_neg]
  have hmeas :=
    measurableSet_setOf_normalizedAbsoluteValue_eq (K := K) (normalizedAbsoluteValue K a)
  rw [← ha, withDensity_apply _ hmeas,
    setLIntegral_congr_fun hmeas (g := fun _ ↦ scalingDensity K β a) (fun x (hx : _ = _) ↦ ?_),
    setLIntegral_const, addHaar_setOf_normalizedAbsoluteValue_eq,
    scalingDensity_apply_of_ne_zero ha0, ← mul_assoc]
  · congr 1
    have h1 : (1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 - (Nat.card 𝓀[K] : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_inv_of_pos hq0,
        ENNReal.ofReal_natCast]
    have h2 : ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (normalizedAbsoluteValue K a : ℝ) := by
      have hc : ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ) = normalizedAbsoluteValue K a :=
        map_nnratCast NNReal.toRealHom _
      rw [← ENNReal.ofReal_coe_nnreal, hc]
    have hq1 : 0 < 1 - (Nat.card 𝓀[K] : ℝ)⁻¹ := by linarith [inv_lt_one_of_one_lt₀ hq]
    rw [h1, h2, ← ENNReal.ofReal_mul hq1.le, ← ENNReal.ofReal_mul' (by positivity)]
    congr 1
    have hx : ((Nat.card 𝓀[K] : ℝ) ^ (-k)) ^ (β - 1) * (Nat.card 𝓀[K] : ℝ) ^ (-k) =
        (Nat.card 𝓀[K] : ℝ) ^ (-(k * β)) := by
      rw [← Real.rpow_add_one (by positivity), sub_add_cancel, ← Real.rpow_intCast,
        ← Real.rpow_mul hq0.le]
      push_cast
      ring_nf
    rw [ha, NNRat.cast_zpow, NNRat.cast_natCast, ← hx]
    field_simp
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact ha0 (by simpa using hx.symm)
    rw [scalingDensity_apply_of_ne_zero hx0, scalingDensity_apply_of_ne_zero ha0, hx]

/-- **Mass of the units.** The units `|x|_K = 1` of `𝒪[K]` have mass `(1 - q ^ (-β)) μ(𝒪[K])`
for the `β`-scaling measure. -/
theorem withDensity_scalingDensity_setOf_eq_one (β : ℝ) :
    μ.withDensity (scalingDensity K β) {x | normalizedAbsoluteValue K x = 1} =
      ENNReal.ofReal (1 - (Nat.card 𝓀[K] : ℝ) ^ (-β)) * μ 𝒪[K] := by
  simpa using withDensity_scalingDensity_setOf_eq_zpow μ β 0

omit [μ.IsAddHaarMeasure] in
variable {μ} in
/-- The `β`-scaling measure has no atom at `0`, where its density vanishes. -/
theorem withDensity_scalingDensity_singleton_zero (β : ℝ) :
    μ.withDensity (scalingDensity K β) {0} = 0 := by
  rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_singleton]
  simp

/-- **The case `β = 1`.** The `1`-scaling measure is the Haar measure `μ` itself. -/
@[simp]
theorem withDensity_scalingDensity_one : μ.withDensity (scalingDensity K 1) = μ := by
  have h0 : μ {0} = 0 := by simpa using addHaar_setOf_normalizedAbsoluteValue_le μ (0 : K)
  rw [scalingDensity_one, withDensity_indicator (measurableSet_singleton 0).compl,
    withDensity_one]
  exact restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 h0)

private theorem withDensity_scalingDensity_smul_of_measurableSet {a : K} (ha : a ≠ 0) (β : ℝ)
    {s : Set K} (hs : MeasurableSet s) :
    μ.withDensity (scalingDensity K β) (a • s) =
      ENNReal.ofReal ((normalizedAbsoluteValue K a : ℝ) ^ β) *
        μ.withDensity (scalingDensity K β) s := by
  have hna : ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using ((normalizedAbsoluteValue K).pos ha).ne'
  -- Change variables `x = a • y`: Haar measure pushes forward to `|a|_K⁻¹ • μ`.
  have hcov (g : K → ℝ≥0∞) : ∫⁻ x, g x ∂μ = ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ≥0∞) *
      ∫⁻ y, g (a • y) ∂μ := by
    have h := lintegral_map_equiv g (MeasurableEquiv.smul₀ (α := K) a ha) (μ := μ)
    rw [MeasurableEquiv.coe_smul₀, map_addHaar_smul_eq_inv_normalizedAbsoluteValue_smul μ ha,
      lintegral_smul_measure] at h
    rw [← h, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (by simpa using ha), ← mul_assoc,
      ENNReal.mul_inv_cancel hna ENNReal.coe_ne_top, one_mul]
  have has : MeasurableSet (a • s) := hs.const_smul_of_ne_zero ha
  have hind (y : K) : (a • s).indicator (scalingDensity K β) (a • y) =
      ENNReal.ofReal ((normalizedAbsoluteValue K a : ℝ) ^ (β - 1)) *
        s.indicator (scalingDensity K β) y := by
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem (Set.smul_mem_smul_set hy), Set.indicator_of_mem hy, smul_eq_mul,
        scalingDensity_mul ha]
    · rw [Set.indicator_of_notMem ((Set.smul_mem_smul_set_iff₀ ha _ _).not.2 hy),
        Set.indicator_of_notMem hy, mul_zero]
  have hc : ((normalizedAbsoluteValue K a : ℝ≥0) : ℝ) = normalizedAbsoluteValue K a :=
    map_nnratCast NNReal.toRealHom _
  rw [withDensity_apply _ has, withDensity_apply _ hs, ← lintegral_indicator has, hcov,
    ← lintegral_indicator hs, funext hind, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← mul_assoc, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), hc,
    mul_comm (normalizedAbsoluteValue K a : ℝ),
    ← Real.rpow_add_one (by exact_mod_cast ((normalizedAbsoluteValue K).pos ha).ne'),
    sub_add_cancel]

/-- **Pushforward under dilation.** For `a ≠ 0`, multiplication by `a` pushes the `β`-scaling
measure forward to `|a|_K ^ (-β)` times itself. -/
theorem map_smul_withDensity_scalingDensity {a : K} (ha : a ≠ 0) (β : ℝ) :
    (μ.withDensity (scalingDensity K β)).map (a • ·) =
      ENNReal.ofReal ((normalizedAbsoluteValue K a : ℝ) ^ (-β)) •
        μ.withDensity (scalingDensity K β) := by
  ext s hs
  have hpos : (0 : ℝ) < normalizedAbsoluteValue K a := by
    exact_mod_cast (normalizedAbsoluteValue K).pos ha
  rw [map_apply (measurable_const_smul a) hs, Set.preimage_smul₀ ha,
    withDensity_scalingDensity_smul_of_measurableSet μ (inv_ne_zero ha) β hs, smul_apply,
    smul_eq_mul, map_inv₀, NNRat.cast_inv, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]

/-- **The scaling law.** For every `a ∈ K` and every set `s`, the `β`-scaling measure of `a • s`
is `|a|_K ^ β` times that of `s`. -/
@[simp]
theorem withDensity_scalingDensity_smul (a : K) (β : ℝ) (s : Set K) :
    μ.withDensity (scalingDensity K β) (a • s) =
      ENNReal.ofReal ((normalizedAbsoluteValue K a : ℝ) ^ β) *
        μ.withDensity (scalingDensity K β) s := by
  rcases eq_or_ne a 0 with rfl | ha
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    rw [Set.zero_smul_set hs, ← Set.singleton_zero, withDensity_scalingDensity_singleton_zero]
    rcases eq_or_ne β 0 with rfl | hβ
    · simp [scalingDensity_eq_zero_of_nonpos le_rfl]
    · simp [Real.zero_rpow hβ]
  have hpos : (0 : ℝ) < normalizedAbsoluteValue K a := by
    exact_mod_cast (normalizedAbsoluteValue K).pos ha
  have h := (MeasurableEquiv.smul₀ (α := K) a⁻¹ (inv_ne_zero ha)).map_apply
    (μ := μ.withDensity (scalingDensity K β)) s
  rw [MeasurableEquiv.coe_smul₀, map_smul_withDensity_scalingDensity μ (inv_ne_zero ha),
    Set.preimage_smul_inv₀ ha, smul_apply, smul_eq_mul, map_inv₀, NNRat.cast_inv,
    Real.inv_rpow hpos.le] at h
  rw [← h, Real.rpow_neg hpos.le, inv_inv]

/-- **Normalization.** For `β > 0`, the `β`-scaling measure gives the ring of integers the same
mass as the Haar measure `μ`; in particular it is a probability measure on `𝒪[K]` when
`μ 𝒪[K] = 1`. -/
theorem withDensity_scalingDensity_integer {β : ℝ} (hβ : 0 < β) :
    μ.withDensity (scalingDensity K β) 𝒪[K] = μ 𝒪[K] := by
  have hq : (1 : ℚ≥0) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ ↦
      {x | normalizedAbsoluteValue K x = (Nat.card 𝓀[K] : ℚ≥0) ^ (-(n : ℤ))}) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun x (hm : _ = _) (hn : _ = _) ↦ hmn ?_
    have := zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' (hm.symm.trans hn)
    omega
  have h0 : (0 : K) ∉ ⋃ n : ℕ,
      {x | normalizedAbsoluteValue K x = (Nat.card 𝓀[K] : ℚ≥0) ^ (-(n : ℤ))} := by
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, map_zero, not_exists]
    exact fun n h ↦ (zpow_pos (zero_lt_one.trans hq) _).ne h
  have hmeas (n : ℕ) := measurableSet_setOf_normalizedAbsoluteValue_eq (K := K)
    ((Nat.card 𝓀[K] : ℚ≥0) ^ (-(n : ℤ)))
  conv_lhs => rw [integer_eq_union_iUnion_setOf_normalizedAbsoluteValue_eq]
  rw [measure_union (Set.disjoint_singleton_left.2 h0) (MeasurableSet.iUnion hmeas),
    measure_iUnion hdisj hmeas, withDensity_scalingDensity_singleton_zero, zero_add]
  simp_rw [withDensity_scalingDensity_setOf_eq_zpow]
  rw [ENNReal.tsum_mul_right]
  convert one_mul (μ 𝒪[K])
  -- The shell masses `(1 - r) r ^ n`, with `r = q ^ (-β) < 1`, sum to `1`.
  have hq' : (1 : ℝ) < Nat.card 𝓀[K] := by exact_mod_cast hq
  set r : ℝ := (Nat.card 𝓀[K] : ℝ) ^ (-β) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq' (by linarith)
  have hterm (n : ℕ) :
      (1 - r) * (Nat.card 𝓀[K] : ℝ) ^ (-(((n : ℤ) : ℝ) * β)) = (1 - r) * r ^ n := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    push_cast
    ring_nf
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ mul_nonneg (by linarith) (pow_nonneg hr0 n))
      ((summable_geometric_of_lt_one hr0 hr1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one hr0 hr1, mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]

/-- The `β`-scaling measure is finite on compact sets. For `β > 0`, a compact set lies in some
ball `|x|_K ≤ q ^ n`, whose mass is `q ^ (nβ) μ(𝒪[K])` by the scaling law; for `β ≤ 0` the
measure is zero. -/
instance isFiniteMeasureOnCompacts_withDensity_scalingDensity (β : ℝ) :
    IsFiniteMeasureOnCompacts (μ.withDensity (scalingDensity K β)) := by
  refine ⟨fun s hs ↦ ?_⟩
  rcases le_or_gt β 0 with hβ | hβ
  · simp [scalingDensity_eq_zero_of_nonpos hβ]
  have hq : (1 : ℝ) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  obtain ⟨M, hM⟩ := hs.bddAbove_image continuous_normalizedAbsoluteValue.continuousOn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hsub : s ⊆ ((ϖ : K) ^ (-(n : ℤ))) • (𝒪[K] : Set K) := by
    intro x hx
    rw [smul_integer_eq_setOf_normalizedAbsoluteValue_le, Set.mem_ofPred_eq, map_zpow₀,
      normalizedAbsoluteValue_irreducible hϖ, inv_zpow', neg_neg, zpow_natCast]
    have h : (normalizedAbsoluteValue K x : ℝ) ≤ (Nat.card 𝓀[K] : ℝ) ^ n :=
      (hM ⟨x, hx, rfl⟩).trans hn.le
    exact_mod_cast h
  refine (measure_mono hsub).trans_lt ?_
  rw [withDensity_scalingDensity_smul, withDensity_scalingDensity_integer μ hβ]
  have hcpt : IsCompact (𝒪[K] : Set K) := by
    simpa using (integerPositiveCompacts K).isCompact
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcpt.measure_lt_top

end MeasureTheory.Measure
