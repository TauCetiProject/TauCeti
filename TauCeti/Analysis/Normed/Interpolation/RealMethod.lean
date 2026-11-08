/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import TauCeti.Analysis.Normed.Interpolation.KFunctional
public import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# The real interpolation method

For a compatible couple `(X₀, X₁)`, a real `θ` and `q ∈ [1, ∞]`, the real interpolation space
`(X₀, X₁)_{θ,q}` of the `K`-method consists of the elements `u` of the sum space `X₀ + X₁` for
which `t ↦ t ^ (-θ) K(t, u)` lies in `L^q(dt / t)` on `(0, ∞)`, with the norm

`‖u‖_{θ,q} = ‖t ↦ t ^ (-θ) K(t, u)‖_{L^q(dt / t)}`.

Here `K` is Peetre's `K`-functional `CompatibleCouple.kFunctional` and `dt / t` is
`TauCeti.multHaar`. The case `q = ∞`, where the norm is the essential supremum of
`t ^ (-θ) K(t, u)`, is included. The interesting range is `0 < θ < 1`, where the intersection
`X₀ ∩ X₁` embeds into `(X₀, X₁)_{θ,q}`; the other constructions need no condition on `θ`.

## Main declarations

* `CompatibleCouple.kMethodENorm θ q u`: the norm `‖t ^ (-θ) K(t, u)‖_{L^q(dt / t)}` in `[0, ∞]`
  of an element of the sum space.
* `CompatibleCouple.kMethod θ q`: the space `(X₀, X₁)_{θ,q}` as a submodule of the sum space.
* `CompatibleCouple.KMethodSpace θ q`: the same space as a type, normed by `‖·‖_{θ,q}`. It is a
  normed space for `1 ≤ q` and a `T₁` ambient space, and a Banach space when `X₀` and `X₁` are.
* `KMethodSpace.toSum`: the continuous inclusion into the sum space, with
  `‖u‖ ≤ c_{θ,q}⁻¹ ‖u‖_{θ,q}` (`KMethodSpace.norm_toSumₗ_le`), from the lower bound
  `c_{θ,q} ‖u‖ ≤ ‖u‖_{θ,q}` (`CompatibleCouple.kMethodConst_mul_enorm_le_kMethodENorm`).
* `KMethodSpace.ofInter`: for `0 < θ < 1`, the continuous inclusion of the intersection, with
  `‖x‖_{θ,q} ≤ c_{θ,q} ‖x‖`, where `c_{θ,q} = ‖t ^ (-θ) min 1 t‖_{L^q(dt / t)}` is
  `CompatibleCouple.kMethodConst θ q`.
* `KMethodSpace.map`: over a nontrivially normed field, a linear map `T` of sum spaces
  restricting to continuous linear maps `X₀ →L[𝕜] Y₀` and `X₁ →L[𝕜] Y₁` induces a continuous
  linear map of the real interpolation spaces. For any endpoint bounds `M₀`, `M₁` it multiplies
  the norm by at most `M₀ ^ (1 - θ) * M₁ ^ θ` (`KMethodSpace.norm_map_le`,
  `KMethodSpace.opNorm_map_le`; the underlying estimate `CompatibleCouple.kMethodENorm_map_le`
  holds over any normed field). It respects identities and composition
  (`KMethodSpace.map_id`, `KMethodSpace.map_comp`). Thus the real method is an exact
  interpolation functor of exponent `θ`. Endpoint contractions induce a contraction
  (`KMethodSpace.norm_map_le_of_norm_le`).
* `CompatibleCouple.kMethod_eq_comap_of_leftInverse`,
  `CompatibleCouple.kMethod_eq_map_of_leftInverse`: if `(X₀, X₁)` is a retract of `(Y₀, Y₁)`,
  with morphisms of couples `I` and `P` such that `P ∘ I = id`, then `u ∈ (X₀, X₁)_{θ,q}` exactly
  when `I u ∈ (Y₀, Y₁)_{θ,q}`, and `(X₀, X₁)_{θ,q} = P ((Y₀, Y₁)_{θ,q})`. The norms of `u` and
  `I u` are equivalent (`CompatibleCouple.kMethodENorm_le_of_leftInverse`,
  `KMethodSpace.norm_le_mul_norm_map_of_leftInverse`), and the induced map of `P` is a left
  inverse of that of `I` (`KMethodSpace.leftInverse_map`).
* `KMethodSpace.mapEquiv`: isomorphisms of the endpoints, compatible on the sum spaces, induce an
  isomorphism of the real interpolation spaces, isometric when the endpoint isomorphisms are
  (`KMethodSpace.norm_mapEquiv`).
* `CompatibleCouple.kMethodConst_eq`: `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)` for `0 < θ < 1` and
  finite `q ≠ 0`, and `c_{θ,∞} = 1` for `0 ≤ θ ≤ 1` (`CompatibleCouple.kMethodConst_top`); by
  `CompatibleCouple.kMethodENorm_refl`, for the couple `(X, X)` the norm is
  `‖u‖_{θ,q} = c_{θ,q} ‖u‖`. For instance `c_{1/2,2} = 2 ^ (1 / 2)` and `c_{1/2,∞} = 1`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §3.1 (Theorem 3.1.2), §3.4 (Theorem 3.4.2(a)) and, for retracts, §6.4
  (Theorem 6.4.2).
-/

public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti

namespace CompatibleCouple

/-! ### The constant `c_{θ,q}` -/

/-- The constant `c_{θ,q} = ‖t ↦ t ^ (-θ) min 1 t‖_{L^q(dt / t)}`. It is the `K`-method norm of a
unit vector for the couple `(X, X)` (`kMethodENorm_refl`), and bounds the norm of the inclusion
of the intersection into the real interpolation space. It is finite for `0 < θ < 1`
(`kMethodConst_lt_top`), with the value `(θ (1 - θ) q) ^ (-1 / q)` for finite `q ≠ 0`
(`kMethodConst_eq`) and the value `1` for `q = ∞` (`kMethodConst_top`). -/
def kMethodConst (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ => t ^ (-θ) * min 1 t) q multHaar

theorem kMethodConst_def (θ : ℝ) (q : ℝ≥0∞) :
    kMethodConst θ q = eLpNorm (fun t : ℝ => t ^ (-θ) * min 1 t) q multHaar :=
  (rfl)

private theorem continuousOn_rpow_neg_mul_min (θ : ℝ) :
    ContinuousOn (fun t : ℝ => t ^ (-θ) * min 1 t) (Ioi 0) :=
  (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul
    (continuous_const.min continuous_id).continuousOn

/-- The integrand of `c_{θ,q} ^ q` in the variable `t = e^s`. -/
private theorem enorm_rpow_neg_mul_min_exp_rpow (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ‖Real.exp s ^ (-θ) * min 1 (Real.exp s)‖ₑ ^ r =
      (Iic 0).indicator (fun s => ENNReal.ofReal (Real.exp ((1 - θ) * r * s))) s +
        (Iic 0)ᶜ.indicator (fun s => ENNReal.ofReal (Real.exp (-(θ * r) * s))) s := by
  rw [Real.enorm_of_nonneg (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) hr]
  by_cases hs : s ≤ 0
  · rw [indicator_of_mem (mem_Iic.2 hs), indicator_of_notMem (by simpa using hs), add_zero,
      min_eq_right (Real.exp_le_one_iff.2 hs)]
    simp only [← Real.exp_mul, ← Real.exp_add]
    ring_nf
  · rw [indicator_of_notMem (by simpa using hs), indicator_of_mem (by simpa using hs), zero_add,
      min_eq_left (Real.one_le_exp (le_of_not_ge hs)), mul_one]
    simp only [← Real.exp_mul]
    ring_nf

/-- For finite `q ≠ 0` and `0 < θ < 1`, `c_{θ,q} = (θ (1 - θ) q) ^ (-1 / q)`. -/
theorem kMethodConst_eq {θ : ℝ} (hθ : θ ∈ Ioo 0 1) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) :
    kMethodConst θ q = ENNReal.ofReal ((θ * (1 - θ) * q.toReal) ^ (-q.toReal⁻¹)) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  set r := q.toReal with hr_def
  have hr : 0 < r := ENNReal.toReal_pos hq0 hq
  have hθ1' : 0 < 1 - θ := sub_pos.2 hθ1
  -- in the variable `t = e^s`, `c_{θ,q} ^ q` is
  -- `∫_{s ≤ 0} e^{(1 - θ) q s} ds + ∫_{s > 0} e^{-θ q s} ds`
  have hg : AEStronglyMeasurable (fun t : ℝ => t ^ (-θ) * min 1 t) (volume.map Real.exp) :=
    map_volume_exp ▸ (continuousOn_rpow_neg_mul_min θ).aestronglyMeasurable_multHaar
  rw [kMethodConst, ← map_volume_exp, eLpNorm_map_measure hg Real.measurable_exp.aemeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq
      (hg.comp_aemeasurable Real.measurable_exp.aemeasurable)]
  simp only [Function.comp_apply, ← hr_def, enorm_rpow_neg_mul_min_exp_rpow θ hr.le]
  rw [lintegral_add_left ((by fun_prop : Measurable fun s : ℝ =>
      ENNReal.ofReal (Real.exp ((1 - θ) * r * s))).indicator measurableSet_Iic),
    lintegral_indicator measurableSet_Iic, lintegral_indicator measurableSet_Iic.compl, compl_Iic,
    lintegral_Iic_ofReal_exp_mul (by positivity), lintegral_Ioi_ofReal_exp_neg_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  have hsum : ((1 - θ) * r)⁻¹ + (θ * r)⁻¹ = (θ * (1 - θ) * r)⁻¹ := by
    field_simp
    ring
  rw [hsum, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), one_div]

/-- `c_{θ,q}` is nonzero for `q ≠ 0`. -/
theorem kMethodConst_ne_zero (θ : ℝ) {q : ℝ≥0∞} (hq : q ≠ 0) : kMethodConst θ q ≠ 0 := by
  rw [kMethodConst, Ne, eLpNorm_eq_zero_iff hq]
  intro h
  have : (ae multHaar).NeBot :=
    ae_neBot.2 fun h0 => by simpa [h0] using multHaar_Icc_one_exp_one
  obtain ⟨t, ht, hft⟩ := (ae_pos_multHaar.and h).exists
  exact (mul_pos (Real.rpow_pos_of_pos ht _) (lt_min one_pos ht)).ne' hft

/-- For `0 ≤ θ ≤ 1`, `c_{θ,∞} = 1`, so for the couple `(X, X)` the `K`-method norm with
`q = ∞` is the norm of `X` (`kMethodENorm_refl`). -/
theorem kMethodConst_top {θ : ℝ} (hθ : θ ∈ Icc 0 1) : kMethodConst θ ∞ = 1 := by
  have hg : AEStronglyMeasurable (fun t : ℝ => t ^ (-θ) * min 1 t) (volume.map Real.exp) :=
    map_volume_exp ▸ (continuousOn_rpow_neg_mul_min θ).aestronglyMeasurable_multHaar
  have hcont : Continuous fun s : ℝ => ‖Real.exp s ^ (-θ) * min 1 (Real.exp s)‖ₑ :=
    ((Real.continuous_exp.rpow_const fun s => Or.inl (Real.exp_pos s).ne').mul
      (continuous_const.min Real.continuous_exp)).enorm
  rw [kMethodConst, ← map_volume_exp, eLpNorm_map_measure hg Real.measurable_exp.aemeasurable,
    eLpNorm_exponent_top (hg.comp_aemeasurable Real.measurable_exp.aemeasurable), eLpNormEssSup,
    Function.comp_def, ← iSup_eq_essSup fun s _ hs =>
      (isOpen_lt continuous_const hcont).measure_ne_zero volume ⟨s, hs⟩]
  refine le_antisymm (iSup_le fun s => ?_) (le_iSup_of_le 0 (by simp))
  have ht := Real.exp_pos s
  rw [Real.enorm_of_nonneg (by positivity), ENNReal.ofReal_le_one]
  rcases le_total (Real.exp s) 1 with h | h
  · rw [min_eq_right h, ← Real.rpow_add_one ht.ne']
    exact Real.rpow_le_one ht.le h (by linarith [hθ.2])
  · rw [min_eq_left h, mul_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos h (by linarith [hθ.1])

/-- `c_{θ,q}` is finite for `0 < θ < 1`, so the intersection embeds into the real
interpolation space. -/
theorem kMethodConst_lt_top {θ : ℝ} (hθ : θ ∈ Ioo 0 1) (q : ℝ≥0∞) : kMethodConst θ q < ∞ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [kMethodConst, eLpNorm_exponent_zero
      ((continuousOn_rpow_neg_mul_min θ).aestronglyMeasurable_multHaar)]
    exact ENNReal.zero_lt_top
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [kMethodConst_top (Ioo_subset_Icc_self hθ)]
    exact ENNReal.one_lt_top
  · rw [kMethodConst_eq hθ hq0 hq]
    exact ENNReal.ofReal_lt_top

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-! ### The `K`-method norm on the sum space -/

/-- The `K`-method norm `‖t ↦ t ^ (-θ) K(t, u)‖_{L^q(dt / t)}` of an element `u` of the sum space,
with values in `[0, ∞]`. -/
def kMethodENorm (θ : ℝ) (q : ℝ≥0∞) (u : C.SumSpace) : ℝ≥0∞ :=
  eLpNorm (fun t => t ^ (-θ) * C.kFunctional t u) q multHaar

theorem kMethodENorm_def (θ : ℝ) (q : ℝ≥0∞) (u : C.SumSpace) :
    C.kMethodENorm θ q u = eLpNorm (fun t => t ^ (-θ) * C.kFunctional t u) q multHaar :=
  (rfl)

variable {C} {θ : ℝ} {q : ℝ≥0∞}

/-- The integrand `t ↦ t ^ (-θ) K(t, u)` of the `K`-method norm is continuous on `(0, ∞)`, hence
almost everywhere strongly measurable for `dt / t`. -/
theorem aestronglyMeasurable_rpow_neg_mul_kFunctional (θ : ℝ) (u : C.SumSpace) :
    AEStronglyMeasurable (fun t => t ^ (-θ) * C.kFunctional t u) multHaar :=
  ContinuousOn.aestronglyMeasurable_multHaar <|
    (continuousOn_id.rpow_const fun _ ht => Or.inl (ne_of_gt ht)).mul (continuousOn_kFunctional u)

@[simp]
theorem kMethodENorm_zero : C.kMethodENorm θ q 0 = 0 := by
  rw [kMethodENorm, eLpNorm_congr_ae (g := 0), eLpNorm_zero]
  filter_upwards [ae_pos_multHaar] with t ht
  simp [kFunctional_zero ht.le]

/-- A pointwise bound `t ^ (-θ) K(t, u) ≤ g t` for `t > 0` bounds the `K`-method norm of `u` by the
`L^q(dt / t)` norm of `g`. -/
theorem kMethodENorm_le_eLpNorm_of_le {u : C.SumSpace} {g : ℝ → ℝ}
    (h : ∀ t > 0, t ^ (-θ) * C.kFunctional t u ≤ g t) :
    C.kMethodENorm θ q u ≤ eLpNorm g q multHaar := by
  refine eLpNorm_mono_ae_real (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u) ?_
  filter_upwards [ae_pos_multHaar] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]
  exact h t ht

private theorem kMethodENorm_add_le_eLpNorm (u v : C.SumSpace) :
    C.kMethodENorm θ q (u + v) ≤
      eLpNorm ((fun t => t ^ (-θ) * C.kFunctional t u) + fun t => t ^ (-θ) * C.kFunctional t v)
        q multHaar :=
  kMethodENorm_le_eLpNorm_of_le fun t ht => by
    rw [Pi.add_apply, ← mul_add]
    exact mul_le_mul_of_nonneg_left (kFunctional_add_le ht.le u v) (Real.rpow_nonneg ht.le _)

/-- For `1 ≤ q` the `K`-method norm satisfies the triangle inequality. -/
theorem kMethodENorm_add_le (hq : 1 ≤ q) (u v : C.SumSpace) :
    C.kMethodENorm θ q (u + v) ≤ C.kMethodENorm θ q u + C.kMethodENorm θ q v :=
  (kMethodENorm_add_le_eLpNorm u v).trans (eLpNorm_add_le hq)

/-- The `K`-method norm is absolutely homogeneous: `‖c • u‖_{θ,q} = ‖c‖ ‖u‖_{θ,q}`. -/
theorem kMethodENorm_smul (c : 𝕜) (u : C.SumSpace) :
    C.kMethodENorm θ q (c • u) = ‖c‖ₑ * C.kMethodENorm θ q u := by
  have h : (fun t => t ^ (-θ) * C.kFunctional t (c • u)) =ᵐ[multHaar]
      ‖c‖ • fun t => t ^ (-θ) * C.kFunctional t u := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [kFunctional_smul ht.le, Pi.smul_apply, smul_eq_mul]
    ring
  rw [kMethodENorm, eLpNorm_congr_ae h, eLpNorm_const_smul, enorm_norm, kMethodENorm]

@[simp]
theorem kMethodENorm_neg (u : C.SumSpace) : C.kMethodENorm θ q (-u) = C.kMethodENorm θ q u := by
  rw [← neg_one_smul 𝕜 u, kMethodENorm_smul, enorm_neg, enorm_one, one_mul]

/-- The `K`-method norm dominates the sum norm: `c_{θ,q} ‖u‖ ≤ ‖u‖_{θ,q}`, with equality for the
couple `(X, X)` (`kMethodENorm_refl`). -/
theorem kMethodConst_mul_enorm_le_kMethodENorm (u : C.SumSpace) :
    kMethodConst θ q * ‖u‖ₑ ≤ C.kMethodENorm θ q u := by
  calc kMethodConst θ q * ‖u‖ₑ = eLpNorm (‖u‖ • fun t : ℝ => t ^ (-θ) * min 1 t) q multHaar := by
        rw [eLpNorm_const_smul, enorm_norm, mul_comm, kMethodConst]
    _ ≤ C.kMethodENorm θ q u := by
        refine eLpNorm_mono_ae_real
          ((continuousOn_rpow_neg_mul_min θ).aestronglyMeasurable_multHaar.const_smul _) ?_
        filter_upwards [ae_pos_multHaar] with t ht
        have h0 := Real.rpow_nonneg ht.le (-θ)
        rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg
          (mul_nonneg (norm_nonneg u) (mul_nonneg h0 (le_min zero_le_one ht.le)))]
        calc ‖u‖ * (t ^ (-θ) * min 1 t) = t ^ (-θ) * (min 1 t * ‖u‖) := by ring
          _ ≤ t ^ (-θ) * C.kFunctional t u := by
              gcongr
              exact min_one_mul_norm_le_kFunctional ht.le u

/-- For `q ≠ 0` and a `T₁` ambient space, the `K`-method norm is definite: `‖u‖_{θ,q} = 0` only
for `u = 0`. -/
theorem kMethodENorm_eq_zero_iff [T1Space V] (hq : q ≠ 0) {u : C.SumSpace} :
    C.kMethodENorm θ q u = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ kMethodENorm_zero⟩
  have h' := kMethodConst_mul_enorm_le_kMethodENorm (θ := θ) (q := q) u
  rw [h, nonpos_iff_eq_zero, mul_eq_zero, or_iff_right (kMethodConst_ne_zero θ hq)] at h'
  exact norm_eq_zero.1 (by rw [← toReal_enorm, h', ENNReal.toReal_zero])

/-- On the intersection, `‖x‖_{θ,q} ≤ c_{θ,q} ‖x‖`. -/
theorem kMethodENorm_fstToSum_interFst_le (x : C.inter) :
    C.kMethodENorm θ q (C.fstToSum (C.interFst x)) ≤ kMethodConst θ q * ‖x‖ₑ := by
  calc C.kMethodENorm θ q (C.fstToSum (C.interFst x)) ≤
        eLpNorm (‖x‖ • fun t : ℝ => t ^ (-θ) * min 1 t) q multHaar :=
        kMethodENorm_le_eLpNorm_of_le fun t ht => by
        rw [Pi.smul_apply, smul_eq_mul]
        calc t ^ (-θ) * C.kFunctional t (C.fstToSum (C.interFst x)) ≤
              t ^ (-θ) * (min 1 t * ‖x‖) := by
              gcongr
              exact kFunctional_fstToSum_interFst_le ht.le x
          _ = ‖x‖ * (t ^ (-θ) * min 1 t) := by ring
    _ = kMethodConst θ q * ‖x‖ₑ := by
        rw [eLpNorm_const_smul, enorm_norm, mul_comm, kMethodConst]

/-- For the couple `(X, X)`, `‖u‖_{θ,q} = c_{θ,q} ‖u‖`. -/
theorem kMethodENorm_refl {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (u : (refl 𝕜 X).SumSpace) : (refl 𝕜 X).kMethodENorm θ q u = kMethodConst θ q * ‖u‖ₑ := by
  have h : (fun t => t ^ (-θ) * (refl 𝕜 X).kFunctional t u) =ᵐ[multHaar]
      ‖u‖ • fun t : ℝ => t ^ (-θ) * min 1 t := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [kFunctional_refl ht.le, Pi.smul_apply, smul_eq_mul]
    ring
  rw [kMethodENorm, eLpNorm_congr_ae h, eLpNorm_const_smul, enorm_norm, mul_comm, kMethodConst]

/-! ### The real interpolation space -/

variable (C) in
/-- The real interpolation space `(X₀, X₁)_{θ,q}` of the `K`-method, as a submodule of the sum
space: the `u` for which `t ↦ t ^ (-θ) K(t, u)` lies in `L^q(dt / t)`. -/
def kMethod (θ : ℝ) (q : ℝ≥0∞) : Submodule 𝕜 C.SumSpace where
  carrier := {u | C.kMethodENorm θ q u < ∞}
  zero_mem' := by simp
  add_mem' {u v} hu hv := (kMethodENorm_add_le_eLpNorm u v).trans_lt <|
    eLpNorm_add_lt_top hu hv
  smul_mem' c u hu := by
    simp only [mem_ofPred_eq, kMethodENorm_smul]
    exact ENNReal.mul_lt_top enorm_lt_top hu

theorem mem_kMethod_iff {u : C.SumSpace} : u ∈ C.kMethod θ q ↔ C.kMethodENorm θ q u < ∞ :=
  Iff.rfl

theorem mem_kMethod_iff_memLp {u : C.SumSpace} :
    u ∈ C.kMethod θ q ↔ MemLp (fun t => t ^ (-θ) * C.kFunctional t u) q multHaar := by
  rw [mem_kMethod_iff, kMethodENorm_def, memLp_iff]

/-- For `0 < θ < 1` the intersection lies in the real interpolation space. -/
theorem fstToSum_interFst_mem_kMethod (hθ : θ ∈ Ioo 0 1) (x : C.inter) :
    C.fstToSum (C.interFst x) ∈ C.kMethod θ q :=
  (kMethodENorm_fstToSum_interFst_le x).trans_lt
    (ENNReal.mul_lt_top (kMethodConst_lt_top hθ q) enorm_lt_top)

/-- For `0 < θ < 1`, the real interpolation space of the couple `(X, X)` is all of `X`. -/
theorem kMethod_refl_eq_top {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (hθ : θ ∈ Ioo 0 1) : (refl 𝕜 X).kMethod θ q = ⊤ :=
  Submodule.eq_top_iff'.2 fun u => by
    rw [mem_kMethod_iff, kMethodENorm_refl]
    exact ENNReal.mul_lt_top (kMethodConst_lt_top hθ q) enorm_lt_top

variable (C) in
/-- The real interpolation space `(X₀, X₁)_{θ,q}` of the `K`-method, as a type: the elements of
`C.kMethod θ q`, normed by the `K`-method norm `‖u‖_{θ,q} = ‖t ↦ t ^ (-θ) K(t, u)‖_{L^q(dt / t)}`
instead of the sum norm. It is a normed space for `1 ≤ q` and a `T₁` ambient space, and a Banach
space when `X₀` and `X₁` are. -/
def KMethodSpace (θ : ℝ) (q : ℝ≥0∞) : Type _ :=
  ↥(C.kMethod θ q)

namespace KMethodSpace

instance : AddCommGroup (C.KMethodSpace θ q) :=
  inferInstanceAs (AddCommGroup (C.kMethod θ q))

instance : Module 𝕜 (C.KMethodSpace θ q) :=
  inferInstanceAs (Module 𝕜 (C.kMethod θ q))

/-- The element of the real interpolation space given by an element of the sum space with
finite `K`-method norm. -/
def mk (u : C.SumSpace) (hu : u ∈ C.kMethod θ q) : C.KMethodSpace θ q :=
  (⟨u, hu⟩ : ↥(C.kMethod θ q))

/-- The inclusion of the real interpolation space into the sum space, as a linear map. `toSum` is
its continuous version. -/
def toSumₗ : C.KMethodSpace θ q →ₗ[𝕜] C.SumSpace :=
  (C.kMethod θ q).subtype

@[simp]
theorem toSumₗ_mk (u : C.SumSpace) (hu : u ∈ C.kMethod θ q) : toSumₗ (mk u hu) = u :=
  (rfl)

theorem toSumₗ_mem (u : C.KMethodSpace θ q) : toSumₗ u ∈ C.kMethod θ q :=
  -- `KMethodSpace` is by definition the subtype `↥(C.kMethod θ q)`
  (C.kMethod θ q).coe_mem u

@[simp]
theorem mk_toSumₗ (u : C.KMethodSpace θ q) : mk (toSumₗ u) (toSumₗ_mem u) = u :=
  (rfl)

theorem toSumₗ_injective : Function.Injective (toSumₗ : C.KMethodSpace θ q → C.SumSpace) :=
  Subtype.val_injective

@[ext]
theorem ext {u v : C.KMethodSpace θ q} (h : toSumₗ u = toSumₗ v) : u = v :=
  toSumₗ_injective h

private theorem kMethodENorm_toSumₗ_lt_top (u : C.KMethodSpace θ q) :
    C.kMethodENorm θ q (toSumₗ u) < ∞ :=
  toSumₗ_mem u

variable [T1Space V] [hq : Fact (1 ≤ q)]

private theorem q_ne_zero : q ≠ 0 :=
  (zero_lt_one.trans_le hq.out).ne'

instance : NormedAddCommGroup (C.KMethodSpace θ q) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun u := (C.kMethodENorm θ q (toSumₗ u)).toReal
      map_zero' := by simp
      add_le' u v := by
        rw [map_add, ← ENNReal.toReal_add (kMethodENorm_toSumₗ_lt_top u).ne
          (kMethodENorm_toSumₗ_lt_top v).ne]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(kMethodENorm_toSumₗ_lt_top u).ne,
          (kMethodENorm_toSumₗ_lt_top v).ne⟩) (kMethodENorm_add_le hq.out _ _)
      neg' u := by simp
      eq_zero_of_map_eq_zero' u hu := by
        rw [ENNReal.toReal_eq_zero_iff, or_iff_left (kMethodENorm_toSumₗ_lt_top u).ne,
          kMethodENorm_eq_zero_iff q_ne_zero] at hu
        exact toSumₗ_injective (hu.trans (map_zero _).symm) }

theorem norm_def (u : C.KMethodSpace θ q) : ‖u‖ = (C.kMethodENorm θ q (toSumₗ u)).toReal :=
  (rfl)

theorem ofReal_norm (u : C.KMethodSpace θ q) :
    ENNReal.ofReal ‖u‖ = C.kMethodENorm θ q (toSumₗ u) :=
  ENNReal.ofReal_toReal (kMethodENorm_toSumₗ_lt_top u).ne

theorem norm_mk (u : C.SumSpace) (hu : u ∈ C.kMethod θ q) :
    ‖mk u hu‖ = (C.kMethodENorm θ q u).toReal :=
  (rfl)

instance : NormedSpace 𝕜 (C.KMethodSpace θ q) where
  norm_smul_le c u := by
    rw [norm_def, norm_def, map_smul, kMethodENorm_smul, ENNReal.toReal_mul, toReal_enorm]

/-- The inclusion into the sum space is bounded: `‖u‖ ≤ c_{θ,q}⁻¹ ‖u‖_{θ,q}`. -/
theorem norm_toSumₗ_le (u : C.KMethodSpace θ q) :
    ‖toSumₗ u‖ ≤ (kMethodConst θ q).toReal⁻¹ * ‖u‖ := by
  have h := kMethodConst_mul_enorm_le_kMethodENorm (θ := θ) (q := q) (toSumₗ u)
  rw [← ofReal_norm] at h
  rcases eq_or_ne (kMethodConst θ q) ∞ with hc | hc
  · -- an infinite constant forces `u = 0`
    have h0 : ‖toSumₗ u‖ₑ = 0 := by
      by_contra h0
      rw [hc, ENNReal.top_mul h0] at h
      exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
    rw [← toReal_enorm, h0, ENNReal.toReal_zero]
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (norm_nonneg u)
  · rw [le_inv_mul_iff₀ (ENNReal.toReal_pos (kMethodConst_ne_zero θ q_ne_zero) hc),
      ← toReal_enorm (toSumₗ u), ← ENNReal.toReal_mul]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg u) h

/-- The continuous inclusion of the real interpolation space into the sum space. -/
def toSum : C.KMethodSpace θ q →L[𝕜] C.SumSpace :=
  LinearMap.mkContinuous (toSumₗ (C := C) (θ := θ) (q := q)) (kMethodConst θ q).toReal⁻¹
    norm_toSumₗ_le

@[simp]
theorem toSum_apply (u : C.KMethodSpace θ q) : toSum u = toSumₗ u :=
  (rfl)

/-- The real interpolation space of a couple of Banach spaces is a Banach space. -/
instance [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace (C.KMethodSpace θ q) := by
  -- a Cauchy sequence converges in the sum space, and Fatou's lemma bounds the `K`-method norm
  -- of the difference with the limit
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (toSum.uniformContinuous.comp_cauchySeq hu)
  have key (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ n ≥ N,
      C.kMethodENorm θ q (w - toSumₗ (u n)) ≤ ENNReal.ofReal ε := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    calc C.kMethodENorm θ q (w - toSumₗ (u n)) ≤
          liminf (fun m => C.kMethodENorm θ q (toSumₗ (u m) - toSumₗ (u n))) atTop := by
          refine Lp.eLpNorm_lim_le_liminf_eLpNorm
            (fun m => aestronglyMeasurable_rpow_neg_mul_kFunctional θ _) _
            (aestronglyMeasurable_rpow_neg_mul_kFunctional θ _) ?_
          filter_upwards [ae_pos_multHaar] with t ht
          exact (((continuous_kFunctional ht.le).tendsto _).comp
            (hw.sub_const (toSumₗ (u n)))).const_mul _
      _ ≤ ENNReal.ofReal ε := by
          refine liminf_le_of_frequently_le' ((eventually_ge_atTop N).frequently.mono
            fun m hm => ?_)
          rw [← map_sub, ← ofReal_norm, ← dist_eq_norm]
          exact ENNReal.ofReal_le_ofReal (hN m hm n hn).le
  obtain ⟨N, hN⟩ := key 1 one_pos
  have hw : w ∈ C.kMethod θ q := by
    rw [← sub_add_cancel w (toSumₗ (u N))]
    exact Submodule.add_mem _ ((hN N le_rfl).trans_lt ENNReal.ofReal_lt_top) (toSumₗ_mem _)
  refine ⟨mk w hw, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := key (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm, norm_def, map_sub, toSumₗ_mk]
  exact (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le (hN n hn)).trans_lt (half_lt_self hε)

/-! ### The inclusion of the intersection -/

private theorem norm_mk_fstToSum_interFst_le (hθ : θ ∈ Ioo 0 1) (x : C.inter) :
    ‖mk (q := q) (C.fstToSum (C.interFst x)) (fstToSum_interFst_mem_kMethod hθ x)‖ ≤
      (kMethodConst θ q).toReal * ‖x‖ := by
  rw [norm_mk, ← toReal_enorm x, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (kMethodConst_lt_top hθ q).ne enorm_ne_top)
    (kMethodENorm_fstToSum_interFst_le x)

variable (θ q) in
/-- For `0 < θ < 1`, the continuous inclusion `X₀ ∩ X₁ → (X₀, X₁)_{θ,q}`, of norm at most
`c_{θ,q}`. -/
def ofInter (hθ : θ ∈ Ioo 0 1) : C.inter →L[𝕜] C.KMethodSpace θ q :=
  LinearMap.mkContinuous
    { toFun x := mk (C.fstToSum (C.interFst x)) (fstToSum_interFst_mem_kMethod hθ x)
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp }
    (kMethodConst θ q).toReal (norm_mk_fstToSum_interFst_le hθ)

@[simp]
theorem toSumₗ_ofInter (hθ : θ ∈ Ioo 0 1) (x : C.inter) :
    toSumₗ (ofInter θ q hθ x) = C.fstToSum (C.interFst x) :=
  (rfl)

/-- The norm of `x ∈ X₀ ∩ X₁` in the real interpolation space is at most `c_{θ,q} ‖x‖`. -/
theorem norm_ofInter_le (hθ : θ ∈ Ioo 0 1) (x : C.inter) :
    ‖ofInter θ q hθ x‖ ≤ (kMethodConst θ q).toReal * ‖x‖ :=
  norm_mk_fstToSum_interFst_le hθ x

/-- For the couple `(X, X)`, `‖u‖_{θ,q} = c_{θ,q} ‖u‖`. -/
theorem norm_refl {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (u : (refl 𝕜 X).KMethodSpace θ q) : ‖u‖ = (kMethodConst θ q).toReal * ‖toSumₗ u‖ := by
  rw [norm_def, kMethodENorm_refl, ENNReal.toReal_mul, toReal_enorm]

end KMethodSpace

/-! ### Functoriality -/

section Map

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁]
  [NormedSpace 𝕜 Y₁] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W]
  {D : CompatibleCouple 𝕜 Y₀ Y₁ W}

/-- A linear map `T` between the sum spaces of two couples that restricts to maps
`T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` with `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖`, where `M₀`, `M₁`
are positive, multiplies the `K`-method norm by at most `M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem kMethodENorm_map_le (T : C.SumSpace →ₗ[𝕜] D.SumSpace) {T₀ : X₀ → Y₀} {T₁ : X₁ → Y₁}
    (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.SumSpace) :
    D.kMethodENorm θ q (T u) ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.kMethodENorm θ q u := by
  set c := M₁ / M₀ with hc_def
  have hc : 0 < c := div_pos hM₁ hM₀
  have hmp : MeasurePreserving (c * ·) multHaar multHaar :=
    ⟨measurable_const_mul c, map_multHaar_mul_left hc⟩
  -- the constant `M₀` is `M₀ ^ (1 - θ) * M₁ ^ θ * c ^ (-θ)`
  have hconst : M₀ ^ (1 - θ) * M₁ ^ θ * c ^ (-θ) = M₀ := by
    rw [hc_def, Real.div_rpow hM₁.le hM₀.le, Real.rpow_sub hM₀, Real.rpow_one, Real.rpow_neg hM₁.le,
      Real.rpow_neg hM₀.le]
    have h₀' := (Real.rpow_pos_of_pos hM₀ θ).ne'
    have h₁' := (Real.rpow_pos_of_pos hM₁ θ).ne'
    field_simp
  have hct (t : ℝ) : t * M₁ / M₀ = c * t := by
    rw [hc_def]
    ring
  calc D.kMethodENorm θ q (T u) ≤ eLpNorm ((M₀ ^ (1 - θ) * M₁ ^ θ) •
        ((fun t => t ^ (-θ) * C.kFunctional t u) ∘ (c * ·))) q multHaar :=
        kMethodENorm_le_eLpNorm_of_le fun t ht => by
        rw [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
        calc t ^ (-θ) * D.kFunctional t (T u) ≤
              t ^ (-θ) * (M₀ * C.kFunctional (t * M₁ / M₀) u) := by
              gcongr
              exact kFunctional_map_le T hT₀ hT₁ hM₀ h₀ h₁ ht.le u
          _ = M₀ ^ (1 - θ) * M₁ ^ θ * ((c * t) ^ (-θ) * C.kFunctional (c * t) u) := by
              rw [hct, Real.mul_rpow hc.le ht.le]
              linear_combination (-(t ^ (-θ) * C.kFunctional (c * t) u)) * hconst
    _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.kMethodENorm θ q u := by
        rw [eLpNorm_const_smul, eLpNorm_comp_measurePreserving
          (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u) hmp,
          Real.enorm_of_nonneg (by positivity), kMethodENorm]

/-- A linear map `P` of sum spaces is a left inverse of another one `I` as soon as their
restrictions to the endpoints are left inverses of each other. -/
theorem leftInverse_of_leftInverse {I : C.SumSpace →ₗ[𝕜] D.SumSpace}
    {P : D.SumSpace →ₗ[𝕜] C.SumSpace} {I₀ : X₀ → Y₀} {I₁ : X₁ → Y₁} {P₀ : Y₀ → X₀}
    {P₁ : Y₁ → X₁} (hI₀ : ∀ x, I (C.fstToSum x) = D.fstToSum (I₀ x))
    (hI₁ : ∀ x, I (C.sndToSum x) = D.sndToSum (I₁ x))
    (hP₀ : ∀ y, P (D.fstToSum y) = C.fstToSum (P₀ y))
    (hP₁ : ∀ y, P (D.sndToSum y) = C.sndToSum (P₁ y)) (h₀ : Function.LeftInverse P₀ I₀)
    (h₁ : Function.LeftInverse P₁ I₁) : Function.LeftInverse P I := by
  intro u
  obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
  rw [map_add, map_add, hI₀, hI₁, hP₀, hP₁, h₀, h₁]

/-- **Retracts.** Let `P` be a linear map of sum spaces restricting to maps `P₀ : Y₀ → X₀` and
`P₁ : Y₁ → X₁` with `‖P₀ y‖ ≤ N₀ ‖y‖` and `‖P₁ y‖ ≤ N₁ ‖y‖`, where `N₀`, `N₁` are positive. If `P`
is a left inverse of a linear map `I` of sum spaces, then the `K`-method norm of `u` is at most
`N₀ ^ (1 - θ) * N₁ ^ θ` times that of `I u`. When `I` is a morphism of couples as well,
`kMethodENorm_map_le` gives the reverse estimate, so the two norms are equivalent. -/
theorem kMethodENorm_le_of_leftInverse {I : C.SumSpace →ₗ[𝕜] D.SumSpace}
    (P : D.SumSpace →ₗ[𝕜] C.SumSpace) {P₀ : Y₀ → X₀} {P₁ : Y₁ → X₁}
    (hP₀ : ∀ y, P (D.fstToSum y) = C.fstToSum (P₀ y))
    (hP₁ : ∀ y, P (D.sndToSum y) = C.sndToSum (P₁ y)) (hPI : Function.LeftInverse P I)
    {N₀ N₁ : ℝ} (hN₀ : 0 < N₀) (hN₁ : 0 < N₁) (h₀ : ∀ y, ‖P₀ y‖ ≤ N₀ * ‖y‖)
    (h₁ : ∀ y, ‖P₁ y‖ ≤ N₁ * ‖y‖) (u : C.SumSpace) :
    C.kMethodENorm θ q u ≤ ENNReal.ofReal (N₀ ^ (1 - θ) * N₁ ^ θ) * D.kMethodENorm θ q (I u) := by
  have h := kMethodENorm_map_le P hP₀ hP₁ hN₀ hN₁ h₀ h₁ (θ := θ) (q := q) (I u)
  rwa [hPI u] at h

end Map

end CompatibleCouple

/-! ### Operator norms and functoriality -/

namespace CompatibleCouple

variable {𝕜 X₀ X₁ V Y₀ Y₁ W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {C : CompatibleCouple 𝕜 X₀ X₁ V} {D : CompatibleCouple 𝕜 Y₀ Y₁ W} {θ : ℝ} {q : ℝ≥0∞}
  [Fact (1 ≤ q)]

omit [T1Space V] [T1Space W] [Fact (1 ≤ q)] in
/-- A linear map `T` of sum spaces that restricts to continuous linear maps `T₀ : X₀ →L[𝕜] Y₀`
and `T₁ : X₁ →L[𝕜] Y₁` maps `(X₀, X₁)_{θ,q}` into `(Y₀, Y₁)_{θ,q}`. -/
theorem map_mem_kMethod (T : C.SumSpace →ₗ[𝕜] D.SumSpace) {T₀ : X₀ →L[𝕜] Y₀}
    {T₁ : X₁ →L[𝕜] Y₁} (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) {u : C.SumSpace}
    (hu : u ∈ C.kMethod θ q) : T u ∈ D.kMethod θ q := by
  obtain ⟨M₀, hM₀, h₀⟩ := T₀.bound
  obtain ⟨M₁, hM₁, h₁⟩ := T₁.bound
  exact (kMethodENorm_map_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (mem_kMethod_iff.1 hu))

namespace KMethodSpace

/-- The inclusion into the sum space has norm at most `c_{θ,q}⁻¹`. -/
theorem opNorm_toSum_le :
    ‖(toSum : C.KMethodSpace θ q →L[𝕜] C.SumSpace)‖ ≤ (kMethodConst θ q).toReal⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 ENNReal.toReal_nonneg) _

/-- For `0 < θ < 1`, the inclusion of the intersection has norm at most `c_{θ,q}`. -/
theorem opNorm_ofInter_le (hθ : θ ∈ Ioo 0 1) :
    ‖ofInter (C := C) θ q hθ‖ ≤ (kMethodConst θ q).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-! ### The induced maps -/

section Map

variable (T : C.SumSpace →ₗ[𝕜] D.SumSpace) {T₀ : X₀ →L[𝕜] Y₀} {T₁ : X₁ →L[𝕜] Y₁}
  (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
  (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))
include hT₀ hT₁

private theorem norm_mk_map_toSumₗ_le {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.KMethodSpace θ q) :
    ‖mk (T (toSumₗ u)) (map_mem_kMethod T hT₀ hT₁ (toSumₗ_mem u))‖ ≤
      M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ := by
  rw [norm_mk, norm_def, ← ENNReal.toReal_ofReal (by positivity : 0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ),
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (kMethodENorm_toSumₗ_lt_top u).ne) (kMethodENorm_map_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ _)

/-- The continuous linear map `(X₀, X₁)_{θ,q} → (Y₀, Y₁)_{θ,q}` induced by a linear map `T` of
sum spaces that restricts to continuous linear maps `T₀ : X₀ →L[𝕜] Y₀` and
`T₁ : X₁ →L[𝕜] Y₁`. If `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖` for positive `M₀`, `M₁`, it
multiplies the norm by at most `M₀ ^ (1 - θ) * M₁ ^ θ` (`KMethodSpace.norm_map_le`). -/
def map : C.KMethodSpace θ q →L[𝕜] D.KMethodSpace θ q :=
  LinearMap.mkContinuous
    { toFun u := mk (T (toSumₗ u)) (map_mem_kMethod T hT₀ hT₁ (toSumₗ_mem u))
      map_add' u v := by ext; simp
      map_smul' c u := by ext; simp }
    (T₀.bound.choose ^ (1 - θ) * T₁.bound.choose ^ θ)
    (norm_mk_map_toSumₗ_le T hT₀ hT₁ T₀.bound.choose_spec.1 T₁.bound.choose_spec.1
      T₀.bound.choose_spec.2 T₁.bound.choose_spec.2)

@[simp]
theorem toSumₗ_map (u : C.KMethodSpace θ q) : toSumₗ (map T hT₀ hT₁ u) = T (toSumₗ u) :=
  (rfl)

/-- **Exactness of the real method.** If `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖` for positive
`M₀`, `M₁`, the induced map multiplies the norm by at most `M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem norm_map_le {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (u : C.KMethodSpace θ q) :
    ‖map T hT₀ hT₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ :=
  norm_mk_map_toSumₗ_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁ u

/-- **Exactness of the real method.** If `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖` for positive
`M₀`, `M₁`, the induced map has norm at most `M₀ ^ (1 - θ) * M₁ ^ θ`. -/
theorem opNorm_map_le {M₀ M₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (h₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖)
    (h₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) :
    ‖(map T hT₀ hT₁ : C.KMethodSpace θ q →L[𝕜] D.KMethodSpace θ q)‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_map_le T hT₀ hT₁ hM₀ hM₁ h₀ h₁)

/-- **Exactness of the real method** for contractions: if `T₀` and `T₁` do not increase norms,
neither does the induced map. -/
theorem norm_map_le_of_norm_le (h₀ : ∀ x, ‖T₀ x‖ ≤ ‖x‖) (h₁ : ∀ x, ‖T₁ x‖ ≤ ‖x‖)
    (u : C.KMethodSpace θ q) : ‖map T hT₀ hT₁ u‖ ≤ ‖u‖ := by
  simpa using norm_map_le T hT₀ hT₁ one_pos one_pos (fun x => by simpa using h₀ x)
    (fun x => by simpa using h₁ x) u

end Map

/-- The identity of the couple induces the identity of the real interpolation space. -/
theorem map_id :
    map (θ := θ) (q := q) (LinearMap.id : C.SumSpace →ₗ[𝕜] C.SumSpace)
      (T₀ := ContinuousLinearMap.id 𝕜 X₀) (T₁ := ContinuousLinearMap.id 𝕜 X₁)
      (fun _ => rfl) (fun _ => rfl) = ContinuousLinearMap.id 𝕜 _ := by
  ext u
  rfl

variable {Z₀ Z₁ U : Type*} [NormedAddCommGroup Z₀] [NormedSpace 𝕜 Z₀] [NormedAddCommGroup Z₁]
  [NormedSpace 𝕜 Z₁] [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U] [ContinuousAdd U]
  [T1Space U] {E : CompatibleCouple 𝕜 Z₀ Z₁ U} in
/-- The map induced by a composite of morphisms of couples is the composite of the induced
maps. -/
theorem map_comp (S : D.SumSpace →ₗ[𝕜] E.SumSpace) (T : C.SumSpace →ₗ[𝕜] D.SumSpace)
    {S₀ : Y₀ →L[𝕜] Z₀} {S₁ : Y₁ →L[𝕜] Z₁} {T₀ : X₀ →L[𝕜] Y₀} {T₁ : X₁ →L[𝕜] Y₁}
    (hS₀ : ∀ y, S (D.fstToSum y) = E.fstToSum (S₀ y))
    (hS₁ : ∀ y, S (D.sndToSum y) = E.sndToSum (S₁ y))
    (hT₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (hT₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x)) :
    map (θ := θ) (q := q) (S ∘ₗ T) (T₀ := S₀.comp T₀) (T₁ := S₁.comp T₁)
        (fun x => by simp [hT₀, hS₀]) (fun x => by simp [hT₁, hS₁]) =
      (map S hS₀ hS₁).comp (map T hT₀ hT₁) := by
  ext u
  rfl

end KMethodSpace

/-! ### Retracts and isomorphisms of couples -/

section Retract

variable (I : C.SumSpace →ₗ[𝕜] D.SumSpace) {I₀ : X₀ →L[𝕜] Y₀} {I₁ : X₁ →L[𝕜] Y₁}
  (hI₀ : ∀ x, I (C.fstToSum x) = D.fstToSum (I₀ x))
  (hI₁ : ∀ x, I (C.sndToSum x) = D.sndToSum (I₁ x))
  (P : D.SumSpace →ₗ[𝕜] C.SumSpace) {P₀ : Y₀ →L[𝕜] X₀} {P₁ : Y₁ →L[𝕜] X₁}
  (hP₀ : ∀ y, P (D.fstToSum y) = C.fstToSum (P₀ y))
  (hP₁ : ∀ y, P (D.sndToSum y) = C.sndToSum (P₁ y))

omit [T1Space V] [T1Space W] [Fact (1 ≤ q)] in
include hI₀ hI₁ hP₀ hP₁ in
/-- **Retracts.** If `(X₀, X₁)` is a retract of `(Y₀, Y₁)`, that is, a morphism of couples `P`
is a left inverse of a morphism of couples `I`, then `u` lies in `(X₀, X₁)_{θ,q}` exactly when
`I u` lies in `(Y₀, Y₁)_{θ,q}`. -/
theorem kMethod_eq_comap_of_leftInverse (hPI : Function.LeftInverse P I) :
    C.kMethod θ q = (D.kMethod θ q).comap I := by
  ext u
  refine ⟨map_mem_kMethod I hI₀ hI₁, fun hu => ?_⟩
  rw [← hPI u]
  exact map_mem_kMethod P hP₀ hP₁ hu

omit [T1Space V] [T1Space W] [Fact (1 ≤ q)] in
include hI₀ hI₁ hP₀ hP₁ in
/-- **Retracts.** If a morphism of couples `P` is a left inverse of a morphism of couples `I`,
then `(X₀, X₁)_{θ,q}` is the image of `(Y₀, Y₁)_{θ,q}` under `P`. -/
theorem kMethod_eq_map_of_leftInverse (hPI : Function.LeftInverse P I) :
    C.kMethod θ q = (D.kMethod θ q).map P := by
  ext u
  refine ⟨fun hu => ⟨I u, map_mem_kMethod I hI₀ hI₁ hu, hPI u⟩, ?_⟩
  rintro ⟨v, hv, rfl⟩
  exact map_mem_kMethod P hP₀ hP₁ hv

namespace KMethodSpace

/-- **Retracts.** If a morphism of couples `P` is a left inverse of a morphism of couples `I`,
then the induced map of `P` is a left inverse of the induced map of `I`. -/
theorem leftInverse_map (hPI : Function.LeftInverse P I) :
    Function.LeftInverse (map P hP₀ hP₁ : D.KMethodSpace θ q →L[𝕜] C.KMethodSpace θ q)
      (map I hI₀ hI₁) := fun u => by
  ext
  simp only [toSumₗ_map]
  exact hPI _

include hP₀ hP₁ in
/-- **Retracts.** If a morphism of couples `P` is a left inverse of a morphism of couples `I`, and
`‖P₀ y‖ ≤ N₀ ‖y‖`, `‖P₁ y‖ ≤ N₁ ‖y‖` for positive `N₀`, `N₁`, then
`‖u‖_{θ,q} ≤ N₀ ^ (1 - θ) * N₁ ^ θ * ‖I u‖_{θ,q}`. With `norm_map_le` for `I`, the norm of the
retract `(X₀, X₁)_{θ,q}` is equivalent to the norm of its image in `(Y₀, Y₁)_{θ,q}`. -/
theorem norm_le_mul_norm_map_of_leftInverse (hPI : Function.LeftInverse P I) {N₀ N₁ : ℝ}
    (hN₀ : 0 < N₀) (hN₁ : 0 < N₁) (h₀ : ∀ y, ‖P₀ y‖ ≤ N₀ * ‖y‖) (h₁ : ∀ y, ‖P₁ y‖ ≤ N₁ * ‖y‖)
    (u : C.KMethodSpace θ q) : ‖u‖ ≤ N₀ ^ (1 - θ) * N₁ ^ θ * ‖map I hI₀ hI₁ u‖ := by
  conv_lhs => rw [← leftInverse_map I hI₀ hI₁ P hP₀ hP₁ hPI u]
  exact norm_map_le P hP₀ hP₁ hN₀ hN₁ h₀ h₁ _

end KMethodSpace

end Retract

section Equiv

variable {e : C.SumSpace ≃ₗ[𝕜] D.SumSpace} {e₀ : X₀ ≃L[𝕜] Y₀} {e₁ : X₁ ≃L[𝕜] Y₁}

omit [T1Space V] [T1Space W] [Fact (1 ≤ q)] in
/-- If a linear equivalence of sum spaces restricts to an isomorphism `e₀` of the first
endpoints, its inverse restricts to `e₀.symm`. -/
theorem symm_apply_fstToSum (he₀ : ∀ x, e (C.fstToSum x) = D.fstToSum (e₀ x)) (y : Y₀) :
    e.symm (D.fstToSum y) = C.fstToSum (e₀.symm y) :=
  e.symm_apply_eq.2 (by rw [he₀, ContinuousLinearEquiv.apply_symm_apply])

omit [T1Space V] [T1Space W] [Fact (1 ≤ q)] in
/-- If a linear equivalence of sum spaces restricts to an isomorphism `e₁` of the second
endpoints, its inverse restricts to `e₁.symm`. -/
theorem symm_apply_sndToSum (he₁ : ∀ x, e (C.sndToSum x) = D.sndToSum (e₁ x)) (y : Y₁) :
    e.symm (D.sndToSum y) = C.sndToSum (e₁.symm y) :=
  e.symm_apply_eq.2 (by rw [he₁, ContinuousLinearEquiv.apply_symm_apply])

variable (e)

namespace KMethodSpace

variable (he₀ : ∀ x, e (C.fstToSum x) = D.fstToSum (e₀ x))
  (he₁ : ∀ x, e (C.sndToSum x) = D.sndToSum (e₁ x))

/-- **Invariance under endpoint isomorphisms.** A linear equivalence `e` of sum spaces that
restricts to isomorphisms `e₀ : X₀ ≃L[𝕜] Y₀` and `e₁ : X₁ ≃L[𝕜] Y₁` induces an isomorphism
`(X₀, X₁)_{θ,q} ≃L[𝕜] (Y₀, Y₁)_{θ,q}`, acting as `e` on the sum spaces (`toSumₗ_mapEquiv`). The
norms of the endpoint isomorphisms and of their inverses bound its norm and the norm of its
inverse by `norm_map_le`; if `e₀` and `e₁` preserve norms, so does it (`norm_mapEquiv`). -/
def mapEquiv : C.KMethodSpace θ q ≃L[𝕜] D.KMethodSpace θ q :=
  ContinuousLinearEquiv.equivOfInverse
    (map e.toLinearMap (T₀ := e₀.toContinuousLinearMap) (T₁ := e₁.toContinuousLinearMap) he₀ he₁)
    (map e.symm.toLinearMap (T₀ := e₀.symm.toContinuousLinearMap)
      (T₁ := e₁.symm.toContinuousLinearMap) (symm_apply_fstToSum he₀) (symm_apply_sndToSum he₁))
    (leftInverse_map _ _ _ _ _ _ e.symm_apply_apply)
    (leftInverse_map _ _ _ _ _ _ e.apply_symm_apply)

theorem mapEquiv_apply (u : C.KMethodSpace θ q) :
    mapEquiv e he₀ he₁ u =
      map e.toLinearMap (T₀ := e₀.toContinuousLinearMap) (T₁ := e₁.toContinuousLinearMap)
        he₀ he₁ u :=
  (rfl)

theorem mapEquiv_symm_apply (v : D.KMethodSpace θ q) :
    (mapEquiv e he₀ he₁).symm v =
      map e.symm.toLinearMap (T₀ := e₀.symm.toContinuousLinearMap)
        (T₁ := e₁.symm.toContinuousLinearMap) (symm_apply_fstToSum he₀)
        (symm_apply_sndToSum he₁) v :=
  (rfl)

@[simp]
theorem toSumₗ_mapEquiv (u : C.KMethodSpace θ q) :
    toSumₗ (mapEquiv e he₀ he₁ u) = e (toSumₗ u) :=
  (rfl)

@[simp]
theorem toSumₗ_mapEquiv_symm (v : D.KMethodSpace θ q) :
    toSumₗ ((mapEquiv e he₀ he₁).symm v) = e.symm (toSumₗ v) :=
  (rfl)

/-- If the endpoint isomorphisms `e₀` and `e₁` preserve norms, then so does the induced
isomorphism of real interpolation spaces. -/
theorem norm_mapEquiv (h₀ : ∀ x, ‖e₀ x‖ = ‖x‖) (h₁ : ∀ x, ‖e₁ x‖ = ‖x‖)
    (u : C.KMethodSpace θ q) : ‖mapEquiv e he₀ he₁ u‖ = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · rw [mapEquiv_apply]
    exact norm_map_le_of_norm_le _ he₀ he₁ (fun x => (h₀ x).le) (fun x => (h₁ x).le) u
  · conv_lhs => rw [← (mapEquiv e he₀ he₁).symm_apply_apply u, mapEquiv_symm_apply]
    refine norm_map_le_of_norm_le _ _ _ (fun y => ?_) (fun y => ?_) _
    · rw [ContinuousLinearEquiv.coe_coe, ← h₀ (e₀.symm y), ContinuousLinearEquiv.apply_symm_apply]
    · rw [ContinuousLinearEquiv.coe_coe, ← h₁ (e₁.symm y), ContinuousLinearEquiv.apply_symm_apply]

end KMethodSpace

end Equiv

end CompatibleCouple

end TauCeti
