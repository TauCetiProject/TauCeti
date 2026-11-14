/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.SpanningSets
import TauCeti.MeasureTheory.Order.Lattice
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Norming mixed `L^p_t L^q_x` norms

Let `F : T → L²(X, E)` be a family of square-integrable functions indexed by a σ-finite measure
space `T`, for instance a solution `t ↦ u(t)` of an evolution equation. Its mixed norm

`‖F‖_{L^p_t L^q_x} = ‖t ↦ ‖F t‖_{L^q(X)}‖_{L^p(T)}`

is written `eLpNorm (fun t ↦ eLpNorm (F t) q μ) p ν`. This file proves the duality bound for
mixed norms: if

`|∫ ⟪F t, G t⟫ dt| ≤ C ‖G‖_{L^{p'}_t L^{q'}_x}`

for every bounded `G : T → L²(X, E)` vanishing off a set of finite measure, then
`‖F‖_{L^p_t L^q_x} ≤ C`, for all Hölder conjugate pairs `(p, p')`, `(q, q')`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`).
Bounds proved by duality, such as the Strichartz estimates obtained from the `TT*` argument, come
in this tested form, and this theorem turns them into bounds on the mixed norm itself. The
finiteness of `‖F t‖_q` is not assumed: it follows for almost every `t` when `C < ∞`. The function
`t ↦ ‖F t‖_q` is almost everywhere measurable
(`MeasureTheory.AEStronglyMeasurable.aemeasurable_eLpNorm_Lp`).

## The argument

The difficulty is to choose, measurably in `t`, a test function `G t` that nearly norms `F t` in
`L^q`. Each single `h ∈ L²` is normed by test functions `g ∈ L²` in the unit ball of `L^{q'}`
(`MeasureTheory.Lp.exists_eLpNorm_le_one_and_lt_re_inner`). Almost every `F t` lies in a
separable set `S`, and on `S` countably many test functions suffice
(`TopologicalSpace.IsSeparable.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner`): for each rational
level `c`, the sets `{h | c < re ⟪h, g⟫}` are open and cover `{h ∈ S | c < ‖h‖_q}`, and `S` is
Lindelöf. With such a sequence `gₘ`,

`‖F t‖_q = supₘ re ⟪F t, gₘ⟫`

for almost every `t`. For the bound when `p < ∞`, let `φ_N(t) = max_{m < N} (re ⟪F t, gₘ⟫)⁺`, choose
for each `t` the last index `m < N` attaining the maximum, and test against
`G t = φ_N(t) ^ (p - 1) gₘ` on a set of finite measure where `‖F t‖₂ ≤ N`. Then
`re ⟪F t, G t⟫ = φ_N(t) ^ p` and `‖G t‖_{q'} ≤ φ_N(t) ^ (p - 1)`, so the hypothesis gives
`‖φ_N‖_p ^ p ≤ C ‖φ_N‖_p ^ (p - 1)`, that is `‖φ_N‖_p ≤ C`. Fatou's lemma passes to the limit
`N → ∞`. For `p = ∞`, testing against `G` supported in a set `A` of finite measure and applying
the case `p = 1` to the restriction of `ν` to `A` gives `∫_A ‖F t‖_q ≤ C ν(A)` for every such `A`,
hence `‖F t‖_q ≤ C` for almost every `t`.

## Main declarations

* `MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`: the
  duality bound for mixed norms.

## References

* A. Benedek and R. Panzone, *The space `Lᵖ`, with mixed norm*, Duke Math. J. 28 (1961), 301–324,
  Section 2 (duality of mixed-norm spaces).
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Strichartz estimates by duality).
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

variable {𝕜 X E : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace MeasureTheory.AEStronglyMeasurable

variable {T : Type*} {mT : MeasurableSpace T} {ν : Measure T}

/-- The positive part `t ↦ (re ⟪F t, g⟫)⁺` of the pairing with a fixed `g` is measurable. -/
private theorem measurable_re_inner_toNNReal {F : T → Lp E 2 μ} (hF : StronglyMeasurable F)
    (g : Lp E 2 μ) : Measurable fun t ↦ (RCLike.re ⟪F t, g⟫_𝕜).toNNReal :=
  ((RCLike.continuous_re.comp (continuous_id.inner continuous_const)).comp_stronglyMeasurable
    hF).measurable.real_toNNReal

/-- **The testing step.** If a nonnegative `u ∈ L^p` and a test function `G` satisfy
`re ⟪F t, G t⟫ = u(t) ^ p` and `‖G t‖_{q'} ≤ u(t) ^ (p - 1)`, then the duality bound
`|∫ ⟪F t, G t⟫| ≤ C ‖G‖_{L^{p'}_t L^{q'}_x}` gives `‖u‖_p ≤ C`: the left side is `‖u‖_p ^ p` and
the right side is at most `C ‖u‖_p ^ (p - 1)`. -/
private theorem eLpNorm_le_of_re_inner_eq_rpow {p p' q' : ℝ≥0∞} [hpp : p.HolderConjugate p']
    (hp : p ≠ ∞) {C : ℝ≥0∞} {F G : T → Lp E 2 μ} {u : T → ℝ} (hu : MemLp u p ν)
    (hum : Measurable u) (hu0 : ∀ t, 0 ≤ u t) (hG : AEStronglyMeasurable G ν)
    (hint : Integrable (fun t ↦ ⟪F t, G t⟫_𝕜) ν)
    (hre : ∀ᵐ t ∂ν, RCLike.re ⟪F t, G t⟫_𝕜 = u t ^ p.toReal)
    (hGq : ∀ t, eLpNorm (G t) q' μ ≤ ENNReal.ofReal (u t ^ (p.toReal - 1)))
    (hC : ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν) :
    eLpNorm u p ν ≤ C := by
  have hp0 : p ≠ 0 := hpp.ne_zero
  set X := eLpNorm u p ν
  have hXr : X ^ p.toReal = ENNReal.ofReal (∫ t, u t ^ p.toReal ∂ν) := by
    rw [hu.eLpNorm_rpow_toReal_eq_enorm_integral (𝕜 := ℝ) hp0 hp,
      ← Real.eNorm_eq_ofReal (integral_nonneg fun t ↦ Real.rpow_nonneg (hu0 t) _)]
    congr 2 with t
    rw [Real.norm_of_nonneg (hu0 t), RCLike.ofReal_real_eq_id, id]
  refine ENNReal.le_of_rpow_le_mul_rpow_sub_one (r := p.toReal) hu.eLpNorm_ne_top ?_
  calc X ^ p.toReal = ENNReal.ofReal (∫ t, u t ^ p.toReal ∂ν) := hXr
    _ = ENNReal.ofReal (RCLike.re (∫ t, ⟪F t, G t⟫_𝕜 ∂ν)) := by
        rw [← integral_re hint, integral_congr_ae (hre.mono fun t ht ↦ ht.symm)]
    _ ≤ ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
    _ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν := hC
    _ ≤ C * eLpNorm (fun t ↦ u t ^ (p.toReal - 1)) p' ν := by
        gcongr
        refine eLpNorm_mono_eNorm (hG.aemeasurable_eLpNorm_Lp
          Measure.AbsolutelyContinuous.rfl q').aestronglyMeasurable fun t ↦ ?_
        rw [eNorm_eq_self, Real.eNorm_eq_ofReal (Real.rpow_nonneg (hu0 t) _)]
        exact hGq t
    _ ≤ C * X ^ (p.toReal - 1) := by
        gcongr
        refine TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one (q' := p') hp
          (hum.pow_const _).aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hu0 t) _), Real.norm_of_nonneg (hu0 t)]

/-- **Testing against a chosen index.** Let `gₘ` be test functions in the unit ball of `L^{q'}`
and let `s` be a measurable set of finite measure on which `‖F t‖₂ ≤ R`. Let `φ ≥ 0` and an index
`ψ` be measurable, with `φ ≤ M` on `s`, `‖g_{ψ(t)}‖₂ ≤ K`, and `re ⟪F t, g_{ψ(t)}⟫ = φ(t)` wherever
`φ(t) ≠ 0`. Testing against `G t = φ(t) ^ (p - 1) g_{ψ(t)}` on `s ∩ {φ ≠ 0}` bounds `‖1_s φ‖_p`
by `C`. -/
private theorem eLpNorm_indicator_le_of_re_inner_eq {p p' q' : ℝ≥0∞}
    [hpp : p.HolderConjugate p'] (hp : p ≠ ∞) {F : T → Lp E 2 μ} (hF : StronglyMeasurable F)
    {g : ℕ → Lp E 2 μ} (hg1 : ∀ m, eLpNorm (g m) q' μ ≤ 1) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν)
    {s : Set T} (hs : MeasurableSet s) (hsν : ν s ≠ ∞) {R M K : ℝ≥0} (hR : ∀ t ∈ s, ‖F t‖ ≤ R)
    {φ : T → ℝ≥0} (hφm : Measurable φ) (hφM : ∀ t ∈ s, φ t ≤ M) {ψ : T → ℕ}
    (hψm : Measurable ψ) (hgK : ∀ t, ‖g (ψ t)‖ ≤ K)
    (hψ : ∀ t, φ t ≠ 0 → RCLike.re ⟪F t, g (ψ t)⟫_𝕜 = φ t) :
    eLpNorm (s.indicator fun t ↦ (φ t : ℝ)) p ν ≤ C := by
  set r := p.toReal
  have hr1 : 1 ≤ r := by simpa using ENNReal.toReal_mono hp hpp.one_le
  have hr0 : r ≠ 0 := by positivity
  -- Test on the part `D` of `s` where `φ` is positive, so that `ψ` attains `φ` there.
  set D : Set T := s ∩ {t | φ t ≠ 0}
  have hDm : MeasurableSet D := hs.inter (hφm (measurableSet_singleton 0)).compl
  set u : T → ℝ := D.indicator fun t ↦ (φ t : ℝ)
  have hsu : s.indicator (fun t ↦ (φ t : ℝ)) = u := by
    ext t
    by_cases hs : t ∈ s <;> by_cases h0 : φ t = 0 <;> simp [u, D, Set.indicator, hs, h0]
  rw [hsu]
  set G : T → Lp E 2 μ := D.indicator fun t ↦ (((φ t : ℝ) ^ (r - 1) : ℝ) : 𝕜) • g (ψ t)
  have hu_mem : ∀ t ∈ D, u t = φ t := fun t ht ↦ Set.indicator_of_mem ht _
  have hu_notMem : ∀ t, t ∉ D → u t = 0 := fun t ht ↦ Set.indicator_of_notMem ht _
  have hu_nonneg : ∀ t, 0 ≤ u t := Set.indicator_nonneg fun t _ ↦ NNReal.coe_nonneg _
  have hu_le : ∀ t, u t ≤ M := fun t ↦ by
    by_cases ht : t ∈ D
    · rw [hu_mem t ht]
      exact_mod_cast hφM t ht.1
    · rw [hu_notMem t ht]
      exact M.coe_nonneg
  have hum : Measurable u := (NNReal.continuous_coe.measurable.comp hφm).indicator hDm
  -- The test function `G` and its properties.
  have hG_eq : ∀ t ∈ D, G t = (((φ t : ℝ) ^ (r - 1) : ℝ) : 𝕜) • g (ψ t) := fun t ht ↦
    Set.indicator_of_mem ht _
  have hG_zero : ∀ t, t ∉ D → G t = 0 := fun t ht ↦ Set.indicator_of_notMem ht _
  have hGm : StronglyMeasurable G := by
    have h₁ : StronglyMeasurable fun t ↦ (((φ t : ℝ) ^ (r - 1) : ℝ) : 𝕜) :=
      RCLike.continuous_ofReal.comp_stronglyMeasurable
        ((NNReal.continuous_coe.measurable.comp hφm).pow_const _).stronglyMeasurable
    have h₂ : StronglyMeasurable fun t ↦ g (ψ t) :=
      StronglyMeasurable.of_discrete.comp_measurable hψm
    exact (h₁.smul h₂).indicator hDm
  have hG_re : ∀ t, RCLike.re ⟪F t, G t⟫_𝕜 = u t ^ r := fun t ↦ by
    by_cases ht : t ∈ D
    · have hpos : 0 < (φ t : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht.2)
      rw [hG_eq t ht, inner_smul_right, RCLike.re_ofReal_mul, hψ t ht.2, hu_mem t ht,
        Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']
    · rw [hG_zero t ht, inner_zero_right, map_zero, hu_notMem t ht, Real.zero_rpow hr0]
  have hG_norm : ∀ t, ‖G t‖ ≤ (M : ℝ) ^ (r - 1) * K := fun t ↦ by
    by_cases ht : t ∈ D
    · rw [hG_eq t ht, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      refine mul_le_mul ?_ (hgK t) (norm_nonneg _) (Real.rpow_nonneg M.coe_nonneg _)
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (hu_mem t ht ▸ hu_le t) (by linarith)
    · rw [hG_zero t ht, norm_zero]
      positivity
  have hG_eLpNorm : ∀ t, eLpNorm (G t) q' μ ≤ ENNReal.ofReal (u t ^ (r - 1)) := fun t ↦ by
    by_cases ht : t ∈ D
    · rw [hG_eq t ht, eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, hu_mem t ht,
        ← ofReal_norm, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      exact mul_le_of_le_one_right' (hg1 _)
    · rw [hG_zero t ht, Lp.eLpNorm_coeFn_zero]
      exact zero_le
  have hGs : ∀ t, t ∉ s → G t = 0 := fun t ht ↦ hG_zero t fun h ↦ ht h.1
  have hint : Integrable (fun t ↦ ⟪F t, G t⟫_𝕜) ν := by
    refine memLp_one_iff_integrable.1 ((memLp_top_of_bound (hF.inner hGm).aestronglyMeasurable
      (R * ((M : ℝ) ^ (r - 1) * K)) (ae_of_all _ fun t ↦ ?_))
      |>.mono_exponent_of_measure_support_ne_top
        (fun t ht ↦ by rw [hGs t ht, inner_zero_right]) hsν le_top)
    by_cases ht : t ∈ s
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hR t ht) (hG_norm t) (norm_nonneg _) R.coe_nonneg)
    · rw [hGs t ht, inner_zero_right, norm_zero]
      positivity
  -- Testing against `G` bounds the `L^p` norm of `u = 1_D φ` by `C`.
  have huLp : MemLp u p ν := (memLp_top_of_bound hum.aestronglyMeasurable M
    (ae_of_all _ fun t ↦ by rw [Real.norm_of_nonneg (hu_nonneg t)]; exact hu_le t)
    ).mono_exponent_of_measure_support_ne_top (fun t ht ↦ hu_notMem t fun h ↦ ht h.1) hsν le_top
  exact eLpNorm_le_of_re_inner_eq_rpow (p' := p') (q' := q') hp huLp hum hu_nonneg
    hGm.aestronglyMeasurable hint (ae_of_all _ hG_re) hG_eLpNorm
    (hC G s hsν hGs (memLp_top_of_bound hGm.aestronglyMeasurable _ (ae_of_all _ hG_norm)))

/-- **The truncated testing step.** Let `gₘ` be test functions in the unit ball of `L^{q'}`, let
`φ_N(t) = max_{m < N} (re ⟪F t, gₘ⟫)⁺`, and let `s` be a measurable set of finite measure on which
`‖F t‖₂ ≤ R`. Testing against `G t = φ_N(t) ^ (p - 1) gₘ`, where `m < N` is the last index
attaining the maximum, bounds `‖1_s φ_N‖_p` by `C`. -/
private theorem eLpNorm_indicator_finsetSup_le {p p' q' : ℝ≥0∞} [hpp : p.HolderConjugate p']
    (hp : p ≠ ∞) {F : T → Lp E 2 μ} (hF : StronglyMeasurable F) {g : ℕ → Lp E 2 μ}
    (hg1 : ∀ m, eLpNorm (g m) q' μ ≤ 1) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν)
    (N : ℕ) {s : Set T} (hs : MeasurableSet s) (hsν : ν s ≠ ∞) {R : ℝ≥0}
    (hR : ∀ t ∈ s, ‖F t‖ ≤ R) :
    eLpNorm (s.indicator fun t ↦
      (((Finset.range N).sup fun m ↦ (RCLike.re ⟪F t, g m⟫_𝕜).toNNReal : ℝ≥0) : ℝ)) p ν ≤ C := by
  have hf : ∀ m, Measurable fun t ↦ (RCLike.re ⟪F t, g m⟫_𝕜).toNNReal := fun m ↦
    measurable_re_inner_toNNReal hF (g m)
  obtain ⟨ψ, hψm, hψN, hψ⟩ := TauCeti.exists_measurable_finsetSup_eq hf N
  set K : ℝ≥0 := ∑ m ∈ Finset.range (N + 1), ‖g m‖₊
  have hgK : ∀ m ≤ N, ‖g m‖ ≤ K := fun m hm ↦ by
    rw [← coe_nnNorm]
    exact NNReal.coe_le_coe.2 (Finset.single_le_sum (f := fun m ↦ ‖g m‖₊) (fun m _ ↦ zero_le)
      (Finset.mem_range_succ_iff.2 hm))
  refine eLpNorm_indicator_le_of_re_inner_eq hp hF hg1 hC hs hsν hR
    (TauCeti.measurable_finsetSup _ fun m _ ↦ hf m) (M := R * K) (fun t ht ↦ ?_) hψm
    (fun t ↦ hgK _ (hψN t)) fun t ht ↦ ?_
  · refine Finset.sup_le fun m hm ↦ Real.toNNReal_le_iff_le_coe.2 ?_
    push_cast
    exact (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (mul_le_mul (hR t ht)
      (hgK m (Finset.mem_range.1 hm).le) (norm_nonneg _) R.coe_nonneg))
  · have h0 : 0 < (RCLike.re ⟪F t, g (ψ t)⟫_𝕜).toNNReal := by
      rw [hψ t ht]
      exact pos_iff_ne_zero.2 ht
    rw [← hψ t ht, Real.coe_toNNReal _ (Real.toNNReal_pos.1 h0).le]

/-- The case `p < ∞` of `eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`. -/
private theorem eLpNorm_eLpNorm_le_of_ne_top [SigmaFinite μ] [SigmaFinite ν]
    {p p' q q' : ℝ≥0∞} [hpp : p.HolderConjugate p'] [hqq : q.HolderConjugate q'] (hp : p ≠ ∞)
    {F : T → Lp E 2 μ} (hF : AEStronglyMeasurable F ν) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν) :
    eLpNorm (fun t ↦ eLpNorm (F t) q μ) p ν ≤ C := by
  -- Structure: norm almost every `F t` by a countable sequence `gₘ`; for each `N` the truncated
  -- testing step bounds `‖1_{s_N} φ_N‖_p` by `C`, where `φ_N` is the running maximum of the first
  -- `N` pairings; Fatou's lemma passes to the limit, since `φ_N(t)` increases to `‖F t‖_q`.
  obtain ⟨S, hS, hFS⟩ := hF.isSeparable_ae_range
  obtain ⟨g, hg1, hgS⟩ :=
    hS.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner (𝕜 := 𝕜) (q := q) (q' := q')
  set F' := hF.mk F
  have hF' : StronglyMeasurable F' := hF.stronglyMeasurable_mk
  have hFF' : F =ᵐ[ν] F' := hF.ae_eq_mk
  have hC' : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F' t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν :=
    fun G s hs hGs hG ↦ by
      have hFG : (fun t ↦ ⟪F t, G t⟫_𝕜) =ᵐ[ν] fun t ↦ ⟪F' t, G t⟫_𝕜 :=
        hFF'.mono fun t ht ↦ by simp only [ht]
      rw [← integral_congr_ae hFG]
      exact hC G s hs hGs hG
  -- The running maxima `φ_N`, truncated to sets `s_N` of finite measure where `‖F t‖₂ ≤ N`.
  set φ : ℕ → T → ℝ≥0 := fun N t ↦
    (Finset.range N).sup fun m ↦ (RCLike.re ⟪F' t, g m⟫_𝕜).toNNReal
  set s : ℕ → Set T := fun N ↦ spanningSets ν N ∩ {t | ‖F' t‖ ≤ N}
  have hsm : ∀ N, MeasurableSet (s N) := measurableSet_spanningSets_inter_norm_le hF'
  set u : ℕ → T → ℝ := fun N ↦ (s N).indicator fun t ↦ (φ N t : ℝ)
  have hum : ∀ N, Measurable (u N) := fun N ↦
    (NNReal.continuous_coe.measurable.comp (TauCeti.measurable_finsetSup _
      fun m _ ↦ measurable_re_inner_toNNReal hF' (g m))).indicator (hsm N)
  have hX : ∀ N, eLpNorm (u N) p ν ≤ C := fun N ↦
    eLpNorm_indicator_finsetSup_le hp hF' hg1 hC' N (hsm N)
      (measure_mono_top Set.inter_subset_left |>.mt (measure_spanningSets_lt_top ν N).ne)
      (R := N) fun t ht ↦ by exact_mod_cast ht.2
  -- Passage to the limit `N → ∞`: `u_N(t)` increases to `‖F t‖_q` for almost every `t`.
  have hΦ : ∀ᵐ t ∂ν, Tendsto (fun N ↦ ‖u N t‖ₑ) atTop (𝓝 (eLpNorm (F t) q μ)) := by
    filter_upwards [hFS, hFF'] with t htS ht
    rw [ht, hgS _ (ht ▸ htS)]
    have hiSup : ⨆ N, (φ N t : ℝ≥0∞) = ⨆ m, ENNReal.ofReal (RCLike.re ⟪F' t, g m⟫_𝕜) := by
      refine le_antisymm (iSup_le fun N ↦ ?_) (iSup_le fun m ↦ le_iSup_of_le (m + 1) ?_)
      · rw [ENNReal.coe_finset_sup]
        exact Finset.sup_le fun m _ ↦ le_iSup (fun m ↦ ENNReal.ofReal (RCLike.re ⟪F' t, g m⟫_𝕜)) m
      · exact ENNReal.coe_le_coe.2 (Finset.le_sup (f := fun m ↦ (RCLike.re ⟪F' t, g m⟫_𝕜).toNNReal)
          (Finset.self_mem_range_succ m))
    have hev : ∀ᶠ N in atTop, (φ N t : ℝ≥0∞) = ‖u N t‖ₑ := by
      filter_upwards [eventually_mem_spanningSets ν t,
        tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖F' t‖] with N ht₁ ht₂
      rw [show u N t = φ N t from Set.indicator_of_mem (⟨ht₁, ht₂⟩ : t ∈ s N) _,
        Real.eNorm_eq_ofReal (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [← hiSup]
    exact (tendsto_atTop_iSup fun N M hNM ↦ ENNReal.coe_le_coe.2
      (Finset.sup_mono (Finset.range_mono hNM))).congr' hev
  exact TauCeti.eLpNorm_ennreal_le_of_ae_tendsto (fun N ↦ (hum N).eNorm.aemeasurable) hΦ
    (Frequently.of_forall fun N ↦ (eLpNorm_eNorm _ (hum N).aestronglyMeasurable).trans_le (hX N))

/-- The case `p = ∞` of `eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`. For a set `A` of
finite measure, testing against `1_A G` and applying the case `p = 1` to the restriction of `ν` to
`A` gives `∫_A ‖F t‖_q ≤ C ν(A)`. As `A` is arbitrary, `‖F t‖_q ≤ C` for almost every `t`. -/
private theorem eLpNorm_eLpNorm_top_le [SigmaFinite μ] [SigmaFinite ν] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] {F : T → Lp E 2 μ} (hF : AEStronglyMeasurable F ν) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) 1 ν) :
    eLpNorm (fun t ↦ eLpNorm (F t) q μ) ∞ ν ≤ C := by
  have hFq : AEMeasurable (fun t ↦ eLpNorm (F t) q μ) ν :=
    hF.aemeasurable_eLpNorm_Lp Measure.AbsolutelyContinuous.rfl q
  rw [eLpNorm_exponent_top hFq.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
  refine (ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ (g := fun _ ↦ C) hFq
    fun A hA hAν ↦ ?_).mono fun t ht ↦ (eNorm_eq_self _).trans_le ht
  have h1 := eLpNorm_eLpNorm_le_of_ne_top (𝕜 := 𝕜) (p := 1) (p' := ∞) (q := q) (q' := q')
    ENNReal.one_ne_top (hF.restrict (s := A)) (C := C * ν A) fun G _ _ _ hG ↦ ?_
  · rw [eLpNorm_one_eq_lintegral_eNorm (hFq.restrict (s := A)).aestronglyMeasurable] at h1
    simpa only [eNorm_eq_self, setLIntegral_const] using h1
  -- Test against `1_A G`, which vanishes off `A`.
  have hGA := hC (A.indicator G) A hAν.ne (fun t ht ↦ Set.indicator_of_notMem ht _)
    ((memLp_indicator_iff_restrict hA.nullMeasurableSet).2 hG)
  have hint : ∫ t, ⟪F t, A.indicator G t⟫_𝕜 ∂ν = ∫ t in A, ⟪F t, G t⟫_𝕜 ∂ν := by
    rw [← integral_indicator hA]
    congr 1 with t
    by_cases ht : t ∈ A <;> simp [ht]
  have hnorm : (fun t ↦ eLpNorm (A.indicator G t : Lp E 2 μ) q' μ) =
      A.indicator fun t ↦ eLpNorm (G t) q' μ := by
    ext t
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht]
      exact Lp.eLpNorm_coeFn_zero
  rw [hint, hnorm, eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet] at hGA
  refine hGA.trans ?_
  rw [mul_assoc]
  gcongr
  calc eLpNorm (fun t ↦ eLpNorm (G t) q' μ) 1 (ν.restrict A)
      ≤ eLpNorm (fun t ↦ eLpNorm (G t) q' μ) ∞ (ν.restrict A) *
          ν.restrict A Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (∞ : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ le_top (hG.aestronglyMeasurable
          |>.aemeasurable_eLpNorm_Lp Measure.AbsolutelyContinuous.rfl q').aestronglyMeasurable
    _ = ν A * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) ∞ (ν.restrict A) := by
        simp [mul_comm]

/-- **Duality for mixed norms.** On σ-finite measure spaces `T` and `X`, let `(p, p')` and
`(q, q')` be Hölder conjugate pairs, and let `F : T → L²(X, E)` be almost everywhere strongly
measurable. If

`|∫ ⟪F t, G t⟫ dt| ≤ C ‖G‖_{L^{p'}_t L^{q'}_x}`

for every bounded `G : T → L²(X, E)` vanishing off a set of finite measure, then

`‖F‖_{L^p_t L^q_x} = ‖t ↦ ‖F t‖_{L^q(X)}‖_{L^p(T)} ≤ C`.

In particular `F t ∈ L^q` for almost every `t` as soon as `C < ∞`. -/
theorem eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le [SigmaFinite μ] [SigmaFinite ν]
    {p p' q q' : ℝ≥0∞} [hpp : p.HolderConjugate p'] [hqq : q.HolderConjugate q']
    {F : T → Lp E 2 μ} (hF : AEStronglyMeasurable F ν) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν) :
    eLpNorm (fun t ↦ eLpNorm (F t) q μ) p ν ≤ C := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl : p' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p').1 rfl
    exact eLpNorm_eLpNorm_top_le hF hC
  · exact eLpNorm_eLpNorm_le_of_ne_top hp hF hC

end MeasureTheory.AEStronglyMeasurable
