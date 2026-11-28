/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Ehrling
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# The Aubin–Lions compactness theorem

Let `X₀` be a normed space and `X`, `X₁` Banach spaces, with a compact operator `i : X₀ → X` and
an injective continuous linear map `j : X → X₁`. The **Aubin–Lions theorem** says that a sequence
`uₙ` of functions of time, bounded in `Lᵖ(a, b; X₀)`, whose images `j ∘ i ∘ uₙ` have weak time
derivatives bounded in `Lʳ(a, b; X₁)` for some `r > 1`, has a subsequence along which `i ∘ uₙ`
converges in `Lᵖ(a, b; X)`.

This is the compactness step of the existence theory for nonlinear evolution equations, such as
the construction of Leray–Hopf weak solutions of the Navier–Stokes equations. There `X₀` is a
Sobolev space on a bounded set, `X` the corresponding `L²` space and `X₁` a negative Sobolev
space: energy estimates bound the approximate solutions in `L²(0, T; H¹)` and their time
derivatives in a weak norm, and the theorem upgrades the resulting weak convergence to strong
`L²` convergence, which is what lets nonlinear terms pass to the limit.

No reflexivity is assumed, as in Simon's version of the theorem. The exponent `p` is arbitrary in
`[1, ∞]`, `r` is any exponent in `(1, ∞]`, and `X₀` need only be a normed space, not a Banach
space.

## Proof

Let `vₙ` be the continuous representative of `j ∘ i ∘ uₙ` on `[a, b]`. By
`TauCeti.HasWeakLineDerivOn.norm_sub_le_rpow_mul_eLpNorm` the `vₙ` are uniformly Hölder continuous
with exponent `1 - 1 / r > 0`. Their values are also uniformly close to a compact set: on a
subinterval of length `h` containing `t`, the first moment method gives a time `s` with
`vₙ s = j (i (uₙ s))` and `‖uₙ s‖ ≤ h⁻¹ ‖uₙ‖_{L¹(a, b)}`, so `vₙ t` lies within `O(h ^ (1 - 1 / r))`
of the image under `j ∘ i` of a ball of `X₀`, which is relatively compact. By the Arzelà–Ascoli
theorem (`TauCeti.exists_subseq_uniformCauchySeqOn_of_continuity_modulus`) a subsequence of `vₙ`
converges uniformly on `[a, b]`. Ehrling's inequality
`‖i x‖ ≤ ε ‖x‖ + C_ε ‖j (i x)‖`, integrated in time
(`IsCompactOperator.exists_eLpNorm_le_mul_eLpNorm_add_mul_eLpNorm`), then shows that this
subsequence of `i ∘ uₙ` is Cauchy in `Lᵖ(a, b; X)`.

## Main declarations

* `IsCompactOperator.exists_subseq_tendsto_eLpNorm_of_hasWeakLineDerivOn`: the Aubin–Lions
  theorem.

## References

* J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non linéaires*,
  Dunod, 1969, Chapitre 1, Théorème 5.1.
* J. Simon, *Compact sets in the space `Lᵖ(0, T; B)`*, Ann. Mat. Pura Appl. **146** (1987),
  65–96, Corollary 4.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Interval BoundedContinuousFunction

variable {X₀ X X₁ : Type*} [NormedAddCommGroup X₀] [NormedSpace ℝ X₀]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]

namespace TauCeti

/-- The value at `t` of the continuous representative `v` of `j ∘ i ∘ u` is within
`h ^ α * K` of `j (i x)` for some `x` with `‖x‖ ≤ h⁻¹ ‖u‖_{L¹(a, b)}`, provided `v` has the
modulus of continuity `d ↦ d ^ α * K` on `Icc a b` and `0 < h ≤ b - a`. -/
private theorem exists_norm_le_and_norm_sub_le {i : X₀ →L[ℝ] X} {j : X →L[ℝ] X₁} {a b α K h : ℝ}
    (hα : 0 < α) (hK : 0 ≤ K) (hh : 0 < h) (hhb : h ≤ b - a) {u : ℝ → X₀} {v : ℝ → X₁}
    (hu : IntegrableOn (fun t ↦ ‖u t‖) (Ioo a b))
    (hae : (fun t ↦ j (i (u t))) =ᵐ[volume.restrict (Ioo a b)] v)
    (hmod : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖v t - v s‖ ≤ |t - s| ^ α * K)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ x : X₀, ‖x‖ ≤ (∫ s in Ioo a b, ‖u s‖) / h ∧ ‖v t - j (i x)‖ ≤ h ^ α * K := by
  -- A subinterval `Ioo c (c + h)` of `Ioo a b` whose closure contains `t`.
  set c := min t (b - h)
  have hcI : Ioo c (c + h) ⊆ Ioo a b :=
    Ioo_subset_Ioo (le_min ht.1 (by linarith)) (by linarith [min_le_right t (b - h)])
  have htc : t ∈ Icc c (c + h) := ⟨min_le_left _ _, by
    rw [← min_add_add_right]; exact le_min (by linarith) (by linarith [ht.2])⟩
  set ν := volume.restrict (Ioo c (c + h))
  have hν : ν univ = ENNReal.ofReal h := by simp [ν]
  have hν0 : ν ≠ 0 := fun h0 ↦ by simp [h0] at hν; linarith
  have : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  -- The first moment method gives a good time `s` in the subinterval.
  have hgood : ∀ᵐ s ∂ν, s ∈ Ioo c (c + h) ∧ j (i (u s)) = v s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hcI hae] with s hs hs' using ⟨hs, hs'⟩
  obtain ⟨s, hsN, hs⟩ := exists_notMem_null_le_average hν0 (hu.mono_set hcI) (ae_iff.1 hgood)
  simp only [mem_ofPred_eq, not_not] at hsN
  refine ⟨u s, hs.trans ?_, ?_⟩
  · rw [average_eq, smul_eq_mul, measureReal_def, hν, ENNReal.toReal_ofReal hh.le, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (setIntegral_mono_set hu
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall hcI)) hh.le
  · have hs' : s ∈ Icc a b := Ioo_subset_Icc_self (hcI hsN.1)
    rw [hsN.2]
    refine (hmod s hs' t ht).trans (mul_le_mul_of_nonneg_right ?_ hK)
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hα.le
    rw [abs_le]
    constructor <;> linarith [hsN.1.1, hsN.1.2, htc.1, htc.2]

end TauCeti

namespace IsCompactOperator

/-- The uniform part of the Aubin–Lions theorem: under its hypotheses, the continuous
representatives `v n` of `j ∘ i ∘ u n` have a subsequence converging uniformly on `Icc a b`. -/
private theorem exists_subseq_uniformCauchySeqOn_of_hasWeakLineDerivOn [CompleteSpace X₁]
    {i : X₀ →L[ℝ] X} (hi : IsCompactOperator i) {j : X →L[ℝ] X₁} {r : ℝ≥0∞} (hr : 1 < r)
    {a b : ℝ} (hab : a < b) {C₁ : ℝ} {M' : ℝ≥0} {u : ℕ → ℝ → X₀} {u' v : ℕ → ℝ → X₁}
    (hu : ∀ n, IntegrableOn (fun t ↦ ‖u n t‖) (Ioo a b))
    (huC : ∀ n, ∫ t in Ioo a b, ‖u n t‖ ≤ C₁)
    (hderiv : ∀ n, TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ j (i (u n t))) (u' n) 1)
    (hu' : ∀ n, MemLp (u' n) r (volume.restrict (Ioo a b)))
    (hu'M : ∀ n, eLpNorm (u' n) r (volume.restrict (Ioo a b)) ≤ M')
    (hv : ∀ n, ContinuousOn (v n) (Icc a b))
    (hae : ∀ n, (fun t ↦ j (i (u n t))) =ᵐ[volume.restrict (Ioo a b)] v n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ UniformCauchySeqOn (fun n ↦ v (φ n)) atTop (Icc a b) := by
  set α := 1 - 1 / r.toReal
  have hα : 0 < α := by
    rcases eq_or_ne r ∞ with rfl | hrt
    · simp [α]
    · have h1 : 1 < r.toReal := by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hrt).2 hr
      exact sub_pos.2 ((div_lt_one (by linarith)).2 h1)
  -- The Hölder bound with the uniform constant `M'`.
  have hmod : ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖v n t - v n s‖ ≤ |t - s| ^ α * M' :=
    fun n s hs t ht ↦ ((hderiv n).norm_sub_le_rpow_mul_eLpNorm hr.le (hu' n) (hv n) (hae n) hs
      ht).trans (mul_le_mul_of_nonneg_left
        (ENNReal.toReal_le_of_le_ofReal M'.coe_nonneg (by simpa using hu'M n))
        (Real.rpow_nonneg (abs_nonneg _) _))
  have hlim : Tendsto (fun h : ℝ ↦ h ^ α * M') (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using
      (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.mul_const (M' : ℝ)
  refine TauCeti.exists_subseq_uniformCauchySeqOn_of_continuity_modulus isCompact_Icc hlim
    (fun n s hs t ht ↦ by rw [dist_eq_norm, Real.dist_eq]; exact hmod n t ht s hs)
    fun δ hδ ↦ ?_
  -- A subinterval length `h` with `h ^ α * M' ≤ δ`.
  obtain ⟨h, hhδ, hh0, hhb⟩ :=
    (((hlim.mono_left nhdsWithin_le_nhds).eventually (ge_mem_nhds hδ)).and
      (Ioo_mem_nhdsGT (sub_pos.2 hab))).exists
  -- The values are within `δ` of the image of a ball of `X₀`, which `j ∘ i` maps into a compact.
  obtain ⟨S, hS, hSsub⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := (i : X₀ →ₗ[ℝ] X)) hi (C₁ / h)
  refine ⟨j '' S, hS.image j.continuous, fun n t ht ↦ ?_⟩
  obtain ⟨x, hx, hxv⟩ :=
    TauCeti.exists_norm_le_and_norm_sub_le hα M'.coe_nonneg hh0 hhb.le (hu n) (hae n) (hmod n) ht
  exact ⟨j (i x), mem_image_of_mem j (hSsub (mem_image_of_mem i (mem_closedBall_zero_iff.2
    (hx.trans (div_le_div_of_nonneg_right (huC n) hh0.le))))), by
      rw [dist_eq_norm]; exact hxv.trans hhδ⟩

/-- In the setting of the Aubin–Lions theorem, a sequence `i ∘ u n` is Cauchy in `Lᵖ(a, b; X)` if
`u n` is bounded in `Lᵖ(a, b; X₀)` and the continuous representatives `v n` of `j ∘ i ∘ u n` are
uniformly Cauchy on `Icc a b`. -/
private theorem cauchySeq_toLp_of_uniformCauchySeqOn {i : X₀ →L[ℝ] X} (hi : IsCompactOperator i)
    {j : X →L[ℝ] X₁} (hj : Function.Injective j) {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ} {M : ℝ≥0}
    {u : ℕ → ℝ → X₀} {v : ℕ → ℝ → X₁} (hu : ∀ n, MemLp (u n) p (volume.restrict (Ioo a b)))
    (huM : ∀ n, eLpNorm (u n) p (volume.restrict (Ioo a b)) ≤ M)
    (hae : ∀ n, (fun t ↦ j (i (u n t))) =ᵐ[volume.restrict (Ioo a b)] v n)
    (hunif : UniformCauchySeqOn v atTop (Icc a b)) :
    CauchySeq fun n ↦ (i.comp_memLp' (hu n)).toLp := by
  set μ := volume.restrict (Ioo a b)
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε hε ↦ ?_
  obtain ⟨C, hC, hE⟩ := hi.exists_eLpNorm_le_mul_eLpNorm_add_mul_eLpNorm (μ := μ) hj
    (ε := (ε : ℝ) / (4 * ((M : ℝ) + 1))) (by positivity)
  set L := (μ univ ^ p.toReal⁻¹).toReal
  have hL : μ univ ^ p.toReal⁻¹ = ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp [μ]))).symm
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hunif (ε / (4 * (C * L + 1))) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Lp.edist_toLp_toLp]
  have hsub : AEStronglyMeasurable (u n - u N) μ :=
    (hu n).aestronglyMeasurable.sub (hu N).aestronglyMeasurable
  have h1 : eLpNorm (u n - u N) p μ ≤ ENNReal.ofReal (2 * M) := by
    rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, two_mul, ENNReal.ofReal_coe_nnreal]
    exact (eLpNorm_sub_le Fact.out).trans (add_le_add (huM n) (huM N))
  have h2 : eLpNorm (fun t ↦ j (i ((u n - u N) t))) p μ ≤
      ENNReal.ofReal L * ENNReal.ofReal (ε / (4 * (C * L + 1))) := by
    rw [← hL]
    refine eLpNorm_le_of_ae_bound ((j.comp i).continuous.comp_aestronglyMeasurable hsub) ?_
    filter_upwards [hae n, hae N, ae_restrict_mem measurableSet_Ioo] with t hn' hN' ht
    simp only [Pi.sub_apply, map_sub, hn', hN']
    rw [← dist_eq_norm]
    exact (hN n hn N le_rfl t (Ioo_subset_Icc_self ht)).le
  have hreal : (ε : ℝ) / (4 * ((M : ℝ) + 1)) * (2 * M) +
      C * (L * (ε / (4 * (C * L + 1)))) < ε := by
    have e1 : (ε : ℝ) / (4 * ((M : ℝ) + 1)) * (2 * M) ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [M.coe_nonneg, NNReal.coe_pos.2 hε]
    have e2 : C * (L * ((ε : ℝ) / (4 * (C * L + 1)))) ≤ ε / 4 := by
      rw [← mul_assoc, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hC (ENNReal.toReal_nonneg : 0 ≤ L), NNReal.coe_pos.2 hε]
    linarith [NNReal.coe_pos.2 hε]
  calc eLpNorm ((fun t ↦ i (u n t)) - fun t ↦ i (u N t)) p μ
      = eLpNorm (fun t ↦ i ((u n - u N) t)) p μ := by congr 1; ext; simp
    _ ≤ _ := hE Fact.out _
    _ ≤ ENNReal.ofReal ((ε : ℝ) / (4 * ((M : ℝ) + 1))) * ENNReal.ofReal (2 * M) +
        ENNReal.ofReal C * (ENNReal.ofReal L * ENNReal.ofReal (ε / (4 * (C * L + 1)))) := by
      gcongr
    _ < ε := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top]
      simpa using hreal

/-- **The Aubin–Lions theorem.** Let `i : X₀ → X` be a compact operator and `j : X → X₁` an
injective continuous linear map, where `X₀` is a normed space and `X`, `X₁` are Banach spaces,
and let `1 ≤ p ≤ ∞` and `1 < r ≤ ∞`. Let `u n` be bounded in `Lᵖ(a, b; X₀)`, and let
`j ∘ i ∘ u n` have weak derivatives `u' n` on `(a, b)` bounded in `Lʳ(a, b; X₁)`. Then a
subsequence of `i ∘ u n` converges in `Lᵖ(a, b; X)`.
No reflexivity is assumed, as in Simon's version of the theorem. -/
theorem exists_subseq_tendsto_eLpNorm_of_hasWeakLineDerivOn [CompleteSpace X] [CompleteSpace X₁]
    {i : X₀ →L[ℝ] X} (hi : IsCompactOperator i) {j : X →L[ℝ] X₁} (hj : Function.Injective j)
    {p r : ℝ≥0∞} (hp : 1 ≤ p) (hr : 1 < r) {a b : ℝ} {M M' : ℝ≥0} {u : ℕ → ℝ → X₀}
    {u' : ℕ → ℝ → X₁} (huM : ∀ n, eLpNorm (u n) p (volume.restrict (Ioo a b)) ≤ M)
    (hderiv : ∀ n, TauCeti.HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ j (i (u n t))) (u' n) 1)
    (hu'M : ∀ n, eLpNorm (u' n) r (volume.restrict (Ioo a b)) ≤ M') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → X, MemLp g p (volume.restrict (Ioo a b)) ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦ i (u (φ n) t) - g t) p (volume.restrict (Ioo a b)))
        atTop (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have hu n : MemLp (u n) p (volume.restrict (Ioo a b)) := (huM n).trans_lt ENNReal.coe_lt_top
  have hu' n : MemLp (u' n) r (volume.restrict (Ioo a b)) :=
    (hu'M n).trans_lt ENNReal.coe_lt_top
  rcases le_or_gt b a with hba | hab
  · exact ⟨id, strictMono_id, 0, MemLp.zero, by simp [Ioo_eq_empty_of_le hba]⟩
  -- A uniform bound on `‖u n‖_{L¹(a, b)}`, by Hölder's inequality.
  have huC : ∀ n, ∫ t in Ioo a b, ‖u n t‖ ≤
      (volume (Ioo a b) ^ (1 - 1 / p.toReal)).toReal * M := fun n ↦ by
    refine ((hu n).integral_norm_le_mul_eLpNorm hp).trans ?_
    rw [Measure.restrict_apply_univ]
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal M.coe_nonneg
      (by simpa using huM n)) ENNReal.toReal_nonneg
  -- The continuous representatives converge uniformly along a subsequence.
  choose v hv hae using fun n ↦ (hderiv n).exists_continuousOn_ae_eq ((hu' n).integrable hr.le)
  obtain ⟨φ, hφ, hunif⟩ := exists_subseq_uniformCauchySeqOn_of_hasWeakLineDerivOn hi hr hab
    (fun n ↦ ((hu n).integrable hp).norm) huC hderiv hu' hu'M hv hae
  -- Ehrling's inequality turns this into a Cauchy sequence in `Lᵖ(a, b; X)`.
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete (cauchySeq_toLp_of_uniformCauchySeqOn hi hj
    (fun n ↦ hu (φ n)) (fun n ↦ huM (φ n)) (fun n ↦ hae (φ n)) hunif)
  refine ⟨φ, hφ, G, Lp.memLp G, ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).1 hG).congr
    fun n ↦ eLpNorm_congr_ae ?_⟩
  exact (i.comp_memLp' (hu (φ n))).coeFn_toLp.sub EventuallyEq.rfl

end IsCompactOperator
