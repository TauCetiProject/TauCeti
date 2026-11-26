/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Sobolev.Local.FirstOrder
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.Hyperplane
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable
import TauCeti.MeasureTheory.Function.MemLpLoc.NormInv
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.Topology.Algebra.Module.Trace

/-!
# Membership, counterexamples, and sharpness for `MemW1pLoc`

This file records explicit membership, non-membership, and sharpness examples for the first-order
local Sobolev class `TauCeti.MemW1pLoc`:

* **Bochner measurability vs. scalar weak differentiability.** Without prior Bochner strong
  measurability, `t ↦ lp.single 2 t 1` into non-separable `ℓ²(ℝ)` satisfies scalar
  `MemW1pLoc p ⊤` after every continuous linear functional while failing `MemLpLoc p Set.univ`
  (`TauCeti.forall_strongDual_memW1pLoc_and_not_memLpLoc_lpSingle`, cf. Arendt–Kreuter), showing
  that prior `MemLpLoc` hypotheses in `TauCeti.MemLpLoc.memW1pLoc_of_forall_strongDual` cannot be
  omitted in infinite dimensions.
* **Identity and norm.** The identity belongs to `MemW1pLoc p Ω` (`TauCeti.memW1pLoc_id`) without
  belonging to global `Lᵖ` for `p ≠ 0` on a nontrivial space (`TauCeti.not_memLp_id` in
  `TauCeti.MeasureTheory.Integral.NormRpow`); `x ↦ ‖x‖` belongs to `MemW1pLoc p Ω` for all `p` via
  `lipschitzWith_one_norm.memW1pLoc`, with `‖fderiv ℝ (‖·‖) x‖ ≤ 1` from
  `norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm` (`TauCeti.norm_fderiv_norm_le` in
  `TauCeti.Analysis.Calculus.FDeriv.Norm`, while on `ι → ℝ` with the supremum norm its classical
  derivative at points where a single nonzero coordinate strictly dominates is given by
  `TauCeti.hasFDerivAt_pi_norm_of_abs_lt` there).
* **Unit radial field.** On an inner product space of dimension `d ≥ 2` and an open set `Ω`
  containing `0`, the unit radial map `x ↦ ‖x‖⁻¹ • x` belongs to `MemW1pLoc p Ω` if and only if
  `p < d` (`TauCeti.memW1pLoc_norm_inv_smul_iff`).
* **Hyperplane half-space indicators.** For `ℓ ≠ 0`, the indicator of `{x | 0 < ℓ x}` belongs to
  `MemLpLoc p Ω` for all `p` (`StrongDual.memLpLoc_indicator_pos`) but never to `MemW1pLoc p Ω`
  when `Ω` meets `{x | ℓ x = 0}` (`TauCeti.not_memW1pLoc_indicator_pos`).

## References

* W. P. Ziemer, *Weakly Differentiable Functions*, Graduate Texts in Mathematics 120, Springer,
  1989, §2.1–§2.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299.
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology RealInnerProductSpace

namespace TauCeti

/-- **Scalar Sobolev regularity does not imply Bochner measurability.** Let
`u : ℝ → lp (fun _ : ℝ => ℝ) 2` send `t` to the basis vector `lp.single 2 t 1` in non-separable
`ℓ²(ℝ)`. Every continuous linear functional `ℓ` vanishes on `u t` outside a countable set, so
`ℓ ∘ u =ᵐ[volume] 0` and `MemW1pLoc p ⊤ (ℓ ∘ u)` holds for every `p : ℝ≥0∞`; yet `u` has discrete
uncountable essential range on `[0, 1]`, so `u` fails `MemLpLoc p Set.univ` (and hence
`MemW1pLoc p ⊤`) for every `p : ℝ≥0∞`. -/
theorem forall_strongDual_memW1pLoc_and_not_memLpLoc_lpSingle (p : ℝ≥0∞) :
    (∀ ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2),
      MemW1pLoc p ⊤ (fun t : ℝ => ℓ (lp.single 2 t (1 : ℝ)))) ∧
    ¬ MemLpLoc p (Set.univ : Set ℝ) (fun t : ℝ => lp.single 2 t (1 : ℝ)) := by
  classical
  set H := lp (fun _ : ℝ => ℝ) 2
  set u : ℝ → H := fun t => lp.single 2 t (1 : ℝ)
  constructor
  -- Each `ℓ ∈ H*` is represented by `w ∈ ℓ²(ℝ)` of countable support, so `ℓ ∘ u =ᵐ 0`.
  · intro ℓ
    let w : H := (InnerProductSpace.toDual ℝ H).symm ℓ
    have hw_eval : ∀ t : ℝ, ℓ (u t) = w t := fun t => by
      have h1 : ℓ (u t) = ⟪w, lp.single 2 t (1 : ℝ)⟫ := by simp [u, w]
      rw [h1, lp.inner_single_right]
      simp
    have hcnt : (Function.support fun t : ℝ => (w : ℝ → ℝ) t).Countable := by
      have hs : Summable fun t : ℝ => ‖(w : ℝ → ℝ) t‖ ^ (2 : ℝ≥0∞).toReal :=
        (lp.memℓp w).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      refine hs.countable_support.mono fun t ht => ?_
      simp [ht]
    have hae : (0 : ℝ → ℝ) =ᵐ[volume.restrict (⊤ : Opens ℝ)] fun t : ℝ => ℓ (u t) := by
      refine ae_restrict_of_ae ?_
      filter_upwards [compl_mem_ae_iff.2 (hcnt.measure_zero _)] with t ht
      rw [Pi.zero_apply, hw_eval]
      exact (Function.notMem_support.1 ht).symm
    exact (memW1pLoc_zero (p := p) (Ω := (⊤ : Opens ℝ)) (F := ℝ)).congr_ae hae
  -- Conversely, `u` sends `[0, 1]` (of positive measure) to pairwise `1`-separated vectors, so `u`
  -- is not a.e. strongly measurable on `[0, 1]`.
  · intro hu
    refine not_aestronglyMeasurable_restrict_of_pairwise_le_dist (μ := volume)
      (s := Icc (0 : ℝ) 1) (ε := 1) (by simp [Real.volume_Icc]) one_pos (fun x _ y _ hxy => ?_)
      (memLpLoc_iff.1 hu (Icc 0 1) (subset_univ _) isCompact_Icc).aestronglyMeasurable
    simp only [dist_eq_norm]
    have hle : |(u x - u y) x| ≤ ‖u x - u y‖ := lp.norm_apply_le_norm two_ne_zero (u x - u y) x
    have heval : (u x - u y) x = 1 := by simp [u, lp.single_apply, hxy]
    simpa [heval] using hle

/-- The identity map of a finite-dimensional real normed space belongs to `MemW1pLoc p Ω` on every
open set and for every exponent `p : ℝ≥0∞`. -/
theorem memW1pLoc_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (p : ℝ≥0∞) (Ω : Opens E) :
    MemW1pLoc p Ω (id : E → E) μ :=
  (ContinuousLinearMap.id ℝ E).memW1pLoc

/-- **Sharpness on the unit radial map.** On a finite-dimensional real inner product space `E` of
dimension `d ≥ 2` and an open set `Ω` containing `0`, the unit radial map `x ↦ ‖x‖⁻¹ • x` belongs
to `MemW1pLoc p Ω` if and only if `p < Module.finrank ℝ E`. -/
theorem memW1pLoc_norm_inv_smul_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {p : ℝ≥0∞} {Ω : Opens E} (hd : 2 ≤ Module.finrank ℝ E) (h0 : (0 : E) ∈ Ω) :
    MemW1pLoc p Ω (fun x : E => ‖x‖⁻¹ • x) μ ↔ p < Module.finrank ℝ E := by
  have hd1 : 1 < Module.finrank ℝ E := lt_of_lt_of_le one_lt_two hd
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd1)
  let D : E → E →L[ℝ] E := fun x => ‖x‖ ^ (-1 : ℝ) • ContinuousLinearMap.id ℝ E +
    ((-1 * ‖x‖ ^ ((-1 : ℝ) - 2)) • innerSL ℝ x).smulRight x
  have hweak : HasWeakFDerivOn μ Ω (fun x : E => ‖x‖⁻¹ • x) D := by
    convert hasWeakFDerivOn_norm_rpow_neg_one_smul_self (μ := μ) hd1 Ω using 1
    funext x
    rw [Real.rpow_neg_one]
  constructor
  · intro hu
    have hDLp : MemLpLoc p Ω D μ := hu.memLpLoc_of_hasWeakFDerivOn hweak
    have htr : (fun x => traceCLM ℝ E (D x)) =
        fun x : E => ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹ := by
      funext x
      rw [traceCLM_apply, trace_rpow_smul_id_add_smulRight, Real.rpow_neg_one, ← sub_eq_add_neg]
    have hscLp : MemLpLoc p Ω (fun x : E => ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖⁻¹) μ :=
      htr ▸ hDLp.clm_comp (traceCLM ℝ E)
    have hc_ne : ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_le.2 hd
      linarith
    have hinvLp : MemLpLoc p Ω (fun x : E => ‖x‖⁻¹) μ := by
      simpa [Pi.smul_def, smul_eq_mul, inv_mul_cancel_left₀ hc_ne] using
        hscLp.const_smul ((Module.finrank ℝ E : ℝ) - 1)⁻¹
    exact (memLpLoc_norm_inv_iff_lt_finrank (Ω.isOpen.mem_nhds h0)).1 hinvLp
  · intro hp
    refine memW1pLoc_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, D, hweak,
      memLpLoc_iff.2 fun K _ hK => ?_⟩
    · have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
      refine MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable 1
        (Eventually.of_forall fun x => ?_)
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
    · have hd_r : -(Module.finrank ℝ E : ℝ) < -1 := by
        have : (2 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_le.2 hd
        linarith
      have hDmeas : AEStronglyMeasurable D (μ.restrict K) :=
        (locallyIntegrable_rpow_smul_id_add_smulRight (μ := μ) hd_r).aestronglyMeasurable.restrict
      refine ((hK.isBounded.memLp_norm_inv_restrict (mu := μ) hp).const_mul
        (1 + |(-1 : ℝ)|)).of_le hDmeas (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
      exact norm_rpow_smul_id_add_smulRight_le (-1) x

/-- **Jump discontinuities across hyperplanes are not in `MemW1pLoc`.** While the indicator of
`{x : E | 0 < ℓ x}` belongs to `MemLpLoc p Ω` for every `p` (`StrongDual.memLpLoc_indicator_pos`),
it belongs to `MemW1pLoc p Ω` for *no* exponent `p : ℝ≥0∞` whenever `ℓ ≠ 0` and `Ω` meets
`{x | ℓ x = 0}`. -/
theorem not_memW1pLoc_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0) {p : ℝ≥0∞} {Ω : Opens E} {x₀ : E}
    (hx₀ : x₀ ∈ Ω) (hx₀0 : ℓ x₀ = 0) :
    ¬ MemW1pLoc p Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) μ := by
  intro h
  obtain ⟨_, Du, hDu, _⟩ := memW1pLoc_iff.1 h
  exact not_hasWeakFDerivOn_indicator_pos hℓ hx₀ hx₀0 Du hDu

end TauCeti
