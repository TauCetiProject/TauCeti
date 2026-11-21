/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.Local.Haar
import TauCeti.Analysis.Sobolev.Local.Jump
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.Local.Radial
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Membership and non-membership examples for Euclidean local Sobolev classes

This file checks `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` across finite-dimensional real normed
spaces, arbitrary Borel additive Haar measures, and infinite-dimensional Banach targets,
illustrating the general criteria proved in `Local.Basic`, `Local.Lipschitz`, `Local.Radial`,
`Local.Jump`, and `Local.Haar`:

* The identity map `x ↦ x` belongs to every `MemWkpLoc p U k` (`TauCeti.memWkpLoc_id`), yet fails
  global `Lᵖ` membership for every `0 < p` on any nontrivial space (`TauCeti.not_memLp_id`).
* The norm `x ↦ ‖x‖` belongs to `MemWkpLoc p U 1` on any finite-dimensional real normed space
  (`TauCeti.memWkpLoc_one_norm`), including non-inner-product models such as `ℝ × ℝ` with the
  supremum norm, where the inner-product gradient formula fails (`TauCeti.fderiv_norm_prod_apply`).
* Near the origin of a nontrivial finite-dimensional space `E`, `x ↦ ‖x‖⁻¹` is locally `Lᵖ`
  iff `p < dim E` (`TauCeti.memLpLoc_norm_inv_iff`), and on a real inner product space of
  dimension at least two `NormedSpace.normalize` (`x ↦ ‖x‖⁻¹ • x`) lies in `MemWkpLoc p U 1`
  near the origin iff `p < dim E` (`TauCeti.memWkpLoc_one_normalize_iff`).
* The indicator of a half-space `{x | 0 < ℓ x}` for a nonzero continuous linear functional `ℓ`
  is locally `Lᵖ` everywhere (`TauCeti.memLpLoc_indicator_pos`) but admits no weak derivative on
  any open set meeting `ker ℓ` (`TauCeti.not_hasWeakFDerivOn_indicator_pos`,
  `TauCeti.not_memWkpLoc_indicator_pos`).
* Scaling `volume` by a positive constant (`TauCeti.memWkpLoc_smul_measure_iff`) or switching
  between `EuclideanSpace ℝ (Fin 2)` and `ℝ × ℝ` (supremum norm, product volume) via a continuous
  linear equivalence (`ContinuousLinearEquiv.memWkpLoc_comp_iff`) preserves local Sobolev classes.
* For infinite-dimensional Banach targets such as `lp (fun _ : ℕ => ℝ) 2`, scalar local Sobolev
  functions produce vector-valued ones (`TauCeti.memWkpLoc_one_norm.smul_const`). On the
  non-separable Hilbert space `lp (fun _ : ℝ => ℝ) 2`, however, the bounded map
  `x ↦ lp.single 2 x 1` (`lp.norm_single`) composes with every continuous linear functional to a
  function equal almost everywhere to zero—hence in every `MemWkpLoc p U k`
  (`ContinuousLinearMap.memWkpLoc_comp_lpSingle`)—yet fails Bochner strong measurability and
  therefore belongs to no `MemLpLoc p U` on any set with nonempty interior
  (`TauCeti.not_memLpLoc_lpSingle`).

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2.
-/

public noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped Topology ENNReal

namespace TauCeti

/-! ### Non-inner-product norm example -/

/-- On the non-inner-product model space `ℝ × ℝ` (equipped with the supremum norm), the
Fréchet derivative of the norm at `(1, 1 / 2)` vanishes in the second coordinate direction,
illustrating that the inner-product gradient formula does not apply to general normed spaces
even though `TauCeti.memWkpLoc_one_norm` still places `y ↦ ‖y‖` in `MemWkpLoc p U 1`. -/
theorem fderiv_norm_prod_apply :
    fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, (1 / 2 : ℝ)) (0, 1) = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | 0 < y.1 ∧ |y.2| < y.1} :=
    (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_abs.comp continuous_snd) continuous_fst)
  have hmem : ((1 : ℝ), (1 / 2 : ℝ)) ∈ {y : ℝ × ℝ | 0 < y.1 ∧ |y.2| < y.1} := by
    norm_num
  have heq : (fun y : ℝ × ℝ => ‖y‖) =ᶠ[𝓝 ((1 : ℝ), (1 / 2 : ℝ))]
      (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    filter_upwards [hopen.mem_nhds hmem] with y hy
    simp only [Prod.norm_def, Real.norm_eq_abs, ContinuousLinearMap.coe_fst',
      abs_of_pos hy.1, max_eq_left hy.2.le]
  have hfd : HasFDerivAt (fun y : ℝ × ℝ => ‖y‖)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (1, (1 / 2 : ℝ)) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.congr_of_eventuallyEq heq
  rw [hfd.fderiv]
  rfl

/-! ### Haar-measure independence and model-space comparison checks -/

section HaarAndModelChecks

-- Scaling the ambient Lebesgue measure by `2` yields the exact same local Sobolev classes.
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ ⟨(2 : ℝ≥0∞) • (volume : Measure E)⟩ p U k F _ _ f ↔ MemWkpLoc p U k f :=
  memWkpLoc_smul_measure_iff (by norm_num) (by norm_num)

-- Local Sobolev classes on `EuclideanSpace ℝ (Fin 2)` and the non-inner-product model `ℝ × ℝ`
-- (with supremum norm and product measure) agree under any continuous linear equivalence.
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {U : Set (ℝ × ℝ)} {k : ℕ} {u : ℝ × ℝ → F}
    (e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ) :
    MemWkpLoc p (e ⁻¹' U) k (u ∘ e) ↔ MemWkpLoc p U k u := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact e.memWkpLoc_comp_iff

end HaarAndModelChecks

/-! ### Infinite-dimensional Banach targets and non-separable counterexample -/

section BanachTargets

-- On `lp (fun _ : ℕ => ℝ) 2`, scaling a fixed vector by the norm yields a `W^{1,p}_loc` map on any
-- finite-dimensional real normed space for every exponent `p` and every set `U`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {p : ENNReal} {U : Set E}
    (v : lp (fun _ : ℕ => ℝ) 2) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ • v) :=
  memWkpLoc_one_norm.smul_const v

-- On the non-separable Hilbert space `lp (fun _ : ℝ => ℝ) 2`, `x ↦ lp.single 2 x 1` has unit
-- norm everywhere.
example (x : ℝ) : ‖lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)‖ = 1 := by
  rw [lp.norm_single (by norm_num), norm_one]

/-- Composing `x ↦ lp.single 2 x 1` with any continuous linear functional on
`lp (fun _ : ℝ => ℝ) 2` vanishes outside a countable set, hence equals `0` almost everywhere on
`ℝ` and belongs to every local Sobolev class `MemWkpLoc p U k`. -/
theorem _root_.ContinuousLinearMap.memWkpLoc_comp_lpSingle
    (ℓ : lp (fun _ : ℝ => ℝ) 2 →L[ℝ] ℝ) {p : ENNReal} {U : Set ℝ} {k : ℕ} :
    MemWkpLoc p U k (ℓ ∘ fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) := by
  set y : lp (fun _ : ℝ => ℝ) 2 :=
    (InnerProductSpace.toDual ℝ (lp (fun _ : ℝ => ℝ) 2)).symm ℓ
  have happly :
      ∀ x : ℝ, ℓ (lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) = y x := fun x => by
    have h := InnerProductSpace.toDual_symm_apply
      (x := lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) (y := ℓ)
    rw [← h, lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul]
  have hsum : Summable (fun x : ℝ => ‖y x‖ ^ (2 : ℝ)) := by
    simpa [ENNReal.toReal_ofNat] using (lp.memℓp y).summable (by norm_num)
  have hcount : ({x : ℝ | y x ≠ 0}).Countable := by
    refine hsum.countable_support.mono fun x hx => ?_
    simp only [Function.mem_support, ne_eq]
    have hpos : 0 < ‖y x‖ := norm_pos_iff.2 hx
    positivity
  have hae :
      (ℓ ∘ fun x : ℝ =>
        lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) =ᵐ[volume] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hcount.measure_zero volume)] with x hx
    have hyx : y x = 0 := not_not.1 hx
    simp [Function.comp_apply, happly, hyx]
  exact (memWkpLoc_zero_fun (p := p) (U := U) (k := k)).congr_ae (ae_restrict_of_ae hae.symm)

/-- **Strong measurability counterexample in a non-separable Banach space.** Although
`x ↦ lp.single 2 x 1` on `lp (fun _ : ℝ => ℝ) 2` has unit norm everywhere (`lp.norm_single`)
and composes with every continuous linear functional into every `MemWkpLoc p U k`
(`ContinuousLinearMap.memWkpLoc_comp_lpSingle`), it fails Bochner strong measurability on every
compact set of positive measure and therefore lies in no `MemLpLoc p U` whenever `interior U` is
nonempty. -/
theorem not_memLpLoc_lpSingle {p : ENNReal} {U : Set ℝ} (hU : (interior U).Nonempty) :
    ¬ MemLpLoc p U (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) := by
  intro h
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  set K : Set ℝ := closedBall x₀ (r / 2)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith)).trans (hrU.trans interior_subset)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) (volume.restrict K) :=
    (memLpLoc_iff.1 h K hKU (isCompact_closedBall x₀ _)).aestronglyMeasurable
  obtain ⟨t, ht_sep, ht_ae⟩ := hmeas.isSeparable_ae_range
  set u : ℝ → lp (fun _ : ℝ => ℝ) 2 := fun x => lp.single 2 x (1 : ℝ)
  set s : Set ℝ := K ∩ u ⁻¹' t
  have hs_uncount : ¬ s.Countable := by
    intro hs_count
    have hK_le : volume K ≤ volume s + volume (K \ s) := by
      simpa only [inter_eq_right.mpr (show s ⊆ K from inter_subset_left)] using
        measure_le_inter_add_sdiff volume K s
    have hdiff : volume (K \ s) = 0 := by
      have hsub : K \ s ⊆ {x | u x ∉ t} ∩ K :=
        fun x hx => ⟨fun hxt => hx.2 ⟨hx.1, hxt⟩, hx.1⟩
      refine measure_mono_null hsub ?_
      rw [← Measure.restrict_apply' measurableSet_closedBall]
      simpa [ae_iff] using ht_ae
    rw [hs_count.measure_zero, hdiff, add_zero] at hK_le
    exact (measure_closedBall_pos volume x₀ (half_pos hr)).not_ge hK_le
  have hdist : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist (u x) (u y) := fun x _ y _ hxy => by
    rw [dist_eq_norm]
    have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (u x - u y) x
    have hval : (u x - u y) x = 1 := by
      rw [lp.coeFn_sub, Pi.sub_apply]
      simp [u, Pi.single_eq_same, Pi.single_eq_of_ne hxy]
    rwa [hval, norm_one] at hle
  exact hs_uncount (ht_sep.countable_of_mapsTo_of_le_dist (fun _ hx => hx.2) one_pos hdist)

end BanachTargets

end TauCeti
