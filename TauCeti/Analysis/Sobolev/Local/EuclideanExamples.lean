/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Sobolev.Local.Haar
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable

/-!
# Membership and non-membership examples for Euclidean local Sobolev classes

This file checks `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` across non-inner-product normed models,
arbitrary Borel additive Haar measures, and infinite-dimensional Banach targets, illustrating
results from `Local.Basic`, `Local.Lipschitz`, and `Local.Haar`:

* On the non-inner-product model space `ℝ × ℝ` (with the supremum norm), the Fréchet derivative of
  `y ↦ ‖y‖` at `(1, 1 / 2)` vanishes in the second coordinate direction, showing that the
  inner-product gradient formula fails even though `TauCeti.memWkpLoc_one_norm` still places
  `y ↦ ‖y‖` in `MemWkpLoc p U 1`.
* Scaling `volume` by a positive constant (`TauCeti.memWkpLoc_smul_measure_iff`) or switching
  between `EuclideanSpace ℝ (Fin 2)` and `ℝ × ℝ` (supremum norm, product volume) via a continuous
  linear equivalence (`ContinuousLinearEquiv.memWkpLoc_comp_right_iff`) preserves local Sobolev
  classes.
* For infinite-dimensional Banach targets such as `lp (fun _ : ℕ => ℝ) 2`, scalar local Sobolev
  functions produce vector-valued ones (`TauCeti.memWkpLoc_one_norm.smul_const`). On the
  non-separable Hilbert space `lp (fun _ : ℝ => ℝ) 2`, however, the bounded map
  `x ↦ lp.single 2 x 1` (`lp.norm_single`) composes with every continuous linear functional to a
  function equal almost everywhere to zero (`ContinuousLinearMap.comp_lpSingle_ae_eq_zero`)—hence
  in every `MemWkpLoc p U k` (`ContinuousLinearMap.memWkpLoc_comp_lpSingle`)—yet fails Bochner
  strong measurability on every measurable set of positive measure
  (`TauCeti.not_aestronglyMeasurable_restrict_lpSingle`) and therefore belongs to no
  `MemLpLoc p U` on any set with nonempty interior (`TauCeti.not_memLpLoc_lpSingle`).

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

-- On the non-inner-product model space `ℝ × ℝ` (equipped with the supremum norm), the Fréchet
-- derivative of the norm at `(1, 1 / 2)` vanishes in the second coordinate direction, illustrating
-- that the inner-product gradient formula does not apply to general normed spaces even though
-- `TauCeti.memWkpLoc_one_norm` still places `y ↦ ‖y‖` in `MemWkpLoc p U 1`.
example : fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, (1 / 2 : ℝ)) (0, 1) = 0 := by
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
  exact e.memWkpLoc_comp_right_iff

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
`ℝ`. -/
theorem _root_.ContinuousLinearMap.comp_lpSingle_ae_eq_zero
    (ℓ : lp (fun _ : ℝ => ℝ) 2 →L[ℝ] ℝ) :
    (ℓ ∘ fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) =ᵐ[volume] 0 := by
  set y : lp (fun _ : ℝ => ℝ) 2 :=
    (InnerProductSpace.toDual ℝ (lp (fun _ : ℝ => ℝ) 2)).symm ℓ
  have happly :
      ∀ x : ℝ, ℓ (lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) = y x := fun x => by
    have h := InnerProductSpace.toDual_symm_apply
      (x := lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) (y := ℓ)
    rw [← h, lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul]
  have hcount : ({x : ℝ | y x ≠ 0}).Countable :=
    lp.countable_dsupport (by norm_num : (2 : ℝ≥0∞) ≠ ∞) y
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hcount.measure_zero volume)] with x hx
  have hyx : y x = 0 := not_not.1 hx
  simp [Function.comp_apply, happly, hyx]

/-- Composing `x ↦ lp.single 2 x 1` with any continuous linear functional on
`lp (fun _ : ℝ => ℝ) 2` belongs to every local Sobolev class `MemWkpLoc p U k`. -/
theorem _root_.ContinuousLinearMap.memWkpLoc_comp_lpSingle
    (ℓ : lp (fun _ : ℝ => ℝ) 2 →L[ℝ] ℝ) {p : ENNReal} {U : Set ℝ} {k : ℕ} :
    MemWkpLoc p U k (ℓ ∘ fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) :=
  (memWkpLoc_zero_fun (p := p) (U := U) (k := k)).congr_ae
    (ae_restrict_of_ae ℓ.comp_lpSingle_ae_eq_zero.symm)

/-- On any subset of `ℝ` of positive measure, `x ↦ lp.single 2 x 1` in the
non-separable Hilbert space `lp (fun _ : ℝ => ℝ) 2` fails Bochner strong measurability. -/
theorem not_aestronglyMeasurable_restrict_lpSingle {K : Set ℝ} (hKpos : 0 < volume K) :
    ¬ AEStronglyMeasurable
      (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) (volume.restrict K) := by
  set u : ℝ → lp (fun _ : ℝ => ℝ) 2 := fun x => lp.single 2 x (1 : ℝ)
  refine not_aestronglyMeasurable_restrict_of_pairwise_le_dist hKpos.ne' one_pos
    fun x _ y _ hxy => ?_
  dsimp only
  rw [dist_eq_norm]
  have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (u x - u y) x
  have hval : (u x - u y) x = 1 := by
    rw [lp.coeFn_sub, Pi.sub_apply]
    simp [u, Pi.single_eq_same, Pi.single_eq_of_ne hxy]
  rwa [hval, norm_one] at hle

/-- **Strong measurability counterexample in a non-separable Banach space.** Although
`x ↦ lp.single 2 x 1` on `lp (fun _ : ℝ => ℝ) 2` has unit norm everywhere (`lp.norm_single`)
and composes with every continuous linear functional to an almost-everywhere zero function
(`ContinuousLinearMap.comp_lpSingle_ae_eq_zero`) and hence into every `MemWkpLoc p U k`
(`ContinuousLinearMap.memWkpLoc_comp_lpSingle`), it fails Bochner strong measurability on every
subset of positive measure (`TauCeti.not_aestronglyMeasurable_restrict_lpSingle`) and
therefore lies in no `MemLpLoc p U` whenever `interior U` is nonempty. -/
theorem not_memLpLoc_lpSingle {p : ENNReal} {U : Set ℝ} (hU : (interior U).Nonempty) :
    ¬ MemLpLoc p U (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) 2 x (1 : ℝ)) := by
  intro h
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  set K : Set ℝ := closedBall x₀ (r / 2)
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith)).trans (hrU.trans interior_subset)
  exact not_aestronglyMeasurable_restrict_lpSingle (measure_closedBall_pos volume x₀ (half_pos hr))
    (memLpLoc_iff.1 h K hKU (isCompact_closedBall x₀ _)).aestronglyMeasurable

end BanachTargets

end TauCeti
