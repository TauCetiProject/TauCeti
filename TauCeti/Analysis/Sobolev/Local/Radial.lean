/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import TauCeti.Analysis.Sobolev.Local.Sharpness
import TauCeti.Analysis.Sobolev.WeakDeriv.Jump
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.MeasureTheory.Function.LpSeminorm.Identity

/-!
# Affine, norm, radial, retraction, and jump maps in local Lebesgue and Sobolev classes

This file establishes exact membership and non-membership results for benchmark vector-valued and
singular maps in `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` on finite-dimensional real spaces,
building on the general weak-derivative, continuity, and global `Lᵖ` lemmas proved in lower-level
modules (`TauCeti.Analysis.Sobolev.WeakDeriv.Classical`, `Lipschitz`, `NormRpow`, `Jump`,
`TauCeti.Analysis.SpecialFunctions.Pow.Continuity`, and
`TauCeti.MeasureTheory.Function.LpSeminorm.Identity`):

1. **Continuous affine maps and global vs local `Lᵖ`.** Every continuous affine map
   `T : E →ᴬ[ℝ] F` into a complete space belongs to `MemWkpLoc p U k` for all `p`, `U`, and `k`.
   On any nontrivial space `E` and `p ≠ 0` (including `p = ∞`), `id : E → E` lies in
   `MemWkpLoc p Set.univ k` for all `k` while failing global `MemLp id p volume`.
2. **Non-Euclidean norm derivative.** On `Fin 2 → ℝ` (`ℓ∞` norm) at `![1, 1 / 2]`, `fderiv ℝ norm`
   is the first coordinate projection rather than the radial Euclidean inner-product functional.
3. **Inverse norm in three dimensions and vector radial powers.** On `EuclideanSpace ℝ (Fin 3)`,
   `x ↦ ‖x‖⁻¹` lies in `MemLpLoc p U` near `0` iff `p < 3`. On any nontrivial finite-dimensional
   real inner product space `E`, for `-1 < α` and `0 < p < ∞`, the continuous radial field
   `x ↦ ‖x‖ ^ α • x` lies in `MemWkpLoc p U 1` near `0` iff `-Module.finrank ℝ E < α * p.toReal`.
4. **Unit radial retraction `x ↦ ‖x‖⁻¹ • x`.** On a finite-dimensional real inner product space `E`
   with `1 < Module.finrank ℝ E` (`dim E ≥ 2`) and any `p : ℝ≥0∞` (including `0` and `∞`), the
   discontinuous unit radial retraction lies in `MemWkpLoc p U 1` near `0` iff
   `p < Module.finrank ℝ E`.
5. **Hyperplane jumps.** For a continuous linear functional `φ : E →L[ℝ] ℝ` and vector `c : F`,
   the half-space indicator `{x | 0 < φ x}.indicator (fun _ => c)` belongs to `MemLpLoc p U` for
   all `p` and `U` (`ContinuousLinearMap.memLpLoc_indicator_pos`). When `φ ≠ 0` and `c ≠ 0`, it
   lies outside `MemWkpLoc p U (k + 1)` whenever `interior U` meets `ker φ`.

## Main declarations

* `ContinuousAffineMap.memWkpLoc`, `TauCeti.memWkpLoc_id_and_not_memLp_id`.
* `TauCeti.hasFDerivAt_norm_pi_fin_two`, `TauCeti.fderiv_norm_pi_fin_two_apply`.
* `TauCeti.memLpLoc_norm_inv_euclidean_fin_three_iff`.
* `TauCeti.memWkpLoc_one_norm_rpow_smul`, `TauCeti.not_memWkpLoc_one_norm_rpow_smul`,
  `TauCeti.memWkpLoc_one_norm_rpow_smul_iff`.
* `TauCeti.memWkpLoc_one_norm_inv_smul`, `TauCeti.not_memWkpLoc_one_norm_inv_smul`,
  `TauCeti.memWkpLoc_one_norm_inv_smul_iff`.
* `ContinuousLinearMap.memLpLoc_indicator_pos`, `TauCeti.not_memWkpLoc_indicator_pos`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.2.
* H. Brezis, L. Nirenberg, *Degree theory and BMO; part I: Compact manifolds without boundary*,
  Selecta Math. (N.S.) 1 (1995), 197–263.
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Continuous affine maps and global versus local `Lᵖ` -/

section Affine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every continuous affine map into a complete space belongs to `MemWkpLoc p U k` for every
exponent `p`, subset `U`, and order `k`. -/
theorem _root_.ContinuousAffineMap.memWkpLoc (T : E →ᴬ[ℝ] F) (p : ℝ≥0∞) (U : Set E) (k : ℕ) :
    MemWkpLoc p U k T :=
  (T.contDiff.contDiffOn (s := ((⊤ : Opens E) : Set E))).memWkpLoc (subset_univ U)

/-- **Global `id : E → E` lies in every `MemWkpLoc` class but in no nonzero global `Lᵖ` space.** -/
theorem memWkpLoc_id_and_not_memLp_id [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0) (k : ℕ) :
    MemWkpLoc p (univ : Set E) k (id : E → E) ∧ ¬ MemLp (id : E → E) p (volume : Measure E) :=
  ⟨(ContinuousAffineMap.id ℝ E).memWkpLoc p univ k, not_memLp_id hp0⟩

end Affine

/-! ### Concrete non-Euclidean norm derivative on `Fin 2 → ℝ` -/

section NormMap

/-- On `Fin 2 → ℝ` equipped with the `ℓ∞` norm, at `![1, 1 / 2]` the norm locally coincides with
the first coordinate projection, so its Fréchet derivative is `ContinuousLinearMap.proj 0`. -/
theorem hasFDerivAt_norm_pi_fin_two :
    HasFDerivAt (fun y : Fin 2 → ℝ => ‖y‖)
      (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)) ![1, (1 / 2 : ℝ)] := by
  let π₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)
  let S : Set (Fin 2 → ℝ) := {y | |y 1| < y 0}
  have hS_open : IsOpen S :=
    isOpen_lt (continuous_abs.comp (continuous_apply 1)) (continuous_apply 0)
  have hxS : (![1, (1 / 2 : ℝ)] : Fin 2 → ℝ) ∈ S := by
    simp [S]
    norm_num
  have heq : (fun y : Fin 2 → ℝ => ‖y‖) =ᶠ[𝓝 ![1, (1 / 2 : ℝ)]] π₀ := by
    filter_upwards [hS_open.mem_nhds hxS] with y hy
    have hy0 : 0 < y 0 := (abs_nonneg (y 1)).trans_lt hy
    refine le_antisymm ?_ ((le_abs_self (y 0)).trans (norm_le_pi_norm y 0))
    refine (pi_norm_le_iff_of_nonneg hy0.le).2 fun i => ?_
    fin_cases i
    · simp [Real.norm_of_nonneg hy0.le]
    · simpa [Real.norm_eq_abs] using hy.le
  exact π₀.hasFDerivAt.congr_of_eventuallyEq heq

/-- On `Fin 2 → ℝ` (`ℓ∞` norm), the derivative of `y ↦ ‖y‖` at `![1, 1 / 2]` annihilates `![0, 1]`,
witnessing that it is not proportional to the radial Euclidean inner-product functional at
`![1, 1 / 2]`. -/
theorem fderiv_norm_pi_fin_two_apply :
    fderiv ℝ (fun y : Fin 2 → ℝ => ‖y‖) ![1, (1 / 2 : ℝ)] ![0, 1] = 0 := by
  rw [hasFDerivAt_norm_pi_fin_two.fderiv]
  simp

end NormMap

/-! ### Three-dimensional inverse norm and vector radial powers `x ↦ ‖x‖ ^ α • x` -/

/-- **Inverse norm on `ℝ³`.** For any neighbourhood `U` of `0` in `EuclideanSpace ℝ (Fin 3)` and
every `p : ℝ≥0∞` (including `0` and `∞`), `x ↦ ‖x‖⁻¹` belongs to `MemLpLoc p U` iff `p < 3`. -/
theorem memLpLoc_norm_inv_euclidean_fin_three_iff {p : ℝ≥0∞}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ∈ 𝓝 0) :
    MemLpLoc p U (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) ↔ p < 3 := by
  simpa [finrank_euclideanSpace_fin] using memLpLoc_norm_inv_iff (p := p) hU

section RadialPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- For `-1 < α` and `0 < p < ∞`, if `-Module.finrank ℝ E < α * p.toReal`, then `x ↦ ‖x‖ ^ α • x`
belongs to `MemWkpLoc p U 1` on every subset `U` of `E`. -/
theorem memWkpLoc_one_norm_rpow_smul [Nontrivial E] {p : ℝ≥0∞} {U : Set E} {α : ℝ}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hα : -1 < α)
    (hs : -(Module.finrank ℝ E : ℝ) < α * p.toReal) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) := by
  have hnorm := memLpLoc_norm_rpow (E := E) (p := p) (U := U) hp hs
  refine memWkpLoc_one_iff.2 ⟨(continuous_norm_rpow_smul hα).continuousOn.memLpLoc,
    radialRpowDeriv α, hasWeakFDerivOn_norm_rpow_smul hα _, memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine ((memLpLoc_iff.1 hnorm K hKU hK).const_mul (1 + |α|)).of_le
    (aestronglyMeasurable_radialRpowDeriv α) ?_
  filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
  refine (norm_radialRpowDeriv_le α hx).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]

/-- For `-1 < α` and `0 < p < ∞`, if `α * p.toReal ≤ -Module.finrank ℝ E`, then `x ↦ ‖x‖ ^ α • x`
does not belong to `MemWkpLoc p U 1` on any neighbourhood `U` of `0`. -/
theorem not_memWkpLoc_one_norm_rpow_smul [Nontrivial E] {p : ℝ≥0∞} {U : Set E} {α : ℝ}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E)) (hα : -1 < α)
    (hs : α * p.toReal ≤ -(Module.finrank ℝ E : ℝ)) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) := by
  intro h
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_one_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  have hae : D =ᵐ[volume.restrict (Opens.interior U)] radialRpowDeriv α :=
    hD.ae_eq (hasWeakFDerivOn_norm_rpow_smul hα (Opens.interior U))
  have hDK : MemLp D p (volume.restrict (closedBall (0 : E) r)) :=
    memLpLoc_iff.1 hDp _ (hrU.trans interior_subset) (isCompact_closedBall (0 : E) r)
  have hradK : MemLp (radialRpowDeriv α) p (volume.restrict (closedBall (0 : E) r)) :=
    hDK.ae_eq (hae.filter_mono (ae_mono (Measure.restrict_mono hrU le_rfl)))
  have hc_pos : 0 < 1 + α := by linarith
  have hpowK : MemLp (fun x : E => ‖x‖ ^ α) p (volume.restrict (closedBall (0 : E) r)) := by
    refine (hradK.norm.const_mul (1 + α)⁻¹).of_le
      (measurable_norm.pow_const α).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) α),
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (norm_nonneg _))]
    exact (le_inv_mul_iff₀ hc_pos).2 (le_norm_radialRpowDeriv hα hx)
  exact not_memLpLoc_norm_rpow hp0 hp (closedBall_mem_nhds (0 : E) hr) hs hpowK.memLpLoc

/-- **Local `W^{1,p}` threshold of `x ↦ ‖x‖ ^ α • x` (`-1 < α`).** On a nontrivial
finite-dimensional real inner product space `E`, for `0 < p < ∞`, `-1 < α`, and any neighbourhood
`U` of `0`, `x ↦ ‖x‖ ^ α • x` belongs to `MemWkpLoc p U 1` iff
`-Module.finrank ℝ E < α * p.toReal`. -/
theorem memWkpLoc_one_norm_rpow_smul_iff [Nontrivial E] {p : ℝ≥0∞} {U : Set E} {α : ℝ}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E)) (hα : -1 < α) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) ↔ -(Module.finrank ℝ E : ℝ) < α * p.toReal :=
  ⟨fun h => not_le.1 fun hs => not_memWkpLoc_one_norm_rpow_smul hp0 hp hU hα hs h,
    memWkpLoc_one_norm_rpow_smul hp0 hp hα⟩

end RadialPower

/-! ### The unit radial retraction `x ↦ ‖x‖⁻¹ • x` in dimension at least `2` -/

section UnitRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **Sufficiency for `x ↦ ‖x‖⁻¹ • x` in `W^{1,p}_loc`.** For `1 < Module.finrank ℝ E` and any
`p < Module.finrank ℝ E` (including `0 ≤ p < 1` and `1 ≤ p < dim E`), the unit radial retraction
lies in `MemWkpLoc p U 1` on every subset `U` of `E`. -/
theorem memWkpLoc_one_norm_inv_smul (hd : 1 < Module.finrank ℝ E) {p : ℝ≥0∞}
    (hp : p < Module.finrank ℝ E) (U : Set E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) := by
  have hu : MemLpLoc p U (fun x : E => ‖x‖⁻¹ • x) := by
    refine memLpLoc_iff.2 fun K _ hK => ?_
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    refine MemLp.of_bound (measurable_norm.inv.smul measurable_id).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  have hinv := memLpLoc_norm_inv (E := E) (U := U) hp
  refine memWkpLoc_one_iff.2 ⟨hu, unitRadialDeriv, hasWeakFDerivOn_norm_inv_smul hd _,
    memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine ((memLpLoc_iff.1 hinv K hKU hK).const_mul 2).of_le
    aestronglyMeasurable_unitRadialDeriv (Eventually.of_forall fun x => ?_)
  refine (norm_unitRadialDeriv_le x).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]

/-- **Sharp failure of `x ↦ ‖x‖⁻¹ • x` at and above the dimension (`dim E ≤ p ≤ ∞`).** When
`1 < Module.finrank ℝ E` and `U` is a neighbourhood of `0`, `x ↦ ‖x‖⁻¹ • x` does not belong to
`MemWkpLoc p U 1` for any `p ≥ Module.finrank ℝ E` (including `p = ∞`): in dimension `≥ 2`, every
nonzero point has a unit tangential direction along which `unitRadialDeriv x` stretches by
`‖x‖⁻¹`, which fails `Lᵖ` near `0`. -/
theorem not_memWkpLoc_one_norm_inv_smul (hd : 1 < Module.finrank ℝ E) {p : ℝ≥0∞} {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (hp : (Module.finrank ℝ E : ℝ≥0∞) ≤ p) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd)
  intro h
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_one_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  have hae : D =ᵐ[volume.restrict (Opens.interior U)] unitRadialDeriv :=
    hD.ae_eq (hasWeakFDerivOn_norm_inv_smul hd (Opens.interior U))
  have hDK : MemLp D p (volume.restrict (closedBall (0 : E) r)) :=
    memLpLoc_iff.1 hDp _ (hrU.trans interior_subset) (isCompact_closedBall (0 : E) r)
  have hradK : MemLp unitRadialDeriv p (volume.restrict (closedBall (0 : E) r)) :=
    hDK.ae_eq (hae.filter_mono (ae_mono (Measure.restrict_mono hrU le_rfl)))
  have hinvK : MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict (closedBall (0 : E) r)) := by
    refine hradK.of_le measurable_norm.inv.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
    rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x))]
    exact norm_inv_le_norm_unitRadialDeriv hd hx
  exact not_memLpLoc_norm_inv (closedBall_mem_nhds (0 : E) hr) hp hinvK.memLpLoc

/-- **Complete `W^{1,p}_loc` classification of the unit radial retraction (`dim E ≥ 2`).** For
`1 < Module.finrank ℝ E`, any neighbourhood `U` of `0`, and any `p : ℝ≥0∞` (including `0` and `∞`),
`x ↦ ‖x‖⁻¹ • x` lies in `MemWkpLoc p U 1` iff `p < Module.finrank ℝ E`. -/
theorem memWkpLoc_one_norm_inv_smul_iff (hd : 1 < Module.finrank ℝ E) {p : ℝ≥0∞} {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_one_norm_inv_smul hd hU hp h,
    fun hp => memWkpLoc_one_norm_inv_smul hd hp U⟩

end UnitRetraction

/-! ### Hyperplane jump indicators -/

section HyperplaneJump

/-- The indicator `{x | 0 < φ x}.indicator (fun _ => c)` of an open half-space belongs to
`MemLpLoc p U` for every exponent `p` (including `p = ∞`) and every subset `U`. -/
theorem _root_.ContinuousLinearMap.memLpLoc_indicator_pos {E F : Type*} [TopologicalSpace E]
    [AddCommMonoid E] [Module ℝ E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [NormedAddCommGroup F]
    (φ : E →L[ℝ] ℝ) (c : F) (p : ℝ≥0∞) (U : Set E) :
    MemLpLoc p U ({x : E | 0 < φ x}.indicator fun _ => c) := by
  have hm : MeasurableSet {x : E | 0 < φ x} :=
    (isOpen_lt continuous_const φ.continuous).measurableSet
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact (memLp_const c).indicator hm.nullMeasurableSet

/-- **A nonzero hyperplane jump lies outside every positive-order `MemWkpLoc` class whose interior
meets the hyperplane.** -/
theorem not_memWkpLoc_indicator_pos {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) {c : F} (hc : c ≠ 0)
    {p : ℝ≥0∞} {U : Set E} {x₀ : E} (hx₀ : x₀ ∈ interior U) (hφ₀ : φ x₀ = 0) (k : ℕ) :
    ¬ MemWkpLoc p U (k + 1) ({x : E | 0 < φ x}.indicator fun _ => c) := by
  intro h
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_pos hφ hc hx₀ hφ₀ D hD

end HyperplaneJump

end TauCeti
