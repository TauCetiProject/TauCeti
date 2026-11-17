/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.Haar
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# Haar-measure independence and linear transport for local Sobolev classes

This file establishes two invariance properties of the local Lebesgue and Sobolev classes
`TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc`:

1. **Scaling and Haar-measure independence.** Multiplying the reference measure `μ` by a finite
   constant `c : ℝ≥0∞` preserves `MemWkpLoc` (`TauCeti.MemWkpLoc.smul_measure`), and a positive
   finite factor leaves `MemWkpLoc` unchanged (`TauCeti.memWkpLoc_smul_measure_iff`) while scaling
   `TauCeti.eLpNormWkp` by `c ^ (1 / p).toReal` (`TauCeti.eLpNormWkp_smul_measure`). Because any
   two additive Haar measures on a locally compact, second-countable Hausdorff topological group
   differ by a positive finite scalar (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`), the
   predicates `MemLpLoc` and `MemWkpLoc` are independent of the choice of additive Haar measure
   (`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`, `TauCeti.memWkpLoc_iff_of_isAddHaarMeasure`).

2. **Linear transport.** Any continuous linear equivalence `e : E ≃L[ℝ] E'` between
   finite-dimensional real normed spaces pushes an additive Haar measure `μ` on `E` forward to an
   additive Haar measure `μ.map e` on `E'`. Combining Haar independence with the weak chain rule
   `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv` carries `MemLpLoc` and `MemWkpLoc` of
   every order `k` across `e` for arbitrary additive Haar measures `μ` on `E` and `ν` on `E'`
   (`TauCeti.MemLpLoc.comp_continuousLinearEquiv`,
   `ContinuousLinearEquiv.memLpLoc_comp_preimage_iff`,
   `TauCeti.MemWkpLoc.comp_continuousLinearEquiv`,
   `ContinuousLinearEquiv.memWkpLoc_comp_preimage_iff`).
   In particular, replacing a norm on `E` by an equivalent norm (not necessarily an inner product
   norm) leaves the local Lebesgue and Sobolev classes unchanged.

## References

* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2, pp. 2–3.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Haar-measure independence of `MemLpLoc` -/

section HaarMemLpLoc

variable {G ε : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace ε] [ENorm ε] {p : ℝ≥0∞} {U : Set G} {f : G → ε}

/-- On a locally compact, second-countable additive topological group with its Borel σ-algebra (in
particular, any finite-dimensional real normed space), local `Lᵖ` membership is independent of the
choice of additive Haar measure. -/
theorem memLpLoc_iff_of_isAddHaarMeasure (μ ν : Measure G) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] :
    MemLpLoc p U f μ ↔ MemLpLoc p U f ν := by
  have hμν : μ = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  have hc0 : (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  conv_lhs => rw [hμν]
  exact memLpLoc_smul_measure_iff hc0 ENNReal.coe_ne_top

end HaarMemLpLoc

/-! ### Measure scaling and Haar-measure independence of `MemWkpLoc` and `eLpNormWkp` -/

section SmulMeasure

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {k : ℕ}
  {f : E → F}

private theorem memWkpLoc_smul_measure_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : MemWkpLoc p U k f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    MemWkpLoc p U k f (c • μ) := by
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hf).smul_measure hc)
  | succ k ih =>
    obtain ⟨hLp, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hLp.smul_measure hc, D, hD.smul_measure hc, ih hDk⟩

/-- Scaling the reference measure by a finite constant preserves local Sobolev membership of every
order. -/
theorem MemWkpLoc.smul_measure (hf : MemWkpLoc p U k f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    MemWkpLoc p U k f (c • μ) := by
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hf).smul_measure hc)
  | succ k =>
    obtain ⟨hLp, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2
      ⟨hLp.smul_measure hc, D, hD.smul_measure hc, memWkpLoc_smul_measure_max hDk hc⟩

/-- Scaling the reference measure by a positive finite constant leaves local Sobolev membership of
every order unchanged. -/
theorem memWkpLoc_smul_measure_iff {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    MemWkpLoc p U k f (c • μ) ↔ MemWkpLoc p U k f μ := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'

private theorem eLpNormWkp_smul_measure_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    eLpNormWkp p U k f (c • μ) = c ^ (1 / p).toReal * eLpNormWkp p U k f μ := by
  have ha0 : c ^ (1 / p).toReal ≠ 0 :=
    (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hc0) ENNReal.toReal_nonneg).ne'
  have hat : c ^ (1 / p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc
  induction k generalizing F with
  | zero =>
    rw [eLpNormWkp_zero, eLpNormWkp_zero, Measure.restrict_smul,
      eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul]
  | succ k ih =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, Measure.restrict_smul,
      eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul, mul_add]
    congr 1
    simp_rw [hasWeakFDerivOn_smul_measure_iff hc0 hc, ih, ENNReal.mul_iInf_of_ne ha0 hat]

/-- Scaling the reference measure by a positive finite constant `c` scales the extended `W^{k,p}`
norm by `c ^ (1 / p).toReal`, for every order `k` and every exponent `p` including `0` and `∞`. -/
theorem eLpNormWkp_smul_measure {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    eLpNormWkp p U k f (c • μ) = c ^ (1 / p).toReal * eLpNormWkp p U k f μ := by
  have ha0 : c ^ (1 / p).toReal ≠ 0 :=
    (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hc0) ENNReal.toReal_nonneg).ne'
  have hat : c ^ (1 / p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc
  cases k with
  | zero =>
    rw [eLpNormWkp_zero, eLpNormWkp_zero, Measure.restrict_smul,
      eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul]
  | succ k =>
    rw [eLpNormWkp_succ, eLpNormWkp_succ, Measure.restrict_smul,
      eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul, mul_add]
    congr 1
    simp_rw [hasWeakFDerivOn_smul_measure_iff hc0 hc,
      eLpNormWkp_smul_measure_max.{u, v} (F := E →L[ℝ] F) hc0 hc, ENNReal.mul_iInf_of_ne ha0 hat]

end SmulMeasure

section HaarMemWkpLoc

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F}

/-- On a locally compact, second-countable real normed space with its Borel σ-algebra (in
particular, any finite-dimensional real normed space), local Sobolev membership of every order is
independent of the choice of additive Haar measure. -/
theorem memWkpLoc_iff_of_isAddHaarMeasure (μ ν : Measure E) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] :
    MemWkpLoc p U k f μ ↔ MemWkpLoc p U k f ν := by
  have hμν : μ = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  have hc0 : (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne'
  conv_lhs => rw [hμν]
  exact memWkpLoc_smul_measure_iff hc0 ENNReal.coe_ne_top

end HaarMemWkpLoc

/-! ### Source transport by continuous linear equivalences -/

section ContinuousLinearEquivLp

universe u₁ u₂

variable {E : Type u₁} {E' : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  {μ : Measure E} {ν : Measure E'} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

/-- **Linear transport of local `Lᵖ` membership.** Precomposing with a continuous linear
equivalence `e : E ≃L[ℝ] E'` carries `MemLpLoc p V u ν` to `MemLpLoc p U (u ∘ e) μ` whenever `e`
maps `U` into `V`, for arbitrary additive Haar measures `μ` on `E` and `ν` on `E'`. -/
theorem MemLpLoc.comp_continuousLinearEquiv {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {u : E' → ε} (hu : MemLpLoc p V u ν) (e : E ≃L[ℝ] E')
    (hUV : MapsTo e U V) : MemLpLoc p U (u ∘ e) μ := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hu' : MemLpLoc p V u (μ.map e) := (memLpLoc_iff_of_isAddHaarMeasure (μ.map e) ν).2 hu
  have he : MeasurePreserving e μ (μ.map e) := ⟨e.continuous.measurable, rfl⟩
  exact memLpLoc_iff.2 fun K hKU hK =>
    e.toHomeomorph.memLp_comp_restrict_of_forall_isCompact he
      (fun L hL hLV => memLpLoc_iff.1 hu' L hLV hL) hK (hKU.trans hUV)

/-- **Equivalence of local `Lᵖ` classes under a continuous linear equivalence.** For arbitrary
additive Haar measures `μ` on `E` and `ν` on `E'`, `u ∘ e` is locally `Lᵖ(μ)` on `e ⁻¹' V` exactly
when `u` is locally `Lᵖ(ν)` on `V`. -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_preimage_iff
    {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {p : ℝ≥0∞} {V : Set E'} {u : E' → ε}
    (e : E ≃L[ℝ] E') :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) μ ↔ MemLpLoc p V u ν := by
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V (e ⁻¹' V) := fun y hy => by simpa using hy
  have h' : MemLpLoc p V ((u ∘ e) ∘ e.symm) ν := h.comp_continuousLinearEquiv e.symm hVU
  have heq : (u ∘ e) ∘ e.symm = u := funext fun y => by simp
  rwa [heq] at h'

end ContinuousLinearEquivLp

section ContinuousLinearEquivWkp

universe u₁ u₂ v

variable {E : Type u₁} {E' : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  {μ : Measure E} {ν : Measure E'} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

private theorem memWkpLoc_comp_continuousLinearEquiv_max {F : Type max u₁ u₂ v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {V : Set E'} {k : ℕ}
    {u : E' → F} (hu : MemWkpLoc p V k u ν) (e : E ≃L[ℝ] E') (hUV : MapsTo e U V) :
    MemWkpLoc p U k (u ∘ e) μ := by
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  have hUV_int : MapsTo e (Opens.interior U) (Opens.interior V) := by
    intro x hx
    exact interior_maximal ((image_mono interior_subset).trans hUV.image_subset)
      (e.toHomeomorph.isOpenMap _ isOpen_interior) ⟨x, hx, rfl⟩
  induction k generalizing F with
  | zero => exact memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).comp_continuousLinearEquiv e hUV)
  | succ k ih =>
    obtain ⟨hLp, D, hD, hDk⟩ := memWkpLoc_succ_iff.1 hu
    have : CompleteSpace F := hD.completeSpace
    refine memWkpLoc_succ_iff.2 ⟨hLp.comp_continuousLinearEquiv e hUV,
      fun x => (D (e x)).comp (e : E →L[ℝ] E'),
      hD.comp_continuousLinearEquiv (μ := μ) e hUV_int, ?_⟩
    exact (ih hDk).clm_comp ((ContinuousLinearMap.compL ℝ E E' F).flip (e : E →L[ℝ] E'))

/-- **Linear transport of local Sobolev classes.** Precomposing with a continuous linear equivalence
`e : E ≃L[ℝ] E'` carries `MemWkpLoc p V k u ν` to `MemWkpLoc p U k (u ∘ e) μ` for every order `k`
whenever `e` maps `U` into `V`, for arbitrary additive Haar measures `μ` on `E` and `ν` on `E'`. -/
theorem MemWkpLoc.comp_continuousLinearEquiv {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {k : ℕ} {u : E' → F} (hu : MemWkpLoc p V k u ν)
    (e : E ≃L[ℝ] E') (hUV : MapsTo e U V) : MemWkpLoc p U k (u ∘ e) μ := by
  let lift : F ≃L[ℝ] ULift.{max u₁ u₂} F := (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := F)).symm
  have hu' : MemWkpLoc p V k (fun y => lift (u y)) ν := lift.comp_memWkpLoc_iff.2 hu
  have h' : MemWkpLoc p U k (fun x => lift ((u ∘ e) x)) μ :=
    memWkpLoc_comp_continuousLinearEquiv_max hu' e hUV
  exact lift.comp_memWkpLoc_iff.1 h'

/-- **Equivalence of local Sobolev classes under a continuous linear equivalence.** For arbitrary
additive Haar measures `μ` on `E` and `ν` on `E'` and every order `k`, `u ∘ e` lies in
`W^{k,p}_loc(e ⁻¹' V; μ)` exactly when `u` lies in `W^{k,p}_loc(V; ν)`. -/
theorem _root_.ContinuousLinearEquiv.memWkpLoc_comp_preimage_iff {F : Type v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {V : Set E'} {k : ℕ} {u : E' → F}
    (e : E ≃L[ℝ] E') :
    MemWkpLoc p (e ⁻¹' V) k (u ∘ e) μ ↔ MemWkpLoc p V k u ν := by
  have : FiniteDimensional ℝ E := e.symm.toLinearEquiv.finiteDimensional
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V (e ⁻¹' V) := fun y hy => by simpa using hy
  have h' : MemWkpLoc p V k ((u ∘ e) ∘ e.symm) ν := h.comp_continuousLinearEquiv e.symm hVU
  have heq : (u ∘ e) ∘ e.symm = u := funext fun y => by simp
  rwa [heq] at h'

end ContinuousLinearEquivWkp

end TauCeti
