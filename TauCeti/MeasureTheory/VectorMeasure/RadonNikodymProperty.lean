/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import TauCeti.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import TauCeti.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# The Radon–Nikodým property

A real normed space `X` has the *Radon–Nikodým property with respect to* a positive measure `μ`
(`TauCeti.HasRNPWith X μ`) if every `X`-valued vector measure of finite total variation whose
variation is absolutely continuous with respect to `μ` is given by a Bochner-integrable density,
`m = μ.withDensityᵥ f`. The intrinsic property `TauCeti.HasRNP X` is the relative property for
Lebesgue measure on the unit interval `[0, 1]`.

This file develops the relative property for a fixed measure. It is invariant under continuous
linear equivalences of the target and inherited by closed subspaces. It passes from a measure to
its restriction to a measurable set, and, for σ-finite measures, to every absolutely continuous
measure. Equivalent σ-finite measures therefore give the same property. Scalar targets have it
for every σ-finite measure, by the scalar Radon–Nikodým theorem.

The proofs only use the native vector-measure variation and densities. For closed subspaces the
density of the pushed-forward measure takes values in the subspace almost everywhere, because its
image in the quotient has vanishing set integrals. For an absolutely continuous measure `ν ≪ μ` the
`μ`-density `f` becomes the `ν`-density `(dν/dμ)⁻¹ • f`. The set where `dν/dμ` vanishes is
`ν`-null and hence invisible to the vector measure.

## Main declarations

* `TauCeti.HasRNPWith`: the Radon–Nikodým property with respect to a fixed measure.
* `TauCeti.HasRNP`: the Radon–Nikodým property with respect to Lebesgue measure on `[0, 1]`.
* `ContinuousLinearEquiv.hasRNPWith_iff`: invariance under continuous linear equivalences.
* `TauCeti.HasRNPWith.submodule`: inheritance by closed subspaces.
* `TauCeti.HasRNPWith.restrict`: passage to the restriction to a measurable set.
* `TauCeti.HasRNPWith.mono_ac`: passage to an absolutely continuous σ-finite measure.
* `TauCeti.hasRNPWith_congr_ac`: equivalent σ-finite measures give the same property.
* `TauCeti.hasRNPWith_rclike`: real and complex scalars have the property for σ-finite measures.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Definition 1.3.9 and Definition 1.3.27.
* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Chapter III.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {S : Type*} [MeasurableSpace S]

section Definitions

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A real normed space `X` has the *Radon–Nikodým property with respect to* the measure `μ` if
every `X`-valued vector measure of finite total variation whose variation is absolutely continuous
with respect to `μ` has a Bochner-integrable density with respect to `μ`. -/
def HasRNPWith (μ : Measure S) : Prop :=
  ∀ m : VectorMeasure S X, m.variation univ < ∞ → m.variation ≪ μ →
    ∃ f : S → X, Integrable f μ ∧ m = μ.withDensityᵥ f

/-- A real normed space `X` has the *Radon–Nikodým property* if it has the Radon–Nikodým property
with respect to Lebesgue measure on the unit interval `[0, 1]`. -/
def HasRNP : Prop :=
  HasRNPWith X (volume.restrict (Icc (0 : ℝ) 1))

end Definitions

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ ν : Measure S}

omit [NormedSpace ℝ X] in
/-- A vector measure does not see a measurable set on which its variation vanishes. -/
private theorem apply_eq_apply_diff_of_variation_eq_zero {m : VectorMeasure S X} {Z B : Set S}
    (hZ : MeasurableSet Z) (hB : MeasurableSet B) (h : m.variation Z = 0) :
    m B = m (B \ Z) := by
  have h0 : m (Z ∩ B) = 0 :=
    (VectorMeasure.variation_apply_eq_zero hZ).1 h _ inter_subset_left (hZ.inter hB)
  rw [← VectorMeasure.of_add_of_sdiff (hZ.inter hB) hB inter_subset_right, h0, zero_add,
    sdiff_inter_self_eq_sdiff]

/-- Applying a continuous linear map to a vector measure keeps its total variation finite and
absolutely continuous with respect to a given measure. -/
private theorem variation_mapRangeL_lt_top_and_ac (φ : Y →L[ℝ] X) {m : VectorMeasure S Y}
    (hfin : m.variation univ < ∞) (hac : m.variation ≪ μ) :
    (VectorMeasure.mapRangeL φ m).variation univ < ∞ ∧
      (VectorMeasure.mapRangeL φ m).variation ≪ μ := by
  have hle := VectorMeasure.variation_mapRangeL_le φ m
  refine ⟨(hle univ).trans_lt ?_, (Measure.absolutelyContinuous_of_le hle).trans ?_⟩
  · rw [smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (Measure.AbsolutelyContinuous.smul_left .rfl _).trans hac

/-- The Radon–Nikodým property with respect to `μ` passes along a continuous linear
equivalence. -/
private theorem HasRNPWith.of_continuousLinearEquiv (h : HasRNPWith X μ) (e : X ≃L[ℝ] Y) :
    HasRNPWith Y μ := by
  intro m hfin hac
  obtain ⟨hfin', hac'⟩ := variation_mapRangeL_lt_top_and_ac (e.symm : Y →L[ℝ] X) hfin hac
  obtain ⟨f, hf, hm⟩ := h _ hfin' hac'
  have hef : Integrable (fun s => e (f s)) μ := (e : X →L[ℝ] Y).integrable_comp hf
  refine ⟨fun s => e (f s), hef, ?_⟩
  ext A hA
  rw [withDensityᵥ_apply hef hA, e.integral_comp_comm, ← withDensityᵥ_apply hf hA, ← hm]
  simp

end TauCeti

/-- The Radon–Nikodým property with respect to a fixed measure is invariant under continuous
linear equivalences. -/
theorem ContinuousLinearEquiv.hasRNPWith_iff {S X Y : Type*} [MeasurableSpace S]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : MeasureTheory.Measure S} (e : X ≃L[ℝ] Y) :
    TauCeti.HasRNPWith X μ ↔ TauCeti.HasRNPWith Y μ :=
  ⟨fun h => h.of_continuousLinearEquiv e, fun h => h.of_continuousLinearEquiv e.symm⟩

/-- The Radon–Nikodým property is invariant under continuous linear equivalences. -/
theorem ContinuousLinearEquiv.hasRNP_iff {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : X ≃L[ℝ] Y) : TauCeti.HasRNP X ↔ TauCeti.HasRNP Y :=
  e.hasRNPWith_iff

namespace TauCeti

variable {S : Type*} [MeasurableSpace S]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {μ ν : Measure S}

/-- The Radon–Nikodým property with respect to `μ` is inherited by closed subspaces. -/
theorem HasRNPWith.submodule (h : HasRNPWith X μ) (E : Submodule ℝ X)
    (hE : IsClosed (E : Set X)) : HasRNPWith E μ := by
  intro m hfin hac
  obtain ⟨hfin', hac'⟩ := variation_mapRangeL_lt_top_and_ac E.subtypeL hfin hac
  obtain ⟨f, hf, hm⟩ := h _ hfin' hac'
  -- The pushed-forward measure has the set integrals of `f` as values.
  have hval : ∀ A, MeasurableSet A → (m A : X) = ∫ s in A, f s ∂μ := fun A hA => by
    rw [← withDensityᵥ_apply hf hA, ← hm]
    rfl
  by_cases hX : CompleteSpace X
  swap
  · -- In an incomplete space every integral vanishes, so the measure is zero.
    refine ⟨0, integrable_zero _ _ _, ?_⟩
    ext A hA
    rw [withDensityᵥ_zero, hval A hA, integral_of_not_completeSpace hX]
    rfl
  have : IsClosed (E : Set X) := hE
  have : CompleteSpace E := hE.completeSpace_coe
  -- The image of `f` in the quotient has vanishing set integrals, so `f` lies in `E` a.e.
  have hmem : ∀ᵐ s ∂μ, f s ∈ E := by
    have hq : (fun s => E.mkQL (f s)) =ᵐ[μ] 0 := by
      refine (E.mkQL.integrable_comp hf).ae_eq_zero_of_forall_setIntegral_eq_zero
        fun A hA _ => ?_
      rw [E.mkQL.integral_comp_comm hf.integrableOn, ← hval A hA]
      exact (Submodule.Quotient.mk_eq_zero E).2 (m A).property
    filter_upwards [hq] with s hs
    exact (Submodule.Quotient.mk_eq_zero E).1 hs
  classical
  let g : S → E := fun s => if hs : f s ∈ E then ⟨f s, hs⟩ else 0
  have hgf : (fun s => (g s : X)) =ᵐ[μ] f := by
    filter_upwards [hmem] with s hs
    simp [g, hs]
  have hg' : Integrable (fun s => (g s : X)) μ := hf.congr hgf.symm
  have hg : Integrable g μ :=
    ⟨Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.1 hg'.aestronglyMeasurable,
      hg'.hasFiniteIntegral⟩
  refine ⟨g, hg, ?_⟩
  ext A hA
  rw [hval A hA, withDensityᵥ_apply hg hA]
  change _ = E.subtypeL _
  rw [← E.subtypeL.integral_comp_comm hg.integrableOn]
  exact setIntegral_congr_ae hA (hgf.mono fun s hs _ => hs.symm)

/-- The Radon–Nikodým property with respect to `μ` passes to the restriction of `μ` to a
measurable set. No σ-finiteness is needed. -/
theorem HasRNPWith.restrict (h : HasRNPWith X μ) {A : Set S} (hA : MeasurableSet A) :
    HasRNPWith X (μ.restrict A) := by
  intro m hfin hac
  obtain ⟨f, hf, rfl⟩ :=
    h m hfin (hac.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
  refine ⟨f, hf.restrict, ?_⟩
  ext B hB
  have hvar : (μ.withDensityᵥ f).variation Aᶜ = 0 :=
    hac (by rw [Measure.restrict_apply hA.compl, compl_inter_self, measure_empty])
  rw [apply_eq_apply_diff_of_variation_eq_zero hA.compl hB hvar,
    withDensityᵥ_apply hf (hB.diff hA.compl), withDensityᵥ_apply hf.restrict hB,
    Measure.restrict_restrict hB, sdiff_compl]

/-- The Radon–Nikodým property with respect to `μ` passes to every σ-finite measure `ν ≪ μ`.
A `μ`-density `f` gives the `ν`-density `(dν/dμ)⁻¹ • f`. -/
theorem HasRNPWith.mono_ac [SigmaFinite ν] [ν.HaveLebesgueDecomposition μ]
    (h : HasRNPWith X μ) (hνμ : ν ≪ μ) : HasRNPWith X ν := by
  intro m hfin hac
  obtain ⟨f, hf, rfl⟩ := h m hfin (hac.trans hνμ)
  set r : S → ℝ := fun s => (ν.rnDeriv μ s).toReal
  set Z : Set S := {s | r s = 0} with hZdef
  have hZ : MeasurableSet Z :=
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal (measurableSet_singleton 0)
  -- The density `dν/dμ` is positive and finite `ν`-almost everywhere.
  have hνZ : ν Z = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [Measure.rnDeriv_pos hνμ, hνμ.ae_le (Measure.rnDeriv_lt_top ν μ)]
      with s hs₁ hs₂
    exact (ENNReal.toReal_pos hs₁.ne' hs₂.ne).ne'
  let g : S → X := fun s => (r s)⁻¹ • f s
  have hrg : (fun s => r s • g s) = Zᶜ.indicator f := by
    ext s
    by_cases hs : r s = 0
    · simp [g, hZdef, hs]
    · simp [g, hZdef, hs, smul_smul]
  have hg : Integrable g ν :=
    (integrable_rnDeriv_smul_iff hνμ).1 (by rw [hrg]; exact hf.indicator hZ.compl)
  refine ⟨g, hg, ?_⟩
  ext A hA
  rw [withDensityᵥ_apply hg hA, ← setIntegral_rnDeriv_smul hνμ hA, hrg,
    setIntegral_indicator hZ.compl, ← withDensityᵥ_apply hf (hA.inter hZ.compl),
    apply_eq_apply_diff_of_variation_eq_zero hZ hA (hac hνZ), sdiff_eq]

/-- Equivalent σ-finite measures give the same Radon–Nikodým property. -/
theorem hasRNPWith_congr_ac [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    HasRNPWith X μ ↔ HasRNPWith X ν :=
  ⟨fun h => h.mono_ac hνμ, fun h => h.mono_ac hμν⟩

/-- The Radon–Nikodým property is inherited by closed subspaces. -/
theorem HasRNP.submodule (h : HasRNP X) (E : Submodule ℝ X) (hE : IsClosed (E : Set X)) :
    HasRNP E :=
  HasRNPWith.submodule h E hE

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The real and complex scalars have the Radon–Nikodým property with respect to every σ-finite
measure. Finiteness of the total variation is not needed here. -/
theorem hasRNPWith_rclike (μ : Measure S) [SigmaFinite μ] : HasRNPWith 𝕜 μ :=
  fun m _ hac => ⟨VectorMeasure.scalarRNDeriv m μ, VectorMeasure.integrable_scalarRNDeriv m μ,
    (VectorMeasure.withDensityᵥ_scalarRNDeriv m μ hac).symm⟩

/-- The real and complex scalars have the Radon–Nikodým property. -/
theorem hasRNP_rclike : HasRNP 𝕜 :=
  hasRNPWith_rclike 𝕜 _

end TauCeti
