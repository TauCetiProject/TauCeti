/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.FirstVariation
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.Topology.Algebra.Module.Trace

/-!
# Stationary varifolds: planes and constant plane fields

Let `E` be a finite-dimensional real inner product space. This file checks that a family of
`k`-varifolds carried by affine planes have vanishing first variation
`δV(X) = ∫ tr (P ∘ DX(x)) dV(x, P)` (`Euclidean.firstVariation`), that is, are stationary.

For a subspace `S`, `a ∈ E`, an additive Haar measure `ν` on `S`, an open `W ⊆ E` and a fixed
plane `P ∈ G(E, k)` contained in `S`, let `ρ` be the image of `ν` under `s ↦ a + s`. The varifold
`ρ⌞W ⊗ δ_P`, the image of `ρ` on `W` under `x ↦ (x, P)`, is stationary
(`Euclidean.firstVariation_map_affinePlane_eq_zero`). Since `X` vanishes off `W`, its first
variation is `∫_S tr (P ∘ DX(a + s)) dν(s) = ∫_S tr (Dg(s)) dν(s) = 0`, with
`g = P ∘ X ∘ (a + ·) : S → S` compactly supported, by the cyclicity of the trace.

* *An affine plane.* For `P = P_S`, the orthogonal projection onto a `k`-dimensional `S`, this is
  the varifold of the affine plane `a + S` in `W` with constant multiplicity. Multiplicity one is
  `ν = volume`; for `k = 1` this is the varifold of a line.
* *A measure with a constant plane field.* For `S = E`, `ρ` is any additive Haar measure `μ` on
  `E`, and `μ⌞W ⊗ δ_P` is stationary for every plane `P`
  (`Euclidean.firstVariation_map_prodMk_right_eq_zero`). For `k = dim E` the only plane is `E`,
  and this is the volume of `W`; for `E = ℝ²` and `k = 1` it is Lebesgue measure lifted with a
  constant line.

## Main results

* `Euclidean.firstVariation_map_affinePlane_eq_zero`: a Haar measure on an affine plane, with a
  constant plane field contained in it, is stationary.
* `Euclidean.firstVariation_map_prodMk_right_eq_zero`: a Haar measure with a constant plane field
  is stationary.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §39.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Module
open scoped Distributions

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ}

/-- The first variation of the image of a measure `ν` that is finite on compact sets under a proper
map `f` is `∫ div_{(f a).2} X ((f a).1) dν(a)`. -/
private theorem firstVariation_map_apply {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (ν : Measure α) [IsFiniteMeasureOnCompacts ν] {W : Opens E}
    {f : α → W × grassmannian ℝ E k} (hf : IsProperMap f) (X : 𝓓^{1}(W, E)) :
    firstVariation (ν.map f) X = ∫ a, tangentialDivergence X (f a).1 (f a).2 ∂ν := by
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap ν hf
  rw [firstVariation_apply, integral_map hf.continuous.aemeasurable (by
    simpa using (tangentialDivergenceCc (k := k) X).continuous.aestronglyMeasurable)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The tangential divergence along a map `P` with range in `S` is the trace on `S` of the
derivative of `g = P ∘ X ∘ (a + ·) : S → S`. -/
private theorem tangentialDivergence_eq_traceCLM_fderiv (S : Submodule ℝ E) {P : E →L[ℝ] E}
    (hP : ∀ x, P x ∈ S) {X : E → E} (hX : Differentiable ℝ X) (a : E) (s : S) :
    tangentialDivergence X (a + s) P = TauCeti.traceCLM ℝ S
      (fderiv ℝ (fun s : S => P.codRestrict S hP (X (a + s))) s) := by
  set Q := P.codRestrict S hP
  have hd : HasFDerivAt (fun s : S => Q (X (a + s))) (Q ∘L fderiv ℝ X (a + s) ∘L S.subtypeL) s :=
    Q.hasFDerivAt.comp s ((hX (a + s)).hasFDerivAt.comp s (S.subtypeL.hasFDerivAt.const_add a))
  -- Cyclicity of the trace moves the inclusion `S → E` from the left to the right.
  rw [hd.fderiv, tangentialDivergence_def, TauCeti.traceCLM_apply,
    ← P.subtypeL_comp_codRestrict S hP,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.trace_comp_comm', ← ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.comp_assoc]

/-- **A plane field tangent to an affine plane is stationary.** For a subspace `S`, `a ∈ E`, an
additive Haar measure `ν` on `S`, an open set `W` and a plane `P ∈ G(E, k)` contained in `S`, the
varifold `ρ⌞W ⊗ δ_P`, where `ρ` is the image of `ν` under `s ↦ a + s`, has first variation zero.
With `P = P_S` and `k = dim S` this is the varifold of the affine plane `a + S` in `W` with
constant multiplicity; multiplicity one is `ν = volume`. -/
theorem firstVariation_map_affinePlane_eq_zero (S : Submodule ℝ E) (a : E) (ν : Measure S)
    [ν.IsAddHaarMeasure] (W : Opens E) (P : grassmannian ℝ E k)
    (hP : ∀ x, (P : E →L[ℝ] E) x ∈ S) :
    firstVariation (((ν.map fun s : S => a + (s : E)).comap ((↑) : W → E)).map
      fun x => (x, P)) = 0 := by
  -- `s ↦ a + s` is a closed embedding of `S` into `E`.
  have hg : Topology.IsClosedEmbedding fun s : S => a + (s : E) :=
    (Homeomorph.addLeft a).isClosedEmbedding.comp
      S.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap ν hg.isProperMap
  -- `x ↦ (x, P)` is proper since its first component is the identity.
  have hf : IsProperMap fun x : W => ((x, P) : W × grassmannian ℝ E k) :=
    isProperMap_of_comp_of_t2 (continuous_id.prodMk continuous_const) continuous_fst
      isProperMap_id
  ext X
  rw [firstVariation_map_apply _ hf, zero_apply]
  refine (integral_subtype_comap W.isOpen.measurableSet
    (fun x => tangentialDivergence X x P)).trans ?_
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      tangentialDivergence_eq_zero_of_notMem_tsupport (fun h => hx (X.tsupport_subset h)) _,
    hg.measurableEmbedding.integral_map]
  have hX : Differentiable ℝ (X : E → E) := X.contDiff.differentiable one_ne_zero
  simp_rw [tangentialDivergence_eq_traceCLM_fderiv S hP hX a]
  -- `g = P ∘ X ∘ (a + ·)` is a compactly supported `C¹` map of `S`.
  set Q := (P : E →L[ℝ] E).codRestrict S hP
  have hgd : ContDiff ℝ 1 fun s : S => Q (X (a + s)) :=
    Q.contDiff.comp (X.contDiff.comp (contDiff_const.add S.subtypeL.contDiff))
  have hgc : HasCompactSupport fun s : S => Q (X (a + s)) :=
    (X.hasCompactSupport.comp_isClosedEmbedding hg).comp_left (map_zero _)
  rw [ContinuousLinearMap.integral_comp_comm _ ((hgd.continuous_fderiv one_ne_zero)
    |>.integrable_of_hasCompactSupport (hgc.fderiv (𝕜 := ℝ))),
    TauCeti.integral_fderiv_eq_zero_of_hasCompactSupport hgd hgc, map_zero]

/-- **A Haar measure with a constant plane field is stationary.** For an additive Haar measure `μ`,
an open set `W` and a plane `P ∈ G(E, k)`, the varifold `μ⌞W ⊗ δ_P` has first variation zero. -/
theorem firstVariation_map_prodMk_right_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (W : Opens E) (P : grassmannian ℝ E k) :
    firstVariation ((μ.comap ((↑) : W → E)).map fun x => (x, P)) = 0 := by
  -- `μ` is the image of a Haar measure on `S = E` under `s ↦ 0 + s`.
  let e : E ≃L[ℝ] (⊤ : Submodule ℝ E) := Submodule.topEquiv.symm.toContinuousLinearEquiv
  have hμ : ((μ.map e).map fun s : (⊤ : Submodule ℝ E) => 0 + (s : E)) = μ := by
    rw [Measure.map_map (by fun_prop) e.continuous.measurable]
    convert Measure.map_id
    ext x
    simp [e]
  rw [← hμ]
  exact firstVariation_map_affinePlane_eq_zero ⊤ 0 (μ.map e) W P fun _ => trivial

end Euclidean
