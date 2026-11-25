/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Geometry.MeasureTheory.Varifold.FirstVariation
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Topology.Algebra.Module.Trace

/-!
# Stationary varifolds: planes and constant plane fields

Let `E` be a finite-dimensional real inner product space. This file checks that two families of
`k`-varifolds have vanishing first variation `δV(X) = ∫ tr (P ∘ DX(x)) dV(x, P)`
(`Euclidean.firstVariation`), that is, are stationary.

* *A measure with a constant plane field.* For an additive Haar measure `μ` on `E`, an open
  `W ⊆ E` and a fixed plane `P ∈ G(E, k)`, the varifold `μ⌞W ⊗ δ_P`, the image of `μ` on `W`
  under `x ↦ (x, P)`, is stationary (`Euclidean.firstVariation_map_prodMk_const`): its first
  variation is `∫ tr (P ∘ DX) dμ = tr (P ∘ ∫ DX dμ) = 0`. For `k = dim E` the only plane is `E`,
  and this is the volume of `W`; for `E = ℝ²` and `k = 1` it is Lebesgue measure lifted with a
  constant line.
* *An affine plane.* For a `k`-dimensional subspace `S` and `a ∈ E`, the varifold of the affine
  plane `a + S` with multiplicity one, the image of the volume of `S` under
  `s ↦ (a + s, P_S)` where `P_S` is the orthogonal projection onto `S`, is stationary
  (`Euclidean.firstVariation_map_affinePlane`). Its first variation is
  `∫_S tr (P_S ∘ DX(a + s)) ds = ∫_S tr (Dg(s)) ds = 0`, with `g = P_S ∘ X ∘ (a + ·) : S → S`
  compactly supported, by the cyclicity of the trace. For `k = 1` this is the varifold of a line.

## Main results

* `Euclidean.firstVariation_map_prodMk_const`: a Haar measure with a constant plane field is
  stationary.
* `Euclidean.firstVariation_map_affinePlane`: an affine plane with multiplicity one is stationary.

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

omit [MeasurableSpace E] [BorelSpace E] in
/-- The tangential divergence along `P` is a continuous linear functional of the derivative. -/
private theorem tangentialDivergence_eq_traceCLM_comp (X : E → E) (x : E) (P : E →L[ℝ] E) :
    tangentialDivergence X x P =
      ((TauCeti.traceCLM ℝ E).comp (ContinuousLinearMap.compL ℝ E E E P)) (fderiv ℝ X x) := by
  simp [tangentialDivergence_def, TauCeti.traceCLM_apply]

/-- **A Haar measure with a constant plane field is stationary.** For an additive Haar measure `μ`,
an open set `W` and a plane `P ∈ G(E, k)`, the varifold `μ⌞W ⊗ δ_P` has first variation zero. -/
theorem firstVariation_map_prodMk_const (μ : Measure E) [μ.IsAddHaarMeasure] (W : Opens E)
    (P : grassmannian ℝ E k) :
    firstVariation ((μ.comap ((↑) : W → E)).map fun x => (x, P)) = 0 := by
  have hf : Continuous fun x : W => ((x, P) : W × grassmannian ℝ E k) :=
    continuous_id.prodMk continuous_const
  have : IsFiniteMeasureOnCompacts ((μ.comap ((↑) : W → E)).map fun x => (x, P)) :=
    ⟨fun K hK => by
      have hK' : IsCompact (Prod.fst '' K) := hK.image continuous_fst
      rw [Measure.map_apply hf.measurable hK.isClosed.measurableSet]
      refine (measure_mono (show (fun x => (x, P)) ⁻¹' K ⊆ Prod.fst '' K from
        fun x hx => ⟨(x, P), hx, rfl⟩)).trans_lt ?_
      exact (Measure.comap_apply _ Subtype.val_injective
        (fun _ hs => W.isOpen.measurableSet.subtype_image hs) μ hK'.isClosed.measurableSet).trans_lt
        (hK'.image continuous_subtypeVal).measure_lt_top⟩
  ext X
  change _ = (0 : ℝ)
  rw [firstVariation_apply,
    integral_map hf.aemeasurable (by
      simpa using (tangentialDivergenceCc (k := k) X).continuous.aestronglyMeasurable)]
  refine (integral_subtype_comap W.isOpen.measurableSet
    (fun x => tangentialDivergence X x P)).trans ?_
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      tangentialDivergence_eq_zero_of_notMem_tsupport (fun h => hx (X.tsupport_subset h)) _]
  simp_rw [tangentialDivergence_eq_traceCLM_comp]
  rw [ContinuousLinearMap.integral_comp_comm _ ((X.contDiff.continuous_fderiv one_ne_zero)
    |>.integrable_of_hasCompactSupport (X.hasCompactSupport.fderiv (𝕜 := ℝ))),
    TauCeti.integral_fderiv_eq_zero_of_hasCompactSupport X.contDiff X.hasCompactSupport, map_zero]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The tangential divergence along the orthogonal projection onto `S` is the trace on `S` of the
derivative of `g = P_S ∘ X ∘ (a + ·)`. -/
private theorem tangentialDivergence_starProjection_eq (S : Submodule ℝ E) {X : E → E}
    (hX : Differentiable ℝ X) (a : E) (s : S) :
    tangentialDivergence X (a + s) S.starProjection = TauCeti.traceCLM ℝ S
      (fderiv ℝ (fun s : S => S.orthogonalProjectionOnto (X (a + s))) s) := by
  have hd : HasFDerivAt (fun s : S => S.orthogonalProjectionOnto (X (a + s)))
      (S.orthogonalProjectionOnto ∘L fderiv ℝ X (a + s) ∘L S.subtypeL) s :=
    S.orthogonalProjectionOnto.hasFDerivAt.comp s
      ((hX (a + s)).hasFDerivAt.comp s (S.subtypeL.hasFDerivAt.const_add a))
  rw [hd.fderiv, tangentialDivergence_def, TauCeti.traceCLM_apply, Submodule.starProjection]
  exact LinearMap.trace_comp_comm' (S.orthogonalProjectionOnto ∘L fderiv ℝ X (a + s) :
    E →ₗ[ℝ] S) (S.subtypeL : S →ₗ[ℝ] E)

/-- **An affine plane is stationary.** For a `k`-dimensional subspace `S` and `a ∈ E`, the
varifold of the affine plane `a + S` with multiplicity one, the image of the volume of `S` under
`s ↦ (a + s, P_S)`, has first variation zero. -/
theorem firstVariation_map_affinePlane (S : Submodule ℝ E) (hS : finrank ℝ S = k) (a : E) :
    firstVariation ((volume : Measure S).map fun s : S =>
      (((⟨a + s, by simp⟩ : (⊤ : Opens E))),
        (⟨S.starProjection, grassmannian.starProjection_mem hS⟩ : grassmannian ℝ E k))) = 0 := by
  set P : grassmannian ℝ E k := ⟨S.starProjection, grassmannian.starProjection_mem hS⟩
  set f : S → (⊤ : Opens E) × grassmannian ℝ E k := fun s => (⟨a + s, by simp⟩, P)
  -- `s ↦ a + s` is a closed embedding of `S` into `E`.
  have hg : Topology.IsClosedEmbedding fun s : S => a + (s : E) :=
    (Homeomorph.addLeft a).isClosedEmbedding.comp
      S.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal
  have hf : Continuous f :=
    ((hg.continuous.subtype_mk fun _ => by simp).prodMk continuous_const)
  have : IsFiniteMeasureOnCompacts ((volume : Measure S).map f) :=
    ⟨fun K hK => by
      rw [Measure.map_apply hf.measurable hK.isClosed.measurableSet]
      refine (measure_mono fun s hs => ?_).trans_lt
        (hg.isCompact_preimage ((hK.image continuous_fst).image continuous_subtypeVal)
          |>.measure_lt_top)
      exact ⟨_, ⟨_, hs, rfl⟩, rfl⟩⟩
  ext X
  change _ = (0 : ℝ)
  rw [firstVariation_apply,
    integral_map hf.aemeasurable (by
      simpa using (tangentialDivergenceCc (k := k) X).continuous.aestronglyMeasurable)]
  have hX : Differentiable ℝ (X : E → E) := X.contDiff.differentiable one_ne_zero
  change ∫ s : S, tangentialDivergence X (a + s) S.starProjection = 0
  simp_rw [tangentialDivergence_starProjection_eq S hX a]
  -- `g = P_S ∘ X ∘ (a + ·)` is a compactly supported `C¹` map of `S`.
  have hgd : ContDiff ℝ 1 fun s : S => S.orthogonalProjectionOnto (X (a + s)) :=
    S.orthogonalProjectionOnto.contDiff.comp
      (X.contDiff.comp (contDiff_const.add S.subtypeL.contDiff))
  have hgc : HasCompactSupport fun s : S => S.orthogonalProjectionOnto (X (a + s)) :=
    (X.hasCompactSupport.comp_isClosedEmbedding hg).comp_left (map_zero _)
  rw [ContinuousLinearMap.integral_comp_comm _ ((hgd.continuous_fderiv one_ne_zero)
    |>.integrable_of_hasCompactSupport (hgc.fderiv (𝕜 := ℝ))),
    TauCeti.integral_fderiv_eq_zero_of_hasCompactSupport hgd hgc, map_zero]

end Euclidean
