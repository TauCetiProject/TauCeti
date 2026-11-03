/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Position
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Extension

/-!
# Ambient-isotopic representatives in connected-sum position

Every smooth circle embedding in a sphere of dimension at least two is smoothly ambient
isotopic to one in connected-sum position for any prescribed great circle. Thus the positioning
required to form a connected sum does not change the oriented knot's ambient-isotopy class,
not merely its concordance class. Independence of the connected sum from the choice of such
representatives is a separate question.

The positioning uses the first-order alignment and local straightening of a circle embedding,
followed by the sphere boost from `ConnectedSum.Position`. The boost and its compensating
reparametrization of the circle give a jointly smooth isotopy through embeddings. Isotopy
extension then realizes the entire positioning by an ambient diffeotopy.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (connected sum of oriented knots).
* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1, Theorem 1.3
  (isotopy extension).
-/

public section

noncomputable section

open Metric Module Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

/-- Boosting the sphere while undoing the boost on the parameter circle gives a smooth isotopy
of parametrized knots. -/
theorem smoothIsotopic_boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothIsotopic K.toContMDiffMap (boost ι a K).toContMDiffMap := by
  let Φ := sphereBoostDiffeotopy (n := n) (m := ∞) ι.norm_map_I a
  let Ψ := circleBoostDiffeotopy (m := ∞) (-a)
  refine smoothIsotopic_def.2 ⟨{
    toContMDiffMap := ⟨fun p => Φ (p.1, K (Ψ p)),
      Φ.contMDiff.comp (contMDiff_fst.prodMk (K.contMDiff.comp Ψ.contMDiff))⟩
    map_zero_left := ?_
    map_one_left := ?_
    isSmoothEmbedding := ?_ }⟩
  · intro z
    simp only [ContMDiffMap.coeFn_mk, Ψ.apply_zero, Φ.apply_zero,
      SmoothEmbedding.coe_toContMDiffMap]
  · intro z
    apply Subtype.ext
    simp only [ContMDiffMap.coeFn_mk, SmoothEmbedding.coe_toContMDiffMap, coe_boost_apply,
      Φ, coe_sphereBoostDiffeotopy_apply, Icc.coe_one, mul_one, Diffeotopy.final_apply, Ψ]
  · intro t
    have h := ((K.transDiffeomorph (Φ.timeSlice t)).compDiffeomorph
      (Ψ.timeSlice t)).isSmoothEmbedding
    simpa only [SmoothEmbedding.coe_compDiffeomorph, SmoothEmbedding.coe_transDiffeomorph,
      Diffeotopy.timeSlice_apply, Function.comp_def, ContMDiffMap.coeFn_mk] using h

/-- A boost, including its compensating circle reparametrization, preserves the smooth
ambient-isotopy class of a parametrized knot. -/
theorem smoothAmbientIsotopic_boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothAmbientIsotopic K.toContMDiffMap (boost ι a K).toContMDiffMap := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  exact (smoothIsotopic_boost ι a K).smoothAmbientIsotopic

/-- A knot which is standard near the bottom point of a great circle has an ambient-isotopic
representative in connected-sum position for that great circle. -/
theorem exists_smoothAmbientIsotopic_isConnectedSumPosition
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I) (hK : ⇑K =ᶠ[𝓝 z₀] ⇑(greatCircle (n := n) ι)) :
    ∃ K', SmoothAmbientIsotopic K.toContMDiffMap K'.toContMDiffMap ∧
      IsConnectedSumPosition ι K' := by
  obtain ⟨a, ha⟩ := exists_isConnectedSumPosition_boost hz₀ hK
  exact ⟨boost ι a K, smoothAmbientIsotopic_boost ι a K, ha⟩

/-- First-order agreement with a great circle at its bottom point suffices to put a knot in
connected-sum position by a smooth ambient isotopy. -/
theorem exists_smoothAmbientIsotopic_isConnectedSumPosition_of_mfderiv_eq
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I) (h₀ : K z₀ = greatCircle (n := n) ι z₀)
    (h₁ : mfderiv (𝓡 1) (𝓡 n) K z₀ = mfderiv (𝓡 1) (𝓡 n) (greatCircle (n := n) ι) z₀) :
    ∃ K', SmoothAmbientIsotopic K.toContMDiffMap K'.toContMDiffMap ∧
      IsConnectedSumPosition ι K' := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨K₁, F, hK₁, -⟩ :=
    SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq K
      (greatCircle (n := n) ι).contMDiff h₀ h₁ univ_mem
  obtain ⟨K', hK', hpos⟩ := exists_smoothAmbientIsotopic_isConnectedSumPosition hz₀ hK₁
  exact ⟨K', (smoothIsotopic_def.2 ⟨F⟩).smoothAmbientIsotopic.trans hK', hpos⟩

/-- Every smooth knot in a sphere of dimension at least two has a smoothly ambient-isotopic
representative in connected-sum position for any prescribed great circle. The parameter circle
is preserved, so this is a statement about oriented, parametrized knots. -/
theorem exists_smoothAmbientIsotopic_isConnectedSumPosition_of_two_le (hn : 2 ≤ n)
    (ι : ℂ →ₗᵢ[ℝ] E) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    ∃ K', SmoothAmbientIsotopic K.toContMDiffMap K'.toContMDiffMap ∧
      IsConnectedSumPosition ι K' := by
  -- Choose the bottom point directly as a point of the unit circle.
  let z₀ : Circle := ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩
  have hz₀ : (z₀ : ℂ) = -Complex.I := rfl
  obtain ⟨K₁, hK₁, h₀, h₁⟩ := SmoothEmbedding.exists_smoothAmbientIsotopic_mfderiv_eq hn
    (by simp) K ((greatCircle (n := n) ι).contMDiff.mdifferentiableAt (by simp))
    ((greatCircle (n := n) ι).isImmersion.mfderiv_injective (by simp) z₀)
  obtain ⟨K', hK', hpos⟩ :=
    exists_smoothAmbientIsotopic_isConnectedSumPosition_of_mfderiv_eq hz₀ h₀ h₁
  exact ⟨K', (SmoothEmbedding.smoothAmbientIsotopic_iff_toContMDiffMap.mp hK₁).trans hK',
    hpos⟩

end TauCeti.SmoothCircleEmbedding
