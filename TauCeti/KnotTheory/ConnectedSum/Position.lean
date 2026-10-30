/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.SphereBoost
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Straightening
public import TauCeti.KnotTheory.ConnectedSum.Basic

/-!
# Boosting a knot into connected-sum position

The connected sum `TauCeti.SmoothCircleEmbedding.connectedSum` is defined for knots in
connected-sum position for a great circle `ι`
(`TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition`): standard on the closed lower half of the
circle, and knotted only in the open upper hemisphere `⟪x, ι i⟫ > 0`. This file shows that a knot
which is standard merely near the bottom point `-i` of the circle is concordant to a knot in
connected-sum position.

The tool is the conformal boost of the sphere toward `v = ι i` (`TauCeti.sphereBoost`). It
preserves the great circle `ι`, acting on it by the boost of the circle toward `i`, and for a
large rapidity `a` it pushes everything outside a small cap around `-v` into the upper hemisphere,
while blowing that cap up to cover the lower hemisphere. The **boosted knot**
`TauCeti.SmoothCircleEmbedding.boost ι a K` boosts `K` in the ambient sphere and undoes the boost
on the parameter circle, so that a stretch of `K` along the great circle keeps its standard
parametrization:

`boost ι a K w = sphereBoost (ι i) a (K (sphereBoost i (-a) w))`.

It is concordant to `K`, through the traces of the ambient and the source boost diffeotopies
(`TauCeti.SmoothCircleEmbedding.concordant_boost`). If `K` agrees with the great circle on a
neighbourhood `U` of `-i`, then the complement of `U` is a compact set of parameters whose image
avoids `-v`, so it has height at least `-1 + ε` for some `ε > 0`; boosting by a rapidity `a` with
`tanh a > 1 - ε` puts the boosted knot in connected-sum position
(`TauCeti.SmoothCircleEmbedding.exists_isConnectedSumPosition_boost`).

A knot which merely passes through the bottom point `ι (-i)` of the great circle at the parameter
`-i`, with the same derivative there as the great circle, is first straightened near `-i`
(`TauCeti.SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq`), so it too is
concordant to a knot in connected-sum position
(`TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition_of_mfderiv_eq`).

Not formalized here: that every knot is concordant, or ambient isotopic, to one which passes through
`ι (-i)` at `-i` with the derivative of the great circle there.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.boost ι a K`: the knot `K` boosted by rapidity `a` toward `ι i`,
  with the boost undone on the parameter circle.

## Main results

* `TauCeti.SmoothCircleEmbedding.concordant_boost`: a boosted knot is concordant to the knot.
* `TauCeti.SmoothCircleEmbedding.boost_greatCircle`: boosting preserves the great circle.
* `TauCeti.SmoothCircleEmbedding.exists_isConnectedSumPosition_boost`,
  `TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition`: a knot standard near
  the bottom point of the circle is concordant to a knot in connected-sum position.
* `TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition_of_mfderiv_eq`: so is a
  knot tangent to the great circle at the bottom point.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group, whose operation is the connected sum).
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, Graduate Texts in Mathematics 149,
  3rd ed., Springer (2019), Section 4.5 (Möbius transformations of the sphere).
-/

public section

noncomputable section

open Metric Module Set Filter Topology Real
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

namespace SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

/-- The image `ι i` of the point `i` under a linear isometry is a unit vector. -/
private theorem norm_map_I (ι : ℂ →ₗᵢ[ℝ] E) : ‖ι Complex.I‖ = 1 := by simp

/-- The **boosted knot**: `K` moved by the boost of rapidity `a` toward `ι i` in the ambient
sphere, and reparametrized by the boost of rapidity `-a` toward `i` of the circle, which undoes
the ambient boost along the great circle `ι`. -/
def boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  (K.transDiffeomorph (sphereBoostDiffeotopy (norm_map_I ι) a).final).compDiffeomorph
    (circleBoostDiffeotopy (-a)).final

/-- The boosted knot boosts `K` after undoing the boost on the parameter circle. -/
theorem coe_boost_apply (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (w : Circle) :
    (boost ι a K w : E) =
      sphereBoost (ι Complex.I) a (K ((circleBoostDiffeotopy (m := ∞) (-a)).final w)) := by
  rw [boost, SmoothEmbedding.compDiffeomorph_apply, SmoothEmbedding.transDiffeomorph_apply,
    coe_sphereBoostDiffeotopy_final_apply]

/-- **A boosted knot is concordant to the knot**, through the traces of the boost diffeotopies of
the sphere and of the circle. -/
theorem concordant_boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothEmbedding.Concordant K (boost ι a K) :=
  (SmoothEmbedding.Concordant.of_concordance
    (SmoothEmbedding.Concordance.ofDiffeotopy le_rfl _ K)).trans
      (SmoothEmbedding.Concordant.of_concordance
        (SmoothEmbedding.Concordance.ofSourceDiffeotopy le_rfl _ _))

/-- Where the parameter, boosted back, lands on a stretch of `K` along the great circle, the
boosted knot is the great circle. -/
private theorem boost_apply_eq_greatCircle (a : ℝ)
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {w : Circle}
    (hw : K ((circleBoostDiffeotopy (m := ∞) (-a)).final w) =
      greatCircle (n := n) ι ((circleBoostDiffeotopy (m := ∞) (-a)).final w)) :
    boost (n := n) ι a K w = greatCircle (n := n) ι w := by
  ext
  rw [coe_boost_apply, hw, coe_greatCircle_apply, LinearIsometry.sphereBoost_map,
    coe_circleBoostDiffeotopy_final_apply, sphereBoost_sphereBoost (by simp) (Circle.norm_coe w),
    add_neg_cancel, sphereBoost_zero, id, coe_greatCircle_apply]

/-- **Boosting preserves the great circle.** -/
@[simp]
theorem boost_greatCircle (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) :
    boost ι a (greatCircle (n := n) ι) = greatCircle ι :=
  SmoothEmbedding.ext fun _ => boost_apply_eq_greatCircle a rfl

/-- **Boosting into connected-sum position.** A knot that agrees with the great circle `ι` near
the bottom point `-i` of the circle is in connected-sum position for `ι` once boosted far enough
toward `ι i`. -/
theorem exists_isConnectedSumPosition_boost
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I) (hK : ⇑K =ᶠ[𝓝 z₀] ⇑(greatCircle (n := n) ι)) :
    ∃ a : ℝ, IsConnectedSumPosition ι (boost ι a K) := by
  obtain ⟨U, hU, hUo, hz₀U⟩ := _root_.eventually_nhds_iff.1 hK
  have hC : IsCompact Uᶜ := hUo.isClosed_compl.isCompact
  -- Off `U`, the knot avoids `-ι i = K z₀`, and the parameter avoids `-i = z₀`; so a large boost
  -- carries both into the open upper hemispheres.
  have hKc : Continuous fun z => (K z : E) := continuous_subtype_val.comp K.contMDiff.continuous
  have h₁ := (hC.image hKc).eventually_forall_inner_sphereBoost_pos (norm_map_I ι)
    (by rintro _ ⟨z, -, rfl⟩; exact norm_eq_of_mem_sphere (K z)) fun ⟨z, hz, hKz⟩ => hz <| by
      have hKz' : (K z : E) = -ι Complex.I := hKz
      have : K z = K z₀ := Subtype.ext <| by
        rw [hKz', hU z₀ hz₀U, coe_greatCircle_apply, hz₀, map_neg]
      exact K.isEmbedding.injective this ▸ hz₀U
  have hzc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
  have h₂ := (hC.image hzc).eventually_forall_inner_sphereBoost_pos (v := Complex.I) (by simp)
    (by rintro _ ⟨z, -, rfl⟩; exact Circle.norm_coe z) fun ⟨z, hz, hz'⟩ => by
      have hzz₀ : z = z₀ := Subtype.ext (hz'.trans hz₀.symm)
      exact hz (hzz₀ ▸ hz₀U)
  obtain ⟨a, ha₁, ha₂⟩ := (h₁.and h₂).exists
  set m := (circleBoostDiffeotopy (m := ∞) (-a)).final
  -- Boosting back a parameter `w` with `m w ∉ U` lands in the open upper half of the circle.
  have him (w : Circle) (hw : m w ∉ U) : 0 < (w : ℂ).im := by
    have hw' : (w : ℂ) = sphereBoost Complex.I a (m w) := by
      rw [coe_circleBoostDiffeotopy_final_apply,
        sphereBoost_sphereBoost (by simp) (Circle.norm_coe w), add_neg_cancel, sphereBoost_zero,
        id]
    have hpos := ha₂ _ ⟨m w, hw, rfl⟩
    rw [← hw'] at hpos
    simpa [Complex.inner] using hpos
  refine ⟨a, ⟨fun {w} hw => ?_, fun {w} hw => ?_⟩⟩
  · -- Near a parameter in the closed lower half, the boosted-back parameters stay in `U`.
    have hmU : m ⁻¹' U ∈ 𝓝 w :=
      (hUo.preimage m.continuous).mem_nhds (not_not.1 fun h => (not_le.2 (him w h)) hw)
    filter_upwards [hmU] with w' hw'
    exact boost_apply_eq_greatCircle a (hU _ hw')
  · by_cases hmw : m w ∈ U
    · rw [boost_apply_eq_greatCircle a (hU _ hmw), coe_greatCircle_apply, ι.inner_map_map]
      simpa [Complex.inner] using hw
    · rw [coe_boost_apply]
      exact ha₁ _ ⟨m w, hmw, rfl⟩

/-- **A knot standard near a point is concordant to a knot in connected-sum position.** A knot that
agrees with the great circle `ι` near the bottom point `-i` of the circle is concordant to a knot
in connected-sum position for `ι`. -/
theorem exists_concordant_isConnectedSumPosition
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I) (hK : ⇑K =ᶠ[𝓝 z₀] ⇑(greatCircle (n := n) ι)) :
    ∃ K', SmoothEmbedding.Concordant K K' ∧ IsConnectedSumPosition ι K' :=
  (exists_isConnectedSumPosition_boost hz₀ hK).elim fun a ha => ⟨_, concordant_boost ι a K, ha⟩

/-- **A knot tangent to the great circle at the bottom point is concordant to a knot in
connected-sum position.** A knot which agrees with the great circle `ι` to first order at the
bottom point `-i` of the circle, having the same value and the same derivative there, is
concordant to a knot in connected-sum position for `ι`. -/
theorem exists_concordant_isConnectedSumPosition_of_mfderiv_eq
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I) (h₀ : K z₀ = greatCircle (n := n) ι z₀)
    (h₁ : mfderiv (𝓡 1) (𝓡 n) K z₀ = mfderiv (𝓡 1) (𝓡 n) (greatCircle (n := n) ι) z₀) :
    ∃ K', SmoothEmbedding.Concordant K K' ∧ IsConnectedSumPosition ι K' := by
  obtain ⟨K₁, F, hK₁, -⟩ :=
    SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq K
      (greatCircle (n := n) ι).contMDiff h₀ h₁ univ_mem
  obtain ⟨K', hK', hpos⟩ := exists_concordant_isConnectedSumPosition hz₀ hK₁
  exact ⟨K', (SmoothEmbedding.Concordant.of_smoothIsotopic (smoothIsotopic_def.2 ⟨F⟩) (by simp)
    le_rfl).trans hK', hpos⟩

end SmoothCircleEmbedding

end TauCeti
