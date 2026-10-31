/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Inner
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.SphereBoost
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Straightening
public import TauCeti.KnotTheory.ConnectedSum.Concordance
import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Sphere

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

It is concordant to `K`, through the joint trace of the ambient and the source boost diffeotopies
(`TauCeti.SmoothCircleEmbedding.boostConcordance`,
`TauCeti.SmoothCircleEmbedding.concordant_boost`).

The same boost applies to a concordance `F` (`TauCeti.SmoothEmbedding.Concordance.boost ι a F`).
If `F` is the standard strip `(z, t) ↦ (ι z, t)` on `U × ℝ` for a neighbourhood `U` of `-i`, then
off `U × ℝ` it avoids the line `{-v} × ℝ`. Being a product beyond the times `0` and `1`, its sphere
component there ranges over the image of the compact set `Uᶜ × [0, 1]`, which has height at least
`-1 + ε` for some `ε > 0`; boosting by a rapidity `a` with `tanh a > 1 - ε` puts the boosted
concordance in connected-sum position
(`TauCeti.SmoothEmbedding.Concordance.eventually_isConnectedSumPosition_boost`). Applied to the
constant concordance of a knot `K` which agrees with the great circle near `-i`, this puts the
boosted knot in connected-sum position
(`TauCeti.SmoothCircleEmbedding.exists_isConnectedSumPosition_boost`).

A knot which merely passes through the bottom point `ι (-i)` of the great circle at the parameter
`-i`, with the same derivative there as the great circle, is first straightened near `-i`
(`TauCeti.SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq`), so it too is
concordant to a knot in connected-sum position
(`TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition_of_mfderiv_eq`).

In a sphere of dimension at least two every knot can be brought into that first-order position by
an ambient isotopy, a rotation followed by a boost
(`TauCeti.SmoothEmbedding.exists_smoothAmbientIsotopic_mfderiv_eq`). So **every knot is concordant
to a knot in connected-sum position**
(`TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition_of_two_le`), and every
concordance class of knots has a representative to which the connected sum applies. On the circle,
`n = 1`, a rotation cannot reverse the direction of a tangent vector, and the argument fails.

Not formalized here: that the resulting operation on concordance classes does not depend on the
chosen representatives.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.boost ι a K`: the knot `K` boosted by rapidity `a` toward `ι i`,
  with the boost undone on the parameter circle.
* `TauCeti.SmoothCircleEmbedding.boostConcordance ι a K`: the concordance from `K` to its boost,
  boosting the sphere and the circle simultaneously.
* `TauCeti.SmoothEmbedding.Concordance.boost ι a F`: a concordance boosted by rapidity `a` toward
  `ι i`, with the boost undone on the parameter circle.

## Main results

* `TauCeti.SmoothCircleEmbedding.concordant_boost`: a boosted knot is concordant to the knot.
* `TauCeti.SmoothCircleEmbedding.sphereBoostDiffeotopy_greatCircle_circleBoostDiffeotopy`,
  `TauCeti.SmoothCircleEmbedding.boost_greatCircle`: along the great circle the boosts of the
  sphere and of the circle cancel, so boosting preserves the great circle.
* `TauCeti.SmoothEmbedding.Concordance.eventually_isConnectedSumPosition_boost`: a concordance
  which is the standard strip near the arc `{-i} × ℝ` is in connected-sum position once boosted far
  enough.
* `TauCeti.SmoothCircleEmbedding.exists_isConnectedSumPosition_boost`,
  `TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition`: a knot standard near
  the bottom point of the circle is concordant to a knot in connected-sum position.
* `TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition_of_mfderiv_eq`: so is a
  knot tangent to the great circle at the bottom point.
* `TauCeti.SmoothCircleEmbedding.exists_concordant_isConnectedSumPosition_of_two_le`: in a sphere of
  dimension at least two, every knot is concordant to a knot in connected-sum position.

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

/-- The **boosted knot**: `K` moved by the boost of rapidity `a` toward `ι i` in the ambient
sphere, and reparametrized by the boost of rapidity `-a` toward `i` of the circle, which undoes
the ambient boost along the great circle `ι`. -/
def boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  (K.transDiffeomorph (sphereBoostDiffeotopy ι.norm_map_I a).final).compDiffeomorph
    (circleBoostDiffeotopy (-a)).final

/-- The boosted knot boosts `K` after undoing the boost on the parameter circle. -/
theorem coe_boost_apply (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (w : Circle) :
    (boost ι a K w : E) =
      sphereBoost (ι Complex.I) a (K ((circleBoostDiffeotopy (m := ∞) (-a)).final w)) := by
  rw [boost, SmoothEmbedding.compDiffeomorph_apply, SmoothEmbedding.transDiffeomorph_apply,
    coe_sphereBoostDiffeotopy_final_apply]

/-- The **boost concordance** from `K` to the boosted knot
`TauCeti.SmoothCircleEmbedding.boost ι a K`: the joint trace of the boost diffeotopies of the
sphere and of the circle. At time `t` it is `K` boosted toward `ι i` by rapidity `a s` in the
sphere and reparametrized by the boost toward `i` of rapidity `-a s` of the circle, where
`s = Real.smoothTransition (2 * t - 1 / 2)` runs from `0` to `1`. -/
def boostConcordance (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothEmbedding.Concordance K (boost ι a K) :=
  SmoothEmbedding.Concordance.ofDiffeotopies le_rfl _ _ K

/-- The boost concordance at `(w, t)`: the boosts of the sphere and of the circle at the time
`SmoothEmbedding.Concordance.collaredSmoothTransitionUnit t`, applied around `K`. -/
@[simp]
theorem boostConcordance_apply (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (p : Circle × ℝ) :
    boostConcordance ι a K p =
      (sphereBoostDiffeotopy (n := n) (m := ∞) ι.norm_map_I a
        (SmoothEmbedding.Concordance.collaredSmoothTransitionUnit p.2,
          K (circleBoostDiffeotopy (m := ∞) (-a)
            (SmoothEmbedding.Concordance.collaredSmoothTransitionUnit p.2, p.1))), p.2) :=
  SmoothEmbedding.Concordance.ofDiffeotopies_apply le_rfl _ _ K p

/-- **A boosted knot is concordant to the knot**, through the boost concordance. -/
theorem concordant_boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothEmbedding.Concordant K (boost ι a K) :=
  SmoothEmbedding.Concordant.of_concordance (boostConcordance ι a K)

/-- Along the great circle `ι`, the boost diffeotopy of the sphere toward `ι i` of rapidity `a`
undoes, at every time `s`, the boost diffeotopy of the circle toward `i` of rapidity `-a`. -/
@[simp]
theorem sphereBoostDiffeotopy_greatCircle_circleBoostDiffeotopy (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ)
    (s : unitInterval) (w : Circle) :
    sphereBoostDiffeotopy (n := n) (m := ∞) ι.norm_map_I a
        (s, greatCircle (n := n) ι (circleBoostDiffeotopy (m := ∞) (-a) (s, w))) =
      greatCircle (n := n) ι w := by
  ext
  rw [coe_sphereBoostDiffeotopy_apply, coe_greatCircle_apply, LinearIsometry.sphereBoost_map,
    sphereBoost_circleBoostDiffeotopy_neg, coe_greatCircle_apply]

/-- Where the parameter, boosted back, lands on a stretch of `K` along the great circle, the
boosted knot is the great circle. -/
private theorem boost_apply_eq_greatCircle (a : ℝ)
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {w : Circle}
    (hw : K ((circleBoostDiffeotopy (m := ∞) (-a)).final w) =
      greatCircle (n := n) ι ((circleBoostDiffeotopy (m := ∞) (-a)).final w)) :
    boost (n := n) ι a K w = greatCircle (n := n) ι w := by
  rw [boost, SmoothEmbedding.compDiffeomorph_apply, SmoothEmbedding.transDiffeomorph_apply, hw,
    Diffeotopy.final_apply, Diffeotopy.final_apply,
    sphereBoostDiffeotopy_greatCircle_circleBoostDiffeotopy]

/-- **Boosting preserves the great circle.** -/
@[simp]
theorem boost_greatCircle (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) :
    boost ι a (greatCircle (n := n) ι) = greatCircle ι :=
  SmoothEmbedding.ext fun _ => boost_apply_eq_greatCircle a rfl

end SmoothCircleEmbedding

namespace SmoothEmbedding.Concordance

open SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}
  {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The **boosted concordance**: a concordance `F` from `K` to `K'` moved by the boost of rapidity
`a` toward `ι i` in the sphere factor, and reparametrized by the boost of rapidity `-a` toward `i`
of the circle. It is a concordance between the boosted knots
`TauCeti.SmoothCircleEmbedding.boost ι a K` and `boost ι a K'`. -/
def boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) (F : Concordance K K') :
    Concordance (K.boost ι a) (K'.boost ι a) :=
  (F.transDiffeomorph (sphereBoostDiffeotopy ι.norm_map_I a).final).compDiffeomorph
    (circleBoostDiffeotopy (-a)).final

/-- The boosted concordance boosts `F` after undoing the boost on the parameter circle. -/
@[simp]
theorem boost_apply (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) (F : Concordance K K') (p : Circle × ℝ) :
    F.boost ι a p =
      ((sphereBoostDiffeotopy (n := n) (m := ∞) ι.norm_map_I a).final
          (F ((circleBoostDiffeotopy (m := ∞) (-a)).final p.1, p.2)).1,
        (F ((circleBoostDiffeotopy (m := ∞) (-a)).final p.1, p.2)).2) :=
  (compDiffeomorph_apply _ _ p).trans (transDiffeomorph_apply _ _ _)

/-- **Boosting a concordance into connected-sum position.** A concordance which is the standard
strip `(z, t) ↦ (ι z, t)` for all times `t` and all parameters `z` near the bottom point `-i` of
the circle is in connected-sum position for `ι` once boosted far enough toward `ι i`. -/
theorem eventually_isConnectedSumPosition_boost {F : Concordance K K'} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I)
    (hF : ∀ᶠ z in 𝓝 z₀, ∀ t, F (z, t) = (greatCircle (n := n) ι z, t)) :
    ∀ᶠ a in atTop, (F.boost ι a).IsConnectedSumPosition ι := by
  obtain ⟨U, hU, hUo, hz₀U⟩ := _root_.eventually_nhds_iff.1 hF
  -- Off `U × ℝ`, the sphere component of `F` ranges over the image `C` of the compact set
  -- `Uᶜ × [0, 1]`, since `F` is a product beyond the times `0` and `1`.
  set C := (fun p => ((F p).1 : E)) '' (Uᶜ ×ˢ Icc 0 1)
  have hC : IsCompact C := (hUo.isClosed_compl.isCompact.prod isCompact_Icc).image
    (continuous_subtype_val.comp (continuous_fst.comp F.toSmoothEmbedding.contMDiff.continuous))
  have hmemC {z : Circle} (hz : z ∉ U) (t : ℝ) : ((F (z, t)).1 : E) ∈ C := by
    rcases le_or_gt t 0 with ht | ht
    · exact ⟨(z, 0), ⟨hz, le_rfl, zero_le_one⟩, by
        simp [F.isCollaredTrack.apply_of_nonpos z ht, F.apply_zero]⟩
    rcases le_or_gt 1 t with ht' | ht'
    · exact ⟨(z, 1), ⟨hz, zero_le_one, le_rfl⟩, by
        simp [F.isCollaredTrack.apply_of_one_le z ht', F.apply_one]⟩
    · exact ⟨(z, t), ⟨hz, ht.le, ht'.le⟩, rfl⟩
  -- `C` avoids `-ι i`: over `z₀` the concordance is the line `{-ι i} × ℝ`, and `F` is injective.
  have hCv : -ι Complex.I ∉ C := by
    rintro ⟨⟨z, t⟩, ⟨hz, -⟩, hzt⟩
    have heq : F (z₀, (F (z, t)).2) = F (z, t) := by
      rw [hU z₀ hz₀U]
      refine Prod.ext (Subtype.ext ?_) rfl
      rw [coe_greatCircle_apply, hz₀, map_neg]
      exact hzt.symm
    exact hz (congrArg Prod.fst (F.toSmoothEmbedding.isEmbedding.injective heq) ▸ hz₀U)
  have h₁ := hC.eventually_forall_inner_sphereBoost_pos ι.norm_map_I
    (by rintro _ ⟨p, -, rfl⟩; exact norm_eq_of_mem_sphere (F p).1) hCv
  -- Boosting back a parameter `w` with `m w ∉ U` lands in the open upper half of the circle.
  filter_upwards [h₁, eventually_forall_im_pos_of_circleBoostDiffeotopy_final_notMem (m := ∞)
    (hUo.mem_nhds hz₀U) hz₀] with a ha₁ him
  set m := (circleBoostDiffeotopy (m := ∞) (-a)).final
  -- Where the boosted-back parameter lies in `U`, the boosted concordance is the standard strip.
  have hstrip (q : Circle × ℝ) (hq : m q.1 ∈ U) :
      F.boost ι a q = (greatCircle (n := n) ι q.1, q.2) := by
    rw [boost_apply, hU _ hq, Diffeotopy.final_apply, Diffeotopy.final_apply,
      sphereBoostDiffeotopy_greatCircle_circleBoostDiffeotopy]
  refine isConnectedSumPosition_of_mem_imp_eq (g := fun q => m q.1)
    (m.continuous.comp continuous_fst) hUo hstrip
    (fun q hq => not_not.1 fun h => (not_le.2 (him q.1 h)) hq) fun p _ hmp => ?_
  rw [boost_apply, coe_sphereBoostDiffeotopy_final_apply]
  exact ha₁ _ (hmemC hmp p.2)

end SmoothEmbedding.Concordance

namespace SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

/-- **Boosting into connected-sum position.** A knot that agrees with the great circle `ι` near
the bottom point `-i` of the circle is in connected-sum position for `ι` once boosted far enough
toward `ι i`. -/
theorem exists_isConnectedSumPosition_boost
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I) (hK : ⇑K =ᶠ[𝓝 z₀] ⇑(greatCircle (n := n) ι)) :
    ∃ a : ℝ, IsConnectedSumPosition ι (boost ι a K) :=
  (SmoothEmbedding.Concordance.eventually_isConnectedSumPosition_boost
    (F := SmoothEmbedding.Concordance.refl K) hz₀
    (hK.mono fun z hz t => by rw [SmoothEmbedding.Concordance.refl_apply, hz])).exists.elim
    fun a ha => ⟨a, ha.initial⟩

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

/-- **Every knot is concordant to a knot in connected-sum position.** In a sphere of dimension at
least two, a knot is first moved by an ambient isotopy to agree with the great circle `ι` to first
order at the bottom point `-i` (`TauCeti.SmoothEmbedding.exists_smoothAmbientIsotopic_mfderiv_eq`),
and then straightened and boosted into connected-sum position. -/
theorem exists_concordant_isConnectedSumPosition_of_two_le (hn : 2 ≤ n) (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    ∃ K', SmoothEmbedding.Concordant K K' ∧ IsConnectedSumPosition ι K' := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Circle, (z₀ : ℂ) = -Complex.I :=
    ⟨Circle.exp (-π / 2), by push_cast [Circle.coe_exp]; exact Complex.exp_neg_pi_div_two_mul_I⟩
  obtain ⟨K₁, hK₁, h₀, h₁⟩ := SmoothEmbedding.exists_smoothAmbientIsotopic_mfderiv_eq hn
    (by simp) K ((greatCircle (n := n) ι).contMDiff.mdifferentiableAt (by simp))
    ((greatCircle (n := n) ι).isImmersion.mfderiv_injective (by simp) z₀)
  obtain ⟨K', hK', hpos⟩ := exists_concordant_isConnectedSumPosition_of_mfderiv_eq hz₀ h₀ h₁
  exact ⟨K', (hK₁.concordant le_rfl).trans hK', hpos⟩

end SmoothCircleEmbedding

end TauCeti
