/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Associativity
public import TauCeti.KnotTheory.ConnectedSum.Commutativity
public import TauCeti.KnotTheory.ConnectedSum.Concordance
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Rotation
import TauCeti.Geometry.Manifold.SmoothEmbedding.Arc.FirstOrder
import TauCeti.Geometry.Manifold.SmoothEmbedding.StandardArc
import TauCeti.KnotTheory.ConnectedSum.BoostConcordance

/-!
# Congruence of the connected sum of knots under smooth concordance

The connected sum `TauCeti.SmoothCircleEmbedding.connectedSum` of two smooth circle embeddings into
the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner product space `E` is defined on
representatives in connected-sum position (`TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition`)
with respect to a chosen great circle `ι : ℂ →ₗᵢ[ℝ] E`. For this construction to induce a canonical
abelian monoid structure on smooth concordance classes, two independence statements are needed in
dimension `n ≥ 3`:

* **Independence of the positioned representatives.** Any smooth concordance `F` between knots `K`
  and `K'` in connected-sum position for `ι` can be replaced by a concordance `G` that is itself in
  connected-sum position
  (`TauCeti.SmoothCircleEmbedding.exists_concordance_isConnectedSumPosition_of_three_le`).
  Over the bottom point `z₀ = -i` of the circle, `K` and `K'` agree with the great circle `ι` on a
  neighborhood, hence at `z₀` and to first order there. In `Sⁿ × ℝ` (`n ≥ 3`), the arc of `F` over
  `z₀` is first moved onto the straight line `{ι z₀} × ℝ`
  (`TauCeti.SmoothEmbedding.Concordance.exists_apply_eq_line`), then normalized to first order along
  that line to match the standard strip `ι × id`
  (`TauCeti.SmoothEmbedding.Concordance.exists_mfderiv_eq_prodMap`), and finally straightened near
  the arc and boosted into connected-sum position
  (`TauCeti.SmoothCircleEmbedding.exists_concordance_isConnectedSumPosition_of_mfderiv_eq`). Gluing
  two such concordances (`TauCeti.SmoothCircleEmbedding.concordant_connectedSum`) makes smooth
  concordance a congruence for the connected sum
  (`TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant`).
* **Independence of the great circle.** Any linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` sending
  `ι` to `ι'` transports connected-sum position and commutes with the connected sum
  (`TauCeti.SmoothCircleEmbedding.transLinearIsometryEquiv_connectedSum`). When `E' = E` and
  `n ≥ 2`, rotation diffeotopies of `Sⁿ` act transitively on orthonormal pairs
  (`TauCeti.exists_diffeotopy_final_apply_eq_and_apply_eq`), so every pair of great circles `ι₁` and
  `ι₂` is related by an ambient rotation diffeotopy. In particular, all great circles are smoothly
  ambient isotopic and hence concordant (`TauCeti.SmoothCircleEmbedding.concordant_greatCircle`),
  and for `n ≥ 3` the connected sum of concordance classes does not depend on the choice of great
  circle (`TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant_of_greatCircle`).

The file also records how orientation reversal (`TauCeti.SmoothCircleEmbedding.reverse`) and the
reverse mirror image (`TauCeti.SmoothCircleEmbedding.reverseMirror`) interact with great circles,
connected sums, and concordance. Any linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` negating `ι 1`
and fixing `ι i` sends a knot `K` in `ι`-connected-sum position to one in `ι'`-connected-sum
position via `z ↦ e (K (-z)⁻¹)` and distributes on the nose over `connectedSum`. Taking `e` to be
the reflection in the hyperplane orthogonal to `ι 1` yields `reverseMirror_greatCircle` and
`reverseMirror_connectedSum`; taking `e` to be a rotation in dimension `n ≥ 2` yields
`concordant_reverse_connectedSum`, showing that orientation reversal distributes over the connected
sum up to concordance.

## Main results

* `TauCeti.SmoothCircleEmbedding.exists_concordance_isConnectedSumPosition_of_three_le`: for
  `3 ≤ n`, any two concordant knots in connected-sum position are joined by a concordance in
  connected-sum position.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant`: for `3 ≤ n`, the connected
  sum of concordant knots in connected-sum position is concordant.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_assoc`: for `3 ≤ n`, representative-free
  associativity of the connected sum up to smooth concordance.
* `TauCeti.SmoothCircleEmbedding.transLinearIsometryEquiv_connectedSum`: linear isometry
  equivalences intertwining the great circles commute with the connected sum.
* `TauCeti.SmoothCircleEmbedding.smoothAmbientIsotopic_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.concordant_greatCircle`: for `2 ≤ n`, any two great circles of `Sⁿ`
  are smoothly ambient isotopic and smoothly concordant.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant_of_greatCircle`: for `3 ≤ n`,
  connected sums formed with respect to different great circles give concordant results on
  concordant summands.
* `TauCeti.SmoothCircleEmbedding.reverseMirror_reverseMirror`,
  `TauCeti.SmoothCircleEmbedding.reverseMirror_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.reverseMirror_connectedSum`,
  `TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_of_concordant`: involutivity, unit
  preservation, additivity, and concordance invariance of `reverseMirror`.
* `TauCeti.SmoothCircleEmbedding.concordant_reverse_connectedSum`: for `2 ≤ n`, orientation reversal
  distributes over the connected sum up to concordance.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory*, Elsevier
  (2005), 319–347, Section 2, Theorem 2.2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Graduate Texts in Mathematics 175, Springer
  (1997), Chapters 1 and 8.
* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448.
-/

public section

noncomputable section

open Metric Module Set Filter Topology Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti.SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

/-! ### Concordances in connected-sum position -/

section Congruence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}
  {K K' K₁ K₁' K₂ K₂' K₃ K₁₂ K₂₃ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- **Concordances between knots in connected-sum position can be put in connected-sum position.**
In a unit sphere `Sⁿ` of dimension `n ≥ 3`, any smooth concordance `F` between two knots `K` and
`K'` in connected-sum position for `ι` can be replaced by a smooth concordance `G` from `K` to `K'`
in connected-sum position for `ι`. -/
theorem exists_concordance_isConnectedSumPosition_of_three_le (hn : 3 ≤ n)
    (hK : IsConnectedSumPosition ι K) (hK' : IsConnectedSumPosition ι K')
    (F : SmoothEmbedding.Concordance K K') :
    ∃ G : SmoothEmbedding.Concordance K K', G.IsConnectedSumPosition ι := by
  let z₀ : Circle := ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩
  have hz₀ : (z₀ : ℂ) = -Complex.I := rfl
  have him : (z₀ : ℂ).im ≤ 0 := by simp [hz₀]
  obtain ⟨F₁, hF₁⟩ := F.exists_apply_eq_line hn ((hK'.apply_eq him).trans (hK.apply_eq him).symm)
  have h₀ : ∀ t, F₁ (z₀, t) = (greatCircle (n := n) ι z₀, t) := fun t => by
    rw [hF₁ t, hK.apply_eq him]
  obtain ⟨F₂, h₀', h₁'⟩ := F₁.exists_mfderiv_eq_prodMap hn
    (hK.eventuallyEq_greatCircle him).mfderiv_eq (hK'.eventuallyEq_greatCircle him).mfderiv_eq h₀
  exact exists_concordance_isConnectedSumPosition_of_mfderiv_eq hK hK' hz₀ h₀' h₁'

/-- In dimension `n ≥ 3`, two knots in connected-sum position for `ι` are smoothly concordant if and
only if they are joined by a smooth concordance in connected-sum position for `ι`. -/
theorem concordant_iff_exists_concordance_isConnectedSumPosition (hn : 3 ≤ n)
    (hK : IsConnectedSumPosition ι K) (hK' : IsConnectedSumPosition ι K') :
    SmoothEmbedding.Concordant K K' ↔
      ∃ G : SmoothEmbedding.Concordance K K', G.IsConnectedSumPosition ι :=
  ⟨fun h => (SmoothEmbedding.concordant_iff_nonempty.1 h).elim
      (exists_concordance_isConnectedSumPosition_of_three_le hn hK hK'),
    fun ⟨G, _⟩ => .of_concordance G⟩

/-- **Smooth concordance is a congruence for the connected sum.** In dimension `n ≥ 3`, if `K₁` is
concordant to `K₁'` and `K₂` is concordant to `K₂'`, with all four knots in connected-sum position
for `ι`, then `K₁ # K₂` is concordant to `K₁' # K₂'`. -/
theorem concordant_connectedSum_of_concordant (hn : 3 ≤ n)
    (h₁ : IsConnectedSumPosition ι K₁) (h₁' : IsConnectedSumPosition ι K₁')
    (h₂ : IsConnectedSumPosition ι K₂) (h₂' : IsConnectedSumPosition ι K₂')
    (hc₁ : SmoothEmbedding.Concordant K₁ K₁') (hc₂ : SmoothEmbedding.Concordant K₂ K₂') :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₁' K₂' h₁' h₂') := by
  obtain ⟨G₁, hG₁⟩ := (concordant_iff_exists_concordance_isConnectedSumPosition hn h₁ h₁').1 hc₁
  obtain ⟨G₂, hG₂⟩ := (concordant_iff_exists_concordance_isConnectedSumPosition hn h₂ h₂').1 hc₂
  exact concordant_connectedSum hG₁ hG₂

/-- Varying the first summand of a connected sum within its concordance class preserves the
concordance class of the connected sum, in dimension `n ≥ 3`. -/
theorem concordant_connectedSum_left_of_concordant (hn : 3 ≤ n)
    (h₁ : IsConnectedSumPosition ι K₁) (h₁' : IsConnectedSumPosition ι K₁')
    (h₂ : IsConnectedSumPosition ι K₂) (hc₁ : SmoothEmbedding.Concordant K₁ K₁') :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₁' K₂ h₁' h₂) :=
  concordant_connectedSum_of_concordant hn h₁ h₁' h₂ h₂ hc₁ (.refl K₂)

/-- Varying the second summand of a connected sum within its concordance class preserves the
concordance class of the connected sum, in dimension `n ≥ 3`. -/
theorem concordant_connectedSum_right_of_concordant (hn : 3 ≤ n)
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂)
    (h₂' : IsConnectedSumPosition ι K₂') (hc₂ : SmoothEmbedding.Concordant K₂ K₂') :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₁ K₂' h₁ h₂') :=
  concordant_connectedSum_of_concordant hn h₁ h₁ h₂ h₂' (.refl K₁) hc₂

/-- **Representative-independent associativity of the connected sum up to concordance.** In
dimension `n ≥ 3`, for any positioned representatives `K₁₂` of `K₁ # K₂` and `K₂₃` of `K₂ # K₃`,
the connected sums `K₁₂ # K₃` and `K₁ # K₂₃` are smoothly concordant. -/
theorem concordant_connectedSum_assoc (hn : 3 ≤ n)
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂)
    (h₃ : IsConnectedSumPosition ι K₃) (h₁₂ : IsConnectedSumPosition ι K₁₂)
    (h₂₃ : IsConnectedSumPosition ι K₂₃)
    (hc₁₂ : SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) K₁₂)
    (hc₂₃ : SmoothEmbedding.Concordant (connectedSum K₂ K₃ h₂ h₃) K₂₃) :
    SmoothEmbedding.Concordant (connectedSum K₁₂ K₃ h₁₂ h₃) (connectedSum K₁ K₂₃ h₁ h₂₃) := by
  obtain ⟨P, Q, hP, hQ, hKP, hKQ, hPQ⟩ := exists_concordant_connectedSum_assoc h₁ h₂ h₃
  exact (concordant_connectedSum_left_of_concordant hn h₁₂ hP h₃ (hc₁₂.symm.trans hKP)).trans
    (hPQ.trans (concordant_connectedSum_right_of_concordant hn h₁ hQ h₂₃ (hKQ.symm.trans hc₂₃)))

end Congruence

/-! ### Transport along linear isometry equivalences -/

section LinearIsometry

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ E' = n + 1)]
  {ι : ℂ →ₗᵢ[ℝ] E} {ι' : ℂ →ₗᵢ[ℝ] E'}

/-- If a real-linear map out of `E` sends `ι 1` to `ι' 1` and `ι i` to `ι' i`, it intertwines `ι`
and `ι'` on all of `ℂ`. -/
private theorem forall_map_eq_of_map_one_of_map_I {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) (w : ℂ) :
    e (ι w) = ι' w := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by apply Complex.ext <;> simp
  calc
    e (ι w) = e (ι (w.re • (1 : ℂ) + w.im • Complex.I)) := by rw [← hw]
    _ = w.re • e (ι 1) + w.im • e (ι Complex.I) := by
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    _ = w.re • ι' 1 + w.im • ι' Complex.I := by rw [h1, hI]
    _ = ι' (w.re • (1 : ℂ) + w.im • Complex.I) := by rw [map_add, map_smul, map_smul]
    _ = ι' w := by rw [← hw]

/-- A linear isometry equivalence mapping the plane `ι ℂ` onto `ι' ℂ` intertwines the half-turns in
those two planes. -/
private theorem map_reflection_orthogonal_range {e : E ≃ₗᵢ[ℝ] E'}
    (hrange : (LinearMap.range ι.toLinearMap).map (e.toLinearEquiv : E →ₗ[ℝ] E') =
      LinearMap.range ι'.toLinearMap) (x : E) :
    e ((LinearMap.range ι.toLinearMap)ᗮ.reflection x) =
      (LinearMap.range ι'.toLinearMap)ᗮ.reflection (e x) := by
  have horth : (LinearMap.range ι.toLinearMap)ᗮ.map (e.toLinearEquiv : E →ₗ[ℝ] E') =
      (LinearMap.range ι'.toLinearMap)ᗮ :=
    (Submodule.map_orthogonal_equiv (LinearMap.range ι.toLinearMap) e).trans
      (congrArg Submodule.orthogonal hrange)
  have href := Submodule.reflection_map_apply e (LinearMap.range ι.toLinearMap)ᗮ (e x)
  simp only [horth, LinearIsometryEquiv.symm_apply_apply] at href
  exact href.symm

private theorem map_range_eq_of_forall_map_eq {e : E ≃ₗᵢ[ℝ] E'}
    (he : ∀ w, e (ι w) = ι' w) :
    (LinearMap.range ι.toLinearMap).map (e.toLinearEquiv : E →ₗ[ℝ] E') =
      LinearMap.range ι'.toLinearMap := by
  ext y
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, (he w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨ι w, ⟨w, rfl⟩, he w⟩

/-- A linear isometry equivalence intertwining `ι` and `ι'` transports `greatCircle ι` to
`greatCircle ι'`. -/
theorem transLinearIsometryEquiv_greatCircle {e : E ≃ₗᵢ[ℝ] E'} (he : ∀ w, e (ι w) = ι' w) :
    (greatCircle (n := n) ι).transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      greatCircle (n := n) ι' :=
  SmoothEmbedding.ext fun z => Subtype.ext <| by simp [he]

/-- A linear isometry equivalence intertwining `ι` and `ι'` transports connected-sum position for
`ι` to connected-sum position for `ι'`. -/
theorem IsConnectedSumPosition.transLinearIsometryEquiv
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} (h : IsConnectedSumPosition ι K)
    {e : E ≃ₗᵢ[ℝ] E'} (he : ∀ w, e (ι w) = ι' w) :
    IsConnectedSumPosition ι'
      (K.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) where
  eventuallyEq_greatCircle {z} hz := by
    filter_upwards [h.eventuallyEq_greatCircle hz] with w hw
    exact Subtype.ext (by simp [hw, he])
  inner_pos {z} hz := by
    rw [SmoothEmbedding.transDiffeomorph_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      ← he Complex.I, LinearIsometryEquiv.inner_map_map]
    exact h.inner_pos hz

/-- **Linear isometry equivalences intertwining the great circles commute with the connected
sum.** -/
theorem transLinearIsometryEquiv_connectedSum
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂)
    {e : E ≃ₗᵢ[ℝ] E'} (he : ∀ w, e (ι w) = ι' w) :
    (connectedSum K₁ K₂ h₁ h₂).transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      connectedSum (K₁.transDiffeomorph (e.unitSphereDiffeomorph ∞))
        (K₂.transDiffeomorph (e.unitSphereDiffeomorph ∞))
        (h₁.transLinearIsometryEquiv he) (h₂.transLinearIsometryEquiv he) := by
  ext z : 1
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · simp [connectedSum_apply_of_im_nonneg _ _ hz]
  · apply Subtype.ext
    rw [SmoothEmbedding.transDiffeomorph_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      coe_connectedSum_apply_of_im_neg _ _ hz, coe_connectedSum_apply_of_im_neg _ _ hz,
      SmoothEmbedding.transDiffeomorph_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      map_reflection_orthogonal_range (map_range_eq_of_forall_map_eq he)]

/-! ### Orientation-reversing transport of connected sums -/

/-- A knot reparametrized by `z ↦ (-z)⁻¹` and transported by a linear isometry equivalence `e`.
When `e` sends `(ι 1, ι i)` to `(-ι' 1, ι' i)`, this preserves connected-sum position and
distributes on the nose over `connectedSum`; it unifies `reverseMirror` (when `e` is a reflection)
and orientation reversal up to ambient rotation (when `e` is a rotation). -/
private def reverseTransport (e : E ≃ₗᵢ[ℝ] E')
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E') 1) :=
  ((K.compDiffeomorph circleReflection).compDiffeomorph (circleRotationHom (-1))).transDiffeomorph
    (e.unitSphereDiffeomorph (n := n) (k := n) ∞)

@[simp]
private theorem coe_reverseTransport_apply (e : E ≃ₗᵢ[ℝ] E')
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (z : Circle) :
    (reverseTransport e K z : E') = e (K (-z)⁻¹) := by
  simp [reverseTransport]

private theorem map_eq_neg_conj_of_map_one_eq_neg_of_map_I {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) (w : ℂ) :
    e (ι w) = ι' (-starRingEnd ℂ w) := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by apply Complex.ext <;> simp
  have hw' : -starRingEnd ℂ w = (-w.re) • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    e (ι w) = e (ι (w.re • (1 : ℂ) + w.im • Complex.I)) := by rw [← hw]
    _ = w.re • e (ι 1) + w.im • e (ι Complex.I) := by
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    _ = (-w.re) • ι' 1 + w.im • ι' Complex.I := by rw [h1, hI, neg_smul, smul_neg]
    _ = ι' ((-w.re) • (1 : ℂ) + w.im • Complex.I) := by rw [map_add, map_smul, map_smul]
    _ = ι' (-starRingEnd ℂ w) := by rw [← hw']

private theorem map_range_eq_of_map_one_eq_neg_of_map_I {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    (LinearMap.range ι.toLinearMap).map (e.toLinearEquiv : E →ₗ[ℝ] E') =
      LinearMap.range ι'.toLinearMap := by
  ext y
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨-starRingEnd ℂ w, (map_eq_neg_conj_of_map_one_eq_neg_of_map_I h1 hI w).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨ι (-starRingEnd ℂ w), ⟨-starRingEnd ℂ w, rfl⟩, ?_⟩
    exact (map_eq_neg_conj_of_map_one_eq_neg_of_map_I h1 hI (-starRingEnd ℂ w)).trans (by simp)

private theorem reverseTransport_greatCircle {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    reverseTransport e (greatCircle (n := n) ι) = greatCircle (n := n) ι' := by
  have hzc (z : Circle) : -starRingEnd ℂ ((((-z)⁻¹ : Circle) : ℂ)) = (z : ℂ) := by
    apply Complex.ext <;> simp
  refine SmoothEmbedding.ext fun z => Subtype.ext ?_
  rw [coe_reverseTransport_apply, coe_greatCircle_apply,
    map_eq_neg_conj_of_map_one_eq_neg_of_map_I h1 hI, coe_greatCircle_apply, hzc]

private theorem isConnectedSumPosition_reverseTransport
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} (h : IsConnectedSumPosition ι K)
    {e : E ≃ₗᵢ[ℝ] E'} (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    IsConnectedSumPosition ι' (reverseTransport e K) where
  eventuallyEq_greatCircle {z} hz := by
    have hneg : (((-z)⁻¹ : Circle) : ℂ).im ≤ 0 := by simpa [Circle.coe_inv_eq_conj] using hz
    filter_upwards [((continuous_inv.comp continuous_neg).tendsto z).eventually
      (h.eventuallyEq_greatCircle hneg)] with w hw
    have hw' : K (-w)⁻¹ = greatCircle (n := n) ι (-w)⁻¹ := hw
    refine Subtype.ext ?_
    rw [coe_reverseTransport_apply, hw', ← coe_reverseTransport_apply,
      reverseTransport_greatCircle h1 hI]
  inner_pos {z} hz := by
    rw [coe_reverseTransport_apply, ← hI, LinearIsometryEquiv.inner_map_map]
    exact h.inner_pos (by simpa [Circle.coe_inv_eq_conj] using hz)

private theorem reverseTransport_connectedSum
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂)
    {e : E ≃ₗᵢ[ℝ] E'} (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    reverseTransport e (connectedSum K₁ K₂ h₁ h₂) =
      connectedSum (reverseTransport e K₁) (reverseTransport e K₂)
        (isConnectedSumPosition_reverseTransport h₁ h1 hI)
        (isConnectedSumPosition_reverseTransport h₂ h1 hI) := by
  ext z : 1
  have him : (((-z)⁻¹ : Circle) : ℂ).im = (z : ℂ).im := by simp
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · have hz' : 0 ≤ (((-z)⁻¹ : Circle) : ℂ).im := him ▸ hz
    apply Subtype.ext
    rw [connectedSum_apply_of_im_nonneg _ _ hz, coe_reverseTransport_apply,
      connectedSum_apply_of_im_nonneg _ _ hz', coe_reverseTransport_apply]
  · have hz' : (((-z)⁻¹ : Circle) : ℂ).im < 0 := him ▸ hz
    have hzz : (-((-z)⁻¹ : Circle)) = z⁻¹ := Subtype.ext (by simp)
    apply Subtype.ext
    rw [coe_reverseTransport_apply, coe_connectedSum_apply_of_im_neg _ _ hz',
      coe_connectedSum_apply_of_im_neg _ _ hz, coe_reverseTransport_apply, hzz, neg_neg,
      map_reflection_orthogonal_range (map_range_eq_of_map_one_eq_neg_of_map_I h1 hI)]

end LinearIsometry

/-! ### Independence of the great circle -/

section GreatCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- In a sphere of dimension `n ≥ 2`, any two great circles `ι₁` and `ι₂` are related by a rotation
diffeotopy of the sphere whose final map comes from a linear isometry intertwining `ι₁` and `ι₂`. -/
private theorem exists_diffeotopy_forall_map_eq_greatCircle (hn : 2 ≤ n)
    (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E) :
    ∃ (Φ : Diffeotopy (𝓡 n) ∞ (sphere (0 : E) 1)) (e : E ≃ₗᵢ[ℝ] E),
      Φ.final = e.unitSphereDiffeomorph (n := n) (k := n) ∞ ∧ ∀ w, e (ι₁ w) = ι₂ w := by
  have h1 (ι : ℂ →ₗᵢ[ℝ] E) : ‖ι 1‖ = 1 := by simp
  have hI (ι : ℂ →ₗᵢ[ℝ] E) : ‖ι Complex.I‖ = 1 := ι.norm_map_I
  have hperp (ι : ℂ →ₗᵢ[ℝ] E) : ⟪ι 1, ι Complex.I⟫ = 0 := by simp [ι.inner_map_map, Complex.inner]
  obtain ⟨Φ, e, hΦ, he1, heI⟩ := exists_diffeotopy_final_apply_eq_and_apply_eq (m := ∞) hn
    (h1 ι₁) (hI ι₁) (hperp ι₁) (h1 ι₂) (hI ι₂) (hperp ι₂)
  refine ⟨Φ, e, _root_.Diffeomorph.ext fun z => Subtype.ext ?_,
    forall_map_eq_of_map_one_of_map_I he1 heI⟩
  exact (hΦ z).trans (LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply e z).symm

/-- **All great circles are smoothly ambient isotopic** in a sphere of dimension `n ≥ 2`. -/
theorem smoothAmbientIsotopic_greatCircle (hn : 2 ≤ n) (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E) :
    (greatCircle (n := n) ι₁).SmoothAmbientIsotopic (greatCircle (n := n) ι₂) := by
  obtain ⟨Φ, e, hΦ, he⟩ := exists_diffeotopy_forall_map_eq_greatCircle hn ι₁ ι₂
  rw [← transLinearIsometryEquiv_greatCircle (n := n) he, ← hΦ]
  exact SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_final _ Φ

/-- **All great circles are smoothly concordant** in a sphere of dimension `n ≥ 2`. -/
theorem concordant_greatCircle (hn : 2 ≤ n) (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E) :
    SmoothEmbedding.Concordant (greatCircle (n := n) ι₁) (greatCircle (n := n) ι₂) :=
  (smoothAmbientIsotopic_greatCircle hn ι₁ ι₂).concordant le_rfl

/-- **Independence of the connected sum from the choice of great circle.** In dimension `n ≥ 3`,
if `K₁`, `K₂` are in connected-sum position for `ι₁` and `K₁'`, `K₂'` are in connected-sum
position for `ι₂`, with `K₁` concordant to `K₁'` and `K₂` concordant to `K₂'`, then their
connected sums along `ι₁` and along `ι₂` are smoothly concordant. -/
theorem concordant_connectedSum_of_concordant_of_greatCircle (hn : 3 ≤ n)
    {ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ K₁' K₂' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι₁ K₁) (h₂ : IsConnectedSumPosition ι₁ K₂)
    (h₁' : IsConnectedSumPosition ι₂ K₁') (h₂' : IsConnectedSumPosition ι₂ K₂')
    (hc₁ : SmoothEmbedding.Concordant K₁ K₁') (hc₂ : SmoothEmbedding.Concordant K₂ K₂') :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₁' K₂' h₁' h₂') := by
  obtain ⟨Φ, e, hΦ, he⟩ := exists_diffeotopy_forall_map_eq_greatCircle (n := n) (by omega) ι₁ ι₂
  have hamb (L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
      SmoothEmbedding.Concordant L
        (L.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
    rw [← hΦ]
    exact (SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_final L Φ).concordant le_rfl
  refine (hamb (connectedSum K₁ K₂ h₁ h₂)).trans ?_
  rw [transLinearIsometryEquiv_connectedSum h₁ h₂ he]
  exact concordant_connectedSum_of_concordant hn
    (h₁.transLinearIsometryEquiv he) h₁' (h₂.transLinearIsometryEquiv he) h₂'
    ((hamb K₁).symm.trans hc₁) ((hamb K₂).symm.trans hc₂)

end GreatCircle

/-! ### Reverse mirror image and orientation reversal -/

section ReverseAndMirror

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

private theorem reverseMirror_eq_reverseTransport (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirror ι K = reverseTransport
      ((ℝ ∙ ι Complex.I)ᗮ.reflection.trans (LinearMap.range ι.toLinearMap)ᗮ.reflection) K :=
  SmoothEmbedding.ext fun z => Subtype.ext <| by simp [coe_reverseMirror_apply]

private theorem connectedSum_congr {ι : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₁' K₂ K₂' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    {h₁ : IsConnectedSumPosition ι K₁} {h₁' : IsConnectedSumPosition ι K₁'}
    {h₂ : IsConnectedSumPosition ι K₂} {h₂' : IsConnectedSumPosition ι K₂'}
    (e₁ : K₁ = K₁') (e₂ : K₂ = K₂') :
    connectedSum K₁ K₂ h₁ h₂ = connectedSum K₁' K₂' h₁' h₂' := by
  subst e₁ e₂
  rfl

private theorem reverseMirror_reflection_map_one (ι : ℂ →ₗᵢ[ℝ] E) :
    ((ℝ ∙ ι Complex.I)ᗮ.reflection.trans (LinearMap.range ι.toLinearMap)ᗮ.reflection) (ι 1) =
      -ι 1 := by
  have h1 : ⟪ι Complex.I, ι 1⟫ = 0 := by simp [ι.inner_map_map, Complex.inner]
  simp [reflection_orthogonal_singleton_eq_self_of_inner_eq_zero h1]

private theorem reverseMirror_reflection_map_I (ι : ℂ →ₗᵢ[ℝ] E) :
    ((ℝ ∙ ι Complex.I)ᗮ.reflection.trans (LinearMap.range ι.toLinearMap)ᗮ.reflection)
      (ι Complex.I) = ι Complex.I := by
  simp [Submodule.reflection_orthogonalComplement_singleton_eq_neg]

/-- **Taking the reverse mirror image twice gives back the knot.** -/
@[simp]
theorem reverseMirror_reverseMirror (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirror ι (reverseMirror ι K) = K := by
  have hsub : ((ℝ ∙ ι Complex.I)ᗮ).map
      (((LinearMap.range ι.toLinearMap)ᗮ.reflection).toLinearEquiv : E →ₗ[ℝ] E) =
      (ℝ ∙ ι Complex.I)ᗮ := by
    rw [Submodule.map_orthogonal_equiv]
    congr 1
    ext y
    simp only [Submodule.mem_map, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨-r, by simp [ι.reflection_orthogonal_range_apply]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨(-r) • ι Complex.I, ⟨-r, rfl⟩, by simp [ι.reflection_orthogonal_range_apply]⟩
  refine SmoothEmbedding.ext fun z => Subtype.ext ?_
  have hz : (-((-z)⁻¹ : Circle))⁻¹ = z := Subtype.ext (by simp)
  rw [coe_reverseMirror_apply, coe_reverseMirror_apply, hz,
    ← Submodule.reflection_apply_of_map_eq (ℝ ∙ ι Complex.I)ᗮ hsub,
    Submodule.reflection_reflection, Submodule.reflection_reflection]

/-- **The great circle is its own reverse mirror image.** -/
@[simp]
theorem reverseMirror_greatCircle (ι : ℂ →ₗᵢ[ℝ] E) :
    reverseMirror ι (greatCircle (n := n) ι) = greatCircle (n := n) ι :=
  (reverseMirror_eq_reverseTransport ι _).trans <|
    reverseTransport_greatCircle (reverseMirror_reflection_map_one ι)
      (reverseMirror_reflection_map_I ι)

/-- **The reverse mirror image distributes over the connected sum.** -/
theorem reverseMirror_connectedSum {ι : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    reverseMirror ι (connectedSum K₁ K₂ h₁ h₂) =
      connectedSum (reverseMirror ι K₁) (reverseMirror ι K₂) h₁.reverseMirror h₂.reverseMirror :=
  (reverseMirror_eq_reverseTransport ι _).trans <|
    (reverseTransport_connectedSum h₁ h₂ (reverseMirror_reflection_map_one ι)
      (reverseMirror_reflection_map_I ι)).trans <|
      connectedSum_congr (reverseMirror_eq_reverseTransport ι K₁).symm
        (reverseMirror_eq_reverseTransport ι K₂).symm

/-- **The reverse mirror image respects smooth concordance and does not depend on the great circle**
in dimension `n ≥ 2`. -/
theorem concordant_reverseMirror_of_concordant (hn : 2 ≤ n) (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E)
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (hc : SmoothEmbedding.Concordant K₁ K₂) :
    SmoothEmbedding.Concordant (reverseMirror ι₁ K₁) (reverseMirror ι₂ K₂) := by
  obtain ⟨Φ, e, hΦ, he⟩ := exists_diffeotopy_forall_map_eq_greatCircle hn ι₁ ι₂
  have hsub : ((ℝ ∙ ι₁ Complex.I)ᗮ).map (e.toLinearEquiv : E →ₗ[ℝ] E) = (ℝ ∙ ι₂ Complex.I)ᗮ := by
    rw [Submodule.map_orthogonal_equiv]
    congr 1
    ext y
    simp only [Submodule.mem_map, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp [he]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r • ι₁ Complex.I, ⟨r, rfl⟩, by simp [he]⟩
  have hrefI (x : E) : e ((ℝ ∙ ι₁ Complex.I)ᗮ.reflection x) =
      (ℝ ∙ ι₂ Complex.I)ᗮ.reflection (e x) := by
    have h := Submodule.reflection_map_apply e (ℝ ∙ ι₁ Complex.I)ᗮ (e x)
    simp only [hsub, LinearIsometryEquiv.symm_apply_apply] at h
    exact h.symm
  have hamb (L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
      SmoothEmbedding.Concordant L
        (L.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
    rw [← hΦ]
    exact (SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_final L Φ).concordant le_rfl
  set L₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
    K₁.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)
  have htrans : (reverseMirror ι₁ K₁).transDiffeomorph
      (e.unitSphereDiffeomorph (n := n) (k := n) ∞) = reverseMirror ι₂ L₁ := by
    refine SmoothEmbedding.ext fun z => Subtype.ext ?_
    simp [L₁, coe_reverseMirror_apply, hrefI,
      map_reflection_orthogonal_range (map_range_eq_of_forall_map_eq he)]
  refine (hamb (reverseMirror ι₁ K₁)).trans ?_
  rw [htrans, reverseMirror_eq_reverseTransport ι₂ L₁, reverseMirror_eq_reverseTransport ι₂ K₂]
  set d := ((ℝ ∙ ι₂ Complex.I)ᗮ.reflection.trans
    (LinearMap.range ι₂.toLinearMap)ᗮ.reflection).unitSphereDiffeomorph (n := n) (k := n) ∞
  exact (((((hamb K₁).symm.trans hc).compDiffeomorph circleReflection).compDiffeomorph
    (circleRotationHom (-1))).transDiffeomorph d)

/-- **Orientation reversal distributes over the connected sum up to smooth concordance.** In a
sphere of dimension `n ≥ 2`, the reverse of `K₁ # K₂` is concordant to the connected sum of
positioned representatives of `K₁.reverse` and `K₂.reverse`. -/
theorem concordant_reverse_connectedSum (hn : 2 ≤ n) {ι : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    ∃ (L₁ L₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
      (hL₁ : IsConnectedSumPosition ι L₁) (hL₂ : IsConnectedSumPosition ι L₂),
      SmoothEmbedding.Concordant K₁.reverse L₁ ∧
        SmoothEmbedding.Concordant K₂.reverse L₂ ∧
        SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂).reverse
          (connectedSum L₁ L₂ hL₁ hL₂) := by
  have hperp : ⟪ι 1, ι Complex.I⟫ = 0 := by simp [ι.inner_map_map, Complex.inner]
  obtain ⟨Φ, g, hgΦ, hg1, hgI⟩ := exists_diffeotopy_final_apply_eq_and_apply_eq (m := ∞)
    (x := ι 1) (v := ι Complex.I) (y := ι 1) (w := -ι Complex.I) hn
    (by simp) ι.norm_map_I hperp (by simp) (by rw [norm_neg]; exact ι.norm_map_I)
    (by rw [inner_neg_right, hperp, neg_zero])
  set ρ := (LinearMap.range ι.toLinearMap)ᗮ.reflection
  set e := g.trans ρ
  have he1 : e (ι 1) = -ι 1 := by simp [e, ρ, hg1]
  have heI : e (ι Complex.I) = ι Complex.I := by simp [e, ρ, hgI]
  have hf : Φ.final = g.unitSphereDiffeomorph (n := n) (k := n) ∞ :=
    _root_.Diffeomorph.ext fun z =>
      Subtype.ext ((hgΦ z).trans (LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply g z).symm)
  have hturn (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
      SmoothEmbedding.Concordant K.reverse (reverseTransport e K) := by
    have hΦ' : SmoothEmbedding.Concordant K.reverse
        (K.reverse.transDiffeomorph (g.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
      rw [← hf]
      exact (SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_final _ Φ).concordant le_rfl
    have heq : turnOver ι (K.reverse.transDiffeomorph (g.unitSphereDiffeomorph ∞)) =
        reverseTransport e K := SmoothEmbedding.ext fun z => Subtype.ext (by simp [e, ρ])
    exact hΦ'.trans (heq ▸ concordant_turnOver ι _)
  exact ⟨reverseTransport e K₁, reverseTransport e K₂,
    isConnectedSumPosition_reverseTransport h₁ he1 heI,
    isConnectedSumPosition_reverseTransport h₂ he1 heI,
    hturn K₁, hturn K₂,
    reverseTransport_connectedSum h₁ h₂ he1 heI ▸ hturn (connectedSum K₁ K₂ h₁ h₂)⟩

end ReverseAndMirror

end TauCeti.SmoothCircleEmbedding
