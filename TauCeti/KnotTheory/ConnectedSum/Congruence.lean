/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Associativity
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
  concordance a congruence for the connected sum along a fixed great circle.
* **Independence of the great circle.** Any linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'`
  intertwining `ι : ℂ →ₗᵢ[ℝ] E` and `ι' : ℂ →ₗᵢ[ℝ] E'` transports connected-sum position and
  commutes with the connected sum (`TauCeti.SmoothCircleEmbedding.transDiffeomorph_connectedSum`).
  When `E' = E` and `n ≥ 2`, rotation diffeotopies of `Sⁿ` act transitively on linear isometric
  copies of `ℂ` (`TauCeti.exists_diffeotopy_final_apply_eq_and_forall_map_eq`), so every pair of
  great circles `ι₁` and `ι₂` is related by an ambient rotation diffeotopy. In particular, all great
  circles are smoothly ambient isotopic and hence concordant
  (`TauCeti.SmoothCircleEmbedding.concordant_greatCircle`), and for `n ≥ 3` the connected sum of
  concordance classes depends neither on the positioned representatives nor on the choice of great
  circle (`TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant`).

The file also records how orientation reversal (`TauCeti.SmoothCircleEmbedding.reverse`) and the
reverse mirror image (`TauCeti.SmoothCircleEmbedding.reverseMirror`) interact with concordance and
connected sums. Because `reverseMirror ι K` is concordant to `K.reverse` moved by any reflection
(`TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_of_det_eq_neg_one`), `reverseMirror`
respects smooth concordance and is independent of the great circle in every dimension `n`
(`TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_of_concordant`). Moreover, any linear
isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` sending `ι 1` to `-ι' 1` and `ι i` to `ι' i` sends a knot `K`
in `ι`-connected-sum position to one in `ι'`-connected-sum position via `z ↦ e (K (-z)⁻¹)` and
distributes on the nose over `connectedSum`
(`TauCeti.SmoothCircleEmbedding.transDiffeomorph_reverse_rotate_connectedSum`); taking `e` to be a
rotation in dimension `n ≥ 2` yields `exists_concordant_reverse_connectedSum`, showing that
orientation reversal distributes over the connected sum up to smooth concordance.

## Main results

* `TauCeti.SmoothCircleEmbedding.exists_concordance_isConnectedSumPosition_of_three_le`: for
  `3 ≤ n`, any two concordant knots in connected-sum position are joined by a concordance in
  connected-sum position.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_of_concordant`: for `3 ≤ n`, connected sums
  formed with respect to arbitrary great circles give concordant results on concordant summands.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_assoc`: for `3 ≤ n`, representative-free
  associativity of the connected sum up to smooth concordance.
* `TauCeti.SmoothCircleEmbedding.smoothAmbientIsotopic_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.concordant_greatCircle`: for `2 ≤ n`, any two great circles of `Sⁿ`
  are smoothly ambient isotopic and smoothly concordant.
* `TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_of_concordant`: `reverseMirror` respects
  smooth concordance and does not depend on the great circle, in every sphere dimension `n`.
* `TauCeti.SmoothCircleEmbedding.exists_concordant_reverse_connectedSum`: for `2 ≤ n`, orientation
  reversal distributes over the connected sum up to concordance.

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

private theorem concordant_connectedSum_of_concordant_same (hn : 3 ≤ n)
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
  concordant_connectedSum_of_concordant_same hn h₁ h₁' h₂ h₂ hc₁ (.refl K₂)

/-- Varying the second summand of a connected sum within its concordance class preserves the
concordance class of the connected sum, in dimension `n ≥ 3`. -/
theorem concordant_connectedSum_right_of_concordant (hn : 3 ≤ n)
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂)
    (h₂' : IsConnectedSumPosition ι K₂') (hc₂ : SmoothEmbedding.Concordant K₂ K₂') :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₁ K₂' h₁ h₂') :=
  concordant_connectedSum_of_concordant_same hn h₁ h₁ h₂ h₂' (.refl K₁) hc₂

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

/-! ### Independence of the great circle -/

section GreatCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

private theorem smoothAmbientIsotopic_transDiffeomorph_of_final_apply_eq
    {Φ : Diffeotopy (𝓡 n) ∞ (sphere (0 : E) 1)} {e : E ≃ₗᵢ[ℝ] E}
    (hΦ : ∀ z, (Φ.final z : E) = e z)
    (L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    L.SmoothAmbientIsotopic (L.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
  refine SmoothEmbedding.SmoothAmbientIsotopic.of_diffeotopy Φ fun x => Subtype.ext ?_
  rw [hΦ, SmoothEmbedding.transDiffeomorph_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply]

/-- **All great circles are smoothly ambient isotopic** in a sphere of dimension `n ≥ 2`. -/
theorem smoothAmbientIsotopic_greatCircle (hn : 2 ≤ n) (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E) :
    (greatCircle (n := n) ι₁).SmoothAmbientIsotopic (greatCircle (n := n) ι₂) := by
  obtain ⟨Φ, e, hΦ, he⟩ := exists_diffeotopy_final_apply_eq_and_forall_map_eq (m := ∞) hn ι₁ ι₂
  rw [← transDiffeomorph_unitSphereDiffeomorph_greatCircle (n := n) he]
  exact smoothAmbientIsotopic_transDiffeomorph_of_final_apply_eq hΦ _

/-- **All great circles are smoothly concordant** in a sphere of dimension `n ≥ 2`. -/
theorem concordant_greatCircle (hn : 2 ≤ n) (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E) :
    SmoothEmbedding.Concordant (greatCircle (n := n) ι₁) (greatCircle (n := n) ι₂) :=
  (smoothAmbientIsotopic_greatCircle hn ι₁ ι₂).concordant le_rfl

/-- **Smooth concordance is a congruence for the connected sum, independently of the great circle.**
In dimension `n ≥ 3`, if `K₁`, `K₂` are in connected-sum position for `ι₁` and `K₁'`, `K₂'` are in
connected-sum position for `ι₂`, with `K₁` concordant to `K₁'` and `K₂` concordant to `K₂'`, then
their connected sums along `ι₁` and along `ι₂` are smoothly concordant. -/
theorem concordant_connectedSum_of_concordant (hn : 3 ≤ n)
    {ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E}
    {K₁ K₂ K₁' K₂' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (h₁ : IsConnectedSumPosition ι₁ K₁) (h₂ : IsConnectedSumPosition ι₁ K₂)
    (h₁' : IsConnectedSumPosition ι₂ K₁') (h₂' : IsConnectedSumPosition ι₂ K₂')
    (hc₁ : SmoothEmbedding.Concordant K₁ K₁') (hc₂ : SmoothEmbedding.Concordant K₂ K₂') :
    SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) (connectedSum K₁' K₂' h₁' h₂') := by
  obtain ⟨Φ, e, hΦ, he⟩ := exists_diffeotopy_final_apply_eq_and_forall_map_eq (n := n) (m := ∞)
    (by omega) ι₁ ι₂
  have hamb (L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
      SmoothEmbedding.Concordant L
        (L.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) :=
    (smoothAmbientIsotopic_transDiffeomorph_of_final_apply_eq hΦ L).concordant le_rfl
  refine (hamb (connectedSum K₁ K₂ h₁ h₂)).trans ?_
  rw [transDiffeomorph_connectedSum h₁ h₂ he]
  exact concordant_connectedSum_of_concordant_same hn
    (h₁.transDiffeomorph he) h₁' (h₂.transDiffeomorph he) h₂'
    ((hamb K₁).symm.trans hc₁) ((hamb K₂).symm.trans hc₂)

end GreatCircle

/-! ### Reverse mirror image and orientation reversal -/

section ReverseAndMirror

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The reverse mirror image respects smooth concordance and does not depend on the great circle**
in every sphere dimension `n`. -/
theorem concordant_reverseMirror_of_concordant (ι₁ ι₂ : ℂ →ₗᵢ[ℝ] E)
    {K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (hc : SmoothEmbedding.Concordant K₁ K₂) :
    SmoothEmbedding.Concordant (reverseMirror ι₁ K₁) (reverseMirror ι₂ K₂) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hdet : (LinearEquiv.det (ℝ ∙ ι₂ Complex.I)ᗮ.reflection.toLinearEquiv : ℝ) = -1 :=
    linearEquiv_det_reflection_orthogonal_singleton
      ((map_ne_zero_iff ι₂ ι₂.injective).2 Complex.I_ne_zero)
  refine (concordant_reverseMirror_of_det_eq_neg_one ι₁ hdet K₁).trans
    ((?_ : SmoothEmbedding.Concordant _ _).trans
      (concordant_reverseMirror_of_det_eq_neg_one ι₂ hdet K₂).symm)
  rw [K₁.reverse_def, K₂.reverse_def]
  exact (hc.compDiffeomorph circleReflection).transDiffeomorph _

/-- **Orientation reversal distributes over the connected sum up to smooth concordance.** In a
sphere of dimension `n ≥ 2`, the reverse of `K₁ # K₂` is concordant to the connected sum of
positioned representatives of `K₁.reverse` and `K₂.reverse`. -/
theorem exists_concordant_reverse_connectedSum (hn : 2 ≤ n) {ι : ℂ →ₗᵢ[ℝ] E}
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
    (by simp) (by simp) hperp (by simp) (by simp)
    (by rw [inner_neg_right, hperp, neg_zero])
  set ρ := (LinearMap.range ι.toLinearMap)ᗮ.reflection
  set e := g.trans ρ
  have he1 : e (ι 1) = -ι 1 := by simp [e, ρ, hg1]
  have heI : e (ι Complex.I) = ι Complex.I := by simp [e, ρ, hgI]
  have hturn (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
      SmoothEmbedding.Concordant K.reverse
        ((K.reverse.rotate (-1)).transDiffeomorph
          (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
    have hΦ' :=
      (smoothAmbientIsotopic_transDiffeomorph_of_final_apply_eq hgΦ K.reverse).concordant le_rfl
    have heq : turnOver ι (K.reverse.transDiffeomorph (g.unitSphereDiffeomorph ∞)) =
        (K.reverse.rotate (-1)).transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) :=
      SmoothEmbedding.ext fun z => Subtype.ext (by simp [e, ρ])
    exact hΦ'.trans (heq ▸ concordant_turnOver ι _)
  exact ⟨_, _, h₁.transDiffeomorph_reverse_rotate he1 heI,
    h₂.transDiffeomorph_reverse_rotate he1 heI, hturn K₁, hturn K₂,
    transDiffeomorph_reverse_rotate_connectedSum h₁ h₂ he1 heI ▸
      hturn (connectedSum K₁ K₂ h₁ h₂)⟩

end ReverseAndMirror

end TauCeti.SmoothCircleEmbedding
