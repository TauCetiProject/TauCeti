/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Topology.VectorBundle.Orientation.TwistedHomology
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.Compact

/-!
# Orientability of the real line bundles `𝒪(k)` and the Möbius line

Over `ℝ`, the projective line `OnePoint ℝ` is a circle and the line bundle `𝒪(k)` on it
(`OnePoint.twistCore`) is glued from two trivial lines along the transition `z ↦ z⁻ᵏ` on the
overlap `ℝ ∖ {0}` of the two charts. This transition changes sign between the two components of the
overlap exactly when `k` is odd. So `𝒪(k)` is orientable if and only if `k` is even
(`OnePoint.nonempty_vectorBundleOrientation_twistCore_iff`): for odd `k` it is a Möbius line.

For a nonorientable bundle over a path-connected, locally path-connected base, the zeroth homology
of the orientation local system with integer coefficients is `ℤ/2`
(`TauCeti.VectorBundleOrientationCover.twistedHomology₀SignLocalSystemEquivOfIsEmpty`). So for odd
`k` the zeroth homology of the circle with integer coefficients twisted by the orientation local
system of `𝒪(k)` is `ℤ/2` (`OnePoint.twistedHomology₀TwistCoreAddEquivOfOdd`), and not `ℤ`
(`OnePoint.not_nonempty_twistedHomology₀_twistCore_addEquiv_int_of_odd`), the zeroth homology of
the circle with constant integer coefficients. For a Möbius line `E` over the circle, the twisted
Thom isomorphism `H₁(D(E), S(E); ℤ) ≅ H₀(S¹; o(E))` therefore gives `ℤ/2` in degree one, where
constant coefficients would give `ℤ`.

## Main results

* `OnePoint.nonempty_vectorBundleOrientation_twistCore_iff`: `𝒪(k)` on `OnePoint ℝ` is orientable
  if and only if `k` is even.
* `OnePoint.twistedHomology₀TwistCoreAddEquivOfOdd`: for odd `k`, the zeroth homology of
  `OnePoint ℝ` with integer coefficients twisted by the orientation local system of `𝒪(k)` is
  `ℤ/2`.
* `OnePoint.not_nonempty_twistedHomology₀_twistCore_addEquiv_int_of_odd`: for odd `k` it is not
  `ℤ`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (the canonical line bundle of `ℝℙ¹` and the Möbius band) and §12 (twisted
  coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open Bundle Filter Module Set Topology TauCeti

namespace OnePoint

/-- Reading an orientation of a fibre of `𝒪(k)` in the chart at `y'` gives the same orientation
of `ℝ` as reading it in the chart at `y` when the transition from `y` to `y'` is positive, and the
opposite one when it is negative. -/
private theorem mapOrientation_trivializationAt_twistCore (k : ℤ) {y y' p : OnePoint ℝ}
    (hp : p ∈ (trivializationAt ℝ (twistCore (𝕜 := ℝ) k).Fiber y).baseSet)
    (hp' : p ∈ (trivializationAt ℝ (twistCore (𝕜 := ℝ) k).Fiber y').baseSet)
    (w : Orientation ℝ ((twistCore (𝕜 := ℝ) k).Fiber p) (Fin 1)) :
    ((0 < twistTransition k y y' p) →
      (trivializationAt ℝ _ y').mapOrientation (Fin 1) hp' w =
        (trivializationAt ℝ _ y).mapOrientation (Fin 1) hp w) ∧
    ((twistTransition k y y' p < 0) →
      (trivializationAt ℝ _ y').mapOrientation (Fin 1) hp' w =
        -(trivializationAt ℝ _ y).mapOrientation (Fin 1) hp w) := by
  -- The coordinate change between the two charts is multiplication by the transition. The chart
  -- of the bundle core at `y` is its preferred trivialization at `y`, by definition.
  have hc : (((trivializationAt ℝ (twistCore (𝕜 := ℝ) k).Fiber y).coordChangeL ℝ
      (trivializationAt ℝ _ y') p).toLinearEquiv : ℝ →ₗ[ℝ] ℝ) =
        twistTransition k y y' p • LinearMap.id := by
    have hp₁ := hp
    have hp₁' := hp'
    rw [trivializationAt_twistCore] at hp₁ hp₁'
    ext
    simp only [trivializationAt_twistCore]
    exact ((twistCore k).localTriv_coordChange_eq y y' ⟨hp₁, hp₁'⟩ 1).trans (by simp)
  have hdet : LinearMap.det (((trivializationAt ℝ (twistCore (𝕜 := ℝ) k).Fiber y).coordChangeL ℝ
      (trivializationAt ℝ _ y') p).toLinearEquiv : ℝ →ₗ[ℝ] ℝ) = twistTransition k y y' p := by
    rw [hc, LinearMap.det_smul, LinearMap.det_id, finrank_self, pow_one, mul_one]
  rw [Trivialization.mapOrientation_eq_map_coordChangeL _ _ hp hp']
  have hι : Fintype.card (Fin 1) = finrank ℝ ℝ := (Fintype.card_fin 1).trans (finrank_self ℝ).symm
  exact ⟨fun h ↦ (Orientation.map_eq_iff_det_pos _ _ hι).2 (hdet ▸ h),
    fun h ↦ (Orientation.map_eq_neg_iff_det_neg _ _ hι).2 (hdet ▸ h)⟩

/-- For even `k`, the transition of `𝒪(k)` is positive wherever it is defined. -/
private theorem twistTransition_pos_of_even {k : ℤ} (hk : Even k) {x y p : OnePoint ℝ}
    (hx : p ∈ (chartAt ℝ x).source) (hy : p ∈ (chartAt ℝ y).source) :
    0 < twistTransition k x y p := by
  rw [twistTransition_def]
  by_cases h0 : affineChart p = 0
  · simp [twistIndex_eq_of_affineChart_eq_zero hx h0, twistIndex_eq_of_affineChart_eq_zero hy h0]
  · exact (hk.mul_right _).zpow_pos h0

/-- For even `k`, the line bundle `𝒪(k)` on `OnePoint ℝ` is oriented by the orientation that reads
as a fixed orientation of `ℝ` in the preferred chart at each point. -/
private def twistCoreOrientationOfEven {k : ℤ} (hk : Even k) :
    VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) k).Fiber (Fin 1) :=
  VectorBundleOrientation.ofEventually ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)
    (fun p ↦ ((trivializationAt ℝ _ p).mapOrientation (Fin 1)
      (FiberBundle.mem_baseSet_trivializationAt' p)).symm (Basis.singleton (Fin 1) ℝ).orientation)
    (trivializationAt ℝ _) FiberBundle.mem_baseSet_trivializationAt' fun b ↦
      Eventually.of_forall fun x hx ↦ by
        rw [((mapOrientation_trivializationAt_twistCore k
          (FiberBundle.mem_baseSet_trivializationAt' x) hx _).1
          (twistTransition_pos_of_even hk (mem_chart_source ℝ x)
            (by simpa using hx))), Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]

/-- For odd `k`, the line bundle `𝒪(k)` on `OnePoint ℝ` is not orientable. -/
private theorem isEmpty_vectorBundleOrientation_twistCore_of_odd {k : ℤ} (hk : Odd k) :
    IsEmpty (VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) k).Fiber (Fin 1)) := by
  refine ⟨fun o ↦ ?_⟩
  have hι : Fintype.card (Fin 1) = finrank ℝ ℝ := (Fintype.card_fin 1).trans (finrank_self ℝ).symm
  set e₀ := trivializationAt ℝ (twistCore (𝕜 := ℝ) k).Fiber ((0 : ℝ) : OnePoint ℝ)
  set eInf := trivializationAt ℝ (twistCore (𝕜 := ℝ) k).Fiber ∞
  have h₀ (w : ℝ) : (w : OnePoint ℝ) ∈ e₀.baseSet := by
    simp [e₀]
  have hInf {w : ℝ} (hw : w ≠ 0) : (w : OnePoint ℝ) ∈ eInf.baseSet := by
    simpa [eInf] using hw
  -- Read in the affine chart, the orientation is locally constant on `ℝ`, hence constant.
  have hconst : IsLocallyConstant fun w : ℝ ↦ e₀.mapOrientation (Fin 1) (h₀ w) (o w) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun z ↦ by
      filter_upwards [(continuous_coe.tendsto z).eventually
        (o.eventually_mapOrientation_eq hι e₀ (h₀ z))] with w hw
      exact hw (h₀ w)
  -- Read in the inverted chart, it is locally constant near `∞`.
  have hinf : ∀ᶠ w : ℝ in cocompact ℝ, ∀ hw : (w : OnePoint ℝ) ∈ eInf.baseSet,
      eInf.mapOrientation (Fin 1) hw (o w) =
        eInf.mapOrientation (Fin 1) (FiberBundle.mem_baseSet_trivializationAt' _) (o ∞) := by
    rw [← coclosedCompact_eq_cocompact]
    exact tendsto_coe_infty.eventually
      (o.eventually_mapOrientation_eq hι eInf _)
  -- The transition `w⁻ᵏ` from the affine to the inverted chart is positive for `w > 0` and
  -- negative for `w < 0`, so the two readings far out on either side are opposite.
  obtain ⟨w₁, hw₁, hw₁0⟩ :=
    ((hinf.filter_mono atTop_le_cocompact).and (eventually_gt_atTop 0)).exists
  obtain ⟨w₂, hw₂, hw₂0⟩ :=
    ((hinf.filter_mono atBot_le_cocompact).and (eventually_lt_atBot 0)).exists
  have hpos := (mapOrientation_trivializationAt_twistCore k (h₀ w₁) (hInf hw₁0.ne') (o w₁)).1
    (by simpa [twistTransition_coe_infty] using zpow_pos hw₁0 (-k))
  have hneg := (mapOrientation_trivializationAt_twistCore k (h₀ w₂) (hInf hw₂0.ne) (o w₂)).2
    (by simpa [twistTransition_coe_infty] using (hk.neg.zpow_neg_iff).2 hw₂0)
  rw [hw₁, hconst.apply_eq_of_preconnectedSpace w₁ 0] at hpos
  rw [hw₂, hconst.apply_eq_of_preconnectedSpace w₂ 0] at hneg
  exact Module.Ray.ne_neg_self _ (hpos.symm.trans hneg)

/-- **The line bundle `𝒪(k)` on the real projective line is orientable exactly when `k` is even.**
The transition `z ↦ z⁻ᵏ` between its two charts is positive on the whole overlap `ℝ ∖ {0}` when
`k` is even, and has opposite signs on the two half-lines when `k` is odd. For odd `k` this is the
Möbius line. -/
theorem nonempty_vectorBundleOrientation_twistCore_iff (k : ℤ) :
    Nonempty (VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) k).Fiber (Fin 1)) ↔ Even k := by
  refine ⟨fun ⟨o⟩ ↦ ?_, fun hk ↦ ⟨twistCoreOrientationOfEven hk⟩⟩
  by_contra hk
  exact (isEmpty_vectorBundleOrientation_twistCore_of_odd (Int.not_even_iff_odd.1 hk)).false o

/-- **The zeroth homology of the circle twisted by the orientation of the Möbius line is `ℤ/2`.**
For odd `k`, the zeroth singular homology of `OnePoint ℝ` with integer coefficients twisted by the
orientation local system of `𝒪(k)` is `ℤ/2`. -/
def twistedHomology₀TwistCoreAddEquivOfOdd {k : ℤ} (hk : Odd k) :
    LocalCoefficientSystem.twistedHomology.{0, 0, 0}
      (VectorBundleOrientationCover.signLocalSystem ℝ (twistCore (𝕜 := ℝ) k).Fiber ℤ
        ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)) 0 ≃+ ZMod 2 :=
  -- The projective line `OnePoint ℝ` is a connected one-dimensional manifold, hence
  -- path-connected and locally path-connected.
  haveI : LocallyPathConnectedSpace (OnePoint ℝ) := ChartedSpace.locallyPathConnectedSpace ℝ _
  haveI : PathConnectedSpace (OnePoint ℝ) := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  (VectorBundleOrientationCover.twistedHomology₀SignLocalSystemEquivOfIsEmpty
    ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)
    (isEmpty_vectorBundleOrientation_twistCore_of_odd hk) (b := ((0 : ℝ) : OnePoint ℝ))
    (Basis.singleton (Fin 1) ℝ).orientation).toAddEquiv.trans
    (Int.quotientSpanNatEquivZMod 2).toAddEquiv

/-- **The constant coefficients give the wrong zeroth homology for the Möbius line.** For odd `k`,
the zeroth homology of `OnePoint ℝ` with integer coefficients twisted by the orientation local
system of `𝒪(k)` is not `ℤ`, the zeroth homology of the circle with constant integer
coefficients. -/
theorem not_nonempty_twistedHomology₀_twistCore_addEquiv_int_of_odd {k : ℤ} (hk : Odd k) :
    ¬ Nonempty (LocalCoefficientSystem.twistedHomology.{0, 0, 0}
      (VectorBundleOrientationCover.signLocalSystem ℝ (twistCore (𝕜 := ℝ) k).Fiber ℤ
        ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)) 0 ≃+ ℤ) := fun ⟨e⟩ ↦
  haveI := Finite.of_equiv _
    ((twistedHomology₀TwistCoreAddEquivOfOdd hk).symm.trans e).toEquiv
  not_finite ℤ

end OnePoint
