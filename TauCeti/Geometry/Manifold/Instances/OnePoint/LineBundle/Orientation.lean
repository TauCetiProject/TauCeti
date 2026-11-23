/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Topology.VectorBundle.Orientation.TwistedHomology.Basic
import TauCeti.Topology.VectorBundle.Orientation.Atlas

/-!
# Orientability of the real line bundles `𝒪(k)` and the Möbius line

Over `ℝ`, the projective line `OnePoint ℝ` is a circle and the line bundle `𝒪(k)` on it
(`OnePoint.twistCore`) is glued from two trivial lines along the transition `z ↦ z⁻ᵏ` on the
overlap `ℝ ∖ {0}` of the two charts. This transition changes sign between the two components of the
overlap exactly when `k` is odd. So `𝒪(k)` is orientable if and only if `k` is even
(`OnePoint.nonempty_vectorBundleOrientation_twistCore_iff`): for odd `k` it is a Möbius line. For
even `k` the two charts form a positive atlas (`VectorBundleCore.orientationOfPositiveAtlas`); for
odd `k` the transition is `1` at `1` and `-1` at `-1`, while both chart domains are connected
(`TauCeti.VectorBundleOrientation.isEmpty_of_det_coordChangeL_pos_of_neg`).

For a nonorientable bundle over a connected, locally path-connected base, the zeroth homology of
the orientation local system with integer coefficients is `ℤ/2`
(`TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo`). So for odd
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
* `OnePoint.twistedHomology₀TwistCoreAddEquivOfOdd_ιTwistedHomology₀`: it sends the class of an
  element of a fibre to the residue modulo `2` of its value at either orientation of that fibre.
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

open Bundle Module Set TauCeti

namespace OnePoint

/-- The cardinality condition relating the index type `Fin 1` of orientations of the line `ℝ`
to its dimension. -/
private theorem card_fin_one_eq_finrank : Fintype.card (Fin 1) = finrank ℝ ℝ :=
  (Fintype.card_fin 1).trans (finrank_self ℝ).symm

/-- The domain of each preferred chart of `OnePoint ℝ` is the image of `ℝ` under the inverse
chart, hence preconnected. -/
private theorem isPreconnected_chart_source (x : OnePoint ℝ) :
    IsPreconnected (chartAt ℝ x).source := by
  have ht : (chartAt ℝ x).target = univ := by
    induction x using OnePoint.rec <;> simp
  rw [← (chartAt ℝ x).symm_image_target_eq_source, ht]
  exact isPreconnected_univ.image _ (ht ▸ (chartAt ℝ x).continuousOn_symm)

/-- For even `k`, the transition of `𝒪(k)` is positive wherever it is defined. -/
private theorem twistTransition_pos_of_even {k : ℤ} (hk : Even k) {x y p : OnePoint ℝ}
    (hx : p ∈ (chartAt ℝ x).source) (hy : p ∈ (chartAt ℝ y).source) :
    0 < twistTransition k x y p := by
  rw [twistTransition_def]
  by_cases h0 : affineChart p = 0
  · simp [twistIndex_eq_of_affineChart_eq_zero hx h0, twistIndex_eq_of_affineChart_eq_zero hy h0]
  · exact (hk.mul_right _).zpow_pos h0

/-- For odd `k`, the line bundle `𝒪(k)` on `OnePoint ℝ` is not orientable. -/
private theorem isEmpty_vectorBundleOrientation_twistCore_of_odd {k : ℤ} (hk : Odd k) :
    IsEmpty (VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) k).Fiber (Fin 1)) := by
  have : MemTrivializationAtlas ((twistCore (𝕜 := ℝ) k).localTriv ((0 : ℝ) : OnePoint ℝ)) :=
    ⟨⟨_, rfl⟩⟩
  have : MemTrivializationAtlas ((twistCore (𝕜 := ℝ) k).localTriv ∞) := ⟨⟨_, rfl⟩⟩
  have h₀ (w : ℝ) : (w : OnePoint ℝ) ∈ (chartAt ℝ ((0 : ℝ) : OnePoint ℝ)).source := by simp
  have hInf {w : ℝ} (hw : w ≠ 0) : (w : OnePoint ℝ) ∈ (chartAt ℝ (∞ : OnePoint ℝ)).source := by
    simpa using hw
  -- The transition `w⁻ᵏ` from the affine to the inverted chart is `1` at `w = 1` and `-1` at
  -- `w = -1`.
  refine VectorBundleOrientation.isEmpty_of_det_coordChangeL_pos_of_neg card_fin_one_eq_finrank
    ((twistCore k).localTriv ((0 : ℝ) : OnePoint ℝ)) ((twistCore k).localTriv ∞)
    (isPreconnected_chart_source _) (isPreconnected_chart_source _)
    (twistCore_localTriv_baseSet k _).ge (twistCore_localTriv_baseSet k _).ge (h₀ 1)
    (hInf one_ne_zero) (h₀ (-1)) (hInf (neg_ne_zero.2 one_ne_zero)) ?_ ?_
  · rw [det_coordChangeL_localTriv_twistCore k (h₀ 1) (hInf one_ne_zero)]
    simp
  · rw [det_coordChangeL_localTriv_twistCore k (h₀ (-1)) (hInf (neg_ne_zero.2 one_ne_zero))]
    simp [hk.neg.neg_one_zpow]

/-- **The line bundle `𝒪(k)` on the real projective line is orientable exactly when `k` is even.**
The transition `z ↦ z⁻ᵏ` between its two charts is positive on the whole overlap `ℝ ∖ {0}` when
`k` is even, and has opposite signs on the two half-lines when `k` is odd. For odd `k` this is the
Möbius line. -/
theorem nonempty_vectorBundleOrientation_twistCore_iff (k : ℤ) :
    Nonempty (VectorBundleOrientation ℝ (twistCore (𝕜 := ℝ) k).Fiber (Fin 1)) ↔ Even k := by
  refine ⟨fun ⟨o⟩ ↦ ?_, fun hk ↦ ?_⟩
  · by_contra hk
    exact (isEmpty_vectorBundleOrientation_twistCore_of_odd (Int.not_even_iff_odd.1 hk)).false o
  · -- The preferred charts form a positive atlas.
    exact ⟨(twistCore (𝕜 := ℝ) k).orientationOfPositiveAtlas (Basis.singleton (Fin 1) ℝ).orientation
      card_fin_one_eq_finrank (S := univ)
      (fun x ↦ ⟨x, mem_univ _, (twistCore_baseSet k x).ge (mem_chart_source ℝ x)⟩)
      fun i _ j _ x ⟨hi, hj⟩ ↦ by
        rw [twistCore_baseSet] at hi hj
        rw [det_coordChange_twistCore]
        exact twistTransition_pos_of_even hk hi hj⟩

/-- **The zeroth homology of the circle twisted by the orientation of the Möbius line is `ℤ/2`.**
For odd `k`, the zeroth singular homology of `OnePoint ℝ` with integer coefficients twisted by the
orientation local system of `𝒪(k)` is `ℤ/2`
(`OnePoint.twistedHomology₀TwistCoreAddEquivOfOdd_ιTwistedHomology₀`,
`OnePoint.twistedHomology₀TwistCoreAddEquivOfOdd_symm_intCast`). -/
def twistedHomology₀TwistCoreAddEquivOfOdd {k : ℤ} (hk : Odd k) :
    LocalCoefficientSystem.twistedHomology.{0, 0, 0}
      (VectorBundleOrientationCover.signLocalSystem ℝ (twistCore (𝕜 := ℝ) k).Fiber ℤ
        ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)) 0 ≃+ ZMod 2 :=
  -- The projective line `OnePoint ℝ` is a connected one-dimensional manifold, hence locally
  -- path-connected.
  haveI : LocallyPathConnectedSpace (OnePoint ℝ) := ChartedSpace.locallyPathConnectedSpace ℝ _
  (VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo card_fin_one_eq_finrank
    (isEmpty_vectorBundleOrientation_twistCore_of_odd hk) (b := ((0 : ℝ) : OnePoint ℝ))
    (Basis.singleton (Fin 1) ℝ).orientation).toAddEquiv.trans
    (Int.quotientSpanNatEquivZMod 2).toAddEquiv

/-- The identification of the twisted `H₀` with `ℤ/2` sends the class of an element `a` of the
fibre over any point `b` to the residue modulo `2` of its value at any orientation `o` of the fibre
of `𝒪(k)` over `b`. -/
theorem twistedHomology₀TwistCoreAddEquivOfOdd_ιTwistedHomology₀ {k : ℤ} (hk : Odd k)
    {b : OnePoint ℝ} (o : Orientation ℝ ((twistCore (𝕜 := ℝ) k).Fiber b) (Fin 1))
    (a : (VectorBundleOrientationCover.signLocalSystem ℝ (twistCore (𝕜 := ℝ) k).Fiber ℤ
      ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)).obj (FundamentalGroupoid.mk b)) :
    twistedHomology₀TwistCoreAddEquivOfOdd hk (LocalCoefficientSystem.ιTwistedHomology₀ _ b a) =
      (VectorBundleOrientationCover.signLocalSystemFiberEquiv
        ((Fintype.card_fin 1).trans (finrank_self ℝ).symm) o a : ℤ) := by
  have : LocallyPathConnectedSpace (OnePoint ℝ) := ChartedSpace.locallyPathConnectedSpace ℝ _
  rw [twistedHomology₀TwistCoreAddEquivOfOdd, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  exact (congrArg (Int.quotientSpanNatEquivZMod 2) <|
    VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀ _ _ _ o a).trans
    (RingHom.congr_fun (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 2) _)

/-- The inverse identification of the twisted `H₀` with `ℤ/2` sends the residue of `r` to the
class of the element of the fibre over any point `b` whose value at any orientation `o` of the
fibre of `𝒪(k)` over `b` is `r`. -/
theorem twistedHomology₀TwistCoreAddEquivOfOdd_symm_intCast {k : ℤ} (hk : Odd k)
    {b : OnePoint ℝ} (o : Orientation ℝ ((twistCore (𝕜 := ℝ) k).Fiber b) (Fin 1)) (r : ℤ) :
    (twistedHomology₀TwistCoreAddEquivOfOdd hk).symm (r : ZMod 2) =
      LocalCoefficientSystem.ιTwistedHomology₀ _ b
        ((VectorBundleOrientationCover.signLocalSystemFiberEquiv
          ((Fintype.card_fin 1).trans (finrank_self ℝ).symm) o).symm r) :=
  (AddEquiv.symm_apply_eq _).2 (by
    rw [twistedHomology₀TwistCoreAddEquivOfOdd_ιTwistedHomology₀ hk o,
      LinearEquiv.apply_symm_apply])

/-- **The constant coefficients give the wrong zeroth homology for the Möbius line.** For odd `k`,
the zeroth homology of `OnePoint ℝ` with integer coefficients twisted by the orientation local
system of `𝒪(k)` is not `ℤ`, the zeroth homology of the circle with constant integer
coefficients. -/
theorem not_nonempty_twistedHomology₀_twistCore_addEquiv_int_of_odd {k : ℤ} (hk : Odd k) :
    ¬ Nonempty (LocalCoefficientSystem.twistedHomology.{0, 0, 0}
      (VectorBundleOrientationCover.signLocalSystem ℝ (twistCore (𝕜 := ℝ) k).Fiber ℤ
        ((Fintype.card_fin 1).trans (finrank_self ℝ).symm)) 0 ≃+ ℤ) := fun ⟨e⟩ ↦
  have : LocallyPathConnectedSpace (OnePoint ℝ) := ChartedSpace.locallyPathConnectedSpace ℝ _
  (isEmpty_vectorBundleOrientation_twistCore_of_odd hk).false
    ((VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv
      card_fin_one_eq_finrank two_ne_zero).2 ⟨e.toIntLinearEquiv⟩).some

end OnePoint
