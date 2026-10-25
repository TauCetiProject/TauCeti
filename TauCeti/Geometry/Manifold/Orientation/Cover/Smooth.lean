/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Cover.Basic
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.Instances.Comap

/-!
# The canonical orientation of the smooth orientation cover

The orientation cover receives its smooth structure by pulling charts back along its covering
projection. At a point `(x, o)`, its canonical tangent orientation is the inverse image of `o`
under the derivative of the projection. Thus the projection carries that tangent orientation
to the orientation recorded by the point, even when the base manifold is not orientable.
The deck involution is a smooth diffeomorphism reversing this canonical orientation.

The construction works for every finite-dimensional real model with corners. It uses the
existing topology of the orientation cover and the chart-pullback construction for local
homeomorphisms, rather than putting the sigma topology on the family of tangent orientations.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218, Springer, 2013,
  Chapter 15, The Orientation Covering.
-/

public section

noncomputable section

open Bundle Filter Module
open TauCeti.Manifold.Orientation
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.OrientationCover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The charts of the orientation cover are pulled back along its projection. -/
instance instChartedSpace : ChartedSpace H (OrientationCover I M) :=
  (isCoveringMap_proj I M).isLocalHomeomorph.chartedSpaceComap

/-- A chart of the cover reads a point by projecting it into the corresponding base chart. -/
theorem chartAt_apply (p q : OrientationCover I M) :
    chartAt H p q = chartAt H p.proj q.proj :=
  (isCoveringMap_proj I M).isLocalHomeomorph.chartAt_chartedSpaceComap_apply p q

/-- The orientation cover of a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifold {n : ℕ∞ω} [IsManifold I n M] :
    IsManifold I n (OrientationCover I M) :=
  (isCoveringMap_proj I M).isLocalHomeomorph.isManifold_chartedSpaceComap

/-- The covering projection is a local diffeomorphism. -/
theorem isLocalDiffeomorph_proj {n : ℕ∞ω} :
    IsLocalDiffeomorph I I n (VectorBundleOrientationCover.proj : OrientationCover I M → M) :=
  (isCoveringMap_proj I M).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

/-- The projection of the orientation cover is smooth. -/
theorem contMDiff_proj {n : ℕ∞ω} :
    ContMDiff I I n (VectorBundleOrientationCover.proj : OrientationCover I M → M) :=
  (isCoveringMap_proj I M).isLocalHomeomorph.contMDiff_chartedSpaceComap

private def projDerivEquiv (p : OrientationCover I M) :
    TangentSpace I p ≃L[ℝ] TangentSpace I p.proj :=
  (isLocalDiffeomorph_proj (I := I) (M := M) (n := 1) |>.isInvertible_mfderiv one_ne_zero p).choose

private theorem projDerivEquiv_coe (p : OrientationCover I M) :
    (projDerivEquiv p).toContinuousLinearMap =
      mfderiv I I (VectorBundleOrientationCover.proj : OrientationCover I M → M) p :=
  (isLocalDiffeomorph_proj (I := I) (M := M) (n := 1)
    |>.isInvertible_mfderiv one_ne_zero p).choose_spec

private def tautologicalTangentOrientation :
    VectorBundleOrientation E (TangentSpace I : OrientationCover I M → Type _)
      (Fin (finrank ℝ E)) where
  toFun p := _root_.Orientation.map _ (projDerivEquiv p).symm.toLinearEquiv p.orientation
  eventually_mapOrientation_eq' p := by
    apply Orientation.eventually_mapOrientation_map_symm_eq (contMDiff_proj (n := 1) p)
      projDerivEquiv projDerivEquiv_coe (Fintype.card_fin _) (fun q ↦ q.orientation)
    have hp := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) p.proj
    have hs : p ∈ VectorBundleOrientationCover.sheet
        (trivializationAt E (TangentSpace I) p.proj)
        ((trivializationAt E (TangentSpace I) p.proj).mapOrientation _ hp p.orientation) :=
      VectorBundleOrientationCover.mem_sheet_iff.mpr ⟨hp, rfl⟩
    filter_upwards [(VectorBundleOrientationCover.isOpen_sheet_trivializationAt _ _).mem_nhds hs]
      with q hq hmem
    exact (VectorBundleOrientationCover.mem_sheet_iff.mp hq).choose_spec

/-- The canonical orientation of the orientation cover: the derivative of the projection at
`(x, o)` transports its tangent orientation to `o`. -/
def canonicalOrientation : Orientation I (OrientationCover I M) (Fin (finrank ℝ E)) :=
  Orientation.ofVectorBundleOrientation (Module.finBasis ℝ E).orientation (Fintype.card_fin _)
    tautologicalTangentOrientation

/-- The tangent orientation of the cover at `(x, o)` is the pullback of `o` through the
derivative of the projection. This formula is independent of the equivalence representing it. -/
theorem orientationAt_canonicalOrientation (p : OrientationCover I M)
    (D : TangentSpace I p ≃L[ℝ] TangentSpace I p.proj)
    (hD : D.toContinuousLinearMap =
      mfderiv I I (VectorBundleOrientationCover.proj : OrientationCover I M → M) p) :
    (canonicalOrientation (I := I) (M := M)).orientationAt p =
      _root_.Orientation.map _ D.symm.toLinearEquiv p.orientation := by
  have he : projDerivEquiv p = D :=
    ContinuousLinearEquiv.coe_injective ((projDerivEquiv_coe p).trans hD.symm)
  simp only [canonicalOrientation, Orientation.orientationAt_ofVectorBundleOrientation,
    VectorBundleOrientation.coe_mk, tautologicalTangentOrientation, he]

/-- The derivative of the projection carries the canonical tangent orientation to the
orientation stored by the point of the cover. -/
theorem map_orientationAt_canonicalOrientation (p : OrientationCover I M)
    (D : TangentSpace I p ≃L[ℝ] TangentSpace I p.proj)
    (hD : D.toContinuousLinearMap =
      mfderiv I I (VectorBundleOrientationCover.proj : OrientationCover I M → M) p) :
    _root_.Orientation.map _ D.toLinearEquiv
      ((canonicalOrientation (I := I) (M := M)).orientationAt p) = p.orientation := by
  rw [orientationAt_canonicalOrientation p D hD, ContinuousLinearEquiv.toLinearEquiv_symm,
    ← _root_.Orientation.map_symm, Equiv.apply_symm_apply]

/-- Every smooth manifold's orientation cover is orientable, whether or not the base is. -/
theorem orientable : Orientable I (OrientationCover I M) :=
  ⟨⟨canonicalOrientation⟩⟩

/-- The orientation-changing deck involution of the cover is smooth. -/
theorem contMDiff_deck {n : ℕ∞ω} :
    ContMDiff I I n (VectorBundleOrientationCover.deck : OrientationCover I M → _) := by
  apply (isCoveringMap_proj I M).isLocalHomeomorph.contMDiff_chartedSpaceComap_iff.mpr
  refine ⟨VectorBundleOrientationCover.deck.continuous, ?_⟩
  simpa only [Function.comp_def, VectorBundleOrientationCover.proj_deck] using
    (contMDiff_proj (I := I) (M := M) (n := n))

/-- The smooth deck involution as a diffeomorphism of the orientation cover. -/
def deckDiffeomorph (n : ℕ∞ω) : (OrientationCover I M) ≃ₘ^n⟮I, I⟯ (OrientationCover I M) where
  toFun := VectorBundleOrientationCover.deck
  invFun := VectorBundleOrientationCover.deck
  left_inv := VectorBundleOrientationCover.deck_deck
  right_inv := VectorBundleOrientationCover.deck_deck
  contMDiff_toFun := contMDiff_deck
  contMDiff_invFun := contMDiff_deck

/-- The deck diffeomorphism is the original orientation-changing deck involution. -/
@[simp]
theorem deckDiffeomorph_apply (n : ℕ∞ω) (p : OrientationCover I M) :
    deckDiffeomorph n p = VectorBundleOrientationCover.deck p :=
  (rfl)

/-- The inverse deck diffeomorphism is the same involution. -/
@[simp]
theorem deckDiffeomorph_symm_apply (n : ℕ∞ω) (p : OrientationCover I M) :
    (deckDiffeomorph n).symm p = VectorBundleOrientationCover.deck p :=
  (rfl)

/-- The deck involution reverses the canonical orientation of the orientation cover. -/
theorem isOrientationReversingAt_deck (p : OrientationCover I M) :
    IsOrientationReversingAt canonicalOrientation canonicalOrientation
      VectorBundleOrientationCover.deck p := by
  rw [isOrientationReversingAt_iff]
  let pr : OrientationCover I M → M := VectorBundleOrientationCover.proj
  have hδ : (⇑(deckDiffeomorph (I := I) (M := M) 1)) =
      VectorBundleOrientationCover.deck := funext (deckDiffeomorph_apply 1)
  have hinv : (mfderiv I I VectorBundleOrientationCover.deck p).IsInvertible := by
    rw [← hδ]
    exact (deckDiffeomorph 1).isInvertible_mfderiv one_ne_zero
  have hπδ : pr ∘ VectorBundleOrientationCover.deck = pr :=
    funext VectorBundleOrientationCover.proj_deck
  have hchain := mfderiv_comp p
    ((contMDiff_proj (I := I) (M := M) (n := 1)).mdifferentiableAt one_ne_zero)
    ((contMDiff_deck (I := I) (M := M) (n := 1)).mdifferentiableAt one_ne_zero)
  rw [hπδ] at hchain
  -- Name the image point and identify its base point before comparing derivatives. This
  -- keeps the equality in the actual tangent space, with no identification of distinct fibres.
  generalize hq : VectorBundleOrientationCover.deck p = q at *
  obtain ⟨x, o⟩ := q
  have hx : x = p.proj := by
    rw [← VectorBundleOrientationCover.proj_deck p]
    exact congrArg VectorBundleOrientationCover.proj hq.symm
  subst x
  let A := hinv.choose
  have hA := hinv.choose_spec
  have hcomp : A.trans (projDerivEquiv (⟨p.proj, o⟩ : OrientationCover I M)) =
      projDerivEquiv p := by
    apply ContinuousLinearEquiv.coe_injective
    rw [← ContinuousLinearEquiv.comp_coe, hA, projDerivEquiv_coe, projDerivEquiv_coe]
    exact hchain.symm
  have ho : o = -p.orientation := VectorBundleOrientationCover.mk_eq_mk_iff.mp
    (hq.symm.trans (VectorBundleOrientationCover.deck_apply p))
  refine ⟨A, hA, ?_⟩
  apply (_root_.Orientation.map _
    (projDerivEquiv (⟨p.proj, o⟩ : OrientationCover I M)).toLinearEquiv).injective
  rw [_root_.Orientation.map_neg,
    map_orientationAt_canonicalOrientation _ _ (projDerivEquiv_coe _),
    ← _root_.Orientation.map_trans]
  have hlin := congrArg ContinuousLinearEquiv.toLinearEquiv hcomp
  rw [ContinuousLinearEquiv.trans_toLinearEquiv] at hlin
  rw [hlin, map_orientationAt_canonicalOrientation p _ (projDerivEquiv_coe _)]
  exact ((congrArg Neg.neg ho).trans (neg_neg p.orientation)).symm

end TauCeti.Manifold.OrientationCover
