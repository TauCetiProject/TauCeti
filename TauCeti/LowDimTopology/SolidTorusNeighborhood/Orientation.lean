/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Unknot

/-!
# Orientation-preserving solid torus neighbourhoods in the three-sphere

The surgery coefficient of a Dehn filling of a knot exterior is read in the framing of a solid
torus neighbourhood `Φ : D² × S¹ → S³` (`TauCeti.FramedBoundaryTorus.value`): the slope `p / q` is
the class `p · μ + q · λ`, where the meridian `μ` is `t ↦ Φ (exp (2πit), 1)` and the longitude `λ`
is `t ↦ Φ (1, exp (2πit))`. Precomposing `Φ` with the reflection `(u, w) ↦ (conj u, w)` reverses
`μ` and keeps `λ`, so it changes every coefficient `r` into `-r`. The same holds in the preferred
framing (`TauCeti.IsSolidTorusNeighborhood.preferredFramedBoundaryTorus`), in which
`TauCeti.IsSolidTorusLinkNeighborhood.surgerySlope` reads surgery coefficients: its longitude is
`λ - n · μ` for the framing number `n` of `Φ`, and the reflection sends `μ` to `-μ` and `n` to
`-n`, so it fixes the preferred longitude and still turns `r` into `-r`. Surgery coefficients
therefore only have their usual meaning (Rolfsen, *Knots and Links*, 9F and 9G), and only
distinguish a surgered manifold from its mirror image, once `Φ` is required to preserve
orientation, for the orientation `(Re u, Im u, t)` of `D² × S¹ ∋ (u, exp (t i))`. With that
orientation the meridian `μ` has linking number `+1` with the core `t ↦ Φ (0, exp (t i))`.

This file states that condition for a solid torus in the unit sphere `S³` of a four-dimensional
real inner product space `E` with an orientation `o`. The sphere carries the boundary orientation
of the unit ball: a basis `(v₁, v₂, v₃)` of the tangent space at `p` is positive when
`(p, v₁, v₂, v₃)` is a positive basis of `E`, the outward normal `p` first. The map `Φ` is read
near the point `(0, 1)` of its core through `(u, t) ↦ Φ (u, exp (t i))`
(`TauCeti.SolidTorus.coreReading`), and `TauCeti.IsOrientationPreservingAtCore Φ o` asks that this
reading be differentiable at the origin with derivative `L` satisfying

`0 < o.volumeForm ![Φ (0, 1), L (1, 0), L (i, 0), L (0, 1)]`.

A topological embedding of a connected manifold either preserves or reverses orientation at every
point, and at a point where it is differentiable with invertible derivative it does so according
to the sign of the Jacobian, so for an embedding `Φ` this pointwise condition is the global one.
Neither fact is formalized here; the condition is the one at the core point, which is all that
surgery coefficients need. It is stated through a derivative in `E`, rather than through
`TauCeti.Manifold.Orientation.IsOrientationPreservingAt`, because the solid torus neighbourhoods of
`TauCeti.IsSolidTorusNeighborhood` are only topological embeddings, and neither `D² × S¹` nor `S³`
carries a chosen manifold orientation in this library.

The two orientations of `S³` give opposite answers
(`TauCeti.IsOrientationPreservingAtCore.not_neg`), and the standard neighbourhood
`TauCeti.unknotSolidTorus` of the unknot preserves the standard orientation of `ℝ⁴`
(`TauCeti.isOrientationPreservingAtCore_unknotSolidTorus`): at its core point `(1, 0, 0, 0)` its
derivative sends `(1, 0)`, `(i, 0)` and `(0, 1)` to the third, fourth and second basis vectors.

## Main definitions

* `TauCeti.SolidTorus.coreReading Φ`: the map `(u, t) ↦ Φ (u, exp (t i))`, read in `E`.
* `TauCeti.IsOrientationPreservingAtCore Φ o`: the solid torus `Φ` preserves orientation at the
  point `(0, 1)` of its core, for the boundary orientation of `S³` induced by `o`.

## Main results

* `TauCeti.isOrientationPreservingAtCore_iff`: the definition of
  `TauCeti.IsOrientationPreservingAtCore`, restated.
* `TauCeti.isOrientationPreservingAtCore_neg_iff`: `Φ` preserves the opposite orientation exactly
  when its reading at the core has a derivative with negative volume form.
* `TauCeti.IsOrientationPreservingAtCore.not_neg`: `Φ` does not preserve both orientations.
* `TauCeti.isOrientationPreservingAtCore_unknotSolidTorus`: the standard solid torus
  neighbourhood of the unknot preserves the standard orientation.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Sections 2E, 9F and 9G (meridians and
  longitudes of a framed solid torus, and the orientation conventions for surgery coefficients).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Chapter 15 (the boundary orientation, outward normal first).
-/

public section

noncomputable section

open Metric Complex Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

namespace SolidTorus

/-- A map `Φ` from the solid torus to the unit sphere of `E`, read near the point `(0, 1)` of
its core as the map `(u, t) ↦ Φ (u, exp (t i))` from `ℂ × ℝ` to `E`. It is extended by `0` off the
closed unit disc, which does not affect its derivative at the origin. -/
def coreReading (Φ : SolidTorus → sphere (0 : E) 1) (v : ℂ × ℝ) : E :=
  if hv : ‖v.1‖ ≤ 1 then (Φ (⟨v.1, mem_closedBall_zero_iff.2 hv⟩, Circle.exp v.2) : E) else 0

/-- On the closed unit disc the reading of `Φ` is `(u, t) ↦ Φ (u, exp (t i))`. -/
theorem coreReading_of_norm_le (Φ : SolidTorus → sphere (0 : E) 1) {v : ℂ × ℝ}
    (hv : ‖v.1‖ ≤ 1) :
    coreReading Φ v = Φ (⟨v.1, mem_closedBall_zero_iff.2 hv⟩, Circle.exp v.2) := by
  simp only [coreReading, hv, ↓reduceDIte]

/-- At the origin the reading of `Φ` is the core point `Φ (0, 1)`. -/
@[simp]
theorem coreReading_zero (Φ : SolidTorus → sphere (0 : E) 1) :
    coreReading Φ 0 = Φ (0, 1) := by
  rw [coreReading_of_norm_le Φ (by simp)]
  congr
  simp

/-- Near the origin the reading of `Φ` is `(u, t) ↦ Φ (u, exp (t i))`. -/
theorem eventually_coreReading_eq (Φ : SolidTorus → sphere (0 : E) 1) :
    ∀ᶠ v in nhds (0 : ℂ × ℝ), ∃ hv : ‖v.1‖ ≤ 1,
      coreReading Φ v = Φ (⟨v.1, mem_closedBall_zero_iff.2 hv⟩, Circle.exp v.2) := by
  have hball : {v : ℂ × ℝ | ‖v.1‖ < 1} ∈ nhds (0 : ℂ × ℝ) :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).mem_nhds (by simp)
  filter_upwards [hball] with v hv
  exact ⟨hv.le, coreReading_of_norm_le Φ hv.le⟩

end SolidTorus

variable [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 4)]

/-- A map `Φ : D² × S¹ → S³` into the unit sphere of `E` **preserves orientation at its core
point** `(0, 1)` when its reading `(u, t) ↦ Φ (u, exp (t i))` (`TauCeti.SolidTorus.coreReading`)
has a derivative `L` at the origin with

`0 < o.volumeForm ![Φ (0, 1), L (1, 0), L (i, 0), L (0, 1)]`.

So the derivative carries the orientation `(Re u, Im u, t)` of the solid torus to the boundary
orientation of `S³` as the unit sphere of `E` oriented by `o`, the outward normal `Φ (0, 1)` first.
For a solid torus neighbourhood of a knot this is the orientation for which surgery coefficients
read in the framing of `Φ` follow the usual conventions: the meridian `t ↦ Φ (exp (2πit), 1)` has
linking number `+1` with the core. -/
def IsOrientationPreservingAtCore (Φ : SolidTorus → sphere (0 : E) 1)
    (o : Orientation ℝ E (Fin 4)) : Prop :=
  ∃ L : ℂ × ℝ →L[ℝ] E, HasFDerivAt (SolidTorus.coreReading Φ) L 0 ∧
    0 < o.volumeForm ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)]

variable {Φ : SolidTorus → sphere (0 : E) 1} {o : Orientation ℝ E (Fin 4)}

/-- `Φ` preserves orientation at its core point exactly when its reading there has a derivative
on which the volume form of `o`, with the outward normal first, is positive. -/
theorem isOrientationPreservingAtCore_iff :
    IsOrientationPreservingAtCore Φ o ↔ ∃ L : ℂ × ℝ →L[ℝ] E,
      HasFDerivAt (SolidTorus.coreReading Φ) L 0 ∧
        0 < o.volumeForm ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)] :=
  Iff.rfl

/-- `Φ` preserves the opposite orientation at its core point exactly when the volume form of `o`
is negative on the outward normal and the derivative of its reading there. -/
theorem isOrientationPreservingAtCore_neg_iff :
    IsOrientationPreservingAtCore Φ (-o) ↔ ∃ L : ℂ × ℝ →L[ℝ] E,
      HasFDerivAt (SolidTorus.coreReading Φ) L 0 ∧
        o.volumeForm ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)] < 0 := by
  simp only [isOrientationPreservingAtCore_iff, o.volumeForm_neg_orientation,
    neg_apply, neg_pos]

/-- A solid torus does not preserve both orientations of `S³` at its core point: the derivative
there is unique, and reversing `o` negates its volume form. -/
theorem IsOrientationPreservingAtCore.not_neg (h : IsOrientationPreservingAtCore Φ o) :
    ¬IsOrientationPreservingAtCore Φ (-o) := by
  rw [isOrientationPreservingAtCore_neg_iff]
  rintro ⟨L', hL', hneg⟩
  obtain ⟨L, hL, hpos⟩ := isOrientationPreservingAtCore_iff.1 h
  rw [hL'.unique hL] at hneg
  exact hneg.not_gt hpos

/-! ### The standard neighbourhood of the unknot -/

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- The core point `(0, 1)` of the standard neighbourhood of the unknot is the first standard
basis vector of `ℝ⁴`. -/
private theorem coe_unknotSolidTorus_zero_one :
    (unknotSolidTorus (0, 1) : EuclideanSpace ℝ (Fin 4)) = EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp

/-- The reading of the standard neighbourhood `(u, ζ) ↦ (ζ, u) / √(1 + ‖u‖ ^ 2)` of the unknot
at its core has a derivative at the origin sending `(1, 0)`, `(i, 0)` and `(0, 1)` to the third,
fourth and second standard basis vectors of `ℝ⁴`. -/
private theorem exists_hasFDerivAt_coreReading_unknotSolidTorus :
    ∃ L : ℂ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4),
      HasFDerivAt (SolidTorus.coreReading unknotSolidTorus) L 0 ∧
        L (1, 0) = EuclideanSpace.single 2 1 ∧ L (I, 0) = EuclideanSpace.single 3 1 ∧
          L (0, 1) = EuclideanSpace.single 1 1 := by
  -- The reading is `A ∘ F` near the origin, for the linear isometry `A : ℂ × ℂ → ℝ⁴` and
  -- `F (u, t) = (√(1 + ‖u‖ ^ 2))⁻¹ • (exp (t i), u)`.
  let A : ℂ × ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    complexProdToEuclideanFour.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.toContinuousLinearMap
  let c : ℂ × ℝ → ℝ := fun v ↦ (√(1 + ‖v.1‖ ^ 2))⁻¹
  let G : ℂ × ℝ → ℂ × ℂ := fun v ↦ (exp ((v.2 : ℂ) * I), v.1)
  have hsq : HasFDerivAt (fun v : ℂ × ℝ ↦ √(1 + ‖v.1‖ ^ 2)) _ (0 : ℂ × ℝ) :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ)).norm_sq.const_add 1).sqrt (by positivity)
  have hc : HasFDerivAt c _ (0 : ℂ × ℝ) :=
    (hasFDerivAt_inv (𝕜 := ℝ) (by positivity)).comp (0 : ℂ × ℝ) hsq
  have hG : HasFDerivAt G _ (0 : ℂ × ℝ) :=
    ((((ofRealCLM.hasFDerivAt).comp _ hasFDerivAt_snd).mul_const I).cexp).prodMk hasFDerivAt_fst
  have hF := A.hasFDerivAt.comp (0 : ℂ × ℝ) (hc.smul hG)
  refine ⟨_, hF.congr_of_eventuallyEq ?_, ?_, ?_, ?_⟩
  · filter_upwards [SolidTorus.eventually_coreReading_eq unknotSolidTorus] with v ⟨hv, heq⟩
    rw [heq, coe_unknotSolidTorus_apply]
    simp [A, c, G, Circle.coe_exp]
  all_goals
    ext i
    fin_cases i <;> simp [A, c, G]

/-- In the standard orientation of `ℝ⁴`, the basis `(e₁, e₃, e₄, e₂)` is positive: its
determinant is `1`. -/
private theorem volumeForm_single_zero_two_three_one :
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.orientation.volumeForm
      ![EuclideanSpace.single 0 1, EuclideanSpace.single 2 1, EuclideanSpace.single 3 1,
        EuclideanSpace.single 1 1] = 1 := by
  rw [Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 4) ℝ) rfl]
  simp [Basis.det_apply, Basis.toMatrix_apply, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

/-- The standard solid torus neighbourhood `(u, ζ) ↦ (ζ, u) / √(1 + ‖u‖ ^ 2)` of the unknot
preserves the standard orientation of `ℝ⁴` at its core point `(1, 0, 0, 0)`: the derivative of its
reading there sends `(1, 0)`, `(i, 0)` and `(0, 1)` to the third, fourth and second standard
basis vectors, and the determinant of `(e₁, e₃, e₄, e₂)` is `1`. -/
theorem isOrientationPreservingAtCore_unknotSolidTorus :
    IsOrientationPreservingAtCore unknotSolidTorus
      (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.orientation := by
  obtain ⟨L, hL, h₁, hI, ht⟩ := exists_hasFDerivAt_coreReading_unknotSolidTorus
  refine isOrientationPreservingAtCore_iff.2 ⟨L, hL, ?_⟩
  rw [coe_unknotSolidTorus_zero_one, h₁, hI, ht, volumeForm_single_zero_two_three_one]
  exact one_pos

end TauCeti
