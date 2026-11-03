/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.InnerProductSpace.Orientation
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Sphere
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

Every `C²` embedded circle in `S³` has orientation-preserving solid torus neighbourhoods, inside
any neighbourhood of its image
(`TauCeti.exists_isSolidTorusNeighborhood_isOrientationPreservingAtCore`). The tubular
neighbourhood of `TauCeti.exists_isSolidTorusNeighborhood_sphere_hasFDerivAt_coreReading` has an
injective derivative `L` at the core, valued in the tangent space of `S³`, so the outward normal
followed by `L (1, 0)`, `L (i, 0)`, `L (0, 1)` is a basis of `E` and the volume form does not
vanish on it. If it is negative, precomposing with the reflection `(u, w) ↦ (conj u, w)` negates
`L (i, 0)` and fixes the other vectors, which makes it positive.

## Main definitions

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
* `TauCeti.isOrientationPreservingAtCore_comp_conjDisc_iff`: reflecting the disc of a solid torus
  (`TauCeti.SolidTorus.conjDisc`) gives the opposite orientation at its core point.
* `TauCeti.exists_isSolidTorusNeighborhood_isOrientationPreservingAtCore`: every `C²` embedded
  circle in `S³` has solid torus neighbourhoods preserving either orientation at their core point,
  inside any neighbourhood of its image.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Sections 2E, 9F and 9G (meridians and
  longitudes of a framed solid torus, and the orientation conventions for surgery coefficients).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Chapter 15 (the boundary orientation, outward normal first).
-/

public section

noncomputable section

open Metric Complex Module Function Topology Set
open scoped ComplexConjugate RealInnerProductSpace Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

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
  ∃ L : ℂ × ℝ →L[ℝ] E, HasFDerivAt (SolidTorus.coreReading fun q ↦ (Φ q : E)) L 0 ∧
    0 < o.volumeForm ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)]

variable {Φ : SolidTorus → sphere (0 : E) 1} {o : Orientation ℝ E (Fin 4)}

/-- `Φ` preserves orientation at its core point exactly when its reading there has a derivative
on which the volume form of `o`, with the outward normal first, is positive. -/
theorem isOrientationPreservingAtCore_iff :
    IsOrientationPreservingAtCore Φ o ↔ ∃ L : ℂ × ℝ →L[ℝ] E,
      HasFDerivAt (SolidTorus.coreReading fun q ↦ (Φ q : E)) L 0 ∧
        0 < o.volumeForm ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)] :=
  Iff.rfl

/-- `Φ` preserves the opposite orientation at its core point exactly when the volume form of `o`
is negative on the outward normal and the derivative of its reading there. -/
theorem isOrientationPreservingAtCore_neg_iff :
    IsOrientationPreservingAtCore Φ (-o) ↔ ∃ L : ℂ × ℝ →L[ℝ] E,
      HasFDerivAt (SolidTorus.coreReading fun q ↦ (Φ q : E)) L 0 ∧
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
      HasFDerivAt (SolidTorus.coreReading fun q ↦ (unknotSolidTorus q : EuclideanSpace ℝ (Fin 4)))
        L 0 ∧
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
  · filter_upwards [SolidTorus.eventually_coreReading_eq
      fun q ↦ (unknotSolidTorus q : EuclideanSpace ℝ (Fin 4))] with v ⟨hv, heq⟩
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

/-! ### Reflecting the disc -/

/-- The reflection `(u, t) ↦ (conj u, t)` of `ℂ × ℝ`. -/
private def conjProd : ℂ × ℝ →L[ℝ] ℂ × ℝ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).prodMap (ContinuousLinearMap.id ℝ ℝ)

@[simp]
private theorem conjProd_apply (v : ℂ × ℝ) : conjProd v = (conj v.1, v.2) :=
  (rfl)

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 4)] in
/-- The reading at the core of `Φ` precomposed with the reflection `(u, w) ↦ (conj u, w)` is the
reading of `Φ` precomposed with `(u, t) ↦ (conj u, t)`. -/
private theorem coreReading_comp_conjDisc (Φ : SolidTorus → E) :
    SolidTorus.coreReading (Φ ∘ SolidTorus.conjDisc) =
      SolidTorus.coreReading Φ ∘ conjProd := by
  funext v
  by_cases hv : ‖v.1‖ ≤ 1
  · have hv' : ‖(conjProd v).1‖ ≤ 1 := by simpa
    rw [SolidTorus.coreReading_of_norm_le _ hv, Function.comp_apply, Function.comp_apply,
      SolidTorus.coreReading_of_norm_le _ hv']
    exact congrArg Φ (Prod.ext (Subtype.ext (by simp)) (by simp))
  · have hv' : ¬‖(conjProd v).1‖ ≤ 1 := by simpa using hv
    rw [SolidTorus.coreReading_of_not_norm_le _ hv, Function.comp_apply,
      SolidTorus.coreReading_of_not_norm_le _ hv']

/-- If `Φ` preserves the opposite orientation at its core point, then its precomposition with the
reflection `(u, w) ↦ (conj u, w)` preserves the orientation. -/
private theorem IsOrientationPreservingAtCore.comp_conjDisc_of_neg
    (h : IsOrientationPreservingAtCore Φ (-o)) :
    IsOrientationPreservingAtCore (Φ ∘ SolidTorus.conjDisc) o := by
  obtain ⟨L, hL, hneg⟩ := isOrientationPreservingAtCore_neg_iff.1 h
  refine ⟨L.comp conjProd, ?_, ?_⟩
  · have hread := coreReading_comp_conjDisc fun q ↦ (Φ q : E)
    simp only [Function.comp_def] at hread ⊢
    rw [hread]
    have hL' : HasFDerivAt (SolidTorus.coreReading fun q ↦ (Φ q : E)) L (conjProd 0) := by
      rwa [map_zero]
    exact hL'.comp 0 conjProd.hasFDerivAt
  · -- The reflection negates the derivative on `(i, 0)` and fixes it on `(1, 0)` and `(0, 1)`.
    set w := ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)]
    have hw : ![((Φ ∘ SolidTorus.conjDisc) (0, 1) : E), L.comp conjProd (1, 0),
        L.comp conjProd (I, 0), L.comp conjProd (0, 1)] = Function.update w 2 (-w 2) := by
      ext i : 1
      fin_cases i <;> simp [w, ← map_neg, Prod.neg_mk]
    rw [hw, o.volumeForm.map_update_neg, Function.update_eq_self]
    exact neg_pos.2 hneg

/-- Reflecting the disc reverses orientation at the core: `Φ` precomposed with the reflection
`(u, w) ↦ (conj u, w)` preserves the orientation `o` at its core point exactly when `Φ` preserves
the opposite orientation `-o`. -/
theorem isOrientationPreservingAtCore_comp_conjDisc_iff :
    IsOrientationPreservingAtCore (Φ ∘ SolidTorus.conjDisc) o ↔
      IsOrientationPreservingAtCore Φ (-o) := by
  refine ⟨fun h ↦ ?_, IsOrientationPreservingAtCore.comp_conjDisc_of_neg⟩
  have h' := IsOrientationPreservingAtCore.comp_conjDisc_of_neg (Φ := Φ ∘ SolidTorus.conjDisc)
    (o := -o) (by convert h; exact neg_neg o)
  rwa [Function.comp_assoc, Function.Involutive.comp_self SolidTorus.conjDisc_conjDisc,
    Function.comp_id] at h'

/-! ### Orientation-preserving neighbourhoods of knots -/

/-- **Orientation-preserving solid torus neighbourhoods of knots.** For either orientation `o` of
`E`, every `C²` embedded circle `f` in the unit sphere `S³` of `E` has a solid torus neighbourhood
inside any prescribed neighbourhood of its image which preserves orientation at its core point. -/
theorem exists_isSolidTorusNeighborhood_isOrientationPreservingAtCore
    {f : Circle → sphere (0 : E) 1} (hf : ContMDiff (𝓡 1) (𝓡 3) 2 f)
    (himm : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 3) f z)) (hinj : Injective f)
    (o : Orientation ℝ E (Fin 4)) {U : Set (sphere (0 : E) 1)} (hU : U ∈ 𝓝ˢ (range f)) :
    ∃ Φ : SolidTorus → sphere (0 : E) 1, IsSolidTorusNeighborhood f Φ ∧ range Φ ⊆ U ∧
      IsOrientationPreservingAtCore Φ o := by
  obtain ⟨Φ, hΦ, hΦU, L, hL, hLinj, horth⟩ :=
    exists_isSolidTorusNeighborhood_sphere_hasFDerivAt_coreReading hf himm hinj hU
  -- The derivative sends the standard frame to an independent family.
  have hframe : LinearIndependent ℝ ![L (1, 0), L (I, 0), L (0, 1)] := by
    convert Complex.linearIndependent_one_zero_I_zero_zero_one.map' (L : ℂ × ℝ →ₗ[ℝ] E)
      (LinearMap.ker_eq_bot.2 hLinj) using 1
    ext i
    fin_cases i <;> simp
  -- The outward normal followed by the derivative on the standard frame is a basis.
  have hne : o.volumeForm ![(Φ (0, 1) : E), L (1, 0), L (I, 0), L (0, 1)] ≠ 0 :=
    Orientation.volumeForm_apply_ne_zero_iff.2 (hframe.finCons_of_inner_eq_zero
      (ne_zero_of_mem_unit_sphere _) fun i ↦ by fin_cases i <;> exact horth _)
  rcases hne.lt_or_gt with hneg | hpos
  · exact ⟨Φ ∘ SolidTorus.conjDisc, hΦ.comp_conjDisc, (Set.range_comp_subset_range _ _).trans hΦU,
      isOrientationPreservingAtCore_comp_conjDisc_iff.2
        (isOrientationPreservingAtCore_neg_iff.2 ⟨L, hL, hneg⟩)⟩
  · exact ⟨Φ, hΦ, hΦU, L, hL, hpos⟩

end TauCeti
