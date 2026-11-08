/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Orientation.Pullback
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward

/-!
# Orientations of regular sublevels and bands, and of their boundaries

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space `E` of
dimension `n + 1`, and let `a` be a regular value of `f`. The sublevel `{f ≤ a}` is a manifold with
boundary for its atlas `TauCeti.scalarRegularSublevelChartedSpace`, and the derivative of its
inclusion into `M` is invertible at every point, the points of the level `f⁻¹(a)` included
(`TauCeti.isInvertible_mfderiv_coe_scalarRegularSublevel`). So an orientation `o` of `M` pulls back
to an orientation `TauCeti.scalarRegularSublevelOrientation` of the sublevel, the unique one for
which the inclusion preserves orientation everywhere. Its boundary, which is the level `f⁻¹(a)`,
then carries the outward-first boundary orientation `TauCeti.boundaryOrientation`.

This file computes that boundary orientation in terms of `M` and `f` alone. At a point `x` of the
level, choose any tangent vector `v` of `M` with `df(v) > 0`. A basis `e` of the tangent space of
the boundary at `x` is positively oriented exactly when `v`, followed by the images of `e` in the
tangent space of `M`, is a positively oriented basis for `o`
(`TauCeti.boundaryOrientation_scalarRegularSublevelOrientation_spec`). Indeed, the vectors on which
`df` is positive are exactly the outward vectors of the sublevel
(`TauCeti.isOutwardPointing_scalarRegularSublevel_iff`), so this is the outward-first
characterization `TauCeti.boundaryOrientation_spec`, read in the tangent space of `M` through the
derivative of the inclusion (`TauCeti.boundaryOrientation_spec_of_linearEquiv`).

The same holds for a band `f⁻¹([a, b])` between regular values `a < b`, with orientation
`TauCeti.scalarRegularBandOrientation`, except that the outward vectors at the lower level
`f⁻¹(a)` are those with `df(v) < 0`
(`TauCeti.boundaryOrientation_scalarRegularBandOrientation_spec_of_eq_left` and
`TauCeti.boundaryOrientation_scalarRegularBandOrientation_spec_of_eq_right`), while those at the
upper level `f⁻¹(b)` are again those with `df(v) > 0`.

No metric is involved: the co-orientation is the sign of `df`, and a gradient of `f` for any
metric is one admissible choice of `v`.

## Main declarations

* `TauCeti.scalarRegularSublevelOrientation` and `TauCeti.scalarRegularBandOrientation`: the
  orientations of a regular sublevel and of a regular band induced by an orientation of `M`.
* `TauCeti.eq_scalarRegularSublevelOrientation_iff` and
  `TauCeti.eq_scalarRegularBandOrientation_iff`: they are the unique orientations for which the
  inclusion into `M` preserves orientation at every point.
* `TauCeti.boundaryOrientation_scalarRegularSublevelOrientation_spec`: the induced orientation of
  the boundary of a regular sublevel, with outward co-orientation `df > 0`.
* `TauCeti.boundaryOrientation_scalarRegularBandOrientation_spec_of_eq_left` and
  `TauCeti.boundaryOrientation_scalarRegularBandOrientation_spec_of_eq_right`: the induced
  orientations of the lower and upper boundary levels of a regular band, with outward
  co-orientations `df < 0` and `df > 0`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains) and
  Proposition 15.24 (the induced orientation on the boundary, outward vector first).
-/

public section

noncomputable section

open Module Set
open TauCeti.Manifold.Orientation (IsOrientationPreservingAt)
open scoped Manifold

namespace TauCeti

local instance regularSublevelOrientation_isManifold {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] [IsManifold (𝓡∂ (n + 1)) 1 X] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary X) :=
  isManifold_boundary X one_ne_zero

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a b : ℝ}
  [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M] (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hn : finrank ℝ E = n + 1)

omit [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- Let `s ⊆ M` carry a manifold structure whose inclusion is differentiable at `x`, with
derivative the equivalence `D`, and let `f` be differentiable at `x`. Then the derivative of `f`
on `s`, evaluated at `D⁻¹ v`, is the derivative of `f` on `M` evaluated at `v`. -/
private theorem mvfderiv_coe_symm_apply {s : Set M} [ChartedSpace (EuclideanHalfSpace (n + 1)) s]
    {x : s} (hfx : MDifferentiableAt I 𝓘(ℝ) f x)
    (hx : MDifferentiableAt (𝓡∂ (n + 1)) I (Subtype.val : s → M) x)
    (D : TangentSpace (𝓡∂ (n + 1)) x ≃L[ℝ] TangentSpace I (x : M))
    (hD : (D : TangentSpace (𝓡∂ (n + 1)) x →L[ℝ] TangentSpace I (x : M)) =
      mfderiv (𝓡∂ (n + 1)) I (Subtype.val : s → M) x)
    (v : TangentSpace I (x : M)) :
    mvfderiv (𝓡∂ (n + 1)) (fun w : s ↦ f w) x (D.symm v) = mvfderiv I f x v := by
  rw [mvfderiv_apply_eq_mfderiv_apply, show (fun w : s ↦ f w) = f ∘ Subtype.val from rfl,
    mfderiv_comp_apply _ hfx hx, ← hD,
    ContinuousLinearEquiv.coe_coe, D.apply_symm_apply, ← mvfderiv_apply_eq_mfderiv_apply]

section Sublevel

variable (hreg : IsRegularValue I 𝓘(ℝ) f a)

/-- The orientation of the sublevel `{f ≤ a}` at a regular value `a` induced by an orientation `o`
of `M`: the pullback of `o` along the inclusion, whose derivative is invertible at every point
(`TauCeti.isInvertible_mfderiv_coe_scalarRegularSublevel`). -/
def scalarRegularSublevelOrientation (o : Manifold.Orientation I M (Fin (n + 1))) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    Manifold.Orientation (𝓡∂ (n + 1)) {x | f x ≤ a} (Fin (n + 1)) :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  o.pullback (contMDiff_coe_scalarRegularSublevel hreg hn le_rfl hf)
    (isInvertible_mfderiv_coe_scalarRegularSublevel hf hreg hn) (by simp)

variable (o : Manifold.Orientation I M (Fin (n + 1)))

/-- The inclusion of the sublevel preserves orientation at every point, from the induced
orientation to `o`. -/
theorem isOrientationPreservingAt_scalarRegularSublevelOrientation (x : {x | f x ≤ a}) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    IsOrientationPreservingAt (scalarRegularSublevelOrientation hf hn hreg o) o Subtype.val x := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  exact Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _ x

/-- The induced orientation of the sublevel is the only orientation for which the inclusion
preserves orientation at every point. -/
theorem eq_scalarRegularSublevelOrientation_iff
    {o' : letI := scalarRegularSublevelChartedSpace hf hreg hn
      Manifold.Orientation (𝓡∂ (n + 1)) {x | f x ≤ a} (Fin (n + 1))} :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    o' = scalarRegularSublevelOrientation hf hn hreg o ↔
      ∀ x, IsOrientationPreservingAt o' o Subtype.val x := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  exact Manifold.Orientation.eq_pullback_iff _ _ _ _

/-- Reversing the orientation of `M` reverses the induced orientation of the sublevel. -/
@[simp]
theorem scalarRegularSublevelOrientation_neg :
    scalarRegularSublevelOrientation hf hn hreg (-o) =
      -scalarRegularSublevelOrientation hf hn hreg o := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  exact Manifold.Orientation.pullback_neg _ _ _ _

/-- **The induced orientation of the boundary of a regular sublevel.** Let `o` orient `M`, and let
`x` be a point of the boundary of the sublevel `{f ≤ a}`, that is, of the level `f⁻¹(a)`. For any
tangent vector `v` of `M` at `x` with `df(v) > 0`, a basis `e` of the tangent space of the boundary
at `x` is positively oriented for the boundary orientation of the induced orientation of the
sublevel exactly when `v`, followed by the images of `e` in the tangent space of `M`, is positively
oriented for `o`. -/
theorem boundaryOrientation_scalarRegularSublevelOrientation_spec
    (x : letI := scalarRegularSublevelChartedSpace hf hreg hn
      ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a}))
    {v : TangentSpace I ((x : {x | f x ≤ a}) : M)} (hv : 0 < mvfderiv I f x v)
    (e : letI := scalarRegularSublevelChartedSpace hf hreg hn
      haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
      Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (e' : Basis (Fin (n + 1)) ℝ (TangentSpace I ((x : {x | f x ≤ a}) : M)))
    (he' : letI := scalarRegularSublevelChartedSpace hf hreg hn
      haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
      ⇑e' = Fin.cons v fun i ↦ mfderiv (𝓡∂ (n + 1)) I (Subtype.val : {x | f x ≤ a} → M) x
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary {x | f x ≤ a} → {x | f x ≤ a}) x (e i))) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    e.orientation =
        (boundaryOrientation (scalarRegularSublevelOrientation hf hn hreg o)).orientationAt x ↔
      e'.orientation = o.orientationAt ((x : {x | f x ≤ a}) : M) := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  obtain ⟨D, hD⟩ := isInvertible_mfderiv_coe_scalarRegularSublevel hf hreg hn (x : {x | f x ≤ a})
  have hx : f x = a := (boundary_scalarRegularSublevel hreg hn le_rfl hf).subset x.2
  have hcoe := (contMDiff_coe_scalarRegularSublevel hreg hn le_rfl hf x).mdifferentiableAt
    one_ne_zero
  refine boundaryOrientation_spec_of_linearEquiv _ x D.toLinearEquiv (v := v)
    (Manifold.Orientation.map_orientationAt_pullback _ _ _ _ _ D hD)
    ((isOutwardPointing_scalarRegularSublevel_iff hf hn hreg hx _).2 ?_) e e' ?_
  · rwa [ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      mvfderiv_coe_symm_apply (hf.mdifferentiableAt one_ne_zero) hcoe D hD]
  · rw [he', ← hD]
    simp

end Sublevel

section Band

variable (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- The orientation of the band `f⁻¹([a, b])` between regular values `a < b` induced by an
orientation `o` of `M`: the pullback of `o` along the inclusion, whose derivative is invertible at
every point (`TauCeti.isInvertible_mfderiv_coe_scalarRegularBand`). -/
def scalarRegularBandOrientation (o : Manifold.Orientation I M (Fin (n + 1))) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    Manifold.Orientation (𝓡∂ (n + 1)) (f ⁻¹' Icc a b) (Fin (n + 1)) :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  o.pullback (contMDiff_coe_scalarRegularBand hn ha hb le_rfl hf hab)
    (isInvertible_mfderiv_coe_scalarRegularBand hf hn ha hb hab) (by simp)

variable (o : Manifold.Orientation I M (Fin (n + 1)))

/-- The inclusion of the band preserves orientation at every point, from the induced orientation
to `o`. -/
@[simp]
theorem isOrientationPreservingAt_scalarRegularBandOrientation (x : f ⁻¹' Icc a b) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    IsOrientationPreservingAt (scalarRegularBandOrientation hf hn ha hb hab o) o Subtype.val x := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  exact Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _ x

/-- The induced orientation of the band is the only orientation for which the inclusion preserves
orientation at every point. -/
theorem eq_scalarRegularBandOrientation_iff
    {o' : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      Manifold.Orientation (𝓡∂ (n + 1)) (f ⁻¹' Icc a b) (Fin (n + 1))} :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    o' = scalarRegularBandOrientation hf hn ha hb hab o ↔
      ∀ x, IsOrientationPreservingAt o' o Subtype.val x := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  exact Manifold.Orientation.eq_pullback_iff _ _ _ _

/-- Reversing the orientation of `M` reverses the induced orientation of the band. -/
@[simp]
theorem scalarRegularBandOrientation_neg :
    scalarRegularBandOrientation hf hn ha hb hab (-o) =
      -scalarRegularBandOrientation hf hn ha hb hab o := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  exact Manifold.Orientation.pullback_neg _ _ _ _

/-- **The induced orientation of the lower boundary level of a regular band.** Let `o` orient `M`,
and let `x` be a point of the boundary of the band `f⁻¹([a, b])` on the lower level `f⁻¹(a)`. For
any tangent vector `v` of `M` at `x` with `df(v) < 0`, a basis `e` of the tangent space of the
boundary at `x` is positively oriented for the boundary orientation of the induced orientation of
the band exactly when `v`, followed by the images of `e` in the tangent space of `M`, is positively
oriented for `o`. -/
theorem boundaryOrientation_scalarRegularBandOrientation_spec_of_eq_left
    (x : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)))
    (hx : f x = a) {v : TangentSpace I ((x : f ⁻¹' Icc a b) : M)} (hv : mvfderiv I f x v < 0)
    (e : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
      Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (e' : Basis (Fin (n + 1)) ℝ (TangentSpace I ((x : f ⁻¹' Icc a b) : M)))
    (he' : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
      ⇑e' = Fin.cons v fun i ↦ mfderiv (𝓡∂ (n + 1)) I (Subtype.val : f ⁻¹' Icc a b → M) x
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) → f ⁻¹' Icc a b) x (e i))) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    e.orientation =
        (boundaryOrientation (scalarRegularBandOrientation hf hn ha hb hab o)).orientationAt x ↔
      e'.orientation = o.orientationAt ((x : f ⁻¹' Icc a b) : M) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  obtain ⟨D, hD⟩ := isInvertible_mfderiv_coe_scalarRegularBand hf hn ha hb hab
    (x : f ⁻¹' Icc a b)
  have hcoe := (contMDiff_coe_scalarRegularBand hn ha hb le_rfl hf hab x).mdifferentiableAt
    one_ne_zero
  refine boundaryOrientation_spec_of_linearEquiv _ x D.toLinearEquiv (v := v)
    (Manifold.Orientation.map_orientationAt_pullback _ _ _ _ _ D hD)
    ((isOutwardPointing_scalarRegularBand_iff_of_eq_left hf hn ha hb hab hx _).2 ?_) e e' ?_
  · rwa [ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      mvfderiv_coe_symm_apply (hf.mdifferentiableAt one_ne_zero) hcoe D hD]
  · rw [he', ← hD]
    simp

/-- **The induced orientation of the upper boundary level of a regular band.** Let `o` orient `M`,
and let `x` be a point of the boundary of the band `f⁻¹([a, b])` on the upper level `f⁻¹(b)`. For
any tangent vector `v` of `M` at `x` with `df(v) > 0`, a basis `e` of the tangent space of the
boundary at `x` is positively oriented for the boundary orientation of the induced orientation of
the band exactly when `v`, followed by the images of `e` in the tangent space of `M`, is positively
oriented for `o`. -/
theorem boundaryOrientation_scalarRegularBandOrientation_spec_of_eq_right
    (x : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)))
    (hx : f x = b) {v : TangentSpace I ((x : f ⁻¹' Icc a b) : M)} (hv : 0 < mvfderiv I f x v)
    (e : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
      Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (e' : Basis (Fin (n + 1)) ℝ (TangentSpace I ((x : f ⁻¹' Icc a b) : M)))
    (he' : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
      ⇑e' = Fin.cons v fun i ↦ mfderiv (𝓡∂ (n + 1)) I (Subtype.val : f ⁻¹' Icc a b → M) x
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) → f ⁻¹' Icc a b) x (e i))) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    e.orientation =
        (boundaryOrientation (scalarRegularBandOrientation hf hn ha hb hab o)).orientationAt x ↔
      e'.orientation = o.orientationAt ((x : f ⁻¹' Icc a b) : M) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  obtain ⟨D, hD⟩ := isInvertible_mfderiv_coe_scalarRegularBand hf hn ha hb hab
    (x : f ⁻¹' Icc a b)
  have hcoe := (contMDiff_coe_scalarRegularBand hn ha hb le_rfl hf hab x).mdifferentiableAt
    one_ne_zero
  refine boundaryOrientation_spec_of_linearEquiv _ x D.toLinearEquiv (v := v)
    (Manifold.Orientation.map_orientationAt_pullback _ _ _ _ _ D hD)
    ((isOutwardPointing_scalarRegularBand_iff_of_eq_right hf hn ha hb hab hx _).2 ?_) e e' ?_
  · rwa [ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      mvfderiv_coe_symm_apply (hf.mdifferentiableAt one_ne_zero) hcoe D hD]
  · rw [he', ← hD]
    simp

end Band

end TauCeti
