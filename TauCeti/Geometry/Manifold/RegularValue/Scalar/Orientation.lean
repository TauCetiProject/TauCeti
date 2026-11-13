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
# Boundary orientations of regular sublevels and bands

Let `f : M → ℝ` be a `C¹` function on an oriented boundaryless manifold `M` modelled on a real space
of dimension `n + 1`. At a regular value `a`, the sublevel `{f ≤ a}` is a manifold with boundary
(`TauCeti.isManifold_scalarRegularSublevel`) whose inclusion into `M` has invertible derivative at
every point, also on the level `f⁻¹(a)`
(`TauCeti.isInvertible_mfderiv_subtypeVal_scalarRegularSublevel`). So the orientation `o` of `M`
pulls back to an orientation of the sublevel (`TauCeti.Manifold.Orientation.scalarRegularSublevel`),
the unique one for which the inclusion preserves orientation. Its boundary carries the induced
orientation `TauCeti.boundaryOrientation`, with the outward vector first.

This file computes that boundary orientation without any metric. The outward vectors of the sublevel
are those on which `df > 0` (`TauCeti.isOutwardPointing_scalarRegularSublevel_iff`), so a basis
`e` of the tangent space of the boundary at `x` is positively oriented exactly when `(v, e)`, read
in `M`, is positively oriented for `o`, where `v` is any tangent vector of `M` at `x` with
`df(v) > 0` (`TauCeti.boundaryOrientation_scalarRegularSublevel_spec`). This is the usual
co-orientation of a regular level `f⁻¹(a)` as the boundary of `{f ≤ a}`: a gradient of `f` for any
metric is such a vector `v`.

The same holds for the band `f⁻¹([a, b])` between regular values `a < b`
(`TauCeti.Manifold.Orientation.scalarRegularBand`), with the vector `v` chosen with `df(v) < 0` on
the lower level `f⁻¹(a)` (`TauCeti.boundaryOrientation_scalarRegularBand_spec_of_eq_left`) and
with `df(v) > 0` on the upper level `f⁻¹(b)`
(`TauCeti.boundaryOrientation_scalarRegularBand_spec_of_eq_right`). So, as oriented boundaries, the
two levels of a band appear with opposite co-orientations.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 15.24 (the induced orientation on the boundary, with an outward vector
  first) and Proposition 5.47 (regular sublevel sets are regular domains).
* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965, §5
  (the boundary orientation, with an outward vector first).
-/

public section

noncomputable section

open Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a b : ℝ}
  [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]

namespace Manifold.Orientation

section Sublevel

variable (o : Orientation I M (Fin (n + 1))) (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1)

/-- The orientation of the sublevel `{f ≤ a}` at a regular value `a` of a `C¹` function, for its
preferred atlas, induced by an orientation `o` of `M`: the unique orientation for which the
inclusion into `M` preserves orientation at every point, including the points of the level
`f⁻¹(a)` (`TauCeti.Manifold.Orientation.eq_scalarRegularSublevel_iff`). -/
def scalarRegularSublevel :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    Orientation (𝓡∂ (n + 1)) {x | f x ≤ a} (Fin (n + 1)) :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  o.pullback (contMDiff_subtypeVal_scalarRegularSublevel hreg hn le_rfl hf)
    (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel hf hreg hn) (by simp)

/-- The inclusion of the sublevel preserves orientation from
`TauCeti.Manifold.Orientation.scalarRegularSublevel` at every point. -/
theorem isOrientationPreservingAt_scalarRegularSublevel (x : {x | f x ≤ a}) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    IsOrientationPreservingAt (o.scalarRegularSublevel hf hreg hn) o Subtype.val x :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  isOrientationPreservingAt_pullback o _ _ _ x

/-- `TauCeti.Manifold.Orientation.scalarRegularSublevel` is the only orientation of the sublevel
for which the inclusion into `M` preserves orientation at every point. -/
theorem eq_scalarRegularSublevel_iff
    (o' : letI := scalarRegularSublevelChartedSpace hf hreg hn
      Orientation (𝓡∂ (n + 1)) {x | f x ≤ a} (Fin (n + 1))) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    o' = o.scalarRegularSublevel hf hreg hn ↔
      ∀ x, IsOrientationPreservingAt o' o Subtype.val x :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  eq_pullback_iff o _ _ _

/-- The opposite orientation of `M` induces the opposite orientation of the sublevel. -/
@[simp]
theorem scalarRegularSublevel_neg :
    (-o).scalarRegularSublevel hf hreg hn = -o.scalarRegularSublevel hf hreg hn :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  pullback_neg o _ _ _

end Sublevel

section Band

variable (o : Orientation I M (Fin (n + 1))) (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hn : finrank ℝ E = n + 1) (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
  (hab : a < b)

/-- The orientation of the band `f⁻¹([a, b])` between regular values `a < b` of a `C¹` function,
for its preferred atlas, induced by an orientation `o` of `M`: the unique orientation for which the
inclusion into `M` preserves orientation at every point, including the points of the two levels
(`TauCeti.Manifold.Orientation.eq_scalarRegularBand_iff`). -/
def scalarRegularBand :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    Orientation (𝓡∂ (n + 1)) (f ⁻¹' Icc a b) (Fin (n + 1)) :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  o.pullback (contMDiff_subtypeVal_scalarRegularBand hn ha hb le_rfl hf hab)
    (isInvertible_mfderiv_subtypeVal_scalarRegularBand hn ha hb hf hab) (by simp)

/-- The inclusion of the band preserves orientation from
`TauCeti.Manifold.Orientation.scalarRegularBand` at every point. -/
@[simp]
theorem isOrientationPreservingAt_scalarRegularBand (x : f ⁻¹' Icc a b) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    IsOrientationPreservingAt (o.scalarRegularBand hf hn ha hb hab) o Subtype.val x :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  isOrientationPreservingAt_pullback o _ _ _ x

/-- `TauCeti.Manifold.Orientation.scalarRegularBand` is the only orientation of the band for which
the inclusion into `M` preserves orientation at every point. -/
theorem eq_scalarRegularBand_iff
    (o' : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      Orientation (𝓡∂ (n + 1)) (f ⁻¹' Icc a b) (Fin (n + 1))) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    o' = o.scalarRegularBand hf hn ha hb hab ↔
      ∀ x, IsOrientationPreservingAt o' o Subtype.val x :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  eq_pullback_iff o _ _ _

/-- The opposite orientation of `M` induces the opposite orientation of the band. -/
@[simp]
theorem scalarRegularBand_neg :
    (-o).scalarRegularBand hf hn ha hb hab = -o.scalarRegularBand hf hn ha hb hab :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  pullback_neg o _ _ _

end Band

end Manifold.Orientation

omit [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- The vector of a subset `s` of `M` over a tangent vector `v` of `M` at a point of `s`, when the
derivative of the inclusion is invertible there. -/
private theorem exists_mfderiv_subtypeVal_eq {s : Set M}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) s] (hf : ContMDiff I 𝓘(ℝ) 1 f) {x : s}
    (hx : (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : s → M) x).IsInvertible)
    (v : TangentSpace I (x : M)) :
    ∃ u : TangentSpace (𝓡∂ (n + 1)) x, mfderiv (𝓡∂ (n + 1)) I Subtype.val x u = v ∧
      mvfderiv (𝓡∂ (n + 1)) (fun w : s ↦ f w) x u = mvfderiv I f x v := by
  obtain ⟨D, hD⟩ := hx
  have hDv : mfderiv (𝓡∂ (n + 1)) I Subtype.val x (D.symm v) = v := by
    rw [← hD]
    exact D.apply_symm_apply v
  -- The restriction of `f` to `s` is `f ∘ Subtype.val` by definition.
  have hcomp : (fun w : s ↦ f w) = f ∘ Subtype.val := rfl
  refine ⟨D.symm v, hDv, ?_⟩
  rw [hcomp, mvfderiv_comp _ ((hf _).mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_of_isInvertible_mfderiv ⟨D, hD⟩), ContinuousLinearMap.comp_apply, hDv]

section Sublevel

variable (o : Manifold.Orientation I M (Fin (n + 1))) (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hreg : IsRegularValue I 𝓘(ℝ) f a) (hn : finrank ℝ E = n + 1)

/-- **The boundary orientation of a regular sublevel.** Orient the sublevel `{f ≤ a}` by an
orientation `o` of `M` and its boundary, the level `f⁻¹(a)`, by the induced outward-first
orientation. A basis `e` of the tangent space of the boundary at `x` is positively oriented exactly
when `v` followed by `e`, read in `M`, is positively oriented for `o`, where `v` is any tangent
vector of `M` at `x` on which `df` is positive. -/
theorem boundaryOrientation_scalarRegularSublevel_spec :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := isManifold_boundary (n := n) {x | f x ≤ a} (one_ne_zero : (1 : ℕ∞ω) ≠ 0)
    ∀ (x : (𝓡∂ (n + 1)).boundary {x | f x ≤ a}) {v : TangentSpace I ((x : {x | f x ≤ a}) : M)},
      0 < mvfderiv I f x v →
      ∀ (e : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
        (e' : Basis (Fin (n + 1)) ℝ (TangentSpace I ((x : {x | f x ≤ a}) : M))),
        ⇑e' = Fin.cons v (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (fun y : (𝓡∂ (n + 1)).boundary {x | f x ≤ a} ↦ ((y : {x | f x ≤ a}) : M)) x (e i)) →
        (e.orientation =
            (boundaryOrientation (o.scalarRegularSublevel hf hreg hn)).orientationAt x ↔
          e'.orientation = o.orientationAt x) := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  intro x v hv e e' he'
  obtain ⟨u, hu, hfu⟩ := exists_mfderiv_subtypeVal_eq hf
    (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel hf hreg hn x) v
  have hx : f x = a := (boundary_scalarRegularSublevel hreg hn le_rfl hf).le x.2
  -- The vector of the sublevel over `v` points outward, because `df(v) > 0`.
  refine boundaryOrientation_spec_of_isOrientationPreservingAt x
    (o.isOrientationPreservingAt_scalarRegularSublevel hf hreg hn x) ?_ e e' (by rw [he', hu])
  rw [isOutwardPointing_scalarRegularSublevel_iff hf hn hreg hx, hfu]
  exact hv

end Sublevel

section Band

variable (o : Manifold.Orientation I M (Fin (n + 1))) (hf : ContMDiff I 𝓘(ℝ) 1 f)
  (hn : finrank ℝ E = n + 1) (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b)
  (hab : a < b)

/-- **The boundary orientation of a band at its lower level.** Orient the band `f⁻¹([a, b])` by an
orientation `o` of `M` and its boundary by the induced outward-first orientation. At a point `x` of
the lower level `f⁻¹(a)`, a basis `e` of the tangent space of the boundary is positively oriented
exactly when `v` followed by `e`, read in `M`, is positively oriented for `o`, where `v` is any
tangent vector of `M` at `x` on which `df` is negative. -/
theorem boundaryOrientation_scalarRegularBand_spec_of_eq_left :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := isManifold_boundary (n := n) (f ⁻¹' Icc a b) (one_ne_zero : (1 : ℕ∞ω) ≠ 0)
    ∀ (x : (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)), f x = a →
      ∀ {v : TangentSpace I ((x : f ⁻¹' Icc a b) : M)}, mvfderiv I f x v < 0 →
      ∀ (e : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
        (e' : Basis (Fin (n + 1)) ℝ (TangentSpace I ((x : f ⁻¹' Icc a b) : M))),
        ⇑e' = Fin.cons v (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (fun y : (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) ↦ ((y : f ⁻¹' Icc a b) : M)) x
            (e i)) →
        (e.orientation =
            (boundaryOrientation (o.scalarRegularBand hf hn ha hb hab)).orientationAt x ↔
          e'.orientation = o.orientationAt x) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  intro x hx v hv e e' he'
  obtain ⟨u, hu, hfu⟩ := exists_mfderiv_subtypeVal_eq hf
    (isInvertible_mfderiv_subtypeVal_scalarRegularBand hn ha hb hf hab x) v
  -- The vector of the band over `v` points outward, because `df(v) < 0` on the lower level.
  refine boundaryOrientation_spec_of_isOrientationPreservingAt x
    (o.isOrientationPreservingAt_scalarRegularBand hf hn ha hb hab x) ?_ e e' (by rw [he', hu])
  rw [isOutwardPointing_scalarRegularBand_iff_of_eq_left hf hn ha hb hab hx, hfu]
  exact hv

/-- **The boundary orientation of a band at its upper level.** Orient the band `f⁻¹([a, b])` by an
orientation `o` of `M` and its boundary by the induced outward-first orientation. At a point `x` of
the upper level `f⁻¹(b)`, a basis `e` of the tangent space of the boundary is positively oriented
exactly when `v` followed by `e`, read in `M`, is positively oriented for `o`, where `v` is any
tangent vector of `M` at `x` on which `df` is positive. -/
theorem boundaryOrientation_scalarRegularBand_spec_of_eq_right :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := isManifold_boundary (n := n) (f ⁻¹' Icc a b) (one_ne_zero : (1 : ℕ∞ω) ≠ 0)
    ∀ (x : (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)), f x = b →
      ∀ {v : TangentSpace I ((x : f ⁻¹' Icc a b) : M)}, 0 < mvfderiv I f x v →
      ∀ (e : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
        (e' : Basis (Fin (n + 1)) ℝ (TangentSpace I ((x : f ⁻¹' Icc a b) : M))),
        ⇑e' = Fin.cons v (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
          (fun y : (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) ↦ ((y : f ⁻¹' Icc a b) : M)) x
            (e i)) →
        (e.orientation =
            (boundaryOrientation (o.scalarRegularBand hf hn ha hb hab)).orientationAt x ↔
          e'.orientation = o.orientationAt x) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  intro x hx v hv e e' he'
  obtain ⟨u, hu, hfu⟩ := exists_mfderiv_subtypeVal_eq hf
    (isInvertible_mfderiv_subtypeVal_scalarRegularBand hn ha hb hf hab x) v
  -- The vector of the band over `v` points outward, because `df(v) > 0` on the upper level.
  refine boundaryOrientation_spec_of_isOrientationPreservingAt x
    (o.isOrientationPreservingAt_scalarRegularBand hf hn ha hb hab x) ?_ e e' (by rw [he', hu])
  rw [isOutwardPointing_scalarRegularBand_iff_of_eq_right hf hn ha hb hab hx, hfu]
  exact hv

end Band

end TauCeti
