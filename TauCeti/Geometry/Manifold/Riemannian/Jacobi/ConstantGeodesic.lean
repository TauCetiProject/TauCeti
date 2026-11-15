/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Affine
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Jacobi fields along constant geodesics

Along the constant geodesic at `x`, the Jacobi equation is the ordinary equation
`J'' = 0` in the fixed tangent space at `x`. Its solutions on a preconnected parameter
set are exactly the affine fields `t ↦ u + (t - a) • v`. Here `u` and `v` are arbitrary
initial position and covariant velocity; no curvature hypothesis is needed.

The classification is equality on the parameter set, allowing closed nondegenerate
intervals and arbitrary values outside them. The explicit affine formula defines a
tangent field on the whole real line.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (the Jacobi equation and determination by initial data).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {s : Set ℝ} {a t : ℝ} {x : M}

/-- An affine field in a fixed tangent space is a Jacobi field along the constant
geodesic, for arbitrary initial position and velocity and any parameter set with
unique derivatives. -/
theorem isJacobiFieldOn_const_affine (hs : UniqueDiffOn ℝ s)
    (u v : TangentSpace I x) (a : ℝ) :
    IsJacobiFieldOn I (fun _ ↦ x) (fun r ↦ u + (r - a) • v) s := by
  refine ⟨isGeodesicCurveOn_const hs x, ?_, fun r hr ↦ ?_⟩
  · exact (contMDiffOn_const (c := TotalSpace.mk' E x u)).add_sectionAlong
      ((contMDiffOn_id.sub contMDiffOn_const).smul_totalSpace
        (contMDiffOn_const (c := TotalSpace.mk' E x v)))
  · have hfirst : ∀ r ∈ s,
        alongCurveWithin (leviCivitaConnection I M) (fun _ ↦ x)
          (fun q ↦ u + (q - a) • v) s r = v :=
      fun r hr ↦ alongCurveWithin_const_add_smul (leviCivitaConnection I M) (hs r hr) u v a
    rw [alongCurveWithin_congr _ (fun _ ↦ x) _
      (mem_of_superset self_mem_nhdsWithin (hfirst ·)) (hfirst r hr)]
    have hzero : alongCurveWithin (leviCivitaConnection I M) (fun _ ↦ x)
        (fun _ ↦ v) s r = 0 :=
      alongCurveWithin_const_of_hasDerivWithinAt _ x
        (hasDerivWithinAt_const r s v) (hs r hr)
    simp [hzero, curveVelocityWithin_const]

/-- A Jacobi field along a constant geodesic is the affine field determined by its
value and covariant velocity at any one parameter. The conclusion is only on the
preconnected parameter set, so no extension outside that set is prescribed. -/
theorem IsJacobiFieldOn.eq_add_smul_of_constant {V : ℝ → TangentSpace I x}
    (h : IsJacobiFieldOn I (fun _ ↦ x) V s) (hs : IsPreconnected s)
    (ha : a ∈ s) (ht : t ∈ s) :
    V t = V a + (t - a) •
      alongCurveWithin (leviCivitaConnection I M) (fun _ ↦ x) V s a := by
  exact h.eq_of_eq_of_alongCurveWithin_eq
    (isJacobiFieldOn_const_affine h.uniqueDiffOn (V a)
      (alongCurveWithin (leviCivitaConnection I M) (fun _ ↦ x) V s a) a)
    hs ha (by simp) (by rw [alongCurveWithin_const_add_smul _ (h.uniqueDiffOn a ha)]) ht

/-- On a nonempty preconnected set with unique derivatives, the Jacobi fields along
a constant geodesic are exactly the restrictions of affine tangent-space fields.
No regularity of the field away from the parameter set is required. -/
theorem isJacobiFieldOn_const_iff {V : ℝ → TangentSpace I x}
    (hs : UniqueDiffOn ℝ s) (hsc : IsPreconnected s) (ha : a ∈ s) :
    IsJacobiFieldOn I (fun _ ↦ x) V s ↔
      ∃ u v : TangentSpace I x, EqOn V (fun r ↦ u + (r - a) • v) s := by
  constructor
  · intro h
    exact ⟨V a, alongCurveWithin (leviCivitaConnection I M) (fun _ ↦ x) V s a,
      fun t ht ↦ h.eq_add_smul_of_constant hsc ha ht⟩
  · rintro ⟨u, v, hV⟩
    exact (isJacobiFieldOn_const_affine hs u v a).congr hV

end TauCeti.Manifold
