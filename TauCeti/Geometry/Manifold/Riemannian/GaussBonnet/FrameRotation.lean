/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.RankTwo
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.Geometry.Manifold.Riemannian.Orientation.Preserving

/-!
# Connection forms of two positively oriented frames of a surface

Let `(e₀, e₁)` and `(f₀, f₁)` be orthonormal local frames of an oriented Riemannian surface, both
positively oriented, `vol(e₀, e₁) = vol(f₀, f₁) = 1`. At a point of both domains, `e₀` is the unit
vector `z₀ f₀ + z₁ f₁`, `zₖ = ⟪fₖ, e₀⟫`, and positive orientation forces
`e₁ = J e₀ = -z₁ f₀ + z₀ f₁`, where `J` is the rotation by `+π/2`. The connection one-forms
`ω(X) = ⟪e₁, ∇_X e₀⟫` of a metric connection therefore differ by the pullback of the angle form
of the circle under `z`:

`ω(e) = ω(f) + z₀ dz₁ - z₁ dz₀`

(`IsLocalFrameOn.connectionForm_zero_one_eq_add_smul_sub_smul_of_riemannianVolumeForm_eq_one`).

This is the local step of Chern's proof of the Gauss–Bonnet theorem. With `e₀ = X / ‖X‖` for a
vector field `X` with isolated zeros and `f` a frame on a disc around a zero, the two structure
equations `dω(e) = dω(f) = -K vol` agree on the punctured disc, and the difference of the
connection forms is the angle form whose integral over a small circle measures the index of the
zero.

## Main results

* `IsLocalFrameOn.connectionForm_zero_one_eq_add_smul_sub_smul_of_riemannianVolumeForm_eq_one`: the
  connection forms of two positively oriented orthonormal tangent frames differ by
  `z₀ dz₁ - z₁ dz₀`.

## References

* S.-S. Chern, *A simple intrinsic proof of the Gauss–Bonnet formula for closed Riemannian
  manifolds*, Ann. of Math. 45 (1944), 747–752.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapter 9.
-/

public section

open Bundle CovariantDerivative Set TauCeti
open scoped ContDiff Manifold Topology

noncomputable section

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {n n' : ℕ∞ω} {s t : Fin 2 → Π x : M, TangentSpace I x} {u u' : Set M}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- **The connection forms of two positively oriented frames of a surface.** Let `(t₀, t₁)` be a
`C¹` local frame of an oriented Riemannian surface, orthonormal on its open domain, and `(s₀, s₁)`
a local frame, and let `x` be a point of both domains at which `s₀` is a unit vector and both
frames have oriented area one, `vol(s₀, s₁) = vol(t₀, t₁) = 1`. If `s₀` is differentiable at `x`,
then for a metric connection the connection forms `A¹₀`, `ω(X) = ⟪s₁, ∇_X s₀⟫` for orthonormal
`s`, satisfy at `x`

`A¹₀(s) = A¹₀(t) + z₀ dz₁ - z₁ dz₀`, where `zₖ = ⟪tₖ, s₀⟫`. -/
theorem connectionForm_zero_one_eq_add_smul_sub_smul_of_riemannianVolumeForm_eq_one
    (o : Manifold.Orientation I M (Fin 2)) (hs : IsLocalFrameOn I E n s u)
    (ht : IsLocalFrameOn I E n' t u') (hn' : 1 ≤ n') (hu' : IsOpen u')
    (hot : ∀ y ∈ u', Orthonormal ℝ (fun i ↦ t i y))
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) {x : M} (hx : x ∈ u)
    (hx' : x ∈ u') (hs₀ : MDiffAt (T% (s 0)) x) (hnorm : ‖s 0 x‖ = 1)
    (hors : riemannianVolumeForm o x ![s 0 x, s 1 x] = 1)
    (hort : riemannianVolumeForm o x ![t 0 x, t 1 x] = 1) :
    hs.connectionForm cov 0 1 x = ht.connectionForm cov 0 1 x +
      inner ℝ (t 0 x) (s 0 x) •
        mextDeriv (RoughForm.ofFunction I fun y ↦ inner ℝ (t 1 y) (s 0 y)) x -
      inner ℝ (t 1 x) (s 0 x) •
        mextDeriv (RoughForm.ofFunction I fun y ↦ inner ℝ (t 0 y) (s 0 y)) x := by
  refine hs.connectionForm_zero_one_eq_add_smul_sub_smul ht hn' hu' hot hcov hx hx' hs₀ hnorm ?_
  let := o.fact_finrank_tangentSpace x
  -- Expanding `s` in `t`, the area form multiplies `vol(t₀, t₁) = 1` by the determinant.
  have hs₀x := (ht.sum_inner_smul_eq hx' (hot x hx') (s 0 x)).symm
  have hs₁x := (ht.sum_inner_smul_eq hx' (hot x hx') (s 1 x)).symm
  rw [Fin.sum_univ_two] at hs₀x hs₁x
  rw [Manifold.Orientation.riemannianVolumeForm_eq_areaForm, hs₀x, hs₁x] at hors
  rw [Manifold.Orientation.riemannianVolumeForm_eq_areaForm] at hort
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Orientation.areaForm_apply_self, mul_zero, zero_add, add_zero] at hors
  rw [(o.orientationAt x).areaForm_swap (t 1 x) (t 0 x), hort] at hors
  linear_combination hors

end IsLocalFrameOn
