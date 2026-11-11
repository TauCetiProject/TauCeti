/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent

/-!
# Equivariant exponential charts at fixed points of isometric actions

Let a group `G` act on a Riemannian manifold `M` by smooth maps whose differentials preserve the
metric, and let `x` be a point fixed by every element of `G`. Each element then acts by a
Riemannian isometry (`TauCeti.RiemannianIsometry.ofSMul`), and its differential at `x` is a linear
isometry of `T_x M`. Isometries intertwine exponential maps, so

`a • exp_x v = exp_x (d(a •)_x v)`

for every `v : T_x M` and every `a : G` with `a • x = x`
(`TauCeti.riemannianExp_mfderiv_smul_of_smul_eq`). More generally, without a fixed point,
`exp_{a • x} (d(a •)_x v) = a • exp_x v`
(`TauCeti.riemannianExp_mfderiv_smul`), the differential `d(a •)_x` maps balls about the origin of
`T_x M` onto the balls of the same radius in `T_{a • x} M` (`TauCeti.mfderiv_smul_image_ball`), and
so `a` carries `exp_x '' ball 0 r` onto `exp_{a • x} '' ball 0 r`
(`TauCeti.smul_riemannianExp_image_ball`). Consequently every normal ball at `x` is
`G`-invariant, its normal neighbourhood `exp_x '' ball 0 r` is a `G`-invariant open neighbourhood
of `x`, and the exponential map is a `G`-equivariant diffeomorphism between them, with the tangent
representation `a ↦ d(a •)_x` acting on the ball
(`TauCeti.exists_isNormalDomain_ball_riemannianExp_mfderiv_smul`). Its differential at the origin
is the identity (`TauCeti.Manifold.mfderiv_riemannianExp_zero`).

This is the equivariant local model at a fixed point. For a compact group the hypothesis is met by
the Haar average of any smooth metric (`TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`),
which gives the equivariant chart of Bochner's linearization theorem; for a proper action it
applies to the compact stabilizer of a point. No compactness, finiteness or faithfulness of `G` is
assumed here.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes (2003), proof of Theorem 1.23.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Proposition 5.20
  (naturality of the exponential map).
-/

public section

open Bundle Function Manifold Metric Set
open scoped ContDiff Manifold Pointwise

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless] [T2Space M]

/-- At a point `x` fixed by an element `a` of an isometric action, the exponential map intertwines
`a` with its differential: `exp_x (d(a •)_x v) = a • exp_x v`. -/
theorem riemannianExp_mfderiv_smul_of_smul_eq
    (hG : ∀ (a : G) (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    {x : M} (a : G) (hx : a • x = x) (v : TangentSpace I x) :
    riemannianExp I M x (mfderiv I I (a • ·) x v) = a • riemannianExp I M x v := by
  have h := riemannianExp_mfderiv_smul hG a x v
  rw [hx] at h
  exact h

/-- At a point `x` fixed by an element `a` of an isometric action, the image under `exp_x` of every
ball about the origin of `T_x M` is invariant under `a`. -/
theorem smul_riemannianExp_image_ball_of_smul_eq
    (hG : ∀ (a : G) (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    {x : M} (a : G) (hx : a • x = x) (r : ℝ) :
    a • (riemannianExp I M x '' ball 0 r) = riemannianExp I M x '' ball 0 r := by
  have h := smul_riemannianExp_image_ball hG a x r
  rw [hx] at h
  exact h

/-- **Equivariant exponential charts at a fixed point.** Let `G` act on `M` by smooth maps whose
differentials preserve the metric, and let `x` be fixed by `G`. There is `r > 0` such that the
ball `B` of radius `r` about the origin of `T_x M` is a normal domain at `x`, and the exponential
map `exp_x : B → exp_x '' B` is a `G`-equivariant diffeomorphism onto a `G`-invariant open
neighbourhood of `x`: `exp_x (d(a •)_x v) = a • exp_x v`. -/
theorem exists_isNormalDomain_ball_riemannianExp_mfderiv_smul
    (hG : ∀ (a : G) (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    {x : M} (hx : ∀ a : G, a • x = x) :
    ∃ r : ℝ, 0 < r ∧ Manifold.IsNormalDomain I M x (ball 0 r) ∧
      IsOpen (riemannianExp I M x '' ball 0 r) ∧ x ∈ riemannianExp I M x '' ball 0 r ∧
      (∀ a : G, a • (riemannianExp I M x '' ball 0 r) = riemannianExp I M x '' ball 0 r) ∧
      ∀ (a : G) (v : TangentSpace I x),
        riemannianExp I M x (mfderiv I I (a • ·) x v) = a • riemannianExp I M x v := by
  obtain ⟨r, hr, hU⟩ := Manifold.exists_isNormalDomain_ball (I := I) (M := M) x
  refine ⟨r, hr, hU, hU.isOpen_image, ⟨0, mem_ball_self hr, riemannianExp_zero x⟩,
    fun a ↦ smul_riemannianExp_image_ball_of_smul_eq hG a (hx a) r,
    fun a ↦ riemannianExp_mfderiv_smul_of_smul_eq hG a (hx a)⟩

end TauCeti
