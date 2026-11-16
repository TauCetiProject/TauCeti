/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Exponential

/-!
# Equivariant exponential charts at fixed points of isometric actions

Let `a` be an element of a group `G` acting on a Riemannian manifold `M` by smooth maps, whose
differential preserves the metric, and let `x` be a point with `a • x = x`. Then `a` acts by a
Riemannian isometry (`TauCeti.RiemannianIsometry.constSMul`), its differential `d(a •)_x` is a
linear isometry of `T_x M` leaving every ball about the origin invariant
(`TauCeti.mfderiv_smul_image_ball_of_smul_eq`), and isometries intertwine exponential maps:
`exp_x (d(a •)_x v) = a • exp_x v` (`TauCeti.riemannianExp_mfderiv_smul_of_smul_eq`), so `a`
leaves `exp_x '' ball 0 r` invariant (`TauCeti.smul_riemannianExp_image_ball_of_smul_eq`). These
lemmas, and their versions without a fixed point, live in the `Isometry.Tangent` and
`Isometry.Exponential` modules.

This file adds the inverse chart. On a normal domain `U` at `x` mapped into itself by `d(a •)_x`,
the Riemannian logarithm intertwines `a` with its differential on the normal neighbourhood
`exp_x '' U`: `log_x (a • y) = d(a •)_x (log_x y)` (`TauCeti.riemannianLog_smul_of_smul_eq`), the
fixed-point case of the naturality of the logarithm under Riemannian isometries
(`TauCeti.RiemannianIsometry.riemannianLog_apply`).
Consequently, if every element of `G` acts isometrically and fixes `x`, there is a normal ball
`B = ball 0 r` at `x` that is invariant under every `d(a •)_x`, whose normal neighbourhood
`exp_x '' B` is a `G`-invariant open neighbourhood of `x`, and on which `exp_x` and `log_x`
intertwine the tangent action `a ↦ d(a •)_x` on `B` with the action of `G` on `exp_x '' B`
(`TauCeti.exists_isNormalDomain_ball_riemannianExp_mfderiv_smul`). The differential of `exp_x` at
the origin is the identity (`TauCeti.Manifold.mfderiv_riemannianExp_zero`).

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

/-- At a point `x` fixed by `a`, if the differential of the action of `a` preserves the metric and
maps a normal domain `U` at `x` into itself, then the Riemannian logarithm intertwines `a` with its
differential on the normal neighbourhood `exp_x '' U`: `log_x (a • y) = d(a •)_x (log_x y)`. -/
theorem riemannianLog_smul_of_smul_eq {a : G}
    (ha : ∀ (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    {x : M} (hx : a • x = x) {U : Set (TangentSpace I x)} (hU : IsNormalDomain I M x U)
    (hUa : MapsTo (mfderiv I I (a • ·) x) U U) {y : M} (hy : y ∈ riemannianExp I M x '' U) :
    riemannianLog I M x U (a • y) = mfderiv I I (a • ·) x (riemannianLog I M x U y) := by
  have hΦ : RiemannianIsometry.constSMul a ha x = x := by
    rw [RiemannianIsometry.coe_constSMul]
    exact hx
  have h := (RiemannianIsometry.constSMul a ha).riemannianLog_apply (V := U) hU (by rwa [hΦ])
    (by rwa [RiemannianIsometry.coe_constSMul]) hy
  rwa [hΦ, RiemannianIsometry.coe_constSMul] at h

/-- **Equivariant exponential charts at a fixed point.** Let `G` act on `M` by smooth maps whose
differentials preserve the metric, and let `x` be fixed by `G`. There is `r > 0` such that the
ball `B` of radius `r` about the origin of `T_x M` is a normal domain at `x` (so `exp_x` restricts
to a diffeomorphism from `B` onto `exp_x '' B`), `B` is invariant under every differential
`d(a •)_x`, its image `exp_x '' B` is a `G`-invariant open neighbourhood of `x`, and `exp_x` and
the logarithm `log_x` on `exp_x '' B` intertwine the two actions:
`exp_x (d(a •)_x v) = a • exp_x v` and `log_x (a • y) = d(a •)_x (log_x y)`. -/
theorem exists_isNormalDomain_ball_riemannianExp_mfderiv_smul
    (hG : ∀ (a : G) (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    {x : M} (hx : ∀ a : G, a • x = x) :
    ∃ r : ℝ, 0 < r ∧ Manifold.IsNormalDomain I M x (ball 0 r) ∧
      IsOpen (riemannianExp I M x '' ball 0 r) ∧ x ∈ riemannianExp I M x '' ball 0 r ∧
      (∀ a : G,
        mfderiv I I (a • ·) x '' ball (0 : TangentSpace I x) r = ball (0 : TangentSpace I x) r) ∧
      (∀ a : G, a • (riemannianExp I M x '' ball 0 r) = riemannianExp I M x '' ball 0 r) ∧
      (∀ (a : G) (v : TangentSpace I x),
        riemannianExp I M x (mfderiv I I (a • ·) x v) = a • riemannianExp I M x v) ∧
      ∀ (a : G), ∀ y ∈ riemannianExp I M x '' ball 0 r,
        riemannianLog I M x (ball 0 r) (a • y) =
          mfderiv I I (a • ·) x (riemannianLog I M x (ball 0 r) y) := by
  obtain ⟨r, hr, hU⟩ := Manifold.exists_isNormalDomain_ball (I := I) (M := M) x
  have hball (a : G) := mfderiv_smul_image_ball_of_smul_eq (hG a) (hx a) r
  refine ⟨r, hr, hU, hU.isOpen_image, hU.self_mem_image, hball,
    fun a ↦ smul_riemannianExp_image_ball_of_smul_eq (hG a) (hx a) r,
    fun a ↦ riemannianExp_mfderiv_smul_of_smul_eq (hG a) (hx a),
    fun a _ hy ↦ riemannianLog_smul_of_smul_eq (hG a) (hx a) hU ?_ hy⟩
  intro v hv
  rw [← hball a]
  exact mem_image_of_mem _ hv

end TauCeti
