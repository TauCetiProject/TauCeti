/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.BlowUp
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic

/-!
# Blowing up a metric in normal coordinates

Let `U` be a normal domain at a point `p` of a Riemannian manifold `M`. Pulling the metric `g`
back along the exponential map gives the metric `g` read in normal coordinates,
`TauCeti.Manifold.IsNormalDomain.normalCoordinateMetric`, a metric on the open set `U` of the
tangent space `T_p M`. Since `U` is star-shaped about the origin, this metric can be blown up
(`Bundle.ContMDiffRiemannianMetric.blowUp`): for `t ∈ (0, 1]` the blow-up at scale `t` is the
metric `t⁻² μ_t^* exp_p^* g` of the magnified ball `v ↦ exp_p (t • v)`, and its scalar curvature at
`v` is `t² Scal(g)(exp_p (t • v))`. Since the differential of `exp_p` at the origin is the
identity, the blow-up at scale `0` is the constant metric `g_p` of the Euclidean space `T_p M`.

The blow-up is continuous in `t ∈ [0, 1]` for every chart `Cᵏ` topology
(`Bundle.ContMDiffRiemannianMetric.continuous_blowUp_chartCk`). So a ball around `p` of radius
`t`, magnified to unit size, carries a metric that converges to the flat metric `g_p` as `t → 0`,
uniformly on compact sets with derivatives of every order. This is the comparison with the flat
model at a point used by the Gromov–Lawson construction for surgery on a point, that is, for
connected sums.

## Main definitions

* `TauCeti.Manifold.IsNormalDomain.normalCoordinateMetric`: the metric `exp_p^* g` on a normal
  domain.

## Main results

* `TauCeti.Manifold.IsNormalDomain.blowUp_normalCoordinateMetric_zero_inner`: the blow-up at
  scale `0` is the inner product `g_p` of `T_p M`.
* `TauCeti.Manifold.IsNormalDomain.scalarCurvature_blowUp_normalCoordinateMetric`: for `t > 0` the
  blow-up at scale `t` has scalar curvature `t² Scal(g)(exp_p (t • v))` at `v`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
-/

public section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace IsNormalDomain

variable {p : M} {U : Set (TangentSpace I p)}

/-- A normal domain, as an open subset of the tangent space. -/
@[expose]
def opens (hU : IsNormalDomain I M p U) : Opens (TangentSpace I p) :=
  ⟨U, hU.isOpen⟩

@[simp]
theorem coe_opens (hU : IsNormalDomain I M p U) : (hU.opens : Set (TangentSpace I p)) = U :=
  rfl

/-- The exponential map is smooth on a normal domain. -/
theorem contMDiff_riemannianExp_comp_val (hU : IsNormalDomain I M p U) {n : ℕ∞ω}
    (hn : n ≤ ∞ + 1) :
    ContMDiff 𝓘(ℝ, TangentSpace I p) I n
      (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) := by
  intro v
  have h : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      (v : TangentSpace I p) :=
    hU.isLocalDiffeomorphOn ⟨v, v.2⟩
  exact (h.contMDiffAt.of_le (by simpa using hn)).comp v contMDiff_subtype_val.contMDiffAt

/-- The exponential map has invertible differential on a normal domain. -/
theorem isInvertible_mfderiv_riemannianExp_comp_val (hU : IsNormalDomain I M p U)
    (v : hU.opens) :
    (mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) v).IsInvertible := by
  have h : IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace I p) I ∞ (riemannianExp I M p)
      (v : TangentSpace I p) :=
    hU.isLocalDiffeomorphOn ⟨v, v.2⟩
  rw [mfderiv_comp v (h.contMDiffAt.mdifferentiableAt (by simp))
    (contMDiff_subtype_val.contMDiffAt.mdifferentiableAt one_ne_zero),
    mfderiv_subtype_val (I := 𝓘(ℝ, TangentSpace I p)) v]
  exact (h.isInvertible_mfderiv (by simp)).comp (ContinuousLinearMap.isInvertible_equiv)

/-- The metric `g` read in normal coordinates: its pullback along the exponential map, as a metric
on the normal domain. -/
@[expose]
def normalCoordinateMetric (hU : IsNormalDomain I M p U) :
    ContMDiffRiemannianMetric 𝓘(ℝ, TangentSpace I p) ∞ (TangentSpace I p)
      (fun v : hU.opens ↦ TangentSpace 𝓘(ℝ, TangentSpace I p) v) :=
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)).pullback
      (riemannianExp I M p ∘ Subtype.val) (hU.contMDiff_riemannianExp_comp_val le_rfl)
      fun v ↦ (hU.isInvertible_mfderiv_riemannianExp_comp_val v).injective

/-- The metric in normal coordinates pairs two vectors as `g` pairs their images under the
differential of the exponential map. -/
theorem normalCoordinateMetric_inner (hU : IsNormalDomain I M p U) (v : hU.opens)
    (u w : TangentSpace 𝓘(ℝ, TangentSpace I p) v) :
    hU.normalCoordinateMetric.inner v u w =
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I
          (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) v u)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I
          (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) v w) := by
  rw [normalCoordinateMetric, ContMDiffRiemannianMetric.pullback_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

/-- At scale `0`, the blow-up of the metric in normal coordinates is the constant metric given by
the inner product of `T_p M`. -/
theorem blowUp_normalCoordinateMetric_zero_inner [T2Space M] [I.Boundaryless]
    (hU : IsNormalDomain I M p U) (v : hU.opens) (u w : TangentSpace I p) :
    (hU.normalCoordinateMetric.blowUp hU.starConvex 0).inner v u w = inner ℝ u w := by
  have h0 := ContMDiffRiemannianMetric.blowUp_zero_inner hU.normalCoordinateMetric hU.starConvex v
  rw [h0]
  refine (normalCoordinateMetric_inner hU _ u w).trans ?_
  have hd : mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) ⟨0, hU.zero_mem⟩ =
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0).comp
          (mfderiv 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, TangentSpace I p)
            (Subtype.val : hU.opens → TangentSpace I p) ⟨0, hU.zero_mem⟩) :=
    mfderiv_comp (⟨0, hU.zero_mem⟩ : hU.opens)
      ((contMDiffAt_riemannianExp (zero_mem_expDomain (I := I) (M := M) p)).mdifferentiableAt
        (by simp)) (contMDiff_subtype_val.contMDiffAt.mdifferentiableAt one_ne_zero)
  have hd' (z : TangentSpace I p) : mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) ⟨0, hU.zero_mem⟩ z =
        z := by
    rw [hd, mfderiv_subtype_val (I := 𝓘(ℝ, TangentSpace I p))]
    exact (congrArg (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) 0)
      (tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, TangentSpace I p)) _ z)).trans
        (mfderiv_riemannianExp_apply_zero p z)
  -- The differential lands in the tangent space at `exp_p 0`, which is `p` only propositionally.
  have key : ∀ q : M, q = p → ∀ a b : E, inner ℝ (show TangentSpace I q from a)
      (show TangentSpace I q from b) = inner ℝ (show TangentSpace I p from a)
        (show TangentSpace I p from b) := by
    rintro q rfl a b
    rfl
  exact (congrArg₂ (inner ℝ) (hd' u) (hd' w)).trans (key _ (riemannianExp_zero p) u w)

/-- For `t > 0`, the blow-up at scale `t` of the metric in normal coordinates has scalar
curvature `t² Scal(g)(exp_p (t • v))` at `v`. -/
theorem scalarCurvature_blowUp_normalCoordinateMetric [T2Space M] (hU : IsNormalDomain I M p U)
    (t : Icc (0 : ℝ) 1) (ht : 0 < (t : ℝ)) (v : hU.opens) :
    (hU.normalCoordinateMetric.blowUp hU.starConvex t).scalarCurvature v =
      (t : ℝ) ^ 2 * (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
        (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)).scalarCurvature
          (riemannianExp I M p ((t : ℝ) • (v : TangentSpace I p))) := by
  have ht' := ContMDiffRiemannianMetric.scalarCurvature_blowUp hU.normalCoordinateMetric
    hU.starConvex t ht v
  rw [ht', normalCoordinateMetric,
    ContMDiffRiemannianMetric.scalarCurvature_pullback_of_isInvertible _ _
      hU.isInvertible_mfderiv_riemannianExp_comp_val]
  rfl

end IsNormalDomain

end TauCeti.Manifold
