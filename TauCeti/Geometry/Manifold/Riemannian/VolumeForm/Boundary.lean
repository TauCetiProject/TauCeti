/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Boundary.Integration
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.Riemannian.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.OutwardUnitNormal
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Normal contraction of the Riemannian volume form at the boundary

On a Riemannian manifold `M` with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`),
contracting an oriented volume form along the outward unit normal `N` at a boundary point yields
the induced volume form on `∂M` for the outward-first boundary orientation (`n ≥ 0`). Pulling back
`ι_X dV` to `∂M` therefore gives `⟪X, N⟫ dS`.

## Main results

* `TauCeti.volumeForm_cons_mfderiv_subtypeVal_boundary`: evaluating an oriented ambient volume form
  at `x ∈ ∂M` on `u` followed by `dι(vᵢ)` gives `inner ℝ u N` times the outward-first boundary
  volume form.
* `TauCeti.boundaryRestriction_interior_riemannianVolumeForm`: restricting `ι_X dV` to `∂M` gives
  `⟪X, N⟫ dS`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33 and Theorem 16.32.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

local instance instIsManifoldBoundaryVolumeForm :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
  isManifold_boundary M

private abbrev bdryI (n : ℕ) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- At a boundary point `x`, an orthonormal basis `b` of `T_x (∂M)` extends by `N` to an
orthonormal basis `b'` of `T_x M` whose orientation matches `o` iff `b` matches `∂o`. -/
private theorem exists_orthonormalBasis_cons_outwardUnitNormal
    (x : (𝓡∂ (n + 1)).boundary M)
    (o : Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) (Fin (n + 1))) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (TangentSpace (bdryI n) x))
      (b' : OrthonormalBasis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M))),
      ⇑b'.toBasis = Fin.cons (outwardUnitNormal x) (fun i ↦
          mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) x (b i)) ∧
        (b.toBasis.orientation = Orientation.halfSpaceBoundaryOrientation o ↔
          b'.toBasis.orientation = o) := by
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) x
  set N := outwardUnitNormal x
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace (bdryI n) x) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (by rw [TauCeti.finrank_tangentSpace]; simp))
  have hf_orth : Orthonormal ℝ (Matrix.vecCons N fun i ↦ dι (b i)) :=
    orthonormal_vecCons_iff.2 ⟨norm_outwardUnitNormal x,
      fun i ↦ inner_outwardUnitNormal_mfderiv_subtypeVal x _, orthonormal_iff_ite.2 fun i j ↦ by
        rw [← inner_tangentSpace_boundary]; exact orthonormal_iff_ite.1 b.orthonormal i j⟩
  let b' : OrthonormalBasis (Fin (n + 1)) ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
    (basisOfOrthonormalOfCardEqFinrank hf_orth
      (by rw [TauCeti.finrank_tangentSpace]; simp)).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hf_orth)
  have hb'_coe : ⇑b'.toBasis = Fin.cons N fun i ↦ dι (b i) := by
    rw [Module.Basis.toBasis_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
    rfl
  have hN_neg : (fun w : EuclideanSpace ℝ (Fin (n + 1)) ↦ w 0) N < 0 := by
    have h := (isOutwardPointing_outwardUnitNormal x).coordinate_deriv_neg
    rwa [mfderiv_extChartAt_self] at h
  refine ⟨b, b', hb'_coe, Orientation.halfSpaceBoundaryOrientation_spec o hN_neg b.toBasis
    b'.toBasis (funext fun k ↦ Fin.cases (congrFun hb'_coe 0) (fun i ↦ ?_) k)⟩
  have hi := congrFun hb'_coe i.succ
  simp only [Fin.cons_succ, dι, mfderiv_subtypeVal_boundary, OrthonormalBasis.coe_toBasis] at hi ⊢
  exact hi

/-- **Normal contraction of the volume form at a boundary point.** For any orientation `o` of the
ambient tangent space at `x ∈ ∂M`, evaluating `o.volumeForm` on `u` followed by `dι(vᵢ)` gives
`inner ℝ u N` times the volume form of `Orientation.halfSpaceBoundaryOrientation o`, all `n ≥ 0`. -/
theorem volumeForm_cons_mfderiv_subtypeVal_boundary (x : (𝓡∂ (n + 1)).boundary M)
    [Fact (Module.finrank ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) = n + 1)]
    [Fact (Module.finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) = n)]
    (o : Orientation ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) (Fin (n + 1)))
    (u : TangentSpace (𝓡∂ (n + 1)) (x : M))
    (v : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    o.volumeForm (Fin.cons u fun i ↦
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x (v i)) =
      inner ℝ u (outwardUnitNormal x) *
        Orientation.volumeForm (E := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
          (Orientation.halfSpaceBoundaryOrientation o) v := by
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) x
  set N := outwardUnitNormal x
  set o_b := Orientation.halfSpaceBoundaryOrientation o
  obtain ⟨b, b', hb'_coe, horient⟩ := exists_orthonormalBasis_cons_outwardUnitNormal x o
  -- Reduce evaluation of the boundary `n`-form `η := ι_u (o.volumeForm) ∘ dι` to the basis `b`.
  let η : AlternatingMap ℝ (TangentSpace (bdryI n) x) ℝ (Fin n) :=
    (o.volumeForm.curryLeft u).compLinearMap dι.toLinearMap
  have hη_apply (w) : η w = o.volumeForm (Fin.cons u fun i ↦ dι (w i)) := by rfl
  have hη_det : η v = η b.toBasis * b.toBasis.det v := by
    simpa only [smul_apply, smul_eq_mul] using congrArg (· v) (η.eq_smul_basis_det b.toBasis)
  -- Evaluate `η b` by expanding `u` in the orthonormal basis `b' = (N, dι b₀, …, dι bₙ₋₁)`.
  have hη_basis : η b.toBasis = inner ℝ u N * o.volumeForm b'.toBasis := by
    have hcons : (Fin.cons u fun i ↦ dι (b.toBasis i)) =
        Matrix.vecCons u ((0 : Fin (n + 1)).removeNth b'.toBasis) := by
      ext k; refine Fin.cases rfl (fun i ↦ ?_) k; simp [hb'_coe, dι]
    have hb'0 : b' 0 = N := by simpa using congrFun hb'_coe 0
    have hrepr : b'.toBasis.repr u 0 = inner ℝ u N := by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        real_inner_comm, hb'0]
    rw [hη_apply, hcons, o.volumeForm.map_vecCons_removeNth_basis b'.toBasis u 0, hrepr]; simp
  -- Match the orientation signs of `b` and `b'`.
  rw [← hη_apply, hη_det, hη_basis]
  by_cases hb : b.toBasis.orientation = o_b
  · rw [o.volumeForm_robust b' (horient.1 hb), b'.toBasis.det_self,
      Orientation.volumeForm_robust (E := TangentSpace (bdryI n) x) o_b b hb, mul_one]
  · rw [o.volumeForm_robust_neg b' (mt horient.2 hb), neg_apply, b'.toBasis.det_self,
      Orientation.volumeForm_robust_neg (E := TangentSpace (bdryI n) x) o_b b hb, neg_apply]; ring

/-- **Pullback of the interior product of the Riemannian volume form to the boundary.** On an
oriented Riemannian manifold with boundary, restricting `ι_X dV` to `∂M` gives `⟪X, N⟫ dS`. -/
theorem boundaryRestriction_interior_riemannianVolumeForm
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    (X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x) (x : (𝓡∂ (n + 1)).boundary M) :
    boundaryRestriction ((riemannianVolumeForm o).interior X) x =
      inner ℝ (X (x : M)) (outwardUnitNormal x) •
        riemannianVolumeForm (boundaryOrientation o) x := by
  let _ := o.fact_finrank_tangentSpace (x : M)
  let _ := (boundaryOrientation o).fact_finrank_tangentSpace x
  ext v
  rw [boundaryRestriction_apply, RoughForm.interior_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, riemannianVolumeForm_apply, riemannianVolumeForm_apply,
    orientationAt_boundaryOrientation]
  exact volumeForm_cons_mfderiv_subtypeVal_boundary x (o.orientationAt (x : M)) (X (x : M)) v

end TauCeti
