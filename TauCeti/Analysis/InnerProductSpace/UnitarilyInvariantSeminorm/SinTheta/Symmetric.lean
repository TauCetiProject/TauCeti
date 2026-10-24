/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.BlockSum
public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic

/-!
# The symmetric two-orientation Davis--Kahan bound

Two interval/exterior spectral gaps, one for each of the two opposite directed sine
blocks, control the *whole* projector difference with constant one in every
unitarily invariant seminorm. A single interval/exterior gap only controls the
one-sided sine block in general.

The two cross-block Ky Fan bounds follow from the existing restricted Sylvester
bound. The block-sum majorization theorem combines them without losing the
constant. A pair of subspace reflections then bounds the checkerboard part of
the perturbation by the perturbation itself.

## Source

Adapted from the AIQ-Kitware DKPS formalization, Apache-2.0:
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`,
`sinAngleOperator_perturbation_le`.

## References

* C. Davis and W. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1--46, Proposition 6.1.
* R. Bhatia, *Matrix Analysis*, Springer (1997), Section VII.2.
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E]
  [InnerProductSpace K E] [FiniteDimensional K E]

/-- Ky Fan sums do not change when a rectangular map is extended by zero off
its source subspace and included into the ambient target. -/
private theorem kyFanSum_submodule_compression
    (U W : Submodule K E) [U.HasOrthogonalProjection]
    (T : U →ₗ[K] W) (k : Nat) :
    (W.subtype ∘ₗ T ∘ₗ U.orthogonalProjectionOnto.toLinearMap).kyFanSum k =
      T.kyFanSum k := by
  have hU : LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      U.orthogonalProjectionOnto.toLinearMap := by
    rw [eq_comm]
    apply (LinearMap.eq_adjoint_iff
      U.orthogonalProjectionOnto.toLinearMap U.subtype).2
    intro x y
    change ⟪U.starProjection x, (y : E)⟫_K = ⟪x, (y : E)⟫_K
    rw [U.inner_starProjection_left_eq_right,
      U.starProjection_eq_self_iff.mpr y.2]
  have hcomp :
      W.subtype ∘ₗ T ∘ₗ U.orthogonalProjectionOnto.toLinearMap =
        (W.subtypeₗᵢ.toLinearMap ∘ₗ T) ∘ₗ
          LinearMap.adjoint U.subtypeₗᵢ.toLinearMap := by
    rw [hU]
    ext x
    rfl
  rw [hcomp]
  simp only [LinearMap.kyFanSum_def,
    LinearMap.singularValues_comp_adjoint_linearIsometry,
    LinearMap.singularValues_linearIsometry_comp]

/-- The restricted Sylvester estimate gives Ky Fan domination of each
rectangular cross-projection by the corresponding residual block. -/
private theorem kyFanSum_cross_block_le
    {A B : E →L[K] E}
    (hA : (A : E →ₗ[K] E).IsSymmetric)
    (hB : (B : E →ₗ[K] E).IsSymmetric)
    {U W : Submodule K E} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : forall x, x ∈ U -> A x ∈ U)
    (hW : forall x, x ∈ W -> B x ∈ W)
    {a b delta : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap
      (A : E →ₗ[K] E) U (B : E →ₗ[K] E) W a b delta)
    (k : Nat) :
    delta * (W.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype).kyFanSum k ≤
      (W.orthogonalProjectionOnto.toLinearMap ∘ₗ
        (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)).kyFanSum k := by
  let X : E →L[K] E := W.starProjection ∘L U.starProjection
  let C : E →L[K] E := W.starProjection ∘L (B - A) ∘L U.starProjection
  have hcommA : forall x, U.starProjection (A x) = A (U.starProjection x) :=
    hA.starProjection_apply_comm (fun x hx => hU x hx)
  have hcommB : forall x, W.starProjection (B x) = B (W.starProjection x) :=
    hB.starProjection_apply_comm (fun x hx => hW x hx)
  have hsyl : B.sylvester A X = C := by
    change B.sylvester A (W.starProjection ∘L U.starProjection) =
      W.starProjection ∘L (B - A) ∘L U.starProjection
    ext x
    simp only [ContinuousLinearMap.sylvester_apply, sub_apply,
      ContinuousLinearMap.comp_apply, map_sub, hcommA, hcommB]
  let NK : UnitarilyInvariantSeminorm K E E := UnitarilyInvariantSeminorm.kyFan K E E k
  have hbound : delta * NK X ≤ NK (B.sylvester A X) :=
    NK.mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_swap_of_mem
      hB hA hW hU hgap
      (fun x => W.starProjection_apply_mem (U.starProjection x))
      (fun x hx => by simp [X, U.starProjection_apply_eq_zero_iff.mpr hx])
  rw [hsyl] at hbound
  have hky :
      delta * (X : E →ₗ[K] E).kyFanSum k ≤
        (C : E →ₗ[K] E).kyFanSum k := by
    simpa only [NK, UnitarilyInvariantSeminorm.kyFan_apply] using hbound
  have hx : (X : E →ₗ[K] E) =
      W.subtype ∘ₗ
        (W.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype) ∘ₗ
        U.orthogonalProjectionOnto.toLinearMap := by
    ext x
    rfl
  have hc : (C : E →ₗ[K] E) =
      W.subtype ∘ₗ
        (W.orthogonalProjectionOnto.toLinearMap ∘ₗ
          (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)) ∘ₗ
        U.orthogonalProjectionOnto.toLinearMap := by
    ext x
    rfl
  rw [hx, hc, kyFanSum_submodule_compression,
    kyFanSum_submodule_compression] at hky
  exact hky

/-- Taking adjoints transposes the cross projection between two subspaces. -/
private theorem adjoint_cross_projection
    (W V : Submodule K E) [W.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    LinearMap.adjoint
        (W.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype) =
      V.orthogonalProjectionOnto.toLinearMap ∘ₗ W.subtype := by
  exact ((LinearMap.eq_adjoint_iff _ _).2 fun w v => by simp).symm

/-- Transposition of a compressed symmetric perturbation. -/
private theorem adjoint_cross_perturbation
    (W V : Submodule K E) [W.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    {H : E →ₗ[K] E} (hH : LinearMap.adjoint H = H) :
    LinearMap.adjoint
        (W.orthogonalProjectionOnto.toLinearMap ∘ₗ
          (H ∘ₗ V.subtype)) =
      (V.orthogonalProjectionOnto.toLinearMap ∘ₗ H) ∘ₗ W.subtype := by
  have hW : LinearMap.adjoint W.subtype =
      W.orthogonalProjectionOnto.toLinearMap := by
    rw [eq_comm]
    apply (LinearMap.eq_adjoint_iff
      W.orthogonalProjectionOnto.toLinearMap W.subtype).2
    intro x y
    change ⟪W.starProjection x, (y : E)⟫_K = ⟪x, (y : E)⟫_K
    rw [W.inner_starProjection_left_eq_right,
      W.starProjection_eq_self_iff.mpr y.2]
  have hV : LinearMap.adjoint V.subtype =
      V.orthogonalProjectionOnto.toLinearMap := by
    rw [eq_comm]
    apply (LinearMap.eq_adjoint_iff
      V.orthogonalProjectionOnto.toLinearMap V.subtype).2
    intro x y
    change ⟪V.starProjection x, (y : E)⟫_K = ⟪x, (y : E)⟫_K
    rw [V.inner_starProjection_left_eq_right,
      V.starProjection_eq_self_iff.mpr y.2]
  have hW' : LinearMap.adjoint W.orthogonalProjectionOnto.toLinearMap =
      W.subtype := by
    rw [← hW, LinearMap.adjoint_adjoint]
  simp only [LinearMap.adjoint_comp, hH, hV, hW', LinearMap.comp_assoc]

namespace UnitarilyInvariantSeminorm

/-- **Symmetric, constant-one Davis--Kahan theorem.** If the selected
subspaces of symmetric operators `A` and `B` are invariant, and both opposite
interval/exterior gap conditions hold with width `delta`, the entire
projection difference is bounded in every unitarily invariant seminorm:

`delta * N(P_U - P_V) ≤ N(B - A)`.

Unlike the directed sine theorem, both spectral orientations are required. -/
theorem mul_map_sub_starProjection_le_map_sub
    (N : UnitarilyInvariantSeminorm K E E)
    {A B : E →L[K] E}
    (hA : (A : E →ₗ[K] E).IsSymmetric)
    (hB : (B : E →ₗ[K] E).IsSymmetric)
    {U V : Submodule K E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : forall x, x ∈ U -> A x ∈ U)
    (hV : forall x, x ∈ V -> B x ∈ V)
    {a b c d delta : ℝ} (hdelta : 0 < delta)
    (hgapUV : Module.End.PointIntervalExteriorGap
      (A : E →ₗ[K] E) U (B : E →ₗ[K] E) Vᗮ a b delta)
    (hgapVU : Module.End.PointIntervalExteriorGap
      (B : E →ₗ[K] E) V (A : E →ₗ[K] E) Uᗮ c d delta) :
    delta * N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) ≤
      N ((B - A : E →L[K] E) : E →ₗ[K] E) := by
  classical
  have hUperp : forall x, x ∈ Uᗮ -> A x ∈ Uᗮ :=
    fun _ hx => hA.orthogonalComplement_mem_invtSubmodule
      (p := U) (fun y hy => hU y hy) hx
  have hVperp : forall x, x ∈ Vᗮ -> B x ∈ Vᗮ :=
    fun _ hx => hB.orthogonalComplement_mem_invtSubmodule
      (p := V) (fun y hy => hV y hy) hx
  let XUV : U →ₗ[K] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  let CUV : U →ₗ[K] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
      (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)
  let XVU : V →ₗ[K] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ V.subtype
  let CVU : V →ₗ[K] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ
      (((A - B : E →L[K] E) : E →ₗ[K] E) ∘ₗ V.subtype)
  have hkyUV (k : Nat) :
      (((delta : ℝ) : K) • XUV).kyFanSum k ≤ CUV.kyFanSum k := by
    rw [LinearMap.kyFanSum_smul, RCLike.norm_ofReal,
      abs_of_nonneg hdelta.le]
    exact kyFanSum_cross_block_le hA hB hU hVperp hgapUV k
  have hkyVU (k : Nat) :
      (((delta : ℝ) : K) • (-XVU.adjoint)).kyFanSum k ≤
        CVU.adjoint.kyFanSum k := by
    rw [LinearMap.kyFanSum_smul, RCLike.norm_ofReal,
      abs_of_nonneg hdelta.le, LinearMap.kyFanSum_neg,
      LinearMap.kyFanSum_adjoint, LinearMap.kyFanSum_adjoint]
    exact kyFanSum_cross_block_le hB hA hV hUperp hgapVU k
  let EU : E ≃ₗᵢ[K] WithLp 2 (U × Uᗮ) := U.orthogonalDecomposition
  let EV : E ≃ₗᵢ[K] WithLp 2 (Vᗮ × V) :=
    V.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdComm 2 K V Vᗮ)
  let NB : UnitarilyInvariantSeminorm K
      (WithLp 2 (U × Uᗮ)) (WithLp 2 (Vᗮ × V)) :=
    (UnitarilyInvariantSeminorm.arrowCongr EU EV) N
  let Xblock : WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V) :=
    (XUV.prodMap (-XVU.adjoint)).withLpMap 2
  let Cblock : WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V) :=
    (CUV.prodMap CVU.adjoint).withLpMap 2
  have hsmul :
      (((delta : ℝ) : K) • Xblock) =
        ((((delta : ℝ) : K) • XUV).prodMap
          (((delta : ℝ) : K) • (-XVU.adjoint))).withLpMap 2 := by
    ext x
    apply WithLp.ofLp_injective 2
    simp [Xblock, WithLp.map, LinearMap.prodMap_apply]
  have hblock : delta * NB Xblock ≤ NB Cblock := by
    have h := NB.map_prodMap_withLpMap_le hkyUV hkyVU
    rw [← hsmul, map_smul_eq_mul, RCLike.norm_ofReal,
      abs_of_nonneg hdelta.le] at h
    exact h
  let liftBlock :
      (WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V)) ->
        (E →ₗ[K] E) := fun T =>
    (EV.symm : WithLp 2 (Vᗮ × V) →ₗ[K] E) ∘ₗ T ∘ₗ
      (EU : E →ₗ[K] WithLp 2 (U × Uᗮ))
  have hNB_apply (T : WithLp 2 (U × Uᗮ) →ₗ[K]
      WithLp 2 (Vᗮ × V)) : NB T = N (liftBlock T) := by
    simp only [NB, liftBlock, UnitarilyInvariantSeminorm.arrowCongr_apply]
  have hXVUadj : XVU.adjoint =
      V.orthogonalProjectionOnto.toLinearMap ∘ₗ Uᗮ.subtype :=
    adjoint_cross_projection Uᗮ V
  have hCVUadj : CVU.adjoint =
      (V.orthogonalProjectionOnto.toLinearMap ∘ₗ
        (((A - B : E →L[K] E) : E →ₗ[K] E))) ∘ₗ Uᗮ.subtype :=
    adjoint_cross_perturbation Uᗮ V
      (by simp only [ContinuousLinearMap.toLinearMap_sub, map_sub,
          hA.adjoint_eq, hB.adjoint_eq])
  have hXlift : liftBlock Xblock =
      (U.starProjection : E →ₗ[K] E) - (V.starProjection : E →ₗ[K] E) := by
    ext x
    simp [liftBlock, Xblock, EU, EV, hXVUadj, XUV,
      WithLp.map, LinearMap.prodMap_apply, LinearMap.comp_apply,
      Submodule.orthogonalDecomposition_apply]
  have hClift : liftBlock Cblock =
      (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ
        (U.starProjection : E →ₗ[K] E)) -
      ((V.starProjection : E →ₗ[K] E) ∘ₗ
        ((B - A : E →L[K] E) : E →ₗ[K] E)) := by
    ext x
    simp [liftBlock, Cblock, EU, EV, hCVUadj, CUV,
      WithLp.map, LinearMap.prodMap_apply, LinearMap.comp_apply,
      Submodule.orthogonalDecomposition_apply]
    module
  have hchecker :
      delta * N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) ≤
        N ((((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ
            (U.starProjection : E →ₗ[K] E)) -
          ((V.starProjection : E →ₗ[K] E) ∘ₗ
            ((B - A : E →L[K] E) : E →ₗ[K] E))) := by
    simpa only [hNB_apply, hXlift, hClift,
      ContinuousLinearMap.toLinearMap_sub] using hblock
  let H : E →ₗ[K] E := ((B - A : E →L[K] E) : E →ₗ[K] E)
  let JU : E ≃ₗᵢ[K] E := U.reflection
  let JV : E ≃ₗᵢ[K] E := V.reflection
  -- Twice the checkerboard is the difference of two isometric conjugates.
  -- Working with the factor 2 avoids inverse-scalar elaboration entirely.
  have hdouble :
      (2 : K) • (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
          (V.starProjection : E →ₗ[K] E) ∘ₗ H) =
        H ∘ₗ JU.toLinearMap - JV.toLinearMap ∘ₗ H := by
    ext x
    simp [H, JU, JV, Submodule.reflection_apply, LinearMap.comp_apply]
    module
  have hnorm :
      N (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
          (V.starProjection : E →ₗ[K] E) ∘ₗ H) ≤ N H := by
    have htwonorm :
        N ((2 : K) • (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
            (V.starProjection : E →ₗ[K] E) ∘ₗ H)) =
          2 * N (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
            (V.starProjection : E →ₗ[K] E) ∘ₗ H) := by
      simp only [map_smul_eq_mul, RCLike.norm_ofNat]
    have hscaled :
        2 * N (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
            (V.starProjection : E →ₗ[K] E) ∘ₗ H) ≤ 2 * N H := by
      calc
        _ = N ((2 : K) • (H ∘ₗ (U.starProjection : E →ₗ[K] E) -
            (V.starProjection : E →ₗ[K] E) ∘ₗ H)) := htwonorm.symm
        _ = N (H ∘ₗ JU.toLinearMap - JV.toLinearMap ∘ₗ H) := by rw [hdouble]
        _ ≤ N (H ∘ₗ JU.toLinearMap) + N (-(JV.toLinearMap ∘ₗ H)) := by
          simpa [sub_eq_add_neg] using
            map_add_le_add N (H ∘ₗ JU.toLinearMap) (-(JV.toLinearMap ∘ₗ H))
        _ = N H + N H := by
          have hJU : JU.toLinearMap = (JU : E →ₗ[K] E) := by
            ext x
            simp
          have hJV : JV.toLinearMap = (JV : E →ₗ[K] E) := by
            ext x
            simp
          have hright : N (H ∘ₗ JU.toLinearMap) = N H := by
            rw [hJU]
            exact N.map_comp_linearIsometryEquiv JU H
          have hleft : N (JV.toLinearMap ∘ₗ H) = N H := by
            rw [hJV]
            exact N.map_linearIsometryEquiv_comp JV H
          rw [map_neg_eq_map N, hright, hleft]
        _ = 2 * N H := by ring
    exact le_of_mul_le_mul_left hscaled (by norm_num : (0 : ℝ) < 2)
  exact hchecker.trans hnorm

/-- The same constant-one theorem expressed in the canonical symmetric sine
angle operator `|P_U-P_V|`. -/
theorem mul_map_sinAngleOperator_le_map_sub
    [CompleteSpace E] (N : UnitarilyInvariantSeminorm K E E)
    {A B : E →L[K] E}
    (hA : (A : E →ₗ[K] E).IsSymmetric)
    (hB : (B : E →ₗ[K] E).IsSymmetric)
    {U V : Submodule K E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hU : forall x, x ∈ U -> A x ∈ U)
    (hV : forall x, x ∈ V -> B x ∈ V)
    {a b c d delta : ℝ} (hdelta : 0 < delta)
    (hgapUV : Module.End.PointIntervalExteriorGap
      (A : E →ₗ[K] E) U (B : E →ₗ[K] E) Vᗮ a b delta)
    (hgapVU : Module.End.PointIntervalExteriorGap
      (B : E →ₗ[K] E) V (A : E →ₗ[K] E) Uᗮ c d delta) :
    delta * N ((U.sinAngleOperator V : E →L[K] E) : E →ₗ[K] E) ≤
      N ((B - A : E →L[K] E) : E →ₗ[K] E) := by
  have hmod :
      N ((U.sinAngleOperator V : E →L[K] E) : E →ₗ[K] E) =
        N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) := by
    apply N.map_eq_of_singularValues_eq
    apply LinearMap.singularValues_eq_of_norm_apply_eq
    intro x
    change ‖U.sinAngleOperator V x‖ =
      ‖(U.starProjection - V.starProjection) x‖
    simpa only [sub_apply] using
      (U.norm_sinAngleOperator_apply V x)
  rw [hmod]
  exact N.mul_map_sub_starProjection_le_map_sub hA hB hU hV hdelta hgapUV hgapVU

end UnitarilyInvariantSeminorm

end TauCeti
