/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.BlockSum
public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Projection
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic

/-!
# The symmetric two-orientation Davis--Kahan bound

Two interval/exterior spectral gaps, one for each of the two opposite directed sine
blocks, control the *whole* projector difference with constant one in every
unitarily invariant seminorm. A single interval/exterior gap only controls the
one-sided sine block in general.

The two cross-block Ky Fan bounds follow from the existing restricted Sylvester
bound and the generic Ky Fan compression identity. The block-sum majorization
theorem combines them without losing the constant. The reusable checkerboard
contraction for two orthogonal projections gives the final bound.

## Main results

* `UnitarilyInvariantSeminorm.mul_map_sub_starProjection_le_map_sub`:
  the constant-one bound for the full difference of the selected orthogonal projections.
* `UnitarilyInvariantSeminorm.mul_map_sinAngleOperator_le_map_sub`:
  the equivalent bound for their symmetric sine-angle operator.

Both results assume invariance of the selected subspaces and interval/exterior
spectral separation in each direction. No common diagonalization or equality
of the selected subspace dimensions is assumed. The inequalities also hold for
nonpositive gap parameters.

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
    -- Expand only the local abbreviations `X` and `C` to expose the
    -- continuous-linear-map composition required by `sylvester_apply`.
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
    -- Only the linear-map/continuous-map application wrappers reduce definitionally;
    -- the ambient-to-submodule projection conversion uses Mathlib's named identity.
    calc
      (X : E →ₗ[K] E) x = W.starProjection (U.starProjection x) := rfl
      _ = (W.orthogonalProjectionOnto (U.orthogonalProjectionOnto x) : E) := by
        rw [U.starProjection_apply, W.starProjection_apply]
      _ = (W.subtype ∘ₗ
          (W.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype) ∘ₗ
          U.orthogonalProjectionOnto.toLinearMap) x := rfl
  have hc : (C : E →ₗ[K] E) =
      W.subtype ∘ₗ
        (W.orthogonalProjectionOnto.toLinearMap ∘ₗ
          (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)) ∘ₗ
        U.orthogonalProjectionOnto.toLinearMap := by
    ext x
    -- Project into U before applying the residual, and back into W afterward.
    -- Both projection conversions use Mathlib's explicit ambient/subtype identity.
    calc
      (C : E →ₗ[K] E) x = W.starProjection ((B - A) (U.starProjection x)) := rfl
      _ = (W.orthogonalProjectionOnto ((B - A) (U.orthogonalProjectionOnto x)) : E) := by
        rw [U.starProjection_apply, W.starProjection_apply]
      _ = (W.subtype ∘ₗ
          (W.orthogonalProjectionOnto.toLinearMap ∘ₗ
            (((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ U.subtype)) ∘ₗ
          U.orthogonalProjectionOnto.toLinearMap) x := rfl
  rw [hx, hc, LinearMap.kyFanSum_subtype_comp_comp_orthogonalProjectionOnto,
    LinearMap.kyFanSum_subtype_comp_comp_orthogonalProjectionOnto] at hky
  exact hky

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
    {a b c d delta : ℝ}
    (hgapUV : Module.End.PointIntervalExteriorGap
      (A : E →ₗ[K] E) U (B : E →ₗ[K] E) Vᗮ a b delta)
    (hgapVU : Module.End.PointIntervalExteriorGap
      (B : E →ₗ[K] E) V (A : E →ₗ[K] E) Uᗮ c d delta) :
    delta * N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) ≤
      N ((B - A : E →L[K] E) : E →ₗ[K] E) := by
  classical
  -- For nonpositive gaps the estimate follows from nonnegativity of the seminorm.
  rcases le_or_gt delta 0 with hdelta | hdelta
  · exact (mul_nonpos_of_nonpos_of_nonneg hdelta (apply_nonneg N _)).trans
      (apply_nonneg N _)
  -- Symmetry preserves the orthogonal complements of the selected subspaces.
  have hUperp : forall x, x ∈ Uᗮ -> A x ∈ Uᗮ :=
    fun _ hx => hA.orthogonalComplement_mem_invtSubmodule
      (p := U) (fun y hy => hU y hy) hx
  have hVperp : forall x, x ∈ Vᗮ -> B x ∈ Vᗮ :=
    fun _ hx => hB.orthogonalComplement_mem_invtSubmodule
      (p := V) (fun y hy => hV y hy) hx
  -- Assemble the two directed cross-projection and residual blocks.
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
  -- The two spectral-gap hypotheses bound each directed block in every Ky Fan sum.
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
  -- Orthogonal decompositions put both directed bounds on the diagonal of
  -- a block operator; block-sum majorization preserves constant one.
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
  -- Lift the block estimate back to the ambient space through the isometries.
  let liftBlock :
      (WithLp 2 (U × Uᗮ) →ₗ[K] WithLp 2 (Vᗮ × V)) ->
        (E →ₗ[K] E) := fun T =>
    (EV.symm : WithLp 2 (Vᗮ × V) →ₗ[K] E) ∘ₗ T ∘ₗ
      (EU : E →ₗ[K] WithLp 2 (U × Uᗮ))
  have hNB_apply (T : WithLp 2 (U × Uᗮ) →ₗ[K]
      WithLp 2 (Vᗮ × V)) : NB T = N (liftBlock T) := by
    simp only [NB, liftBlock, UnitarilyInvariantSeminorm.arrowCongr_apply]
  -- Adjoint identities turn the reversed blocks into cross-projections.
  have hXVUadj : XVU.adjoint =
      V.orthogonalProjectionOnto.toLinearMap ∘ₗ Uᗮ.subtype := by
    simp only [XVU, LinearMap.adjoint_comp, Submodule.adjoint_subtype,
      Submodule.adjoint_orthogonalProjectionOnto_toLinearMap]
  have hAB : LinearMap.adjoint (((A - B : E →L[K] E) : E →ₗ[K] E)) =
      ((A - B : E →L[K] E) : E →ₗ[K] E) := by
    simp only [ContinuousLinearMap.toLinearMap_sub, map_sub,
      hA.adjoint_eq, hB.adjoint_eq]
  have hCVUadj : CVU.adjoint =
      (V.orthogonalProjectionOnto.toLinearMap ∘ₗ
        (((A - B : E →L[K] E) : E →ₗ[K] E))) ∘ₗ Uᗮ.subtype := by
    simp only [CVU, LinearMap.adjoint_comp, Submodule.adjoint_subtype,
      Submodule.adjoint_orthogonalProjectionOnto_toLinearMap, hAB,
      LinearMap.comp_assoc]
  -- These two identities identify the lifted block operators with the full
  -- projector difference and its checkerboard residual.
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
  -- The generic checkerboard contraction finishes the perturbation bound.
  have hchecker :
      delta * N (((U.starProjection - V.starProjection : E →L[K] E) : E →ₗ[K] E)) ≤
        N ((((B - A : E →L[K] E) : E →ₗ[K] E) ∘ₗ
            (U.starProjection : E →ₗ[K] E)) -
          ((V.starProjection : E →ₗ[K] E) ∘ₗ
            ((B - A : E →L[K] E) : E →ₗ[K] E))) := by
    simpa only [hNB_apply, hXlift, hClift,
      ContinuousLinearMap.toLinearMap_sub] using hblock
  exact hchecker.trans
    (N.map_comp_starProjection_sub_starProjection_comp_le U V
      ((B - A : E →L[K] E) : E →ₗ[K] E))

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
    {a b c d delta : ℝ}
    (hgapUV : Module.End.PointIntervalExteriorGap
      (A : E →ₗ[K] E) U (B : E →ₗ[K] E) Vᗮ a b delta)
    (hgapVU : Module.End.PointIntervalExteriorGap
      (B : E →ₗ[K] E) V (A : E →ₗ[K] E) Uᗮ c d delta) :
    delta * N ((U.sinAngleOperator V : E →L[K] E) : E →ₗ[K] E) ≤
      N ((B - A : E →L[K] E) : E →ₗ[K] E) := by
  rw [N.map_sinAngleOperator_eq_map_sub_starProjection U V]
  exact N.mul_map_sub_starProjection_le_map_sub hA hB hU hV hgapUV hgapVU

end UnitarilyInvariantSeminorm

end TauCeti
