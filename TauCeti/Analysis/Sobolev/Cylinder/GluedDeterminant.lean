/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Gluing
public import TauCeti.Analysis.Sobolev.Cylinder.GluedIndex
import TauCeti.Analysis.Normed.Operator.PositiveDeterminant

/-!
# The determinant line of operators glued along a neck

Let `D₁` and `D₂` be first-order operators on the cylinder `ℝ × S¹`, from `W^{1,2}` to `L²`,
whose ends match, and let `D_R` be the operator glued along a neck of length `2 R`. Stabilize the
pieces by `ιᵢ : Sᵢ → L²`, so that `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` have right inverses, and the glued
operator by the translated stabilizers `j_R`, so that `A_R (ξ, σ₁, σ₂) = D_R ξ + j_R (σ₁, σ₂)`
is onto. For a right inverse `Q` of `A_R`, the gluing map `E₁ × E₂ → E_R` of the stabilized
kernels (`TauCeti.CylinderSobolev.gluingKerMap`) preglues and corrects along the range of `Q`; for
long necks and uniformly bounded `Q` it is an isomorphism
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_gluingKerMap_bijective`). Through
`ContinuousLinearMap.detLineGluingEquiv` it identifies the determinant lines,

`det D_R ≃ det D₁ ⊗ det D₂`,

in the order `D₁, D₂` and `S₁, S₂`. Up to an explicit sign, its inverse is the four-term
isomorphism of the exact sequence of linear gluing
`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`, whose middle map is the obstruction map `b_R`
(`TauCeti.CylinderSobolev.gluingObstruction`), read through the stabilization isomorphisms of the
pieces (`detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv_gluingObstruction`): through the
gluing map this sequence is the stabilization sequence of `A_R`.

The gluing map depends on the right inverse `Q`, but the orientations it induces do not. Right
inverses of `A_R` form an affine space, and the gluing map is affine in `Q`
(`TauCeti.CylinderSobolev.gluingKerMap_apply_of_eq_add_smul_sub`). Along the segment from `Q` to
another right inverse `Q'` of norm at most `C` all right inverses have norm at most `C`, so for
long necks all their gluing maps are isomorphisms. Hence `det (G_{Q'}⁻¹ ∘ G_Q)` does not vanish
along the segment and is positive, and the two determinant-line isomorphisms differ by a positive
factor (`TauCeti.CylinderSobolev.exists_forall_ge_exists_pos_detLineGluingEquiv_eq_smul`). Over
`ℝ`, for fixed stabilizers, the orientation of `det D_R` glued from orientations of `det D₁` and
`det D₂` therefore does not depend on the right inverse.

## Main results

* `detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv_gluingObstruction`: the glued
  determinant-line isomorphism is the four-term isomorphism of the exact sequence of linear
  gluing, up to sign.
* `TauCeti.CylinderSobolev.gluingKerMap_apply_of_eq_add_smul_sub`: the gluing map is affine in the
  right inverse.
* `TauCeti.CylinderSobolev.exists_forall_ge_exists_pos_detLineGluingEquiv_eq_smul`: for long necks
  the determinant-line isomorphisms `det D_R ≃ det D₁ ⊗ det D₂` of two right inverses of bounded
  norm differ by a positive factor.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section A.2 (determinant line bundles) and Chapter 10
  (linear gluing).
* A. Floer and H. Hofer, *Coherent orientations for periodic orbit problems in symplectic
  geometry*, Math. Z. 212 (1993), 13–38 (gluing of determinant lines along necks).
-/

public section

noncomputable section

open Filter MeasureTheory Set Module TensorProduct
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {S₁ S₂ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁]
  [NormedAddCommGroup S₂] [NormedSpace ℝ S₂]
  {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure}
  {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {R : ℝ}

/-! ### The gluing map is affine in the right inverse -/

/-- **The gluing map is affine in the right inverse.** For right inverses `Q`, `Q'` and
`Q'' = Q + t • (Q' - Q)` of the stabilized glued operator, the gluing map along `Q''` is
`G_Q + t • (G_{Q'} - G_Q)`. -/
theorem gluingKerMap_apply_of_eq_add_smul_sub
    {Q Q' Q'' : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hQ' : Function.RightInverse Q' (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hQ'' : Function.RightInverse Q'' (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))) {t : ℝ}
    (ht : Q'' = Q + t • (Q' - Q))
    (k : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker ×
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker) :
    gluingKerMap hQ'' k = gluingKerMap hQ k + t • (gluingKerMap hQ' k - gluingKerMap hQ k) := by
  subst ht
  refine Subtype.ext ?_
  simp only [coe_gluingKerMap_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub,
    add_apply, smul_apply, sub_apply]
  module

/-! ### The exact sequence of linear gluing -/

section ExactSequence

variable [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).ker]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).ker]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure
    (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
      (H1 V).subtypeL).ker]

/-- **The glued determinant line from the exact sequence of linear gluing.** When the gluing map
along a right inverse `Q` of `A_R` is bijective, the inverse of the determinant-line isomorphism
`det D_R ≃ det D₁ ⊗ det D₂` that it induces, applied to the tensor product of the normalized
stabilization isomorphisms of the pieces, is the four-term isomorphism
`TauCeti.detLineFourTermEquiv` of the exact sequence of linear gluing
`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`, with middle map the obstruction map `b_R`,
applied to the product of the stabilized lines of the pieces, up to the sign
`(-1) ^ (dim S₁ * (dim ker D₂ + dim coker D₂) + dim coker D_R * dim (S₁ × S₂))`. -/
theorem detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv_gluingObstruction
    {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (h : Function.Bijective (gluingKerMap hQ))
    (hA₁ : Function.Surjective
      (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (hA₂ : Function.Surjective
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    (w : (detLine ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker ⊗[ℝ]
        Dual ℝ (detLine ℝ S₁)) ⊗[ℝ]
      (detLine ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker ⊗[ℝ]
        Dual ℝ (detLine ℝ S₂))) :
    (detLineGluingEquiv _ (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h) hA₁ hA₂
        hQ.surjective).symm (TensorProduct.congr (detLineStabilizationEquiv _ ι₁ hA₁)
          (detLineStabilizationEquiv _ ι₂ hA₂) w) =
      (-1 : ℝ) ^ (finrank ℝ S₁ * (finrank ℝ ((jetOperator 2 stripMeasure M₂).comp
          (H1 V).subtypeL).ker + finrank ℝ (Lp W 2 stripMeasure ⧸
            ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).range)) +
          finrank ℝ (Lp W 2 stripMeasure ⧸ ((jetOperator 2 stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
              (H1 V).subtypeL).range) * finrank ℝ (S₁ × S₂)) •
        detLineFourTermEquiv (gluingKerInclusion_injective hQ h)
          (exact_gluingKerInclusion_gluingObstruction hQ h)
          (exact_gluingObstruction_parameterToCoker hQ h.2)
          ((parameterToCoker_surjective_iff_coprod_surjective _ _).2 hQ.surjective)
          (detLineTensorDualProdEquiv ℝ _ _ _ _ w) := by
  have hg : ∀ k, (gluingObstruction hQ : _ →ₗ[ℝ] S₁ × S₂) k = parameterProj _ _
      (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h k) := fun k ↦ by
    rw [ContinuousLinearMap.coe_coe, gluingObstruction_apply, LinearEquiv.ofBijective_apply,
      parameterProj_apply, ContinuousLinearMap.coe_coe, coe_gluingKerMap_apply, Prod.snd_sub,
      neckPreglue_apply_snd]
  exact detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv _ hA₁ hA₂ hQ.surjective
    (gluingKerMap_gluingKerInclusion hQ h) hg (gluingKerInclusion_injective hQ h)
    (exact_gluingKerInclusion_gluingObstruction hQ h)
    (exact_gluingObstruction_parameterToCoker hQ h.2)
    ((parameterToCoker_surjective_iff_coprod_surjective _ _).2 hQ.surjective) w

end ExactSequence

/-! ### Independence of the right inverse -/

variable [CompleteSpace W] in
/-- **The glued orientation does not depend on the right inverse.** Let `D₁` and `D₂` be
first-order operators on the cylinder whose coefficient fields are essentially bounded with matching
ends, and let `ιᵢ : Sᵢ → L²` be finite-dimensional stabilizers supported away from the glued ends,
such that the stabilized operators `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` have bounded right inverses `Qᵢ` and
`Dᵢ` has finite-dimensional kernel. Fix a bound `C`. Then for every sufficiently long neck and any
two right inverses `Q`, `Q'` of the stabilized glued operator `A_R` of norm at most `C`, the gluing
maps along `Q` and `Q'` are isomorphisms `E₁ × E₂ ≃ E_R`, and the determinant-line isomorphisms
`det D_R ≃ det D₁ ⊗ det D₂` that they induce (`ContinuousLinearMap.detLineGluingEquiv`) differ by
a positive factor. -/
theorem exists_forall_ge_exists_pos_detLineGluingEquiv_eq_smul
    {M : ℝ → V × V × V →L[ℝ] W} (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1)) {T : ℝ}
    (hι₁ : ∀ σ, ∀ᵐ z ∂stripMeasure, T < z.1 → ι₁ σ z = 0)
    (hι₂ : ∀ σ, ∀ᵐ z ∂stripMeasure, z.1 < -T → ι₂ σ z = 0)
    {Q₁ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₁} {Q₂ : Lp W 2 stripMeasure →L[ℝ] H1 V × S₂}
    (hQ₁ : (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).comp Q₁ =
      ContinuousLinearMap.id ℝ _)
    (hQ₂ : (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).comp Q₂ =
      ContinuousLinearMap.id ℝ _)
    [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂]
    [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).ker]
    [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).ker] (C : ℝ) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ (Q Q' : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂))
      (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
      (hQ' : Function.RightInverse Q' (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))),
      ‖Q‖ ≤ C → ‖Q'‖ ≤ C →
        ∃ (h : Function.Bijective (gluingKerMap hQ)) (h' : Function.Bijective (gluingKerMap hQ'))
          (c : ℝ), 0 < c ∧
          ∀ (hA₁ : Function.Surjective
              (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
            (hA₂ : Function.Surjective
              (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
            (x : ((jetOperator 2 stripMeasure
              (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
                (H1 V).subtypeL : H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine),
            detLineGluingEquiv _ (LinearEquiv.ofBijective (gluingKerMap hQ').toLinearMap h') hA₁
                hA₂ hQ'.surjective x =
              c • detLineGluingEquiv _ (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h)
                hA₁ hA₂ hQ.surjective x := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_forall_gluingKerMap_bijective hM₁ hM₂ h₁ h₂ hι₁ hι₂ hQ₁ hQ₂ C
  refine ⟨R₀, fun R hR Q Q' hQ hQ' hQn hQn' ↦ ?_⟩
  have hbij := (hR₀ R hR).2
  have h := hbij Q hQ hQn
  have h' := hbij Q' hQ' hQn'
  set G := LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h
  set G' := LinearEquiv.ofBijective (gluingKerMap hQ').toLinearMap h'
  -- The isomorphisms `G` and `G'` are joined by the gluing maps `G_{Q + t (Q' - Q)}`, which are
  -- injective for `0 ≤ t ≤ 1`, since `‖Q + t • (Q' - Q)‖ ≤ C` by convexity of the ball.
  have hpos := LinearEquiv.det_trans_symm_pos_of_forall_injective
    (K := (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁).ker ×
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker)
    (Y := (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)).ker) G G' fun t ht ↦ by
    have hnorm : ‖Q + t • (Q' - Q)‖ ≤ C := by
      refine opNorm_le_bound _ ((norm_nonneg Q).trans hQn) fun y ↦ ?_
      have hy : (Q + t • (Q' - Q)) y = (1 - t) • Q y + t • Q' y := by
        simp only [add_apply, smul_apply, sub_apply]
        module
      rw [hy]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ht.2), Real.norm_of_nonneg ht.1]
      nlinarith [Q.le_of_opNorm_le hQn y, Q'.le_of_opNorm_le hQn' y, ht.1, ht.2, norm_nonneg y]
    -- Affine combinations of right inverses are right inverses.
    have hQt : Function.RightInverse (Q + t • (Q' - Q)) (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)) := fun y ↦ by
      simp [map_add, map_smul, map_sub, hQ y, hQ' y]
    intro k k' hkk'
    refine (hbij _ hQt hnorm).1 ?_
    rw [gluingKerMap_apply_of_eq_add_smul_sub hQ hQ' hQt rfl,
      gluingKerMap_apply_of_eq_add_smul_sub hQ hQ' hQt rfl]
    exact hkk'
  exact ⟨h, h', _, hpos,
    fun hA₁ hA₂ x ↦ detLineGluingEquiv_eq_det_smul G G' hA₁ hA₂ hQ.surjective x⟩

end TauCeti.CylinderSobolev
