/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Gluing
public import TauCeti.Analysis.Sobolev.Cylinder.Glued.Index

/-!
# The determinant line of glued operators on the cylinder

Let `D₁` and `D₂` be first-order operators on the cylinder `ℝ × S¹`, from `W^{1,2}` to `L²`, with
essentially bounded coefficient fields `M₁` and `M₂` whose ends match, and let `D_R` be the
operator of the glued coefficient field along a neck of length `2 R`. Stabilize the pieces by
`ιᵢ : Sᵢ → L²`, so that `Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` is onto with kernel `Eᵢ`, and the glued operator
by the translated stabilizers `j_R`, so that `A_R (ξ, σ₁, σ₂) = D_R ξ + j_R (σ₁, σ₂)` has kernel
`E_R`. For a right inverse `Q` of `A_R`, the corrected pregluing
`TauCeti.CylinderSobolev.gluingKerMap` is a linear isomorphism `E₁ × E₂ ≃ E_R` for long necks
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_gluingKerMap_bijective`). This file turns it
into the ordered isomorphism of determinant lines

`det D₁ ⊗ det D₂ ≃ det D_R`

(`TauCeti.CylinderSobolev.gluingDetLineEquiv`), an instance of the general stabilized gluing
isomorphism `ContinuousLinearMap.detLineGluingEquiv`. Over `ℝ` it carries orientations of the
determinant lines of the pieces to an orientation of that of the glued operator, which is how
coherent orientations of moduli spaces of Floer trajectories are glued.

**The exact sequence of linear gluing.** The obstruction map `b_R : E₁ × E₂ → S₁ × S₂` is the
middle map of the exact sequence

`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`

(`TauCeti.CylinderSobolev.exact_gluingKerInclusion_gluingObstruction`). Its four-term isomorphism
`det (E₁ × E₂) ⊗ (det (S₁ × S₂))^* ≃ det D_R` (`TauCeti.detLineFourTermEquiv`) is the gluing
isomorphism read through the stabilizations of the pieces, up to an explicit sign
(`gluingDetLineEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv`). So the gluing
isomorphism is determined by the projection of the glued kernel to the stabilizers.

**Independence of the right inverse.** The gluing map depends on the right inverse `Q`. If for a
bound `C` every right inverse of norm at most `C` gives a bijective gluing map, as it does for long
necks, then any two such right inverses `Q` and `Q'` give gluing isomorphisms differing by a
positive factor (`TauCeti.CylinderSobolev.exists_pos_gluingDetLineEquiv_apply_eq_smul`), so they
induce the same orientation transport. The right inverses `Q + s (Q' - Q)`, `s ∈ [0, 1]`, all
have norm at most `C`, the gluing maps along them are invertible and affine in `s`, and so the
determinant of the change between the two gluing maps cannot change sign.

## Main definitions

* `TauCeti.CylinderSobolev.gluingDetLineEquiv`: the ordered isomorphism `det D₁ ⊗ det D₂ ≃ det D_R`
  induced by a bijective gluing map.

## Main results

* `gluingDetLineEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv`: the gluing
  isomorphism is the four-term isomorphism of the exact sequence of linear gluing, up to sign.
* `TauCeti.CylinderSobolev.exists_pos_gluingDetLineEquiv_apply_eq_smul`: right inverses of
  bounded norm give gluing isomorphisms differing by positive factors.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Sections 3.3 and A.2 (linear gluing, stabilization and
  determinant line bundles).
* A. Floer, H. Hofer, *Coherent orientations for periodic orbit problems in symplectic geometry*,
  Math. Z. 212 (1993), 13–38 (gluing of determinant lines along necks).
-/

public section

open MeasureTheory Module TensorProduct

namespace TauCeti.CylinderSobolev

open StripSobolev ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {S₁ S₂ : Type*} [NormedAddCommGroup S₁] [NormedSpace ℝ S₁]
  [NormedAddCommGroup S₂] [NormedSpace ℝ S₂] [FiniteDimensional ℝ S₁] [FiniteDimensional ℝ S₂]
  {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {ι₁ : S₁ →L[ℝ] Lp W 2 stripMeasure}
  {ι₂ : S₂ →L[ℝ] Lp W 2 stripMeasure} {R : ℝ}
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).ker]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).ker]
  [FiniteDimensional ℝ ((jetOperator 2 stripMeasure
    (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
      (H1 V).subtypeL).ker]

section Definition

variable {Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
  (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
    (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
      (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))

/-- **The determinant-line isomorphism of gluing on the cylinder.** Let the stabilized pieces
`Aᵢ (ξ, σ) = Dᵢ ξ + ιᵢ σ` be onto, and let the gluing map `E₁ × E₂ → E_R` along the right inverse
`Q` of the stabilized glued operator `A_R` be bijective
(`TauCeti.CylinderSobolev.gluingKerMap`), as it is for long necks. The ordered isomorphism

`det D₁ ⊗ det D₂ ≃ det D_R`

of determinant lines induced by the gluing map through the stabilizations
(`ContinuousLinearMap.detLineGluingEquiv`, which carries the Koszul sign of its ordering). -/
noncomputable def gluingDetLineEquiv
    (h₁ : Function.Surjective (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (h₂ : Function.Surjective (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    (h : Function.Bijective (gluingKerMap hQ)) :
    (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL :
        H1 V →L[ℝ] Lp W 2 stripMeasure) : H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine ⊗[ℝ]
      (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL :
        H1 V →L[ℝ] Lp W 2 stripMeasure) : H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine ≃ₗ[ℝ]
      (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL : H1 V →L[ℝ] Lp W 2 stripMeasure) :
            H1 V →ₗ[ℝ] Lp W 2 stripMeasure).detLine :=
  detLineGluingEquiv h₁ h₂ hQ.surjective (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h)

/-- `TauCeti.CylinderSobolev.gluingDetLineEquiv` is the general stabilized gluing isomorphism
`ContinuousLinearMap.detLineGluingEquiv` of the gluing map. -/
theorem gluingDetLineEquiv_def
    (h₁ : Function.Surjective (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (h₂ : Function.Surjective (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    (h : Function.Bijective (gluingKerMap hQ)) :
    gluingDetLineEquiv hQ h₁ h₂ h = detLineGluingEquiv h₁ h₂ hQ.surjective
      (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h) :=
  (rfl)

/-- **The gluing isomorphism and the exact sequence of linear gluing.** For `x₁` in
`det E₁ ⊗ (det S₁)^*` and `x₂` in `det E₂ ⊗ (det S₂)^*`, the gluing isomorphism sends the tensor
product of their images in `det D₁` and `det D₂` to the image of their product in
`det (E₁ × E₂) ⊗ (det (S₁ × S₂))^*` (`TauCeti.detLineTensorDualProdEquiv`) under the four-term
isomorphism (`TauCeti.detLineFourTermEquiv`) of the exact sequence of linear gluing

`0 → ker D_R → E₁ × E₂ → S₁ × S₂ → coker D_R → 0`,

whose middle map is the obstruction map `b_R`, times the sign
`(-1) ^ (dim S₁ * (dim E₂ + dim S₂) + dim coker D_R * dim (S₁ × S₂))`. -/
theorem gluingDetLineEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv
    (h₁ : Function.Surjective (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (h₂ : Function.Surjective (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    (h : Function.Bijective (gluingKerMap hQ))
    (x₁ : TauCeti.detLine ℝ (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod
      ι₁).ker ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ S₁))
    (x₂ : TauCeti.detLine ℝ (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod
      ι₂).ker ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ S₂)) :
    gluingDetLineEquiv hQ h₁ h₂ h (detLineStabilizationEquiv _ _ h₁ x₁ ⊗ₜ
        detLineStabilizationEquiv _ _ h₂ x₂) =
      (-1 : ℝ) ^ (finrank ℝ S₁ * (finrank ℝ
          (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂).ker + finrank ℝ S₂) +
        finrank ℝ (Lp W 2 stripMeasure ⧸ ((jetOperator 2 stripMeasure
          (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
            (H1 V).subtypeL).range) * finrank ℝ (S₁ × S₂)) •
        TauCeti.detLineFourTermEquiv (gluingKerInclusion_injective hQ h)
          (exact_gluingKerInclusion_gluingObstruction hQ h)
          (exact_gluingObstruction_parameterToCoker hQ h.2)
          ((parameterToCoker_surjective_iff_coprod_surjective _ _).2 hQ.surjective)
          (TauCeti.detLineTensorDualProdEquiv ℝ _ _ _ _ (x₁ ⊗ₜ x₂)) := by
  -- The obstruction map is the stabilizer component of the gluing map.
  have hb : ∀ k, gluingObstruction hQ k = parameterProj _ (gluedStabilizer ι₁ ι₂ R)
      (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h k) := fun k ↦ by
    simp [gluingObstruction_apply]
  exact detLineGluingEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv h₁ h₂
    hQ.surjective (LinearEquiv.ofBijective (gluingKerMap hQ).toLinearMap h)
    (fK := gluingKerInclusion hQ h) (b := (gluingObstruction hQ : _ →ₗ[ℝ] S₁ × S₂))
    (gluingKerMap_gluingKerInclusion hQ h) hb (gluingKerInclusion_injective hQ h)
    (exact_gluingKerInclusion_gluingObstruction hQ h)
    (exact_gluingObstruction_parameterToCoker hQ h.2) x₁ x₂

end Definition

section RightInverse

/-- **The gluing isomorphism does not depend on the right inverse, up to a positive factor.**
Suppose that for some bound `C` the gluing map along every right inverse of `A_R` of norm at most
`C` is bijective; for long necks this holds for every `C`
(`TauCeti.CylinderSobolev.exists_forall_ge_forall_gluingKerMap_bijective`). Then the gluing
isomorphisms along two right inverses `Q` and `Q'` of norm at most `C` differ by a positive
factor, so over `ℝ` they transport orientations of `det D₁ ⊗ det D₂` to the same orientation of
`det D_R`. -/
theorem exists_pos_gluingDetLineEquiv_apply_eq_smul
    (h₁ : Function.Surjective (((jetOperator 2 stripMeasure M₁).comp (H1 V).subtypeL).coprod ι₁))
    (h₂ : Function.Surjective (((jetOperator 2 stripMeasure M₂).comp (H1 V).subtypeL).coprod ι₂))
    {C : ℝ} (hC : ∀ (Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂))
      (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
        (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
          (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R))),
        ‖Q‖ ≤ C → Function.Bijective (gluingKerMap hQ))
    {Q Q' : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂)}
    (hQ : Function.RightInverse Q (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hQ' : Function.RightInverse Q' (((jetOperator 2 stripMeasure
      (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
        (H1 V).subtypeL).coprod (gluedStabilizer ι₁ ι₂ R)))
    (hQC : ‖Q‖ ≤ C) (hQ'C : ‖Q'‖ ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, gluingDetLineEquiv hQ' h₁ h₂ (hC Q' hQ' hQ'C) t =
      c • gluingDetLineEquiv hQ h₁ h₂ (hC Q hQ hQC) t := by
  refine exists_pos_detLineGluingEquiv_apply_eq_smul h₁ h₂ hQ.surjective _ _ fun s hs ↦ ?_
  -- The right inverse `Q + s (Q' - Q) = (1 - s) Q + s Q'` has norm at most `C`, and its gluing map
  -- is `(1 - s)` times the gluing map along `Q` plus `s` times that along `Q'`.
  have hQsC : ‖Q + s • (Q' - Q)‖ ≤ C := by
    rw [show Q + s • (Q' - Q) = (1 - s) • Q + s • Q' by module]
    calc ‖(1 - s) • Q + s • Q'‖ ≤ ‖(1 - s) • Q‖ + ‖s • Q'‖ :=
          norm_add_le ((1 - s) • Q) (s • Q')
      _ ≤ ‖1 - s‖ * ‖Q‖ + ‖s‖ * ‖Q'‖ := add_le_add (opNorm_smul_le _ _) (opNorm_smul_le _ _)
      _ = (1 - s) * ‖Q‖ + s * ‖Q'‖ := by
          rw [Real.norm_of_nonneg (sub_nonneg.2 hs.2), Real.norm_of_nonneg hs.1]
      _ ≤ (1 - s) * C + s * C := by
          gcongr
          · exact sub_nonneg.2 hs.2
          · exact hs.1
      _ = C := by ring
  convert hC (Q + s • (Q' - Q)) (fun y ↦ by simp [-coprod_apply, hQ y, hQ' y]) hQsC using 1
  funext k
  refine Subtype.ext ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe, Submodule.coe_add,
    Submodule.coe_smul, coe_gluingKerMap_apply, add_apply,
    smul_apply, sub_apply]
  module

end RightInverse

end TauCeti.CylinderSobolev
