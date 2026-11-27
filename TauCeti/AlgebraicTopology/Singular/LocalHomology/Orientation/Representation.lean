/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Continuous.Intertwining
public import TauCeti.RepresentationTheory.Dual

/-!
# The orientation representation on local homology

For a finite-dimensional real representation `ρ` on `E`, `Representation.orientation ρ` acts on
`orientationModule E = H_dim E(E, E ∖ {0}; ℤ)` by the induced maps of pairs. This intrinsic
relative-homology module is free of rank one, including when `E` has dimension zero. Its action
is multiplication by the sign of the determinant.

Scalar extension and the dual use `Representation.baseChange` and `Representation.dual`.
Thus the coefficient denoted `o_E^∨` in Pardon, Definition 4.1.1, is
`(ρ.orientation.baseChange R).dual`. The tensor and dual evaluation equations
below specify this coefficient on the actual local-homology carrier. The module is invertible,
so `Representation.dualTprodEquivTrivial` supplies its canonical equivariant evaluation pairing,
including after scalar extension. As a functor `SingleObj G ⥤ ModuleCat R`, the coefficient
`o_E^∨` is `Representation.dualOrientationLine`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Definition 4.1.1.
-/

public section

noncomputable section

open CategoryTheory Module TensorProduct

universe w v u

namespace Representation

open TauCeti

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {G : Type v} [Group G]

/-- The orientation representation of a real representation, acting on the actual integral local
homology module by the induced maps of `(E, E ∖ {0})`. -/
def orientation (ρ : Representation ℝ G E) :
    Representation ℤ G (orientationModule E) where
  toFun g := (TopPair.singularHomologyMap
    (ρ.toContinuousLinearEquiv g).complZeroPairIso.hom
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E)).hom
  map_one' := by
    rw [toContinuousLinearEquiv_one, ContinuousLinearEquiv.complZeroPairIso_refl,
      Iso.refl_hom, TopPair.singularHomologyMap_id]
    rw [ModuleCat.hom_id, Module.End.one_eq_id]
  map_mul' g h := by
    rw [toContinuousLinearEquiv_mul, ContinuousLinearEquiv.complZeroPairIso_trans,
      Iso.trans_hom, TopPair.singularHomologyMap_comp]
    rw [ModuleCat.hom_comp, Module.End.mul_eq_comp]

/-- The orientation action is the linear map induced on local homology by the original action. -/
theorem orientation_def (ρ : Representation ℝ G E) (g : G) :
    orientation ρ g = (TopPair.singularHomologyMap
      (ρ.toContinuousLinearEquiv g).complZeroPairIso.hom
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E)).hom := by
  rfl

/-- Any continuous linear equivalence realizing `ρ g` computes its action on the orientation
module by the induced map of pairs. -/
theorem orientation_apply (ρ : Representation ℝ G E) (g : G)
    (e : E ≃L[ℝ] E) (he : (e : E →ₗ[ℝ] E) = ρ g) (x : orientationModule E) :
    orientation ρ g x =
      TopPair.singularHomologyMap e.complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E) x := by
  have h : ρ.toContinuousLinearEquiv g = e := by
    ext x
    exact (toContinuousLinearEquiv_apply ρ g x).trans
      (DFunLike.congr_fun he x).symm
  rw [orientation_def, h]

/-- The action on integral local homology is the sign of the determinant of the original
representation. -/
theorem orientation_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G) :
    orientation ρ g = (SignType.sign (LinearMap.det (ρ g)) : ℤ) •
      LinearMap.id := by
  have hdet : (ρ.toContinuousLinearEquiv g : E →L[ℝ] E).det =
      LinearMap.det (ρ g) := by
    rw [ContinuousLinearMap.det, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      toContinuousLinearEquiv_toLinearMap]
  have h := singularHomologyMap_continuousLinearMap_compl_zero
    (ModuleCat.of ℤ (ULift.{w} ℤ))
    (ρ.toContinuousLinearEquiv g : E →L[ℝ] E)
    (ρ.toContinuousLinearEquiv g).mapsTo_compl_zero (finrank ℝ E)
  rw [← (ρ.toContinuousLinearEquiv g).complZeroPairIso_hom] at h
  rw [orientation_def, h, ModuleCat.hom_zsmul, ModuleCat.hom_id,
    hdet]

/-- On each local homology class, the orientation action is multiplication by the determinant
sign. -/
theorem orientation_apply_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G)
    (x : orientationModule E) :
    orientation ρ g x = (SignType.sign (LinearMap.det (ρ g)) : ℤ) • x := by
  rw [orientation_eq_sign_det_smul]
  simpa only [LinearMap.applyₗ_apply_apply, LinearMap.id_apply] using
    (map_zsmul (LinearMap.applyₗ (R := ℤ) (M₂ := orientationModule E) x)
      (SignType.sign (LinearMap.det (ρ g)) : ℤ)
      (LinearMap.id : orientationModule E →ₗ[ℤ] orientationModule E))

/-- Restricting a real representation along a group homomorphism restricts its orientation
representation along the same homomorphism. -/
@[simp]
theorem orientation_comp {H : Type*} [Group H]
    (ρ : Representation ℝ G E) (φ : H →* G) :
    orientation (ρ.comp φ) = ρ.orientation.comp φ := by
  ext g x
  simp only [orientation_apply_eq_sign_det_smul, MonoidHom.comp_apply]

/-- The orientation representation of a trivial representation is trivial. -/
@[simp]
theorem orientation_trivial :
    (Representation.trivial ℝ G E).orientation =
      Representation.trivial ℤ G (orientationModule E) := by
  ext g x
  simp [orientation_apply_eq_sign_det_smul, Representation.trivial]

section BaseChange

variable {R : Type u} [Ring R]

/-- Extending coefficients preserves the scalar formula for the orientation operator. -/
theorem baseChange_orientation_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G) :
    (orientation ρ).baseChange R g =
      (SignType.sign (LinearMap.det (ρ g)) : ℤ) • LinearMap.id := by
  rw [Representation.baseChange_apply, orientation_eq_sign_det_smul]
  simpa only [LinearMap.baseChangeHom_apply, LinearMap.baseChange_id] using
    (map_zsmul (LinearMap.baseChangeHom ℤ R (orientationModule E) (orientationModule E))
      (SignType.sign (LinearMap.det (ρ g)) : ℤ)
      (LinearMap.id : orientationModule E →ₗ[ℤ] orientationModule E))

/-- The orientation action on an arbitrary tensor is multiplication by the determinant sign. -/
theorem baseChange_orientation_apply_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G)
    (y : R ⊗[ℤ] orientationModule E) :
    (orientation ρ).baseChange R g y =
      (SignType.sign (LinearMap.det (ρ g)) : ℤ) • y := by
  rw [baseChange_orientation_eq_sign_det_smul, LinearMap.smul_apply, LinearMap.id_apply]

/-- Scalar extension of the orientation representation acts on simple tensors by the determinant
sign of the real representation. -/
theorem baseChange_orientation_tmul (ρ : Representation ℝ G E) (g : G)
    (r : R) (x : orientationModule E) :
    (orientation ρ).baseChange R g (r ⊗ₜ[ℤ] x) =
      r ⊗ₜ[ℤ] ((SignType.sign (LinearMap.det (ρ g)) : ℤ) • x) := by
  rw [baseChange_orientation_apply_eq_sign_det_smul]
  exact (map_zsmul (TensorProduct.mk ℤ R (orientationModule E) r)
    (SignType.sign (LinearMap.det (ρ g)) : ℤ) x).symm

end BaseChange

section Dual

variable {R : Type u} [CommRing R]

/-- The dual of the coefficient extension has the same determinant-sign operator. -/
theorem dual_baseChange_orientation_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G) :
    ((orientation ρ).baseChange R).dual g =
      (SignType.sign (LinearMap.det (ρ g)) : ℤ) • LinearMap.id := by
  have hsign : SignType.sign (LinearMap.det (ρ g⁻¹)) =
      SignType.sign (LinearMap.det (ρ g)) := by
    let χ := (signHom : ℝ →*₀ SignType).toMonoidHom.comp (LinearMap.det.comp ρ)
    have hmul : χ g⁻¹ * χ g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hn := right_ne_zero_of_mul_eq_one hmul
    exact mul_right_cancel₀ hn (hmul.trans (SignType.mul_self_eq_one_iff.mpr hn).symm)
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro y
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    baseChange_orientation_apply_eq_sign_det_smul, hsign, map_zsmul,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smul_apply]

/-- On an arbitrary functional, the dual coefficient action is multiplication by the determinant
sign. -/
theorem dual_baseChange_orientation_apply_eq_sign_det_smul
    (ρ : Representation ℝ G E) (g : G)
    (f : Module.Dual R (R ⊗[ℤ] orientationModule E)) :
    ((orientation ρ).baseChange R).dual g f =
      (SignType.sign (LinearMap.det (ρ g)) : ℤ) • f := by
  rw [dual_baseChange_orientation_eq_sign_det_smul, LinearMap.smul_apply, LinearMap.id_apply]

/-- Evaluation of the dual coefficient action on an arbitrary tensor uses the same determinant
sign as the original action. -/
theorem dual_baseChange_orientation_apply (ρ : Representation ℝ G E) (g : G)
    (f : Module.Dual R (R ⊗[ℤ] orientationModule E)) (y : R ⊗[ℤ] orientationModule E) :
    ((orientation ρ).baseChange R).dual g f y =
      f ((SignType.sign (LinearMap.det (ρ g)) : ℤ) • y) := by
  rw [dual_baseChange_orientation_apply_eq_sign_det_smul, LinearMap.smul_apply, map_zsmul]

/-- On a simple tensor, the dual coefficient action evaluates the functional after multiplying
the local homology class by the determinant sign. -/
theorem dual_baseChange_orientation_apply_tmul (ρ : Representation ℝ G E) (g : G)
    (f : Module.Dual R (R ⊗[ℤ] orientationModule E)) (r : R) (x : orientationModule E) :
    ((orientation ρ).baseChange R).dual g f (r ⊗ₜ[ℤ] x) =
      f (r ⊗ₜ[ℤ] ((SignType.sign (LinearMap.det (ρ g)) : ℤ) • x)) := by
  rw [dual_baseChange_orientation_apply]
  congr 1
  exact (map_zsmul (TensorProduct.mk ℤ R (orientationModule E) r)
    (SignType.sign (LinearMap.det (ρ g)) : ℤ) x).symm

variable (R) in
/-- **The dual orientation line** `o_E^∨` of a real representation `ρ` of `G` on `E`, with
coefficients in `R`: the dual `(ρ.orientation.baseChange R).dual` of the scalar extension to `R`
of the integral orientation line `o_E = H_m(E, E ∖ 0; ℤ)`, `m = dim E`, on which `g ∈ G` acts by
the sign of the determinant of `ρ g` (`dual_baseChange_orientation_eq_sign_det_smul`), as a
functor `SingleObj G ⥤ ModuleCat R`. -/
-- The body is exposed so that the value is definitionally the dual line: the statement of
-- `dualOrientationLine_map`, a map between values, typechecks only then.
@[expose]
def dualOrientationLine (ρ : Representation ℝ G E) :
    SingleObj G ⥤ ModuleCat.{max u w} R :=
  SingleObj.functor <|
    (ModuleCat.endRingEquiv (.of R (Dual R (R ⊗[ℤ] orientationModule E)))).symm.toMonoidHom.comp
      ((orientation ρ).baseChange R).dual

variable (R) in
/-- The dual orientation line is the dual of the scalar extension of `o_E`. -/
@[simp]
theorem dualOrientationLine_obj (ρ : Representation ℝ G E) (Y : SingleObj G) :
    (dualOrientationLine R ρ).obj Y = ModuleCat.of R (Dual R (R ⊗[ℤ] orientationModule E)) :=
  (rfl)

variable (R) in
/-- An element of `G` acts on the dual orientation line by the dual of the scalar extension of
its action on the orientation line of `E`. -/
theorem dualOrientationLine_map (ρ : Representation ℝ G E) (g : G) :
    ((dualOrientationLine R ρ).map (X := SingleObj.star _) (Y := SingleObj.star _) g).hom =
      ((orientation ρ).baseChange R).dual g :=
  (rfl)

end Dual

end Representation
