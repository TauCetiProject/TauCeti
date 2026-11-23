/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear
public import TauCeti.RepresentationTheory.BaseChange
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
including after scalar extension.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Definition 4.1.1.
-/

public section

noncomputable section

open CategoryTheory Module TensorProduct

universe w v u

namespace TauCeti

variable (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral orientation module of a real normed space: its local homology at the origin
in degree `dim E`. -/
abbrev orientationModule :=
  localHomology (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) ({0} : Set E)
    (finrank ℝ E)

/-- A noncanonical identification of the orientation module with `ℤ`, computed using the
identity chart and the existing local homology comparison. -/
private def orientationModuleLinearEquiv [FiniteDimensional ℝ E] :
    orientationModule E ≃ₗ[ℤ] ℤ :=
  (singularHomologyComplSingletonFinrankIso (ModuleCat.of ℤ (ULift.{w} ℤ))
    (OpenPartialHomeomorph.refl E) (Set.mem_univ (0 : E))).toLinearEquiv.trans
    ULift.moduleEquiv

instance orientationModule.instFree [FiniteDimensional ℝ E] :
    Module.Free ℤ (orientationModule E) :=
  Module.Free.of_equiv (orientationModuleLinearEquiv E).symm

instance orientationModule.instFinite [FiniteDimensional ℝ E] :
    Module.Finite ℤ (orientationModule E) :=
  Module.Finite.equiv (orientationModuleLinearEquiv E).symm

instance orientationModule.instInvertible [FiniteDimensional ℝ E] :
    Module.Invertible ℤ (orientationModule E) :=
  Module.Invertible.congr (orientationModuleLinearEquiv E).symm

/-- The integral orientation module has rank one, also for a zero-dimensional space. -/
theorem orientationModule_finrank [FiniteDimensional ℝ E] :
    finrank ℤ (orientationModule E) = 1 := by
  rw [(orientationModuleLinearEquiv E).finrank_eq]
  exact Module.finrank_self ℤ

end TauCeti

namespace Representation

open TauCeti

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {G : Type v} [Group G]

private def representationContinuousLinearEquiv (ρ : Representation ℝ G E) (g : G) :
    E ≃L[ℝ] E :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toContinuousLinearEquiv

private theorem representationContinuousLinearEquiv_apply (ρ : Representation ℝ G E) (g : G)
    (x : E) : representationContinuousLinearEquiv ρ g x = ρ g x := rfl

private theorem representationContinuousLinearEquiv_one (ρ : Representation ℝ G E) :
    representationContinuousLinearEquiv ρ 1 = ContinuousLinearEquiv.refl ℝ E := by
  ext x
  simp [representationContinuousLinearEquiv_apply]

private theorem representationContinuousLinearEquiv_mul (ρ : Representation ℝ G E) (g h : G) :
    representationContinuousLinearEquiv ρ (g * h) =
      (representationContinuousLinearEquiv ρ h).trans
        (representationContinuousLinearEquiv ρ g) := by
  ext x
  simp [representationContinuousLinearEquiv_apply]

/-- The orientation representation of a real representation, acting on the actual integral local
homology module by the induced maps of `(E, E ∖ {0})`. -/
def orientation (ρ : Representation ℝ G E) :
    Representation ℤ G (orientationModule E) where
  toFun g := (TopPair.singularHomologyMap
    (representationContinuousLinearEquiv ρ g).complZeroPairIso.hom
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E)).hom
  map_one' := by
    rw [representationContinuousLinearEquiv_one, ContinuousLinearEquiv.complZeroPairIso_refl,
      Iso.refl_hom, TopPair.singularHomologyMap_id]
    rfl
  map_mul' g h := by
    rw [representationContinuousLinearEquiv_mul, ContinuousLinearEquiv.complZeroPairIso_trans,
      Iso.trans_hom, TopPair.singularHomologyMap_comp]
    rfl

/-- Any continuous linear equivalence realizing `ρ g` computes its action on the orientation
module by the induced map of pairs. -/
theorem orientation_apply (ρ : Representation ℝ G E) (g : G)
    (e : E ≃L[ℝ] E) (he : (e : E →ₗ[ℝ] E) = ρ g) (x : orientationModule E) :
    orientation ρ g x =
      TopPair.singularHomologyMap e.complZeroPairIso.hom
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E) x := by
  have h : representationContinuousLinearEquiv ρ g = e := by
    ext x
    exact (representationContinuousLinearEquiv_apply ρ g x).trans
      (DFunLike.congr_fun he x).symm
  -- Unfold the action to evaluate the induced homology map on the native carrier.
  change TopPair.singularHomologyMap
    (representationContinuousLinearEquiv ρ g).complZeroPairIso.hom
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E) x = _
  rw [h]

/-- The action on integral local homology is the sign of the determinant of the original
representation. -/
theorem orientation_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G) :
    orientation ρ g = (SignType.sign (LinearMap.det (ρ g)) : ℤ) •
      LinearMap.id := by
  have h := singularHomologyMap_continuousLinearMap_compl_zero
    (ModuleCat.of ℤ (ULift.{w} ℤ))
    (representationContinuousLinearEquiv ρ g : E →L[ℝ] E)
    (representationContinuousLinearEquiv ρ g).mapsTo_compl_zero (finrank ℝ E)
  rw [← (representationContinuousLinearEquiv ρ g).complZeroPairIso_hom] at h
  -- The representation stores the linear map underlying the induced ModuleCat morphism.
  change (TopPair.singularHomologyMap
    (representationContinuousLinearEquiv ρ g).complZeroPairIso.hom
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ E)).hom = _
  rw [h]
  rfl

/-- On each local homology class, the orientation action is multiplication by the determinant
sign. -/
theorem orientation_apply_eq_sign_det_smul (ρ : Representation ℝ G E) (g : G)
    (x : orientationModule E) :
    orientation ρ g x = (SignType.sign (LinearMap.det (ρ g)) : ℤ) • x := by
  rw [orientation_eq_sign_det_smul]
  rfl

section BaseChange

variable {R : Type u} [Ring R]

/-- Scalar extension of the orientation representation acts on simple tensors by the determinant
sign of the real representation. -/
theorem orientation_baseChange_tmul (ρ : Representation ℝ G E) (g : G)
    (r : R) (x : orientationModule E) :
    (orientation ρ).baseChange R g (r ⊗ₜ[ℤ] x) =
      r ⊗ₜ[ℤ] ((SignType.sign (LinearMap.det (ρ g)) : ℤ) • x) := by
  rw [Representation.baseChange_apply, LinearMap.baseChange_tmul,
    orientation_apply_eq_sign_det_smul]

end BaseChange

section Dual

variable {R : Type u} [CommRing R]

/-- The dual coefficient acts contragrediently. Since the determinant sign is unchanged under
inversion, its evaluation on a simple tensor has the same sign as the original action. -/
theorem orientation_dual_baseChange_apply (ρ : Representation ℝ G E) (g : G)
    (f : Module.Dual R (R ⊗[ℤ] orientationModule E)) (r : R) (x : orientationModule E) :
    ((orientation ρ).baseChange R).dual g f (r ⊗ₜ[ℤ] x) =
      f (r ⊗ₜ[ℤ] ((SignType.sign (LinearMap.det (ρ g)) : ℤ) • x)) := by
  -- The dual action precomposes a functional with the inverse action.
  change f ((orientation ρ).baseChange R g⁻¹ (r ⊗ₜ[ℤ] x)) = _
  rw [orientation_baseChange_tmul]
  have hsign : SignType.sign (LinearMap.det (ρ g⁻¹)) =
      SignType.sign (LinearMap.det (ρ g)) :=
    map_inv ((signHom : ℝ →*₀ SignType).toMonoidHom.comp (LinearMap.det.comp ρ)) g
  rw [hsign]

end Dual

end Representation
