/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Determinant.Basic
public import TauCeti.RepresentationTheory.OfGL
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Framed continuous representations

A continuous homomorphism `ρ : Γ →ₜ* GL_n(A)`, for the units topology on
`GL_n(A) = Matrix.GeneralLinearGroup n A`, is a *framed* representation. It defines the continuous
representation `TauCeti.ContinuousRep.ofFramed ρ` on `n → A`, by matrix multiplication. Conversely a
continuous representation `ρ` of a group with continuous inversion on a module with a finite basis
`b` and its module topology has a frame `TauCeti.ContinuousRep.frame b ρ : Γ →ₜ* GL_n(A)`, the
matrices of the `ρ g` in `b`, with `ofFramed (frame b ρ) ≅ ρ`, the converse
`frame (Pi.basisFun A n) (ofFramed ρ) = ρ` and the change-of-basis formula
`frame b' ρ = (b'.toMatrix b) (frame b ρ) (b.toMatrix b')`.

Two framed representations are isomorphic exactly when they are conjugate under `GL_n(A)`
(`TauCeti.ContinuousRep.nonempty_iso_ofFramed_iff`), and the determinant character of `ofFramed ρ`
is `det ∘ ρ` (`TauCeti.ContinuousRep.det_ofFramed`). A continuous ring homomorphism `f : A → B`
changes the coefficients of a framed representation entrywise (`TauCeti.ContinuousRep.framedMap`),
functorially in `f`.

## Main definitions

* `TauCeti.ContinuousRep.ofFramed ρ`: the continuous representation on `n → A` of a framed
  representation `ρ : Γ →ₜ* GL_n(A)`, with underlying linear representation `Representation.ofGL ρ`.
* `TauCeti.ContinuousRep.frame b ρ`: the frame of a continuous representation in a basis `b`.
* `TauCeti.ContinuousRep.ofFramedFrameIso b ρ`: `ofFramed (frame b ρ) ≅ ρ`.
* `TauCeti.ContinuousRep.framedMap f hf ρ`: entrywise coefficient change along a continuous
  `f : A →+* B`.

## Main results

* `TauCeti.ContinuousRep.frame_pi_basisFun_ofFramed`: the frame of `ofFramed ρ` in the standard
  basis is `ρ`.
* `TauCeti.ContinuousRep.frame_eq_mul_mul`: the change-of-basis formula.
* `TauCeti.ContinuousRep.nonempty_iso_ofFramed_iff`: isomorphism classes of framed
  representations are `GL_n(A)`-conjugacy classes.
* `TauCeti.ContinuousRep.det_ofFramed`: `det (ofFramed ρ) = det ∘ ρ`.

## References

* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, revised version (2007) of Current
  Developments in Mathematics 1995, §2.1, p. 52.
* K. A. Ribet, *A modular construction of unramified p-extensions of `ℚ(μ_p)`*, Invent. Math. 34
  (1976), §2, p. 154.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.ContinuousRep

variable {Γ A : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] {n : Type*} [Fintype n] [DecidableEq n]

section ofFramed

/-- **The continuous representation of a framed representation** `ρ : Γ →ₜ* GL_n(A)`: `g` acts
on `n → A` by the matrix `ρ g`. Joint continuity is continuity of the matrix entries. -/
def ofFramed (ρ : Γ →ₜ* GL n A) : ContinuousRep Γ A (n → A) where
  toRepresentation := Representation.ofGL (ρ : Γ →* GL n A)
  continuous_action := by
    refine (TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix
      (Pi.basisFun A n) (Pi.basisFun A n) _).2 ?_
    simp only [LinearMap.toMatrix_eq_toMatrix', Representation.ofGL_apply,
      LinearMap.toMatrix'_toLin']
    exact Units.continuous_val.comp ρ.continuous

@[simp]
theorem ofFramed_apply (ρ : Γ →ₜ* GL n A) (g : Γ) (v : n → A) :
    ofFramed ρ g v = (ρ g : Matrix n n A) *ᵥ v :=
  (LinearMap.congr_fun (Representation.ofGL_apply (ρ : Γ →* GL n A) g) v).trans
    (Matrix.toLin'_apply _ v)

theorem ofFramed_apply_eq_toLin' (ρ : Γ →ₜ* GL n A) (g : Γ) :
    ofFramed ρ g = Matrix.toLin' (ρ g : Matrix n n A) :=
  Representation.ofGL_apply (ρ : Γ →* GL n A) g

@[simp]
theorem toRepresentation_ofFramed (ρ : Γ →ₜ* GL n A) :
    (ofFramed ρ).toRepresentation = Representation.ofGL (ρ : Γ →* GL n A) :=
  (rfl)

end ofFramed

/-- **Isomorphism classes of framed representations are conjugacy classes**: `ofFramed ρ` and
`ofFramed σ` are isomorphic exactly when `σ = P ρ P⁻¹` for some `P ∈ GL_n(A)`. -/
theorem nonempty_iso_ofFramed_iff (ρ σ : Γ →ₜ* GL n A) :
    Nonempty (Iso (ofFramed ρ) (ofFramed σ)) ↔ ∃ P : GL n A, ∀ g, σ g = P * ρ g * P⁻¹ := by
  constructor
  · rintro ⟨e⟩
    let L : (n → A) ≃ₗ[A] (n → A) := e.toContinuousLinearEquiv.toLinearEquiv
    refine ⟨GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv L),
      fun g => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    apply GeneralLinearGroup.toLin.injective
    refine Units.ext (LinearMap.ext fun v => ?_)
    simpa [L, ofFramed_apply] using (e.isIntertwining g v).symm
  · rintro ⟨P, hP⟩
    let L : (n → A) ≃ₗ[A] (n → A) := Matrix.GeneralLinearGroup.toLin P |>.toLinearEquiv
    refine ⟨Iso.ofEquiv (.mk L fun g => LinearMap.ext fun v => ?_)⟩
    have hg : (σ g : Matrix n n A) * P = P * ρ g := by simp [hP g, mul_assoc]
    have := congr_arg (fun M => M *ᵥ v) hg
    simpa [L, ofFramed_apply, Matrix.mulVec_mulVec] using this.symm

section Group

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- **The determinant of a framed representation** is the determinant of its matrices. -/
@[simp]
theorem det_ofFramed (ρ : Γ →ₜ* GL n A) :
    (ofFramed ρ).det = Matrix.GeneralLinearGroup.det.comp (ρ : Γ →* GL n A) := by
  ext g
  simp [ofFramed_apply_eq_toLin', LinearMap.det_toLin']

end Group


section Frame

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] {M : Type*}
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]

/-- **The frame of a continuous representation** in a finite basis `b`: the matrices of the `ρ g`
in `b`, a continuous homomorphism into `GL_n(A)`. -/
def frame (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) : Γ →ₜ* GL n A where
  toMonoidHom := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    ρ.toRepresentation.asGroupHom
  continuous_toFun := (MonoidHom.continuous_iff_continuous_val _).2 (ρ.continuous_toMatrix b)

@[simp]
theorem coe_frame_apply (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) (g : Γ) :
    (frame b ρ g : Matrix n n A) = LinearMap.toMatrix b b (ρ g) :=
  (rfl)

/-- **A framed representation is the frame of its representation** in the standard basis. -/
@[simp]
theorem frame_pi_basisFun_ofFramed (ρ : Γ →ₜ* GL n A) : frame (Pi.basisFun A n) (ofFramed ρ) = ρ :=
  ContinuousMonoidHom.ext fun g => Units.ext <| by
    rw [coe_frame_apply, LinearMap.toMatrix_eq_toMatrix', ofFramed_apply_eq_toLin',
      LinearMap.toMatrix'_toLin']

/-- **Change of basis for frames**: `frame b' ρ = (b'.toMatrix b) (frame b ρ) (b.toMatrix b')`,
where `b'.toMatrix b` and `b.toMatrix b'` are inverse matrices. -/
theorem frame_eq_mul_mul {n' : Type*} [Fintype n'] [DecidableEq n'] (b : Module.Basis n A M)
    (b' : Module.Basis n' A M) (ρ : ContinuousRep Γ A M) (g : Γ) :
    (frame b' ρ g : Matrix n' n' A) =
      b'.toMatrix b * (frame b ρ g : Matrix n n A) * b.toMatrix b' := by
  simp

/-- **A continuous representation is the framed representation of its frame**: the coordinate
isomorphism `n → A ≃ M` of the basis `b` is an isomorphism `ofFramed (frame b ρ) ≅ ρ`. -/
def ofFramedFrameIso (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) :
    Iso (ofFramed (frame b ρ)) ρ :=
  Iso.ofEquiv (.mk b.equivFun.symm fun g => LinearMap.ext fun v => b.equivFun.injective <| by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      coe_toRepresentation, ofFramed_apply, coe_frame_apply]
    -- The matrix of `ρ g` in `b` acts on the coordinates `v` of `b.equivFun.symm v`.
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b,
      ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply])

@[simp]
theorem ofFramedFrameIso_apply (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) (v : n → A) :
    ofFramedFrameIso b ρ v = b.equivFun.symm v :=
  Iso.ofEquiv_apply _ _

/-- The inverse of `ofFramedFrameIso b ρ` takes `x : M` to its coordinates in `b`. -/
@[simp]
theorem ofFramedFrameIso_symm_apply (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) (x : M) :
    (ofFramedFrameIso b ρ).symm x = b.equivFun x := by
  rw [← b.equivFun.apply_symm_apply ((ofFramedFrameIso b ρ).symm x), ← ofFramedFrameIso_apply b ρ,
    Iso.apply_symm_apply]

end Frame

section Map

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- **Entrywise coefficient change** of a framed representation along a continuous ring
homomorphism `f : A → B`. -/
def framedMap (f : A →+* B) (hf : Continuous f) (ρ : Γ →ₜ* GL n A) : Γ →ₜ* GL n B where
  toMonoidHom := (Matrix.GeneralLinearGroup.map f).comp (ρ : Γ →* GL n A)
  continuous_toFun := hf.generalLinearGroup_map.comp ρ.continuous

omit [IsTopologicalRing A] [IsTopologicalRing B] in
@[simp]
theorem coe_framedMap_apply (f : A →+* B) (hf : Continuous f) (ρ : Γ →ₜ* GL n A) (g : Γ) :
    (framedMap f hf ρ g : Matrix n n B) = (ρ g : Matrix n n A).map f :=
  (rfl)

omit [IsTopologicalRing A] in
/-- Coefficient change along the identity changes nothing. -/
@[simp]
theorem framedMap_id (ρ : Γ →ₜ* GL n A) : framedMap (RingHom.id A) continuous_id ρ = ρ :=
  ContinuousMonoidHom.ext fun g => DFunLike.congr_fun Matrix.GeneralLinearGroup.map_id (ρ g)

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- Coefficient change is functorial. -/
@[simp]
theorem framedMap_framedMap {C : Type*} [CommRing C] [TopologicalSpace C]
    (f : A →+* B) (hf : Continuous f) (f' : B →+* C) (hf' : Continuous f') (ρ : Γ →ₜ* GL n A) :
    framedMap f' hf' (framedMap f hf ρ) = framedMap (f'.comp f) (hf'.comp hf) ρ :=
  ContinuousMonoidHom.ext fun g =>
    (DFunLike.congr_fun (Matrix.GeneralLinearGroup.map_comp f f') (ρ g)).symm

end Map

end TauCeti.ContinuousRep
