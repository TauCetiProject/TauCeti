/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Topology.Instances.Matrix

/-!
# Framed continuous representations

A continuous homomorphism `ρ : Γ →ₜ* GL_n(A)`, for the units topology on
`GL_n(A) = Matrix.GeneralLinearGroup n A`, is a *framed* representation. It defines the continuous
representation `TauCeti.ContinuousRep.ofFramed ρ` on `n → A`, by matrix multiplication. Conversely a
continuous representation `ρ` of a topological group on a module with a finite basis `b` and its
module topology has a frame `TauCeti.ContinuousRep.frame b ρ : Γ →ₜ* GL_n(A)`, the matrices of the
`ρ g` in `b`, with `ofFramed (frame b ρ) ≅ ρ` and the change-of-basis formula
`frame b' ρ = (b'.toMatrix b) (frame b ρ) (b.toMatrix b')`.

Two framed representations are isomorphic exactly when they are conjugate under `GL_n(A)`
(`TauCeti.ContinuousRep.nonempty_iso_ofFramed_iff`), and the determinant character of `ofFramed ρ`
is `det ∘ ρ` (`TauCeti.ContinuousRep.det_ofFramed`). A continuous ring homomorphism `f : A → B`
changes the coefficients of a framed representation entrywise (`TauCeti.ContinuousRep.framedMap`),
functorially in `f`.

For a group hom into `GL_n(A)` from a topological group, continuity for the units topology is
continuity of the matrix entries (`TauCeti.ContinuousRep.continuous_units_iff`), since `ρ(g)⁻¹` is
`ρ(g⁻¹)`.

## Main definitions

* `TauCeti.ContinuousRep.ofFramed ρ`: the continuous representation on `n → A` of a framed
  representation `ρ : Γ →ₜ* GL_n(A)`.
* `TauCeti.ContinuousRep.frame b ρ`: the frame of a continuous representation in a basis `b`.
* `TauCeti.ContinuousRep.ofFramedFrameIso b ρ`: `ofFramed (frame b ρ) ≅ ρ`.
* `TauCeti.ContinuousRep.framedMap f hf ρ`: entrywise coefficient change along a continuous
  `f : A →+* B`.

## Main results

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

section Units

variable {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid A]
  [TopologicalSpace A]

/-- **Continuity into the units of a topological monoid**: a homomorphism from a topological group
into `Aˣ` is continuous for the units topology exactly when its values in `A` are continuous, since
`ρ(g)⁻¹ = ρ(g⁻¹)`. -/
theorem continuous_units_iff (ρ : Γ →* Aˣ) :
    Continuous ρ ↔ Continuous fun g => (ρ g : A) := by
  refine ⟨fun h => Units.continuous_val.comp h, fun h => Units.continuous_iff.2 ⟨h, ?_⟩⟩
  exact (h.comp continuous_inv).congr fun g => by rw [Function.comp_apply, map_inv]

end Units

variable {Γ A : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] {n : Type*} [Fintype n] [DecidableEq n]

section ofFramed

/-- The linear representation on `n → A` of a homomorphism `Γ →* GL_n(A)`, by matrix
multiplication. -/
def framedRepresentation (ρ : Γ →* GL n A) : Representation A Γ (n → A) :=
  (Matrix.toLinAlgEquiv'.toMonoidHom.comp (Units.coeHom (Matrix n n A))).comp ρ

omit [TopologicalSpace Γ] [TopologicalSpace A] [IsTopologicalRing A] in
theorem framedRepresentation_apply (ρ : Γ →* GL n A) (g : Γ) :
    framedRepresentation ρ g = Matrix.toLin' (ρ g : Matrix n n A) :=
  (rfl)

/-- **The continuous representation of a framed representation** `ρ : Γ →ₜ* GL_n(A)`: `g` acts
on `n → A` by the matrix `ρ g`. Joint continuity is continuity of the matrix entries. -/
def ofFramed (ρ : Γ →ₜ* GL n A) : ContinuousRep Γ A (n → A) where
  toRepresentation := framedRepresentation (ρ : Γ →* GL n A)
  continuous_action := by
    refine (TauCeti.ModuleTopology.continuous_linearMap_apply_iff_continuous_toMatrix
      (Pi.basisFun A n) (Pi.basisFun A n) _).2 ?_
    simp only [LinearMap.toMatrix_eq_toMatrix', framedRepresentation_apply,
      LinearMap.toMatrix'_toLin']
    exact Units.continuous_val.comp ρ.continuous

@[simp]
theorem ofFramed_apply (ρ : Γ →ₜ* GL n A) (g : Γ) (v : n → A) :
    ofFramed ρ g v = (ρ g : Matrix n n A) *ᵥ v :=
  Matrix.toLin'_apply _ v

theorem ofFramed_apply_eq_toLin' (ρ : Γ →ₜ* GL n A) (g : Γ) :
    ofFramed ρ g = Matrix.toLin' (ρ g : Matrix n n A) :=
  (rfl)

end ofFramed

section Group

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- **The determinant of a framed representation** is the determinant of its matrices. -/
theorem det_ofFramed (ρ : Γ →ₜ* GL n A) :
    (ofFramed ρ).det = Matrix.GeneralLinearGroup.det.comp (ρ : Γ →* GL n A) := by
  ext g
  simp [ofFramed_apply_eq_toLin', LinearMap.det_toLin']

/-- **Isomorphism classes of framed representations are conjugacy classes**: `ofFramed ρ` and
`ofFramed σ` are isomorphic exactly when `σ = P ρ P⁻¹` for some `P ∈ GL_n(A)`. -/
theorem nonempty_iso_ofFramed_iff (ρ σ : Γ →ₜ* GL n A) :
    Nonempty (Iso (ofFramed ρ) (ofFramed σ)) ↔ ∃ P : GL n A, ∀ g, σ g = P * ρ g * P⁻¹ := by
  constructor
  · rintro ⟨e⟩
    let L : (n → A) ≃ₗ[A] (n → A) := e.toContinuousLinearEquiv.toLinearEquiv
    refine ⟨Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
      (LinearMap.GeneralLinearGroup.ofLinearEquiv L), fun g => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    ext1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have h := e.isIntertwining g v
    simp only [ofFramed_apply] at h
    change Matrix.toLin' ((σ g : Matrix n n A) * LinearMap.toMatrix' (L : Module.End A (n → A))) v =
      Matrix.toLin' (LinearMap.toMatrix' (L : Module.End A (n → A)) * (ρ g : Matrix n n A)) v
    rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h.symm
  · rintro ⟨P, hP⟩
    let L : (n → A) ≃ₗ[A] (n → A) := Matrix.GeneralLinearGroup.toLin P |>.toLinearEquiv
    refine ⟨Iso.ofEquiv (.mk L fun g => LinearMap.ext fun v => ?_)⟩
    have hg : (σ g : Matrix n n A) * P = P * ρ g := by simp [hP g, mul_assoc]
    have := congr_arg (fun M => M *ᵥ v) hg
    simpa [L, Matrix.GeneralLinearGroup.toLin, ofFramed_apply, Matrix.mulVec_mulVec] using
      this.symm

end Group


section Frame

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {M : Type*}
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]

/-- **The frame of a continuous representation** in a finite basis `b`: the matrices of the `ρ g`
in `b`, a continuous homomorphism into `GL_n(A)`. -/
def frame (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) : Γ →ₜ* GL n A where
  toMonoidHom := (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    ρ.toRepresentation.asGroupHom
  continuous_toFun := (continuous_units_iff _).2 (ρ.continuous_toMatrix b)

@[simp]
theorem coe_frame_apply (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) (g : Γ) :
    (frame b ρ g : Matrix n n A) = LinearMap.toMatrix b b (ρ g) :=
  (rfl)

/-- **Change of basis for frames**: `frame b' ρ = (b'.toMatrix b) (frame b ρ) (b.toMatrix b')`,
where `b'.toMatrix b` and `b.toMatrix b'` are inverse matrices. -/
theorem frame_eq_mul_mul (b b' : Module.Basis n A M) (ρ : ContinuousRep Γ A M) (g : Γ) :
    (frame b' ρ g : Matrix n n A) =
      b'.toMatrix b * (frame b ρ g : Matrix n n A) * b.toMatrix b' := by
  simp

/-- **A continuous representation is the framed representation of its frame**: the coordinate
isomorphism `n → A ≃ M` of the basis `b` is an isomorphism `ofFramed (frame b ρ) ≅ ρ`. -/
def ofFramedFrameIso (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) :
    Iso (ofFramed (frame b ρ)) ρ :=
  Iso.ofEquiv (.mk b.equivFun.symm fun g => LinearMap.ext fun v => by
    change b.equivFun.symm (ofFramed (frame b ρ) g v) = ρ g (b.equivFun.symm v)
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, ofFramed_apply, coe_frame_apply,
      Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b,
      ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply])

@[simp]
theorem ofFramedFrameIso_apply (b : Module.Basis n A M) (ρ : ContinuousRep Γ A M) (v : n → A) :
    ofFramedFrameIso b ρ v = b.equivFun.symm v :=
  Iso.ofEquiv_apply _ _

end Frame

section Map

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- **Entrywise coefficient change** of a framed representation along a continuous ring
homomorphism `f : A → B`. -/
def framedMap (f : A →+* B) (hf : Continuous f) (ρ : Γ →ₜ* GL n A) : Γ →ₜ* GL n B where
  toMonoidHom := (Units.map f.mapMatrix.toMonoidHom).comp (ρ : Γ →* GL n A)
  continuous_toFun := Units.continuous_iff.2
    ⟨((Units.continuous_val.comp ρ.continuous).matrix_map hf).congr fun _ => by simp,
      ((Units.continuous_coe_inv.comp ρ.continuous).matrix_map hf).congr fun _ => by simp⟩

omit [IsTopologicalRing A] [IsTopologicalRing B] in
@[simp]
theorem coe_framedMap_apply (f : A →+* B) (hf : Continuous f) (ρ : Γ →ₜ* GL n A) (g : Γ) :
    (framedMap f hf ρ g : Matrix n n B) = (ρ g : Matrix n n A).map f :=
  (rfl)

omit [IsTopologicalRing A] in
/-- Coefficient change along the identity changes nothing. -/
@[simp]
theorem framedMap_id (ρ : Γ →ₜ* GL n A) : framedMap (RingHom.id A) continuous_id ρ = ρ := by
  ext g : 2
  simp

omit [IsTopologicalRing A] [IsTopologicalRing B] in
/-- Coefficient change is functorial. -/
theorem framedMap_comp {C : Type*} [CommRing C] [TopologicalSpace C]
    (f : A →+* B) (hf : Continuous f) (f' : B →+* C) (hf' : Continuous f') (ρ : Γ →ₜ* GL n A) :
    framedMap (f'.comp f) (hf'.comp hf) ρ = framedMap f' hf' (framedMap f hf ρ) := by
  ext g : 2
  simp [Matrix.map_map]

end Map

end TauCeti.ContinuousRep
