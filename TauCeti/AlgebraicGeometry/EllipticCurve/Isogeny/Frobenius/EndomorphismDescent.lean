/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Composition
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ordinary
import TauCeti.FieldTheory.Finite.GaloisZHat

/-!
# Frobenius descent of elliptic endomorphisms

`TauCeti.Isogeny.existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq` gives descent over algebraic
extensions of finite fields using `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisEquivariant`
and the Krull density of arithmetic Frobenius. Using `WeierstrassCurve.mul_comm_of_isOrdinary`,
`WeierstrassCurve.geometricEndEquivOfIsOrdinary` identifies the rational and geometric endomorphism
rings of ordinary curves. See [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009],
V.2 and V.3.
-/

public section

open TauCeti.Isogeny
open scoped WeierstrassCurve
namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] (W : WeierstrassCurve F)

/-- The pullback of base-field Frobenius composed with arithmetic Frobenius on coefficients
raises every function to the cardinality of the base field. -/
theorem fieldPullback_baseChangeFrobenius_functionFieldGaloisAction
    (z : (W⁄K).toAffine.FunctionField) :
    (baseChangeFrobenius K W.toAffine).fieldPullback
      (W.functionFieldGaloisAction (FiniteField.frobeniusAlgEquivOfAlgebraic F K) z) =
      z ^ Fintype.card F := by
  have h : (baseChangeFrobenius K W.toAffine).fieldPullback.toRingHom.comp
      (W.functionFieldGaloisAction (FiniteField.frobeniusAlgEquivOfAlgebraic F K)).toRingHom =
      (FiniteField.frobeniusAlgHom F (W⁄K).toAffine.FunctionField).toRingHom := by
    apply Affine.FunctionField.ringHom_ext <;>
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, functionFieldGaloisAction_genericX,
        functionFieldGaloisAction_genericY, fieldPullback_baseChangeFrobenius_genericX,
        fieldPullback_baseChangeFrobenius_genericY, FiniteField.frobeniusAlgHom_apply,
        Fintype.card_eq_nat_card]
    intro a
    rw [functionFieldGaloisAction_algebraMap, AlgHom.commutes, ← map_pow,
      ← Fintype.card_eq_nat_card]
    exact congrArg (algebraMap K (W⁄K).toAffine.FunctionField)
      (congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic F K) a)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, FiniteField.frobeniusAlgHom_apply] using
    RingHom.congr_fun h z

/-- A function over an algebraic extension of a finite field fixed by arithmetic Frobenius on
coefficients is fixed by every coefficient automorphism. -/
theorem functionFieldGaloisAction_eq_self_of_frobenius
    {z : (W⁄K).toAffine.FunctionField}
    (hz : W.functionFieldGaloisAction (FiniteField.frobeniusAlgEquivOfAlgebraic F K) z = z)
    (σ : K ≃ₐ[F] K) : W.functionFieldGaloisAction σ z = z := by
  have := FiniteField.isGalois_of_isAlgebraic F K
  let : MulAction (K ≃ₐ[F] K) _ := MulAction.compHom (W⁄K).toAffine.FunctionField
    W.functionFieldGaloisAction
  let S := MulAction.stabilizer (K ≃ₐ[F] K) z
  have mem_S {τ : K ≃ₐ[F] K} : τ ∈ S ↔ W.functionFieldGaloisAction τ z = z :=
    MulAction.mem_stabilizer_iff.trans (by rw [MulAction.compHom_smul_def, RingAut.smul_def])
  obtain ⟨s, hs⟩ := W.exists_finset_functionFieldGaloisAction_eq_self z
  let E := IntermediateField.adjoin F (s : Set K)
  have hle : E.fixingSubgroup ≤ S := fun τ hτ ↦
    mem_S.mpr <| hs τ fun a ha ↦
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ a
        (IntermediateField.subset_adjoin F _ ha)
  have hc := S.isClosed_of_isOpen (Subgroup.isOpen_mono hle E.fixingSubgroup_isOpen)
  have htop := (Subgroup.zpowers _).topologicalClosure_minimal
    (Subgroup.zpowers_le.mpr (mem_S.mpr hz)) hc
  rw [TauCeti.FiniteField.topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic] at htop
  exact mem_S.mp (htop (Subgroup.mem_top σ))

end WeierstrassCurve

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] {W₁ W₂ : WeierstrassCurve F}

/-- Over an algebraic extension of a finite field, an isogeny descends uniquely to the base field
exactly when it commutes with base-field Frobenius (Silverman V.2). -/
theorem existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq
    {φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine} :
    (∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ) ↔
      (baseChangeFrobenius K W₂.toAffine).comp φ = φ.comp (baseChangeFrobenius K W₁.toAffine) := by
  constructor
  · rintro ⟨ψ, rfl, -⟩
    have h := congrArg (fun f : Isogeny W₁.toAffine W₂.toAffine ↦ f.map (algebraMap F K))
      (frobeniusIsogeny_comp ψ)
    simp only [Isogeny.comp_map] at h
    rw [baseChangeFrobenius_def, baseChangeFrobenius_def]
    exact h
  · intro hφ
    let := Fintype.ofFinite F
    have := FiniteField.isGalois_of_isAlgebraic F K
    have heq := congrArg fieldPullback hφ
    simp only [comp_fieldPullback] at heq
    have hfix {z : (W₂⁄K).toAffine.FunctionField}
        (hz : W₂.functionFieldGaloisAction (FiniteField.frobeniusAlgEquivOfAlgebraic F K) z = z)
        (τ : K ≃ₐ[F] K) :
        W₁.functionFieldGaloisAction τ (φ.fieldPullback z) = φ.fieldPullback z := by
      apply W₁.functionFieldGaloisAction_eq_self_of_frobenius (K := K) _ τ
      have hzq : (baseChangeFrobenius K W₂.toAffine).fieldPullback z = z ^ Fintype.card F := by
        simpa only [hz] using W₂.fieldPullback_baseChangeFrobenius_functionFieldGaloisAction z
      apply (baseChangeFrobenius K W₁.toAffine).fieldPullback.injective
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        W₁.fieldPullback_baseChangeFrobenius_functionFieldGaloisAction]
      rw [← AlgHom.comp_apply, ← heq, AlgHom.comp_apply, hzq, map_pow]
    apply (existsUnique_map_eq_iff_galoisEquivariant W₁ W₂ φ).mpr
    intro τ z
    have hequiv :
        (W₁.functionFieldGaloisAction τ).toRingHom.comp φ.fieldPullback.toRingHom =
          φ.fieldPullback.toRingHom.comp (W₂.functionFieldGaloisAction τ).toRingHom := by
      apply WeierstrassCurve.Affine.FunctionField.ringHom_ext <;>
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
          WeierstrassCurve.functionFieldGaloisAction_algebraMap,
          WeierstrassCurve.functionFieldGaloisAction_genericX,
          WeierstrassCurve.functionFieldGaloisAction_genericY]
      · exact fun _ ↦ trivial
      · exact hfix (W₂.functionFieldGaloisAction_genericX _) τ
      · exact hfix (W₂.functionFieldGaloisAction_genericY _) τ
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      RingHom.congr_fun hequiv z

end TauCeti.Isogeny

namespace WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [ExpChar F p]
  (W : WeierstrassCurve F) [W.IsElliptic]

/-- Base change identifies the rational and geometric endomorphism rings of an ordinary
elliptic curve over a finite field (Silverman V.3). -/
noncomputable def geometricEndEquivOfIsOrdinary (hW : W.IsOrdinary p) :
    Hom W.toAffine W.toAffine ≃+* W.GeometricEnd :=
  let V := W.toAffine.map (algebraMap F (SeparableClosure F))
  RingEquiv.ofBijective (S := Hom V V) (Hom.mapRingHom (algebraMap F (SeparableClosure F))) <| by
    constructor
    · intro f g hfg
      apply Hom.map_injective (algebraMap F (SeparableClosure F))
      simpa only [Hom.mapRingHom_apply] using hfg
    · intro f
      rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
      · exact ⟨0, map_zero _⟩
      have : ExpChar (SeparableClosure F) p :=
        expChar_of_injective_algebraMap (algebraMap F (SeparableClosure F)).injective p
      have hgeom := (W.isOrdinary_baseChange_iff (SeparableClosure F)).mpr hW
      let V := (W⁄(SeparableClosure F)).toAffine
      let π : TauCeti.Isogeny V V := baseChangeFrobenius (SeparableClosure F) W.toAffine
      let χ : TauCeti.Isogeny V V := φ
      have hcomm := (W.baseChange (SeparableClosure F)).mul_comm_of_isOrdinary hgeom
        (Hom.ofIsogeny π) (Hom.ofIsogeny χ)
      rw [Hom.mul_def, Hom.mul_def, Hom.ofIsogeny_comp_ofIsogeny,
        Hom.ofIsogeny_comp_ofIsogeny] at hcomm
      obtain ⟨ψ, hψ, -⟩ := existsUnique_map_eq_iff_baseChangeFrobenius_comp_eq.mpr
        (Hom.ofIsogeny_injective hcomm)
      have hmap : ψ.map (algebraMap F (SeparableClosure F)) = φ := hψ
      exact ⟨Hom.ofIsogeny ψ, by rw [Hom.mapRingHom_apply, Hom.ofIsogeny_map, hmap]⟩

/-- The comparison with the geometric endomorphism ring acts by base change. -/
@[simp]
theorem geometricEndEquivOfIsOrdinary_apply (hW : W.IsOrdinary p)
    (f : Hom W.toAffine W.toAffine) :
    W.geometricEndEquivOfIsOrdinary hW f = f.map (algebraMap F (SeparableClosure F)) :=
  (RingEquiv.ofBijective_apply _ _ _).trans (Hom.mapRingHom_apply _ _)

/-- Descent recovers an endomorphism from its base change to the separable closure. -/
@[simp]
theorem geometricEndEquivOfIsOrdinary_symm_map (hW : W.IsOrdinary p)
    (f : Hom W.toAffine W.toAffine) :
    (W.geometricEndEquivOfIsOrdinary hW).symm (f.map (algebraMap F (SeparableClosure F))) = f :=
  (congrArg (W.geometricEndEquivOfIsOrdinary hW).symm
    (W.geometricEndEquivOfIsOrdinary_apply hW f)).symm.trans (RingEquiv.symm_apply_apply _ f)

end WeierstrassCurve
