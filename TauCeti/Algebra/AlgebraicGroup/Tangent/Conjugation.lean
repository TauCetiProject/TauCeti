/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
import TauCeti.Algebra.DualNumber.Convolution

/-!
# Differentiating universal conjugation

Contracting the first factor of the universal conjugation morphism against a point and
its second factor against a tangent derivation gives the adjoint action of that point.
This coordinate formula allows one to compute infinitesimal conjugation families without
choosing a matrix representation.

In particular, differentiating the inner automorphism `HopfAlgebra.pointConjugationBialgEquiv g`
of a rational point `g` recovers the adjoint action `Derivation.adDerivation B` at `g`
(`TauCeti.derivationComp_pointConjugationBialgEquiv`).

The calculation uses `Derivation.snd_conjugate_tangentPoint` and
`TauCeti.HopfAlgebra.productMap_comp_conjugationAlgHom`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 14.
-/

public section

open TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace Derivation

variable {R H B : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommSemiring B] [Algebra R B]

/-- The adjoint action is obtained by evaluating the conjugating coordinate at the point
and differentiating the acted-on coordinate at the identity. -/
theorem adDerivation_eq_lift_conjugationAlgHom
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H B)) (h : H) :
    adDerivation B g d h =
      TensorProduct.lift ((LinearMap.mul R (Bialgebra.CounitAlgebra R H B)).compl₁₂
        g.ofConv.toLinearMap d.toLinearMap)
        (HopfAlgebra.conjugationAlgHom (R := R) (H := H) h) := by
  let C := Bialgebra.CounitAlgebra R H B
  let q := AlgHom.mapValue (H := H) (inlAlgHom R C C) g
  let p := (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  have hc := AlgHom.congr_fun (HopfAlgebra.productMap_comp_conjugationAlgHom q p) h
  rw [AlgHom.comp_apply] at hc
  rw [← snd_conjugate_tangentPoint d g h, ← hc]
  have hm : (sndHom C C).restrictScalars R ∘ₗ
      (Algebra.TensorProduct.productMap q.ofConv p.ofConv).toLinearMap =
      TensorProduct.lift ((LinearMap.mul R C).compl₁₂
        g.ofConv.toLinearMap d.toLinearMap) := by
    apply TensorProduct.ext'
    intro a b
    have hp : snd (p.ofConv b) = d b :=
      derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) b
    simpa [q] using congrArg (fun x => g.ofConv a * x) hp
  exact LinearMap.congr_fun hm _

end Derivation

namespace TauCeti

variable {R H B : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommSemiring B] [Algebra R B]

/-- **The differential of conjugation by a rational point is the adjoint action.** Precomposing a
counit-valued derivation with the inner automorphism `HopfAlgebra.pointConjugationBialgEquiv g`
gives `Derivation.adDerivation B` at `g` (extended to `Bialgebra.CounitAlgebra R H B`). -/
theorem derivationComp_pointConjugationBialgEquiv
    (g : WithConv (H →ₐ[R] R))
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    derivationComp (B := B) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom d =
      Derivation.adDerivation B
        (AlgHom.mapValue (H := H) (Algebra.ofId R (Bialgebra.CounitAlgebra R H B)) g) d := by
  ext x
  have hcomp :
      derivationComp (B := B) (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom d x =
        d (HopfAlgebra.pointConjugationBialgEquiv g x) :=
    (Bialgebra.CounitAlgebra.algEquivSelf R H B).injective
      (algEquivSelf_derivationComp_apply _ _ _)
  rw [hcomp]
  have hpt : HopfAlgebra.pointConjugationBialgEquiv g x =
      HopfAlgebra.pointConjugationAlgHom g x :=
    DFunLike.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) x
  rw [hpt, ← Derivation.coeFn_coe, LinearMap.apply_pointConjugationAlgHom,
    Derivation.adDerivation_eq_lift_conjugationAlgHom]
  induction HopfAlgebra.conjugationAlgHom (R := R) (H := H) x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, Derivation.coeFn_coe,
      TensorProduct.lid_tmul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
      LinearMap.mul_apply', AlgHom.mapValue_apply, AlgHom.comp_apply, Algebra.ofId_apply,
      Algebra.smul_def]

end TauCeti
