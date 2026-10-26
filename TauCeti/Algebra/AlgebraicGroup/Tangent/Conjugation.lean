/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation
import TauCeti.Algebra.DualNumber.Convolution

/-!
# Differentiating universal conjugation

Contracting the first factor of the universal conjugation morphism against a point and
its second factor against a tangent derivation gives the adjoint action of that point.
This coordinate formula allows one to compute infinitesimal conjugation families without
choosing a matrix representation.

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
