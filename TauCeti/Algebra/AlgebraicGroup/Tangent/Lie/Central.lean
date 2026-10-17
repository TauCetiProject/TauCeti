/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Infinitesimal

/-!
# Central points act trivially on tangent vectors

A universally central point acts trivially on tangent vectors over its value algebra:
conjugation fixes their dual-number points. The proof uses
`Derivation.snd_conjugate_tangentPoint`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, Lie algebras and the adjoint action.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
-/

public section

open TauCeti WithConv TrivSqZeroExt

namespace Derivation

universe u v w

variable {R : Type u} {H : Type v} {B : Type (max v w)} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B]

/-- A universally central point acts trivially on tangent vectors over its value algebra. -/
theorem adDerivation_eq_self_of_isCentralPoint
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    {g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H B)}
    (hg : HopfAlgebra.IsCentralPoint g) : adDerivation B g d = d := by
  let C := Bialgebra.CounitAlgebra R H B
  let p := (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  let q := AlgHom.mapValue (H := H) (inlAlgHom R C C) g
  rw [HopfAlgebra.isCentralPoint_def] at hg
  have hc : q * p * q⁻¹ = p := by
    have hq : Commute q p := hg (inlAlgHom R C C) p
    exact Commute.mul_inv_cancel (G := WithConv (H →ₐ[R] DualNumber C)) hq
  ext a
  have ha := congrArg (fun z ↦ snd (z.ofConv a)) hc
  rw [snd_conjugate_tangentPoint, derivationMulEquivTangentKer_apply_snd] at ha
  exact ha

end Derivation
