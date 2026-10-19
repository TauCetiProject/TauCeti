/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# Universally invariant tangent vectors

A tangent vector fixed under every adjoint action, after every change of coefficients,
defines a universally central dual-number point. This criterion uses arbitrary value
algebras, including nonreduced ones, and needs neither smoothness nor finite type.

The dual-number dictionary and adjoint calculation are those of
`TauCeti.derivationMulEquivTangentKer` and `Derivation.snd_conjugate_tangentPoint`.
The universal property `DualNumber.lift` allows specialization of the infinitesimal parameter
to any square-zero element, rather than testing centrality only against constant points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, tangent spaces and the adjoint action.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
-/

public section

open TauCeti WithConv TrivSqZeroExt

namespace Derivation

universe u v w

variable {R : Type u} {H : Type v} {B : Type w}
  [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing B] [Algebra R B]

/-- A tangent vector fixed by every adjoint action after every change of coefficients
defines a universally central dual-number point. The coefficient algebras range over all
commutative `R`-algebras in universe `max v w`, including nonreduced ones. -/
theorem isCentralPoint_tangentPoint_of_forall_adDerivation_eq_self
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (hd : ∀ (A : Type (max v w)) [CommRing A] [Algebra R A] (φ : B →ₐ[R] A)
      (g : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H A)),
      adDerivation A g (mapValue φ d) = mapValue φ d) :
    HopfAlgebra.IsCentralPoint
      (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val := by
  rw [HopfAlgebra.isCentralPoint_def]
  intro A _ _ χ h
  let C := Bialgebra.CounitAlgebra R H B
  let D := Bialgebra.CounitAlgebra R H A
  let φ : B →ₐ[R] A :=
    (χ.comp (inlAlgHom R C C)).comp (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toAlgHom
  let g := AlgHom.mapValue (Bialgebra.CounitAlgebra.algEquivSelf R H A).symm.toAlgHom h
  -- Specialize the dual-number parameter to its image under χ. This factors every
  -- value map through a dual-number algebra over the final coefficient ring.
  let e : DualNumber D →ₐ[R] A := DualNumber.lift
    ⟨((Bialgebra.CounitAlgebra.algEquivSelf R H A).toAlgHom, χ DualNumber.eps),
      by rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩
  have hc := ((adDerivation_eq_self_iff_commute_tangentPoint (mapValue φ d) g).mp
    (hd A φ g)).map (AlgHom.mapValue (H := H) e)
  have hg : AlgHom.mapValue (H := H) e
      (AlgHom.mapValue (inlAlgHom R D D) g) = h := by
    apply ofConv_injective
    apply AlgHom.ext
    intro x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, e, g,
      inlAlgHom_apply, DualNumber.lift_apply_inl, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply]
  -- Under this specialization the constant point becomes h and the extended tangent
  -- point becomes the image of the original tangent point.
  have hp : AlgHom.mapValue (H := H) e
      (derivationMulEquivTangentKer R H A (Multiplicative.ofAdd (mapValue φ d))).val =
      AlgHom.mapValue χ
        (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val :=
    mapValue_lift_tangentPoint d χ
  rw [hg, hp] at hc
  exact hc.symm

end Derivation
