/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Central
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# The tangent space of the scheme-theoretic center

The Lie algebra of the center of an affine group over a field consists exactly of the
tangent vectors fixed by every adjoint action after every change of coefficients. This
description retains the scheme-theoretic center in positive characteristic and imposes
no smoothness, connectedness, reducedness or finite-type hypothesis. When the augmentation
cotangent space is finite-dimensional, the same subspace is the fixed subspace of the
adjoint comodule. In positive characteristic, the center of the tangent Lie algebra can
be larger; universal adjoint invariance is the condition relevant to the group center.

The comparison uses `HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff`
to pass between the tangent space of a closed subgroup and its dual-number points, and
`CommHopfAlgCat.mem_centerPointsSubgroup_iff` to recognize universal centrality.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, tangent spaces and the adjoint action.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
-/

public section

open WithConv

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{v} k)
  {B : Type v} [CommRing B] [Algebra k B]

/-- A tangent vector belongs to the Lie algebra of the scheme-theoretic center exactly
when every adjoint action fixes it after every change of coefficients. -/
theorem mem_lieSubalgebra_centerDefiningIdeal_iff_forall_adDerivation_eq_self
    (d : Derivation k H (Bialgebra.CounitAlgebra k H B)) :
    d ∈ (centerDefiningIdeal H).lieSubalgebra (B := B) ↔
      ∀ (A : Type v) [CommRing A] [Algebra k A] (φ : B →ₐ[k] A)
        (g : WithConv (H →ₐ[k] Bialgebra.CounitAlgebra k H A)),
        Derivation.adDerivation A g (Derivation.mapValue φ d) = Derivation.mapValue φ d := by
  constructor
  · intro hd A _ _ φ g
    have hd' : Derivation.mapValue φ d ∈
        (centerDefiningIdeal H).lieSubalgebra (B := A) :=
      (centerDefiningIdeal H).mapValue_mem_lieSubalgebra φ hd
    have hp := (HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff
      (centerDefiningIdeal H) (Derivation.mapValue φ d)).mpr hd'
    have hc : HopfAlgebra.IsCentralPoint
        (derivationMulEquivTangentKer k H A
          (Multiplicative.ofAdd (Derivation.mapValue φ d))).val :=
      (mem_centerPointsSubgroup_iff H _ _).mp hp
    exact (Derivation.adDerivation_eq_self_iff_commute_tangentPoint _ _).mpr
      (hc.commute _).symm
  · intro hd
    apply (HopfIdeal.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff
      (centerDefiningIdeal H) d).mp
    exact (mem_centerPointsSubgroup_iff H _ _).mpr
      (Derivation.isCentralPoint_tangentPoint_of_forall_adDerivation_eq_self d hd)

end CommHopfAlgCat

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat TensorProduct

universe u

variable {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{u} k)
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule

/-- In cotangent-dual coordinates, the Lie algebra of the scheme-theoretic center is
the fixed subspace of the adjoint comodule. Finite-dimensionality is required only of
the augmentation cotangent space, and no characteristic restriction is imposed. -/
theorem coact_adjointComodule_eq_tmul_one_iff_mem_lieSubalgebra_centerDefiningIdeal
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Comodule.coact (R := k) (C := H) x = x ⊗ₜ[k] 1 ↔
      Derivation.cotangentLinearEquiv (B := k) x ∈
        (centerDefiningIdeal H).lieSubalgebra (B := k) := by
  rw [mem_lieSubalgebra_centerDefiningIdeal_iff_forall_adDerivation_eq_self]
  constructor
  · intro hx A _ _ φ g
    have hφ : φ = Algebra.ofId k A := Subsingleton.elim _ _
    subst φ
    let g' := AlgHom.mapValue (Bialgebra.CounitAlgebra.algEquivSelf k H A).toAlgHom g
    have hg : Derivation.pointInCounitAlgebra A g' = g := by
      apply ofConv_injective
      ext a
      simp [Derivation.pointInCounitAlgebra_apply, g', AlgHom.mapValue_apply]
    have hact : Comodule.endOfPoint (Module.Dual k (Bialgebra.CotangentSpace k H))
        g'.ofConv (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by
      simp [Comodule.endOfPoint_tmul, hx]
    have h := congrArg (Derivation.tangentScalarExtensionEquiv
      (R := k) (A := H) (B := A)) hact
    rw [Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
      (CommAlgCat.of k A) g', Derivation.tangentScalarExtensionEquiv_tmul,
      one_smul, hg] at h
    exact h
  · intro hx
    have hact (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (H →ₐ[k] A)) :
        (Derivation.adjointAction (CommAlgCat.of k A) g).val (1 ⊗ₜ[k] x) = 1 ⊗ₜ[k] x := by
      apply (Derivation.tangentScalarExtensionEquiv (R := k) (A := H) (B := A)).injective
      rw [Derivation.tangentScalarExtensionEquiv_adjointAction (CommAlgCat.of k A) g,
        Derivation.tangentScalarExtensionEquiv_tmul, one_smul]
      exact hx A (Algebra.ofId k A) (Derivation.pointInCounitAlgebra A g)
    rw [Derivation.adjointComodule_coact_apply,
      Derivation.adjointPointRepresentation_action, hact]
    simp

end CommHopfAlgCat
