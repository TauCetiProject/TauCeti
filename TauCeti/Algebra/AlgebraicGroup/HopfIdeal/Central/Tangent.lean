/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Infinitesimal

/-!
# Central subgroups and the tangent Lie algebra

The Lie algebra of a central closed subgroup is contained in the center of the ambient
Lie algebra. This holds over commutative rings and with arbitrary coefficient algebras,
without smoothness or reducedness assumptions. In particular it applies to infinitesimal
central subgroups in positive characteristic.

A universally central point acts trivially on tangent vectors: conjugation fixes their
dual-number points. Applied to a tangent point of a central subgroup, the infinitesimal
adjoint formula then says that the Lie bracket vanishes.

The dual-number argument uses `Derivation.snd_conjugate_tangentPoint` and
`Derivation.adDerivation_dualNumber_apply`. The method follows the normal-subgroup
argument in `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Tangent`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, Lie algebras and the adjoint action.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
-/

public section

open TauCeti WithConv TrivSqZeroExt

namespace TauCeti.HopfIdeal

universe u v w

variable {R : Type u} {H : Type v} {B : Type (max v w)} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B] {I : HopfIdeal R H}

/-- The tangent Lie algebra of a central closed subgroup lies in the center of the ambient
Lie algebra, with coefficients in any commutative value algebra. -/
theorem IsCentral.lieSubalgebra_le_center (hI : I.IsCentral) :
    I.lieSubalgebra (B := B) ≤
      (LieAlgebra.center B (Derivation R H (Bialgebra.CounitAlgebra R H B))).toLieSubalgebra := by
  intro d hd
  let C := Bialgebra.CounitAlgebra R H B
  let p := (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  have hp : p ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R (DualNumber C)) :=
    (I.mem_quotientPointsSubgroup_derivationMulEquivTangentKer_iff d).mpr hd
  let g := (Bialgebra.CounitAlgebra.pointsMulEquiv R H (DualNumber C)).symm p
  have hg_eq : g = AlgHom.mapValue
      (Bialgebra.CounitAlgebra.algEquivSelf R H (DualNumber C)).symm.toAlgHom p := by
    apply WithConv.ofConv_injective
    ext x
    simp only [g, Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply,
      AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  have hg : HopfAlgebra.IsCentralPoint g := by
    rw [hg_eq]
    exact (CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of R H) I hI _ hp).mapValue
        (Bialgebra.CounitAlgebra.algEquivSelf R H (DualNumber C)).symm.toAlgHom
  rw [LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule]
  intro e
  have hact := Derivation.adDerivation_eq_self_of_isCentralPoint
    (Derivation.mapValue ((inlAlgHom R C C).comp
      (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toAlgHom) e) hg
  have hbracket : ⁅d, e⁆ = 0 := by
    ext a
    have ha := congrArg (fun z ↦ snd
      (Bialgebra.CounitAlgebra.algEquivSelf R H (DualNumber C) (z a))) hact
    rw [Derivation.adDerivation_dualNumber_apply] at ha
    simp only [snd_add, snd_inl, snd_inr, zero_add] at ha
    -- `mapValue_apply` views `e a : CounitAlgebra R H B` as an element of `B`.
    -- Matching `AlgHom.comp_apply` then needs the synonym's semireducible body,
    -- which `rw` leaves opaque; `erw` unfolds it to compute the constant inl term.
    erw [Derivation.mapValue_apply, AlgHom.comp_apply, inlAlgHom_apply,
      Bialgebra.CounitAlgebra.algEquivSelf_apply, snd_inl] at ha
    exact ha
  rw [← lie_skew, hbracket, neg_zero]

end TauCeti.HopfIdeal
