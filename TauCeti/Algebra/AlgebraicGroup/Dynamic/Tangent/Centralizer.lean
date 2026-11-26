/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.Algebra.AlgebraicGroup.Tangent.Map

/-!
# Dynamic Levi subgroups and centralizers of cocharacter differentials

Let `l : H →ₐc[R] R[T;T⁻¹]` be a cocharacter of an affine group scheme `G = Spec H`. Differentiating
`l` at a tangent vector `b` of `𝔾ₘ` yields a tangent vector of `G` whose associated dual-number
point is `l(1 + ε b)`
(`BialgHom.derivationMulEquivTangentKer_derivationComp_tangentLinearEquiv_symm`).

Over a field `k` where `H` has finite-dimensional augmentation cotangent space, this tangent-point
compatibility shows that every algebra-valued point of the dynamic Levi subgroup `Z_G(l)` commutes
with the dual-number point of the unit tangent differential `h = dl(1)`, so `Z_G(l)` is a closed
subgroup scheme of the centralizer `C_G(h)`
(`BialgHom.centralizerHopfIdeal_le_leviDefiningHopfIdeal`), without requiring characteristic zero.
In characteristic zero, both closed subgroup schemes have the same Lie algebra `ker (ad h)`
(`BialgHom.lieSubalgebra_leviDefiningHopfIdeal_eq_centralizerHopfIdeal`).

## Main declarations

* `BialgHom.derivationMulEquivTangentKer_derivationComp_tangentLinearEquiv_symm`: the dual-number
  tangent point of a cocharacter's differential at `b` is `Cocharacter.pointsHom` at `1 + ε b`.
* `BialgHom.centralizerHopfIdeal_le_leviDefiningHopfIdeal`: the dynamic Levi subgroup `Z_G(l)` is a
  closed subgroup scheme of the centralizer `C_G(dl(1))`.
* `BialgHom.lieSubalgebra_leviDefiningHopfIdeal_eq_centralizerHopfIdeal`: in characteristic zero,
  `Z_G(l)` and `C_G(dl(1))` have the same tangent Lie algebra.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 13.
-/

public section

open TauCeti TauCeti.Cocharacter WithConv

namespace BialgHom

section TangentPoint

variable {R H B : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B]

/-- The dual-number tangent point attached to the differential of a cocharacter `l` on a tangent
vector `b` of `𝔾ₘ` is the image of the dual-number unit `1 + ε b` under `l`. -/
theorem derivationMulEquivTangentKer_derivationComp_tangentLinearEquiv_symm
    (l : H →ₐc[R] LaurentPolynomial R) (b : B) :
    (derivationMulEquivTangentKer R H B
        (Multiplicative.ofAdd (derivationComp (B := B) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm b)))).val =
      Cocharacter.pointsHom (DualNumber (Bialgebra.CounitAlgebra R H B)) l
        (dualNumberUnit ((Bialgebra.CounitAlgebra.algEquivSelf R H B).symm b)) := by
  have hmap := congrArg Subtype.val <|
    tangentKerMap_derivationMulEquivTangentKer (B := B) l
      (Multiplicative.ofAdd ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm b))
  rw [toAdd_ofAdd] at hmap; rw [← hmap, tangentKerMap_apply_val, Cocharacter.pointsHom_apply]
  have hgm :=
    MultiplicativeGroup.derivationMulEquivTangentKer_tangentLinearEquiv_symm (R := R) (B := B) b
  have hb : ((Bialgebra.CounitAlgebra.algEquivSelf R (LaurentPolynomial R) B).symm b :
      Bialgebra.CounitAlgebra R H B) = (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm b := by
    rw [Bialgebra.CounitAlgebra.algEquivSelf_symm_apply,
      Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
  exact (congrArg
    (BialgHom.mapDomain (A := DualNumber (Bialgebra.CounitAlgebra R H B)) l) hgm).trans
    (by rw [hb]; rfl)

end TangentPoint

section Centralizer

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **In characteristic zero, the dynamic Levi subgroup `Z_G(l)` of a cocharacter `l` and the
centralizer `C_G(dl(1))` of its unit tangent differential have the same tangent Lie algebra.** -/
theorem lieSubalgebra_leviDefiningHopfIdeal_eq_centralizerHopfIdeal [CharZero k]
    (l : H →ₐc[k] LaurentPolynomial k) : (leviDefiningHopfIdeal l).lieSubalgebra (B := k) =
      (TauCeti.centralizerHopfIdeal H
        ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm (derivationComp (B := k) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1)))).lieSubalgebra
        (B := k) := by
  apply LieSubalgebra.toSubmodule_injective
  rw [l.lieSubalgebra_leviDefiningHopfIdeal_eq_eigenspace, Module.End.eigenspace_zero,
    TauCeti.lieSubalgebra_centralizerHopfIdeal, LieEquiv.apply_symm_apply]

/-- **The dynamic Levi subgroup `Z_G(l)` of a cocharacter `l` is a closed subgroup scheme of the
centralizer `C_G(dl(1))` of its unit tangent differential** (contravariantly, the centralizer ideal
lies in the Levi ideal). This holds in arbitrary characteristic. -/
theorem centralizerHopfIdeal_le_leviDefiningHopfIdeal (l : H →ₐc[k] LaurentPolynomial k) :
    TauCeti.centralizerHopfIdeal H ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
        (derivationComp (B := k) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1))) ≤
      leviDefiningHopfIdeal l := by
  rw [HopfIdeal.le_iff_forall_quotientPointsSubgroup_le (H := _root_.CommHopfAlgCat.of k H)]
  intro A g hg; rw [quotientPointsSubgroup_leviDefiningHopfIdeal] at hg
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  suffices hker : (TauCeti.centralizerHopfIdeal H
      ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm (derivationComp (B := k) l
        ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1)))).toIdeal ≤
      RingHom.ker g.ofConv from fun a ha ↦ hker (HopfIdeal.mem_toIdeal.mpr ha)
  rw [TauCeti.centralizerHopfIdeal_le_ker_iff, ← Derivation.cotangentDualLieEquiv_apply,
    LieEquiv.apply_symm_apply,
    MultiplicativeGroup.mapValue_derivationComp_tangentLinearEquiv_symm_one,
    Derivation.adDerivation_eq_self_iff_commute_tangentPoint]
  let C := Bialgebra.CounitAlgebra k H A
  let φ : A →ₐ[k] DualNumber C := (TrivSqZeroExt.inlAlgHom k C C).comp
    (Bialgebra.CounitAlgebra.algEquivSelf k H A).symm.toAlgHom
  have hgφ : AlgHom.mapValue (TrivSqZeroExt.inlAlgHom k C C)
      (Derivation.pointInCounitAlgebra A g) = AlgHom.mapValue φ g := by
    apply ofConv_injective; apply AlgHom.ext; intro a
    rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, AlgHom.comp_apply, AlgHom.comp_apply,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Derivation.pointInCounitAlgebra_apply,
      Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
  rw [hgφ, l.derivationMulEquivTangentKer_derivationComp_tangentLinearEquiv_symm (1 : A)]
  exact l.commute_pointsHom_of_mem_levi (Cocharacter.levi_le_comap φ hg)
    (dualNumberUnit ((Bialgebra.CounitAlgebra.algEquivSelf k H A).symm 1))

end Centralizer

end BialgHom
