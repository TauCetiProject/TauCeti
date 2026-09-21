/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Tangent.CounitPoints
import TauCeti.Algebra.DualNumber.Convolution

/-!
# The infinitesimal adjoint action

The differential of the adjoint representation is the adjoint representation of the Lie
algebra. Concretely, the dual-number point associated to a tangent vector `d` acts on a
constant tangent vector `e` by `e + ε[d,e]`. This identifies the convolution commutator
with the infinitesimal change of the group adjoint action, over any commutative base ring.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.d, 10.18–10.23.
-/

public section

namespace TauCeti

open WithConv TrivSqZeroExt

variable {R H B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B]

/-- The adjoint action of the dual-number point of `d` on the constant lift of `e`
is `e + ε[d,e]`. Thus the differential of the group adjoint action is the Lie bracket. -/
-- Apply before the general adjoint and coefficient-map evaluation rules expand the input.
@[simp↓]
theorem adDerivation_dualNumber
    (d e : Derivation R H (Bialgebra.CounitAlgebra R H B)) (a : H) :
    (Bialgebra.CounitAlgebra.algEquivSelf R H
      (DualNumber (Bialgebra.CounitAlgebra R H B)))
      (Derivation.adDerivation (DualNumber (Bialgebra.CounitAlgebra R H B))
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R H
          (DualNumber (Bialgebra.CounitAlgebra R H B))).symm
            (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val)
        (Derivation.mapValue ((inlAlgHom R (Bialgebra.CounitAlgebra R H B)
          (Bialgebra.CounitAlgebra R H B)).comp
            (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toAlgHom) e) a) =
      inl (e a) + inr (⁅d, e⁆ a) := by
  -- The point of `d` has constant coefficient the counit and infinitesimal coefficient `d`.
  let C := Bialgebra.CounitAlgebra R H B
  let p (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :=
    (derivationMulEquivTangentKer R H B (Multiplicative.ofAdd d)).val
  let F := (fstHom R C C).toLinearMap
  let S := (sndHom C C).restrictScalars R
  have hF (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
      F ∘ₗ (p d).ofConv.toLinearMap =
        (1 : WithConv (H →ₗ[R] C)).ofConv := by
    ext x
    simpa only [F, p, C, LinearMap.comp_apply, AlgHom.toLinearMap_apply, fstHom_apply,
      LinearMap.convOne_apply, Bialgebra.CounitAlgebra.algebraMap_apply,
      Bialgebra.CounitAlgebra.algebraMap_base] using
        derivationMulEquivTangentKer_apply_fst (Multiplicative.ofAdd d) x
  have hS (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
      S ∘ₗ (p d).ofConv.toLinearMap = d.toLinearMap := by
    ext x
    dsimp [S, p, C]
    exact derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) x
  have hinv : (p d)⁻¹ = p (-d) := by
    simpa only [p, ← Subgroup.coe_inv, ← ofAdd_neg] using congrArg Subtype.val
      (map_inv (derivationMulEquivTangentKer R H B) (Multiplicative.ofAdd d)).symm
  let c := (Bialgebra.CounitAlgebra.algEquivSelf R H (DualNumber C)).toAlgHom
  let E := c.toLinearMap ∘ₗ (Derivation.mapValue ((inlAlgHom R C C).comp
    (Bialgebra.CounitAlgebra.algEquivSelf R H B).symm.toAlgHom) e).toLinearMap
  have hFE : F ∘ₗ E = e.toLinearMap := by
    ext x
    dsimp [F, E, c]
    -- The evaluation lemmas identify the exported counit-algebra type synonyms.
    erw [Derivation.mapValue_apply, AlgHom.comp_apply, inlAlgHom_apply,
      Bialgebra.CounitAlgebra.algEquivSelf_apply, fstHom_apply, fst_inl,
      Bialgebra.CounitAlgebra.algEquivSelf_symm_apply]
  have hSE : S ∘ₗ E = 0 := by
    ext x
    dsimp [S, E, c]
    -- As above, evaluate through the counit coefficient identification.
    erw [Derivation.mapValue_apply, AlgHom.comp_apply, inlAlgHom_apply,
      Bialgebra.CounitAlgebra.algEquivSelf_apply, sndHom_apply, snd_inl]
  dsimp only [F] at hF hFE
  dsimp only [S] at hS hSE
  -- Apply the convolution product rule to `(1 + εd) e (1 - εd)`.
  have hprodF : F ∘ₗ
      (toConv (p d).ofConv.toLinearMap * toConv E *
        toConv (p (-d)).ofConv.toLinearMap).ofConv = e.toLinearMap := by
    simp only [F, LinearMap.algHom_comp_convMul_distrib, toConv_ofConv]
    rw [hF, hF, hFE]
    simp
  have hprodS : S ∘ₗ
      (toConv (p d).ofConv.toLinearMap * toConv E *
        toConv (p (-d)).ofConv.toLinearMap).ofConv = (⁅d, e⁆).toLinearMap := by
    rw [snd_comp_convMul, snd_comp_convMul]
    rw [LinearMap.algHom_comp_convMul_distrib]
    simp only [toConv_ofConv, hF, hS, hFE, hSE, Derivation.coe_neg_linearMap,
      toConv_neg, toConv_zero, mul_zero, zero_add, one_mul, mul_one,
      Derivation.coe_bracket, sub_eq_add_neg, ofConv_add]
    have hneg := congrArg WithConv.ofConv
      (mul_neg (toConv e.toLinearMap) (toConv d.toLinearMap))
    rw [hneg, ofConv_neg, add_comm]
  -- Transport the point and action back through the coefficient-algebra equivalence.
  have hc (g : WithConv (H →ₐ[R] DualNumber C)) :
      c.toLinearMap ∘ₗ
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R H (DualNumber C)).symm g).ofConv.toLinearMap =
          g.ofConv.toLinearMap := by
    apply LinearMap.ext
    intro x
    dsimp only [c, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply]
    exact AlgEquiv.apply_symm_apply _ _
  rw [Derivation.adDerivation_apply]
  -- Postcompose convolution by the coefficient equivalence to calculate in actual dual numbers.
  rw [← AlgEquiv.toAlgHom_apply, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply]
  simp only [LinearMap.algHom_comp_convMul_distrib, toConv_ofConv]
  erw [← map_inv (Bialgebra.CounitAlgebra.pointsMulEquiv R H (DualNumber C)).symm (p d)]
  rw [hc, hc]
  rw [hinv]
  -- Expand the local coefficient transport in the computed product coefficients.
  dsimp only [E, c] at hprodF hprodS
  apply TrivSqZeroExt.ext
  · simpa only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, fstHom_apply,
      Derivation.coeFn_coe, fst_add, fst_inl, fst_inr, add_zero] using
        DFunLike.congr_fun hprodF a
  · simpa only [S, LinearMap.comp_apply, LinearMap.restrictScalars_apply, sndHom_apply,
      Derivation.coeFn_coe, snd_add, snd_inl, snd_inr, zero_add] using
        DFunLike.congr_fun hprodS a

end TauCeti
