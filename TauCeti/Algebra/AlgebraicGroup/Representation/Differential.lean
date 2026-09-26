/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction

/-!
# Differentiating a comodule representation

A right comodule over a commutative bialgebra carries a representation of its tangent
Lie algebra at the identity. A counit-valued derivation acts by contraction of the coaction.
This is the infinitesimal part of the existing action on dual-number points, and comodule
morphisms intertwine the differentiated actions.

The construction works over any commutative ring, for comodules of arbitrary rank, without
smoothness or an antipode. For coordinate Hopf algebras it differentiates rational group
representations, providing the passage to Lie-algebra representations used in complete
reducibility arguments.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§3 and 12.
-/

public section

namespace TauCeti.Comodule

open WithConv TensorProduct

variable {R H M N : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]
variable [AddCommGroup N] [Module R N] [Comodule R H N]

section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The differentiated representation of a comodule: contract its coaction against a
counit-valued derivation. -/
noncomputable def differential :
    Derivation R H (Bialgebra.CounitAlgebra R H R) →ₗ⁅R⁆ Module.End R M where
  toFun d := convolutionAction (R := R) (C := H) (M := M) (toConv
    ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap))
  map_add' d e := by
    simp only [Derivation.coe_add_linearMap, LinearMap.comp_add, toConv_add, map_add]
  map_smul' r d := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    apply ofConv_injective
    ext x
    exact algEquivSelf_derivation_smul_apply r d x
  map_lie' {d e} := by
    let a := (Bialgebra.CounitAlgebra.algEquivSelf R H R).toAlgHom
    have h : toConv (a.toLinearMap ∘ₗ (⁅d, e⁆).toLinearMap) =
        toConv (a.toLinearMap ∘ₗ d.toLinearMap) *
            toConv (a.toLinearMap ∘ₗ e.toLinearMap) -
          toConv (a.toLinearMap ∘ₗ e.toLinearMap) *
            toConv (a.toLinearMap ∘ₗ d.toLinearMap) := by
      rw [Derivation.coe_bracket, LinearMap.comp_sub,
        LinearMap.algHom_comp_convMul_distrib, LinearMap.algHom_comp_convMul_distrib,
        toConv_sub, toConv_ofConv, toConv_ofConv]
    simp only [a, AlgEquiv.toAlgHom_toLinearMap] at h
    rw [h, map_sub, map_mul, map_mul, LieRing.of_associative_ring_bracket]

end

/-- The action of a tangent vector is contraction of the coaction by its underlying functional. -/
@[simp]
theorem differential_apply (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    differential (R := R) (H := H) (M := M) d m = LinearMap.tensorComponent
      ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap)
      (coact (R := R) (C := H) m) := by
  simp [differential]

/-- Every comodule morphism intertwines the differentiated representations. -/
theorem Hom.map_differential (f : Hom R H M N)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    f (differential (R := R) (H := H) (M := M) d m) =
      differential (R := R) (H := H) (M := N) d (f m) :=
  f.map_convolutionAction _ m

/-- The coefficient of `ε` in the action of a tangent dual-number point on `1 ⊗ m`
is the differentiated action on `m`. The counit coefficient algebra is identified with `R`
by its canonical algebra equivalence. -/
theorem snd_endOfPoint_derivationToDualNumberEquivLift
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (m : M) :
    TensorProduct.lid R M
      (LinearMap.rTensor M
        ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ
          (TrivSqZeroExt.sndHom (Bialgebra.CounitAlgebra R H R)
            (Bialgebra.CounitAlgebra R H R)).restrictScalars R)
        (endOfPoint M (derivationToDualNumberEquivLift R H
          (Bialgebra.CounitAlgebra R H R) d).val (1 ⊗ₜ[R] m))) =
      differential (R := R) (H := H) (M := M) d m := by
  rw [endOfPoint_tmul, differential_apply]
  induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.smul_add, hx, hy]
  | tmul n h =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, one_mul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TrivSqZeroExt.sndHom_apply,
      AlgHom.toLinearMap_apply, derivationToDualNumberEquivLift_apply_snd,
      Derivation.coeFn_coe, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, LinearMap.tensorComponent_tmul]

end TauCeti.Comodule
